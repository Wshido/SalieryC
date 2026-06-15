#include <windows.h>
#include <mmdeviceapi.h>
#include <audioclient.h>
#include <audiopolicy.h>
#include <functiondiscoverykeys_devpkey.h>
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <locale.h>

#define SAMPLE_RATE 16000
#define FRAME_LEN 512
#define FRAME_SHIFT 160
#define NUM_MFCC 13
#define NUM_MEL_FILTERS 26
#define FFT_SIZE 512
#define MAX_FRAMES 500
#define MAX_TEMPLATES 100
#define MAX_TEMPLATE_NAME 64
#define TEMPLATE_FILE L"templates.bin"

static const double PI = 3.14159265358979323846;

typedef struct {
    char name[MAX_TEMPLATE_NAME];
    double** mfcc;
    int numFrames;
} Template;

static Template g_templates[MAX_TEMPLATES];
static int g_templateCount = 0;

static HRESULT wasapi_init(IAudioClient** ppClient, IAudioCaptureClient** ppCapture) {
    HRESULT hr;
    IMMDeviceEnumerator* pEnum = NULL;
    IMMDevice* pDevice = NULL;
    WAVEFORMATEX* pwfx = NULL;

    hr = CoCreateInstance(__uuidof(MMDeviceEnumerator), NULL, CLSCTX_ALL,
        IID_PPV_ARGS(&pEnum));
    if (FAILED(hr)) return hr;

    hr = pEnum->GetDefaultAudioEndpoint(eCapture, eConsole, &pDevice);
    pEnum->Release();
    if (FAILED(hr)) return hr;

    hr = pDevice->Activate(__uuidof(IAudioClient), CLSCTX_ALL, NULL, (void**)ppClient);
    if (FAILED(hr)) { pDevice->Release(); return hr; }

    hr = (*ppClient)->GetMixFormat(&pwfx);
    if (FAILED(hr)) { (*ppClient)->Release(); pDevice->Release(); return hr; }

    WAVEFORMATEX wf = {};
    wf.wFormatTag = WAVE_FORMAT_PCM;
    wf.nChannels = 1;
    wf.nSamplesPerSec = SAMPLE_RATE;
    wf.wBitsPerSample = 16;
    wf.nBlockAlign = 2;
    wf.nAvgBytesPerSec = SAMPLE_RATE * 2;

    hr = (*ppClient)->Initialize(AUDCLNT_SHAREMODE_SHARED,
        0, 0, 0, pwfx, NULL);
    CoTaskMemFree(pwfx);
    if (FAILED(hr)) { (*ppClient)->Release(); pDevice->Release(); return hr; }

    hr = (*ppClient)->GetService(IID_PPV_ARGS(ppCapture));
    pDevice->Release();
    return hr;
}

static void fft(double* real, double* imag, int n) {
    int j = 0;
    for (int i = 0; i < n - 1; i++) {
        if (i < j) {
            double t = real[i]; real[i] = real[j]; real[j] = t;
            t = imag[i]; imag[i] = imag[j]; imag[j] = t;
        }
        int m = n >> 1;
        while (m >= 1 && j >= m) { j -= m; m >>= 1; }
        j += m;
    }
    for (int step = 2; step <= n; step <<= 1) {
        int half = step >> 1;
        double angle = -2.0 * PI / step;
        double wR = cos(angle), wI = sin(angle);
        for (int i = 0; i < n; i += step) {
            double curR = 1.0, curI = 0.0;
            for (int k = 0; k < half; k++) {
                int a = i + k, b = i + k + half;
                double tR = curR * real[b] - curI * imag[b];
                double tI = curR * imag[b] + curI * real[b];
                real[b] = real[a] - tR;
                imag[b] = imag[a] - tI;
                real[a] += tR;
                imag[a] += tI;
                double newR = curR * wR - curI * wI;
                curI = curR * wI + curI * wR;
                curR = newR;
            }
        }
    }
}

static double hzToMel(double hz) { return 2595.0 * log10(1.0 + hz / 700.0); }
static double melToHz(double mel) { return 700.0 * (pow(10.0, mel / 2595.0) - 1.0); }

static double* extractMFCC(double* frame, int frameLen, double* prevMFCC) {
    static double melBank[NUM_MEL_FILTERS][FFT_SIZE / 2 + 1];

    static int initialized = 0;
    if (!initialized) {
        double melLow = hzToMel(0);
        double melHigh = hzToMel(SAMPLE_RATE / 2.0);
        double melPoints[NUM_MEL_FILTERS + 2];
        for (int i = 0; i < NUM_MEL_FILTERS + 2; i++)
            melPoints[i] = melToHz(melLow + i * (melHigh - melLow) / (NUM_MEL_FILTERS + 1));

        int binPoints[NUM_MEL_FILTERS + 2];
        for (int i = 0; i < NUM_MEL_FILTERS + 2; i++)
            binPoints[i] = (int)(melPoints[i] * FFT_SIZE / SAMPLE_RATE + 0.5);

        for (int m = 0; m < NUM_MEL_FILTERS; m++) {
            for (int k = binPoints[m]; k < binPoints[m + 1]; k++)
                melBank[m][k] = (double)(k - binPoints[m]) / (binPoints[m + 1] - binPoints[m]);
            for (int k = binPoints[m + 1]; k < binPoints[m + 2]; k++)
                melBank[m][k] = (double)(binPoints[m + 2] - k) / (binPoints[m + 2] - binPoints[m + 1]);
        }
        initialized = 1;
    }

    double win[FFT_SIZE];
    for (int i = 0; i < frameLen && i < FFT_SIZE; i++)
        win[i] = frame[i] * (0.54 - 0.46 * cos(2.0 * PI * i / (frameLen - 1)));
    for (int i = frameLen; i < FFT_SIZE; i++) win[i] = 0;

    double real[FFT_SIZE], imag[FFT_SIZE];
    for (int i = 0; i < FFT_SIZE; i++) { real[i] = win[i]; imag[i] = 0; }
    fft(real, imag, FFT_SIZE);

    double power[FFT_SIZE / 2 + 1];
    for (int i = 0; i <= FFT_SIZE / 2; i++)
        power[i] = real[i] * real[i] + imag[i] * imag[i];

    double melEnergies[NUM_MEL_FILTERS];
    for (int m = 0; m < NUM_MEL_FILTERS; m++) {
        melEnergies[m] = 0;
        for (int k = 0; k <= FFT_SIZE / 2; k++)
            melEnergies[m] += power[k] * melBank[m][k];
        if (melEnergies[m] < 1e-22) melEnergies[m] = 1e-22;
        melEnergies[m] = log(melEnergies[m]);
    }

    double* mfcc = (double*)malloc(NUM_MFCC * sizeof(double));
    for (int i = 0; i < NUM_MFCC; i++) {
        mfcc[i] = 0;
        for (int j = 0; j < NUM_MEL_FILTERS; j++)
            mfcc[i] += melEnergies[j] * cos(PI * i * (2 * j + 1) / (2.0 * NUM_MEL_FILTERS));
        mfcc[i] *= sqrt(2.0 / NUM_MEL_FILTERS);
    }

    if (prevMFCC) {
        double delta[NUM_MFCC];
        for (int i = 0; i < NUM_MFCC; i++)
            delta[i] = mfcc[i] - prevMFCC[i];
        double* result = (double*)malloc((NUM_MFCC * 2) * sizeof(double));
        for (int i = 0; i < NUM_MFCC; i++) {
            result[i] = mfcc[i];
            result[NUM_MFCC + i] = delta[i];
        }
        free(mfcc);
        return result;
    }
    return mfcc;
}

static double dtw(double** seq1, int len1, double** seq2, int len2, int dim) {
    double** dist = (double**)malloc((len1 + 1) * sizeof(double*));
    for (int i = 0; i <= len1; i++) {
        dist[i] = (double*)malloc((len2 + 1) * sizeof(double));
        for (int j = 0; j <= len2; j++) dist[i][j] = 1e18;
    }
    dist[0][0] = 0;

    for (int i = 1; i <= len1; i++) {
        for (int j = 1; j <= len2; j++) {
            double d = 0;
            for (int k = 0; k < dim; k++) {
                double diff = seq1[i-1][k] - seq2[j-1][k];
                d += diff * diff;
            }
            d = sqrt(d);
            double minPrev = dist[i-1][j];
            if (dist[i][j-1] < minPrev) minPrev = dist[i][j-1];
            if (dist[i-1][j-1] < minPrev) minPrev = dist[i-1][j-1];
            dist[i][j] = d + minPrev;
        }
    }

    double result = dist[len1][len2] / (len1 + len2);
    for (int i = 0; i <= len1; i++) free(dist[i]);
    free(dist);
    return result;
}

static int captureAudio(IAudioCaptureClient* pCapture, double** outSignal, int* outLen) {
    HRESULT hr;
    UINT32 packetSize = 0;
    BYTE* pData;
    UINT32 numFrames;
    DWORD flags;

    Sleep(200);

    hr = pCapture->GetNextPacketSize(&packetSize);
    if (FAILED(hr) || packetSize == 0) return 0;

    int maxSamples = SAMPLE_RATE * 5;
    short* buffer = (short*)malloc(maxSamples * sizeof(short));
    int totalSamples = 0;

    while (totalSamples < maxSamples) {
        hr = pCapture->GetBuffer(&pData, &numFrames, &flags, NULL, NULL);
        if (FAILED(hr) || numFrames == 0) break;

        if (!(flags & AUDCLNT_BUFFERFLAGS_SILENT)) {
            for (UINT32 i = 0; i < numFrames && totalSamples < maxSamples; i++) {
                buffer[totalSamples++] = ((short*)pData)[i];
            }
        }
        pCapture->ReleaseBuffer(numFrames);
        pCapture->GetNextPacketSize(&packetSize);
        if (packetSize == 0) {
            Sleep(50);
            hr = pCapture->GetNextPacketSize(&packetSize);
            if (FAILED(hr) || packetSize == 0) break;
        }
    }

    *outLen = totalSamples;
    *outSignal = (double*)malloc(totalSamples * sizeof(double));
    for (int i = 0; i < totalSamples; i++)
        (*outSignal)[i] = buffer[i] / 32768.0;
    free(buffer);
    return 1;
}

static double** extractFeatures(double* signal, int sigLen, int* outFrames) {
    int numFrames = (sigLen - FRAME_LEN) / FRAME_SHIFT + 1;
    if (numFrames > MAX_FRAMES) numFrames = MAX_FRAMES;
    if (numFrames < 1) { *outFrames = 0; return NULL; }

    double** features = (double**)malloc(numFrames * sizeof(double*));
    double prevMFCC[NUM_MFCC * 2] = {};

    for (int f = 0; f < numFrames; f++) {
        int start = f * FRAME_SHIFT;
        double frame[FRAME_LEN];
        for (int i = 0; i < FRAME_LEN; i++) {
            if (start + i < sigLen) frame[i] = signal[start + i];
            else frame[i] = 0;
        }
        if (f == 0)
            features[f] = extractMFCC(frame, FRAME_LEN, NULL);
        else {
            features[f] = extractMFCC(frame, FRAME_LEN, prevMFCC);
        }
        for (int i = 0; i < NUM_MFCC * 2; i++)
            prevMFCC[i] = features[f][i];
    }
    *outFrames = numFrames;
    return features;
}

static void saveTemplates(void) {
    FILE* f;
    _wfopen_s(&f, TEMPLATE_FILE, L"wb");
    if (!f) return;
    fwrite(&g_templateCount, sizeof(int), 1, f);
    for (int i = 0; i < g_templateCount; i++) {
        fwrite(g_templates[i].name, sizeof(char), MAX_TEMPLATE_NAME, f);
        fwrite(&g_templates[i].numFrames, sizeof(int), 1, f);
        for (int j = 0; j < g_templates[i].numFrames; j++)
            fwrite(g_templates[i].mfcc[j], sizeof(double), NUM_MFCC * 2, f);
    }
    fclose(f);
}

static void loadTemplates(void) {
    FILE* f;
    _wfopen_s(&f, TEMPLATE_FILE, L"rb");
    if (!f) return;
    fread(&g_templateCount, sizeof(int), 1, f);
    if (g_templateCount > MAX_TEMPLATES) g_templateCount = MAX_TEMPLATES;
    for (int i = 0; i < g_templateCount; i++) {
        fread(g_templates[i].name, sizeof(char), MAX_TEMPLATE_NAME, f);
        fread(&g_templates[i].numFrames, sizeof(int), 1, f);
        g_templates[i].mfcc = (double**)malloc(g_templates[i].numFrames * sizeof(double*));
        for (int j = 0; j < g_templates[i].numFrames; j++) {
            g_templates[i].mfcc[j] = (double*)malloc(NUM_MFCC * 2 * sizeof(double));
            fread(g_templates[i].mfcc[j], sizeof(double), NUM_MFCC * 2, f);
        }
    }
    fclose(f);
}

static int recognize(double** features, int numFrames) {
    if (g_templateCount == 0 || numFrames == 0) return -1;
    int bestIdx = -1;
    double bestDist = 1e18;
    for (int i = 0; i < g_templateCount; i++) {
        double dist = dtw(features, numFrames, g_templates[i].mfcc, g_templates[i].numFrames, NUM_MFCC * 2);
        if (dist < bestDist) {
            bestDist = dist;
            bestIdx = i;
        }
    }
    if (bestDist > 15.0) return -1;
    return bestIdx;
}

static void listDevices(void) {
    IMMDeviceEnumerator* pEnum = NULL;
    IMMDeviceCollection* pColl = NULL;
    CoCreateInstance(__uuidof(MMDeviceEnumerator), NULL, CLSCTX_ALL, IID_PPV_ARGS(&pEnum));
    if (!pEnum) return;
    pEnum->EnumAudioEndpoints(eCapture, DEVICE_STATE_ACTIVE, &pColl);
    if (!pColl) { pEnum->Release(); return; }

    UINT count = 0;
    pColl->GetCount(&count);
    printf("  : %u\n", count);
    for (UINT i = 0; i < count; i++) {
        IMMDevice* pDev = NULL;
        pColl->Item(i, &pDev);
        if (pDev) {
            IPropertyStore* pProps = NULL;
            pDev->OpenPropertyStore(STGM_READ, &pProps);
            if (pProps) {
                PROPVARIANT varName;
                PropVariantInit(&varName);
                pProps->GetValue(PKEY_Device_FriendlyName, &varName);
                if (varName.vt == VT_LPWSTR)
                    wprintf(L"  [%u] %s\n", i, varName.pwszVal);
                PropVariantClear(&varName);
                pProps->Release();
            }
            pDev->Release();
        }
    }
    pColl->Release();
    pEnum->Release();
}

int main(void) {
    setlocale(LC_ALL, "");
    SetConsoleOutputCP(65001);
    SetConsoleCP(65001);

    printf("========================================\n");
    printf("     (  )\n");
    printf("========================================\n");
    printf(" WASAPI +  + MFCC + DTW\n");
    printf("   Microsoft Speech API\n\n");

    CoInitializeEx(NULL, COINIT_APARTMENTTHREADED);

    loadTemplates();
    printf(" : %d\n\n", g_templateCount);

    listDevices();

    printf("\n:\n");
    printf("  1 -  \n");
    printf("  2 -  \n");
    printf("  3 -  \n");
    printf("  4 -   \n");
    printf("  5 -  \n");
    printf("  0 - \n\n");

    IAudioClient* pClient = NULL;
    IAudioCaptureClient* pCapture = NULL;
    HRESULT hr = wasapi_init(&pClient, &pCapture);
    if (FAILED(hr)) {
        printf("!  : 0x%08X\n", hr);
        CoUninitialize();
        return 1;
    }
    printf(" !\n\n");

    int running = 1;
    while (running) {
        printf("> ");
        char cmd[32];
        if (!fgets(cmd, sizeof(cmd), stdin)) break;
        cmd[strcspn(cmd, "\n")] = 0;

        if (strcmp(cmd, "0") == 0) {
            running = 0;
        }
        else if (strcmp(cmd, "1") == 0) {
            if (g_templateCount >= MAX_TEMPLATES) {
                printf(" ! (%d)\n", MAX_TEMPLATES);
                continue;
            }
            printf("  : ");
            char name[MAX_TEMPLATE_NAME];
            if (!fgets(name, sizeof(name), stdin)) continue;
            name[strcspn(name, "\n")] = 0;
            if (strlen(name) == 0) continue;

            printf(" ... ()...\n");
            double* signal = NULL;
            int sigLen = 0;
            if (!captureAudio(pCapture, &signal, &sigLen) || sigLen < SAMPLE_RATE / 4) {
                printf("  !\n");
                free(signal);
                continue;
            }
            printf(" : %d \n", sigLen / SAMPLE_RATE);

            int numFrames = 0;
            double** features = extractFeatures(signal, sigLen, &numFrames);
            free(signal);

            if (!features || numFrames == 0) {
                printf("  !\n");
                continue;
            }

            Template* t = &g_templates[g_templateCount];
            strncpy_s(t->name, MAX_TEMPLATE_NAME, name, _TRUNCATE);
            t->mfcc = features;
            t->numFrames = numFrames;
            g_templateCount++;
            saveTemplates();
            printf(" '%s'  ! ( : %d)\n\n", name, g_templateCount);
        }
        else if (strcmp(cmd, "2") == 0) {
            if (g_templateCount == 0) {
                printf("  !\n\n");
                continue;
            }
            printf(" :\n");
            for (int i = 0; i < g_templateCount; i++)
                printf("  [%d] %s (%d )\n", i, g_templates[i].name, g_templates[i].numFrames);
            printf("\n  : ");
            char numStr[16];
            if (!fgets(numStr, sizeof(numStr), stdin)) continue;
            int idx = atoi(numStr);
            if (idx < 0 || idx >= g_templateCount) {
                printf(" !\n\n");
                continue;
            }
            free(g_templates[idx].mfcc);
            for (int i = idx; i < g_templateCount - 1; i++)
                g_templates[i] = g_templates[i + 1];
            g_templateCount--;
            saveTemplates();
            printf(" ! ( : %d)\n\n", g_templateCount);
        }
        else if (strcmp(cmd, "3") == 0) {
            printf(" ... ()...\n");
            double* signal = NULL;
            int sigLen = 0;
            if (!captureAudio(pCapture, &signal, &sigLen) || sigLen < SAMPLE_RATE / 4) {
                printf("  !\n");
                free(signal);
                continue;
            }
            printf(" : %d \n\n", sigLen / SAMPLE_RATE);

            int numFrames = 0;
            double** features = extractFeatures(signal, sigLen, &numFrames);
            free(signal);

            if (!features || numFrames == 0) {
                printf("  !\n");
                continue;
            }

            int result = recognize(features, numFrames);
            if (result >= 0) {
                printf(": \"%s\"\n", g_templates[result].name);
                double dist = dtw(features, numFrames,
                    g_templates[result].mfcc, g_templates[result].numFrames, NUM_MFCC * 2);
                printf(": %.2f\n", dist);
            } else {
                printf("  !\n");
            }
            for (int i = 0; i < numFrames; i++) free(features[i]);
            free(features);
            printf("\n");
        }
        else if (strcmp(cmd, "4") == 0) {
            printf(" ... (  )...\n");
            printf("Ctrl+C  \n\n");
            while (1) {
                double* signal = NULL;
                int sigLen = 0;
                if (!captureAudio(pCapture, &signal, &sigLen) || sigLen < SAMPLE_RATE / 4) {
                    free(signal);
                    continue;
                }

                int numFrames = 0;
                double** features = extractFeatures(signal, sigLen, &numFrames);
                free(signal);

                if (!features || numFrames == 0) continue;

                int result = recognize(features, numFrames);
                if (result >= 0) {
                    printf("\r: \"%s\"              ", g_templates[result].name);
                } else {
                    printf("\r...                          ");
                }
                for (int i = 0; i < numFrames; i++) free(features[i]);
                free(features);
            }
        }
        else if (strcmp(cmd, "5") == 0) {
            listDevices();
            printf("\n");
        }
        else {
            printf(" !\n\n");
        }
    }

    pCapture->Release();
    pClient->Release();
    CoUninitialize();
    printf("!\n");
    return 0;
}
