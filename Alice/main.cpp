#include <windows.h>
#include <windowsx.h>
#include <shlwapi.h>
#include <objbase.h>
#include <wincodec.h>
#include <shellapi.h>
#include <process.h>
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdarg.h>
#include <mmdeviceapi.h>
#include <audioclient.h>
#include <functiondiscoverykeys_devpkey.h>

#define ID_SIZE_200 200
#define ID_SIZE_300 300
#define ID_SIZE_450 450
#define ID_SIZE_600 600
#define ID_OPEN_BROWSER 1001
#define ID_OPEN_VALORANT 1002
#define ID_OPEN_ADGUARD 1003
#define ID_OPEN_YANDEX 1004
#define WM_POPUP_SHOW (WM_USER + 10)
#define WM_STATUS_SHOW (WM_USER + 12)
#define WM_ANSWER_SHOW (WM_USER + 15)
#define MAX_GIFS 64
#define MAX_FRAMES 256
#define SAMPLE_RATE 16000
#define FRAME_LEN 512
#define FRAME_SHIFT 160
#define NUM_MFCC 13
#define NUM_MEL 26
#define FFT_N 512
#define DTW_THRESH 8.0
#define ENERGY_MIN 600.0
#define COOLDOWN_MS 3000
#define NUM_RECORDS 5

static const double DPI = 3.141592653589793;
static HWND g_hWnd, g_popupWnd, g_statusWnd;
static int g_currentIdx, g_displaySize = 300, g_winW, g_winH;
static IWICImagingFactory* g_pWIC;
static IWICBitmapDecoder* g_pDecoder;
static int g_frames, g_frameCur, *g_frameDelay;
static HBITMAP g_cached[MAX_FRAMES];
static int g_cachedW[MAX_FRAMES], g_cachedH[MAX_FRAMES];
static int g_gifCount;
static wchar_t g_paths[MAX_GIFS][MAX_PATH];
static wchar_t g_names[MAX_GIFS][MAX_PATH];
static volatile int g_speechRunning = 1;

#define NUM_CMDS 10
static const wchar_t* CMD_PHRASES[NUM_CMDS] = {
    L"\x044d\x043b\x0438\x0441 \x043e\x0442\x0432\x0435\x0442\x044c",
    L"\x044d\x043b\x0438\x0441 \x043e\x0442\x043a\x0440\x043e\x0439 \x044f\x043d\x0434\x0435\x043a\x0441 \x043c\x0443\x0437\x044b\x043a\x0443",
    L"\x044d\x043b\x0438\x0441 \x043e\x0442\x043a\x0440\x043e\x0439 \x0431\x0440\x0430\x0443\x0437\x0435\x0440",
    L"\x044d\x043b\x0438\x0441 \x043e\x0442\x043a\x0440\x043e\x0439 \x0432\x0430\x043b\x043e\x0440\x0430\x043d\x0442",
    L"\x044d\x043b\x0438\x0441 \x043e\x0442\x043a\x0440\x043e\x0439 \x0430\x0434\x0433\x0430\x0440\x0434",
    L"\x044d\x043b\x0438\x0441 \x0441\x043a\x043e\x043b\x044c\x043a\x043e \x0432\x0440\x0435\x043c\x0435\x043d\x0438",
    L"\x044d\x043b\x0438\x0441 \x043a\x0430\x043a\x043e\x0439 \x0441\x0435\x0433\x043e\x0434\x043d\x044f \x0434\x0435\x043d\x044c",
    L"\x044d\x043b\x0438\x0441 \x043a\x0442\x043e \x0442\x044b",
    L"\x044d\x043b\x0438\x0441 \x0441\x043f\x0430\x0441\x0438\x0431\x043e",
    L"\x044d\x043b\x0438\x0441 \x043f\x043e\x043a\x0430 \x0437\x0430\x043a\x0440\x043e\x0439",
};
static const char* CMD_ACTIONS[NUM_CMDS] = {
    "popup", "yandex", "browser", "valorant", "adguard",
    "time", "date", "whoami", "thanks", "close"
};

static double** g_phraseMFCC[NUM_CMDS][NUM_RECORDS];
static int g_phraseFrames[NUM_CMDS][NUM_RECORDS];
static int g_phraseCount[NUM_CMDS];

static void logMsg(const char* fmt, ...) {
    FILE* f; fopen_s(&f, "speech_log.txt", "a");
    if (!f) return;
    va_list args; va_start(args, fmt);
    vfprintf_s(f, fmt, args); va_end(args);
    fprintf(f, "\n"); fclose(f);
}

static double hz2mel(double h) { return 2595.0 * log10(1.0 + h / 700.0); }
static double mel2hz(double m) { return 700.0 * (pow(10.0, m / 2595.0) - 1.0); }

static void fft(double* re, double* im, int n) {
    int j = 0;
    for (int i = 0; i < n - 1; i++) {
        if (i < j) { double t = re[i]; re[i] = re[j]; re[j] = t; t = im[i]; im[i] = im[j]; im[j] = t; }
        int m = n >> 1;
        while (m >= 1 && j >= m) { j -= m; m >>= 1; }
        j += m;
    }
    for (int s = 2; s <= n; s <<= 1) {
        int h = s >> 1;
        double a = -2.0 * DPI / s, wR = cos(a), wI = sin(a);
        for (int i = 0; i < n; i += s) {
            double cR = 1.0, cI = 0.0;
            for (int k = 0; k < h; k++) {
                int u = i + k, v = i + k + h;
                double tR = cR * re[v] - cI * im[v], tI = cR * im[v] + cI * re[v];
                re[v] = re[u] - tR; im[v] = im[u] - tI;
                re[u] += tR; im[u] += tI;
                double nR = cR * wR - cI * wI; cI = cR * wI + cI * wR; cR = nR;
            }
        }
    }
}

static double* calcMFCC(double* frame, int len) {
    static double mb[NUM_MEL][FFT_N / 2 + 1];
    static int inited = 0;
    if (!inited) {
        double mL = hz2mel(0), mH = hz2mel(SAMPLE_RATE / 2.0);
        double mp[NUM_MEL + 2]; int bp[NUM_MEL + 2];
        for (int i = 0; i < NUM_MEL + 2; i++) mp[i] = mel2hz(mL + i * (mH - mL) / (NUM_MEL + 1));
        for (int i = 0; i < NUM_MEL + 2; i++) bp[i] = (int)(mp[i] * FFT_N / SAMPLE_RATE + 0.5);
        for (int m = 0; m < NUM_MEL; m++) {
            for (int k = bp[m]; k < bp[m + 1]; k++) mb[m][k] = (double)(k - bp[m]) / (bp[m + 1] - bp[m]);
            for (int k = bp[m + 1]; k < bp[m + 2]; k++) mb[m][k] = (double)(bp[m + 2] - k) / (bp[m + 2] - bp[m + 1]);
        }
        inited = 1;
    }
    double w[FFT_N];
    for (int i = 0; i < len && i < FFT_N; i++) w[i] = frame[i] * (0.54 - 0.46 * cos(2.0 * DPI * i / (len - 1)));
    for (int i = len; i < FFT_N; i++) w[i] = 0;
    double re[FFT_N], im[FFT_N];
    for (int i = 0; i < FFT_N; i++) { re[i] = w[i]; im[i] = 0; }
    fft(re, im, FFT_N);
    double pw[FFT_N / 2 + 1];
    for (int i = 0; i <= FFT_N / 2; i++) pw[i] = re[i] * re[i] + im[i] * im[i];
    double me[NUM_MEL];
    for (int m = 0; m < NUM_MEL; m++) {
        me[m] = 0;
        for (int k = 0; k <= FFT_N / 2; k++) me[m] += pw[k] * mb[m][k];
        if (me[m] < 1e-22) me[m] = 1e-22;
        me[m] = log(me[m]);
    }
    double* mfcc = (double*)malloc(NUM_MFCC * sizeof(double));
    for (int i = 0; i < NUM_MFCC; i++) {
        mfcc[i] = 0;
        for (int j = 0; j < NUM_MEL; j++)
            mfcc[i] += me[j] * cos(DPI * i * (2 * j + 1) / (2.0 * NUM_MEL));
        mfcc[i] *= sqrt(2.0 / NUM_MEL);
    }
    return mfcc;
}

static double dtw(double** s1, int l1, double** s2, int l2) {
    double** d = (double**)malloc((l1 + 1) * sizeof(double*));
    for (int i = 0; i <= l1; i++) {
        d[i] = (double*)malloc((l2 + 1) * sizeof(double));
        for (int j = 0; j <= l2; j++) d[i][j] = 1e18;
    }
    d[0][0] = 0;
    for (int i = 1; i <= l1; i++)
        for (int j = 1; j <= l2; j++) {
            double dist = 0;
            for (int k = 0; k < NUM_MFCC; k++) {
                double diff = s1[i-1][k] - s2[j-1][k];
                dist += diff * diff;
            }
            dist = sqrt(dist);
            double mn = d[i-1][j];
            if (d[i][j-1] < mn) mn = d[i][j-1];
            if (d[i-1][j-1] < mn) mn = d[i-1][j-1];
            d[i][j] = dist + mn;
        }
    double r = d[l1][l2] / (l1 + l2);
    for (int i = 0; i <= l1; i++) free(d[i]);
    free(d);
    return r;
}

static double** extractMFCC(short* buf, int total, int* outN) {
    int n = (total - FRAME_LEN) / FRAME_SHIFT + 1;
    if (n > 300) n = 300;
    if (n < 3) { *outN = 0; return NULL; }
    double** feat = (double**)malloc(n * sizeof(double*));
    for (int f = 0; f < n; f++) {
        double frame[FRAME_LEN];
        int st = f * FRAME_SHIFT;
        for (int i = 0; i < FRAME_LEN; i++)
            frame[i] = (st + i < total) ? buf[st + i] / 32768.0 : 0;
        feat[f] = calcMFCC(frame, FRAME_LEN);
    }
    *outN = n;
    return feat;
}

static void freeMFCC(double** mfcc, int n) {
    for (int i = 0; i < n; i++) free(mfcc[i]);
    free(mfcc);
}

static double audioEnergy(short* buf, int n) {
    double e = 0;
    for (int i = 0; i < n; i++) e += (double)buf[i] * buf[i];
    return sqrt(e / n);
}

static double speechRatio(short* buf, int total) {
    int speechMs = 0;
    int chunk = SAMPLE_RATE / 10;
    for (int i = 0; i < total; i += chunk) {
        int len = (i + chunk < total) ? chunk : total - i;
        if (audioEnergy(buf + i, len) > ENERGY_MIN) speechMs += 100;
    }
    int totalMs = total * 1000 / SAMPLE_RATE;
    return totalMs > 0 ? (double)speechMs / totalMs : 0;
}

static short* trimSilence(short* buf, int total, int* outN) {
    int chunk = SAMPLE_RATE / 20;
    int start = 0, end = total;
    double trimThresh = ENERGY_MIN * 1.5;

    for (int i = 0; i < total; i += chunk) {
        int len = (i + chunk < total) ? chunk : total - i;
        if (audioEnergy(buf + i, len) > trimThresh) { start = i; break; }
    }
    for (int i = total; i > start; i -= chunk) {
        int from = i - chunk; if (from < start) from = start;
        int len = i - from;
        if (audioEnergy(buf + from, len) > trimThresh) { end = i; break; }
    }

    int newLen = end - start;
    if (newLen < SAMPLE_RATE / 8) { *outN = 0; return NULL; }

    short* trimmed = (short*)malloc(newLen * sizeof(short));
    memcpy(trimmed, buf + start, newLen * sizeof(short));
    logMsg("  Trimmed: %d -> %d (%.1fs -> %.1fs)",
        total, newLen, (double)total / SAMPLE_RATE, (double)newLen / SAMPLE_RATE);
    *outN = newLen;
    return trimmed;
}

static void savePhraseBin(int idx) {
    char fname[64]; sprintf_s(fname, "cmd_%d.bin", idx);
    FILE* f; fopen_s(&f, fname, "wb");
    if (!f) return;
    fwrite(&g_phraseCount[idx], sizeof(int), 1, f);
    for (int r = 0; r < g_phraseCount[idx]; r++) {
        fwrite(&g_phraseFrames[idx][r], sizeof(int), 1, f);
        for (int i = 0; i < g_phraseFrames[idx][r]; i++)
            fwrite(g_phraseMFCC[idx][r][i], sizeof(double), NUM_MFCC, f);
    }
    fclose(f);
}

static int loadPhraseBin(int idx) {
    char fname[64]; sprintf_s(fname, "cmd_%d.bin", idx);
    FILE* f; fopen_s(&f, fname, "rb");
    if (!f) return 0;
    int cnt; fread(&cnt, sizeof(int), 1, f);
    if (cnt < 1 || cnt > NUM_RECORDS) { fclose(f); return 0; }
    g_phraseCount[idx] = cnt;
    for (int r = 0; r < cnt; r++) {
        int n; fread(&n, sizeof(int), 1, f);
        if (n > 500 || n < 1) { fclose(f); g_phraseCount[idx] = 0; return 0; }
        g_phraseMFCC[idx][r] = (double**)malloc(n * sizeof(double*));
        for (int i = 0; i < n; i++) {
            g_phraseMFCC[idx][r][i] = (double*)malloc(NUM_MFCC * sizeof(double));
            fread(g_phraseMFCC[idx][r][i], sizeof(double), NUM_MFCC, f);
        }
        g_phraseFrames[idx][r] = n;
    }
    fclose(f);
    return 1;
}

static HRESULT wasapiCapture(short** outBuf, int* outSamples, int durationMs) {
    HRESULT hr;
    IMMDeviceEnumerator* pEnum = NULL;
    IMMDevice* pDevice = NULL;
    IAudioClient* pClient = NULL;
    IAudioCaptureClient* pCapture = NULL;

    hr = CoCreateInstance(__uuidof(MMDeviceEnumerator), NULL, CLSCTX_ALL, IID_PPV_ARGS(&pEnum));
    if (FAILED(hr)) { logMsg("ERR: CoCreateInstance 0x%08X", hr); return hr; }
    hr = pEnum->GetDefaultAudioEndpoint(eCapture, eConsole, &pDevice);
    if (FAILED(hr)) { logMsg("ERR: GetDefaultAudioEndpoint 0x%08X", hr); pEnum->Release(); return hr; }
    pEnum->Release();

    hr = pDevice->Activate(__uuidof(IAudioClient), CLSCTX_ALL, NULL, (void**)&pClient);
    pDevice->Release();
    if (FAILED(hr)) { logMsg("ERR: Activate 0x%08X", hr); return hr; }

    WAVEFORMATEX* pwfx = NULL;
    hr = pClient->GetMixFormat(&pwfx);
    if (FAILED(hr) || !pwfx) { logMsg("ERR: GetMixFormat 0x%08X", hr); pClient->Release(); return hr; }

    WAVEFORMATEX fmt = *pwfx;
    if (pwfx->wFormatTag == WAVE_FORMAT_EXTENSIBLE) {
        WAVEFORMATEXTENSIBLE* ext = (WAVEFORMATEXTENSIBLE*)pwfx;
        fmt.wFormatTag = ext->SubFormat.Data1;
    }
    logMsg("Device: %uHz %uch tag=%u", pwfx->nSamplesPerSec, pwfx->nChannels, fmt.wFormatTag);

    hr = pClient->Initialize(AUDCLNT_SHAREMODE_SHARED, 0, 0, 0, pwfx, NULL);
    CoTaskMemFree(pwfx);
    if (FAILED(hr)) { logMsg("ERR: Initialize 0x%08X", hr); pClient->Release(); return hr; }

    hr = pClient->GetService(IID_PPV_ARGS(&pCapture));
    if (FAILED(hr)) { logMsg("ERR: GetService 0x%08X", hr); pClient->Release(); return hr; }

    hr = pClient->Start();
    if (FAILED(hr)) { logMsg("ERR: Start 0x%08X", hr); pCapture->Release(); pClient->Release(); return hr; }
    Sleep(200);

    int maxBytes = (int)((long long)SAMPLE_RATE * durationMs / 1000) * fmt.nBlockAlign;
    BYTE* raw = (BYTE*)malloc(maxBytes);
    int got = 0;
    int silence = 0;

    while (got < maxBytes) {
        BYTE* pData; UINT32 nFrames; DWORD flags;
        hr = pCapture->GetBuffer(&pData, &nFrames, &flags, NULL, NULL);
        if (FAILED(hr) || nFrames == 0) break;
        if (!(flags & AUDCLNT_BUFFERFLAGS_SILENT)) {
            int bytes = nFrames * fmt.nBlockAlign;
            if (got + bytes <= maxBytes) { memcpy(raw + got, pData, bytes); got += bytes; }
        }
        pCapture->ReleaseBuffer(nFrames);
        UINT32 ps = 0; pCapture->GetNextPacketSize(&ps);
        if (ps == 0) { silence++; if (silence > 10) break; Sleep(20); }
        else silence = 0;
    }

    pClient->Stop(); pCapture->Release(); pClient->Release();

    int totalS = got / fmt.nBlockAlign;
    short* out = (short*)malloc(totalS * sizeof(short));

    if (fmt.wFormatTag == WAVE_FORMAT_PCM) {
        if (fmt.wBitsPerSample == 16)
            for (int i = 0; i < totalS; i++) out[i] = ((short*)raw)[i];
        else if (fmt.wBitsPerSample == 32)
            for (int i = 0; i < totalS; i++) out[i] = (short)(((int*)raw)[i] >> 16);
    } else {
        float* f = (float*)raw;
        for (int i = 0; i < totalS; i++) {
            float v = f[i] * 32767.0f;
            out[i] = (short)(v > 32767 ? 32767 : v < -32768 ? -32768 : v);
        }
    }

    int monoN = totalS;
    short* mono = out;
    if (fmt.nChannels > 1) {
        monoN = totalS / fmt.nChannels;
        mono = (short*)malloc(monoN * sizeof(short));
        for (int i = 0; i < monoN; i++) {
            int sum = 0;
            for (int ch = 0; ch < (int)fmt.nChannels; ch++) sum += out[i * fmt.nChannels + ch];
            mono[i] = (short)(sum / fmt.nChannels);
        }
        free(out);
    }

    int resN = monoN;
    short* res = mono;
    if (fmt.nSamplesPerSec != SAMPLE_RATE) {
        double ratio = (double)SAMPLE_RATE / fmt.nSamplesPerSec;
        resN = (int)(monoN * ratio);
        res = (short*)malloc(resN * sizeof(short));
        for (int i = 0; i < resN; i++) {
            double sp = i / ratio; int idx = (int)sp; double frac = sp - idx;
            if (idx + 1 < monoN) res[i] = (short)(mono[idx] * (1.0 - frac) + mono[idx + 1] * frac);
            else if (idx < monoN) res[i] = mono[idx]; else res[i] = 0;
        }
        free(mono);
    }
    free(raw);

    double energy = audioEnergy(res, resN);
    logMsg("Captured %d samples (%.1fs) energy=%.0f", resN, (double)resN / SAMPLE_RATE, energy);

    *outBuf = res;
    *outSamples = resN;
    return S_OK;
}

static void listMicDevices(void) {
    IMMDeviceEnumerator* pEnum = NULL;
    IMMDeviceCollection* pColl = NULL;
    CoCreateInstance(__uuidof(MMDeviceEnumerator), NULL, CLSCTX_ALL, IID_PPV_ARGS(&pEnum));
    if (!pEnum) return;
    pEnum->EnumAudioEndpoints(eCapture, DEVICE_STATE_ACTIVE, &pColl);
    pEnum->Release();
    if (!pColl) return;
    UINT count = 0; pColl->GetCount(&count);
    logMsg("Mics: %u", count);
    for (UINT i = 0; i < count; i++) {
        IMMDevice* pDev = NULL; pColl->Item(i, &pDev);
        if (!pDev) continue;
        IPropertyStore* pProps = NULL;
        pDev->OpenPropertyStore(STGM_READ, &pProps);
        if (pProps) {
            PROPVARIANT v; PropVariantInit(&v);
            pProps->GetValue(PKEY_Device_FriendlyName, &v);
            if (v.vt == VT_LPWSTR) logMsg("  [%u] %ls", i, v.pwszVal);
            PropVariantClear(&v); pProps->Release();
        }
        pDev->Release();
    }
    pColl->Release();
}

static void showAnswer(const wchar_t* text) {
    PostMessage(g_hWnd, WM_ANSWER_SHOW, (WPARAM)_wcsdup(text), 0);
}

static void executeAction(const char* action) {
    if (strcmp(action, "popup") == 0) {
        PostMessage(g_hWnd, WM_POPUP_SHOW, 0, 0);
    } else if (strcmp(action, "yandex") == 0) {
        ShellExecuteW(NULL, L"open", L"%LOCALAPPDATA%\\Programs\\YandexMusic\\\x042f\x043d\x0434\x0435\x043a\x0441 \x041c\x0443\x0437\x044b\x043a\x0430.exe", NULL, NULL, SW_SHOWNORMAL);
        showAnswer(L"\x041e\x0442\x043a\x0440\x044b\x0432\x0430\x044e \x042f\x043d\x0434\x0435\x043a\x0441 \x041c\x0443\x0437\x044b\x043a\x0443");
    } else if (strcmp(action, "browser") == 0) {
        ShellExecuteW(NULL, L"open", L"https://www.google.com", NULL, NULL, SW_SHOWNORMAL);
        showAnswer(L"\x041e\x0442\x043a\x0440\x044b\x0432\x0430\x044e \x0431\x0440\x0430\x0443\x0437\x0435\x0440");
    } else if (strcmp(action, "valorant") == 0) {
        wchar_t b[MAX_PATH]; ExpandEnvironmentStringsW(L"C:\\Riot Games\\VALORANT\\live\\VALORANT.exe", b, MAX_PATH);
        ShellExecuteW(NULL, L"open", b, NULL, NULL, SW_SHOWNORMAL);
        showAnswer(L"\x0417\x0430\x043f\x0443\x0441\x043a\x0430\x044e VALORANT");
    } else if (strcmp(action, "adguard") == 0) {
        wchar_t b[MAX_PATH]; ExpandEnvironmentStringsW(L"C:\\Program Files\\AdGuardVpn\\AdGuardVpn.exe", b, MAX_PATH);
        ShellExecuteW(NULL, L"open", b, NULL, NULL, SW_SHOWNORMAL);
        showAnswer(L"\x041e\x0442\x043a\x0440\x044b\x0432\x0430\x044e AdGuard VPN");
    } else if (strcmp(action, "time") == 0) {
        SYSTEMTIME st; GetLocalTime(&st);
        wchar_t buf[64]; wsprintfW(buf, L"%02d:%02d", st.wHour, st.wMinute);
        showAnswer(buf);
    } else if (strcmp(action, "date") == 0) {
        SYSTEMTIME st; GetLocalTime(&st);
        const wchar_t* days[] = {L"\x0412\x043e\x0441\x043a\x0440",L"\x041f\x043d",L"\x0412\x0442",
            L"\x0421\x0440",L"\x0427\x0442",L"\x041f\x0442",L"\x0421\x0431"};
        const wchar_t* months[] = {L"",L"\x044f\x043d\x0432",L"\x0444\x0435\x0432",L"\x043c\x0430\x0440",
            L"\x0430\x043f\x0440",L"\x043c\x0430\x0439",L"\x0438\x044e\x043d",L"\x0438\x044e\x043b",
            L"\x0430\x0432\x0433",L"\x0441\x0435\x043d",L"\x043e\x043a\x0442",L"\x043d\x043e\x044f"};
        wchar_t buf[128]; wsprintfW(buf, L"%s %d %s", days[st.wDayOfWeek], st.wDay, months[st.wMonth]);
        showAnswer(buf);
    } else if (strcmp(action, "whoami") == 0) {
        showAnswer(L"\x042f \x042d\x043b\x0438\x0441 \x2014 \x0433\x043e\x043b\x043e\x0441\x043e\x0432\x043e\x0439 \x0430\x0441\x0441\x0438\x0441\x0442\x0435\x043d\x0442!");
    } else if (strcmp(action, "thanks") == 0) {
        showAnswer(L"\x041f\x043e\x0436\x0430\x043b\x0443\x0439\x0441\x0442\x0430!");
    } else if (strcmp(action, "close") == 0) {
        PostMessage(g_hWnd, WM_CLOSE, 0, 0);
    }
}

static unsigned __stdcall SpeechThread(void* param) {
    (void)param;
    FILE* fl; fopen_s(&fl, "speech_log.txt", "w"); if (fl) fclose(fl);

    CoInitializeEx(NULL, COINIT_MULTITHREADED);
    listMicDevices();

    logMsg("Recording %d phrases x %d...", NUM_CMDS, NUM_RECORDS);
    for (int i = 0; i < NUM_CMDS; i++) {
        if (loadPhraseBin(i)) { logMsg("Cmd %d cached (%d recs)", i, g_phraseCount[i]); continue; }

        g_phraseCount[i] = 0;
        for (int r = 0; r < NUM_RECORDS; r++) {
            wchar_t ws[256];
            wsprintfW(ws, L"%d/%d: %s", r + 1, NUM_RECORDS, CMD_PHRASES[i]);
            PostMessage(g_hWnd, WM_STATUS_SHOW, (WPARAM)_wcsdup(ws), 0);

            short* buf = NULL; int total = 0;
            HRESULT hr = wasapiCapture(&buf, &total, 2500);

            if (SUCCEEDED(hr) && buf && total > 1000) {
                double energy = audioEnergy(buf, total);
                double ratio = speechRatio(buf, total);
                logMsg("Rec[%d][%d]: energy=%.0f speech=%.0f%%", i, r, energy, ratio * 100);

                int trimmedN = 0;
                short* trimmed = trimSilence(buf, total, &trimmedN);
                free(buf);
                buf = trimmed;
                total = trimmedN;

                if (buf && total >= 800) {
                    int nFeat = 0;
                    double** feat = extractMFCC(buf, total, &nFeat);
                    free(buf);
                    if (feat && nFeat >= 3) {
                        g_phraseMFCC[i][g_phraseCount[i]] = feat;
                        g_phraseFrames[i][g_phraseCount[i]] = nFeat;
                        g_phraseCount[i]++;
                        logMsg("  Template %d saved: %d frames", g_phraseCount[i], nFeat);
                    } else { if (feat) freeMFCC(feat, nFeat); }
                } else { if (buf) free(buf); }
            } else { if (buf) free(buf); }
            Sleep(500);
        }
        if (g_phraseCount[i] > 0) savePhraseBin(i);
        wchar_t wd[128]; wsprintfW(wd, L"OK: %s (%d/%d)", CMD_PHRASES[i], g_phraseCount[i], NUM_RECORDS);
        PostMessage(g_hWnd, WM_STATUS_SHOW, (WPARAM)_wcsdup(wd), 0);
        logMsg("Cmd %d: %d templates saved", i, g_phraseCount[i]);
    }

    PostMessage(g_hWnd, WM_STATUS_SHOW, (WPARAM)_wcsdup(L"Listening..."), 0);
    logMsg("=== Listening ===");

    DWORD lastAction = 0;
    while (g_speechRunning) {
        short* buf = NULL; int total = 0;
        HRESULT hr = wasapiCapture(&buf, &total, 1500);
        if (FAILED(hr) || !buf || total < 1000) {
            if (buf) free(buf);
            Sleep(100);
            continue;
        }

        double energy = audioEnergy(buf, total);
        double ratio = speechRatio(buf, total);
        logMsg("Listen: energy=%.0f speech=%.0f%%", energy, ratio * 100);
        if (energy < ENERGY_MIN || ratio < 0.15) {
            free(buf);
            continue;
        }

        int trimmedN = 0;
        short* trimmed = trimSilence(buf, total, &trimmedN);
        free(buf);
        buf = trimmed;
        total = trimmedN;
        if (!buf || total < 1000) { if (buf) free(buf); continue; }

        int nFeat = 0;
        double** feat = extractMFCC(buf, total, &nFeat);
        free(buf);
        if (!feat || nFeat < 3) { if (feat) freeMFCC(feat, nFeat); continue; }

        int bestIdx = -1;
        double bestDist = 1e18;
        double secondBest = 1e18;
        for (int i = 0; i < NUM_CMDS; i++) {
            for (int r = 0; r < g_phraseCount[i]; r++) {
                double d = dtw(feat, nFeat, g_phraseMFCC[i][r], g_phraseFrames[i][r]);
                if (d < bestDist) { secondBest = bestDist; bestDist = d; bestIdx = i; }
                else if (d < secondBest) { secondBest = d; }
            }
        }
        freeMFCC(feat, nFeat);

        double confidence = secondBest > 0 ? bestDist / secondBest : 0;
        logMsg("Best[%d] dist=%.1f 2nd=%.1f conf=%.2f", bestIdx, bestDist, secondBest, confidence);

        DWORD now = GetTickCount();
        if (bestIdx >= 0 && bestDist < DTW_THRESH && confidence < 0.7 && (now - lastAction) > COOLDOWN_MS) {
            logMsg(">>> MATCH '%ls' dist=%.1f conf=%.2f", CMD_PHRASES[bestIdx], bestDist, confidence);
            PostMessage(g_hWnd, WM_STATUS_SHOW, (WPARAM)_wcsdup(CMD_PHRASES[bestIdx]), 0);
            executeAction(CMD_ACTIONS[bestIdx]);
            lastAction = now;
        }
    }

    CoUninitialize();
    return 0;
}

/* ============ GIF viewer ============ */

static void ScanGifs(void) {
    wchar_t exe[MAX_PATH], dir[MAX_PATH], search[MAX_PATH];
    WIN32_FIND_DATAW fd;
    g_gifCount = 0;
    GetModuleFileNameW(NULL, exe, MAX_PATH);
    PathRemoveFileSpecW(exe);
    wsprintfW(dir, L"%s\\", exe);
    wsprintfW(search, L"%sgifs\\*.gif", dir);
    HANDLE hFind = FindFirstFileW(search, &fd);
    if (hFind == INVALID_HANDLE_VALUE) return;
    do {
        if (!(fd.dwFileAttributes & FILE_ATTRIBUTE_DIRECTORY) && g_gifCount < MAX_GIFS) {
            wsprintfW(g_paths[g_gifCount], L"%sgifs\\%s", dir, fd.cFileName);
            wcscpy_s(g_names[g_gifCount], MAX_PATH, fd.cFileName);
            g_gifCount++;
        }
    } while (FindNextFileW(hFind, &fd));
    FindClose(hFind);
}

static void FreeGif(void) {
    for (int i = 0; i < MAX_FRAMES; i++)
        if (g_cached[i]) { DeleteObject(g_cached[i]); g_cached[i] = NULL; }
    if (g_pDecoder) { g_pDecoder->Release(); g_pDecoder = NULL; }
    if (g_frameDelay) { free(g_frameDelay); g_frameDelay = NULL; }
    g_frames = g_frameCur = 0;
}

static void CacheAllFrames(void) {
    if (!g_pDecoder) return;
    for (int i = 0; i < g_frames && i < MAX_FRAMES; i++) {
        IWICBitmapFrameDecode* pFrame = NULL; IWICFormatConverter* pConv = NULL;
        if (FAILED(g_pDecoder->GetFrame(i, &pFrame)) || !pFrame) continue;
        if (FAILED(g_pWIC->CreateFormatConverter(&pConv)) || !pConv) { pFrame->Release(); continue; }
        if (FAILED(pConv->Initialize(pFrame, GUID_WICPixelFormat32bppPBGRA,
            WICBitmapDitherTypeNone, NULL, 0.0, WICBitmapPaletteTypeCustom))) { pConv->Release(); pFrame->Release(); continue; }
        UINT w = 0, h = 0; pConv->GetSize(&w, &h);
        if (!w || !h) { pConv->Release(); pFrame->Release(); continue; }
        BITMAPINFO bmi = {}; bmi.bmiHeader.biSize = sizeof(BITMAPINFOHEADER);
        bmi.bmiHeader.biWidth = (LONG)w; bmi.bmiHeader.biHeight = -(LONG)h;
        bmi.bmiHeader.biPlanes = 1; bmi.bmiHeader.biBitCount = 32; bmi.bmiHeader.biCompression = BI_RGB;
        void* bits = NULL; HDC hdc = GetDC(NULL);
        HBITMAP hBmp = CreateDIBSection(hdc, &bmi, DIB_RGB_COLORS, &bits, NULL, 0);
        ReleaseDC(NULL, hdc);
        if (hBmp && bits && SUCCEEDED(pConv->CopyPixels(NULL, w * 4, w * h * 4, (BYTE*)bits))) {
            DWORD* px = (DWORD*)bits;
            for (int j = 0; j < (int)(w * h); j++) if (px[j] & 0x00FFFFFF) px[j] |= 0xFF000000;
            g_cached[i] = hBmp; g_cachedW[i] = (int)w; g_cachedH[i] = (int)h;
        } else if (hBmp) DeleteObject(hBmp);
        pConv->Release(); pFrame->Release();
    }
}

static void RenderFrame(void) {
    if (g_frameCur >= g_frames) return;
    HBITMAP hSrc = g_cached[g_frameCur];
    int srcW = g_cachedW[g_frameCur], srcH = g_cachedH[g_frameCur];
    if (!hSrc || !srcW || !srcH) return;
    double sc = (double)g_displaySize / (srcW > srcH ? srcW : srcH);
    int dW = (int)(srcW * sc), dH = (int)(srcH * sc);
    if (dW < 1) dW = 1; if (dH < 1) dH = 1;
    int nW = dW + 80, nH = dH + 80;
    if (nW != g_winW || nH != g_winH) {
        g_winW = nW; g_winH = nH;
        RECT rc = { 0, 0, g_winW, g_winH };
        AdjustWindowRectEx(&rc, WS_POPUP, FALSE, WS_EX_LAYERED);
        SetWindowPos(g_hWnd, NULL, 0, 0, rc.right - rc.left, rc.bottom - rc.top,
            SWP_NOMOVE | SWP_NOZORDER | SWP_NOACTIVATE);
    }
    HDC hdcS = GetDC(NULL); HDC hdcM = CreateCompatibleDC(hdcS);
    BITMAPINFO bmi = {}; bmi.bmiHeader.biSize = sizeof(BITMAPINFOHEADER);
    bmi.bmiHeader.biWidth = g_winW; bmi.bmiHeader.biHeight = -g_winH;
    bmi.bmiHeader.biPlanes = 1; bmi.bmiHeader.biBitCount = 32; bmi.bmiHeader.biCompression = BI_RGB;
    void* pBits = NULL;
    HBITMAP hL = CreateDIBSection(hdcS, &bmi, DIB_RGB_COLORS, &pBits, NULL, 0);
    HGDIOBJ hO = SelectObject(hdcM, hL);
    HDC hdcG = CreateCompatibleDC(hdcM); HGDIOBJ hOG = SelectObject(hdcG, hSrc);
    int ox = (g_winW - dW) / 2, oy = (g_winH - dH) / 2;
    SetStretchBltMode(hdcM, HALFTONE);
    StretchBlt(hdcM, ox, oy, dW, dH, hdcG, 0, 0, srcW, srcH, SRCCOPY);
    SelectObject(hdcG, hOG); DeleteDC(hdcG);
    if (pBits) { DWORD* px = (DWORD*)pBits; int t = g_winW * g_winH;
        for (int i = 0; i < t; i++) if (px[i] & 0x00FFFFFF) px[i] |= 0xFF000000; }
    POINT pt = { 0, 0 }; SIZE sz = { g_winW, g_winH };
    BLENDFUNCTION bf = { AC_SRC_OVER, 0, 255, AC_SRC_ALPHA };
    UpdateLayeredWindow(g_hWnd, hdcS, NULL, &sz, hdcM, &pt, 0, &bf, ULW_ALPHA);
    SelectObject(hdcM, hO); DeleteObject(hL); DeleteDC(hdcM); ReleaseDC(NULL, hdcS);
}

static void LoadGif(void) {
    UINT fc = 0; FreeGif();
    if (!g_gifCount) return;
    if (FAILED(g_pWIC->CreateDecoderFromFilename(g_paths[g_currentIdx], NULL,
        GENERIC_READ, WICDecodeMetadataCacheOnLoad, &g_pDecoder)) || !g_pDecoder) return;
    g_pDecoder->GetFrameCount(&fc); g_frames = (int)fc;
    if (!g_frames) return;
    g_frameDelay = (int*)calloc(g_frames, sizeof(int));
    for (int i = 0; i < g_frames; i++) g_frameDelay[i] = 100;
    CacheAllFrames(); g_frameCur = 0; RenderFrame();
}

static void CALLBACK GifTimer(HWND h, UINT, UINT_PTR, DWORD) {
    if (g_frames <= 1) return;
    g_frameCur = (g_frameCur + 1) % g_frames; RenderFrame();
}

static void StartAnim(void) {
    KillTimer(g_hWnd, 1);
    if (g_frames > 1 && g_frameDelay) SetTimer(g_hWnd, 1, g_frameDelay[0], GifTimer);
}

static void ShowPopup(const wchar_t* text) {
    if (!g_popupWnd) {
        WNDCLASSEXW wc = { sizeof(wc) }; wc.lpfnWndProc = DefWindowProcW;
        wc.hInstance = GetModuleHandle(NULL); wc.hbrBackground = CreateSolidBrush(RGB(20, 20, 35));
        wc.lpszClassName = L"AlicePopup"; wc.hCursor = LoadCursor(NULL, IDC_ARROW);
        RegisterClassExW(&wc);
        g_popupWnd = CreateWindowExW(WS_EX_LAYERED | WS_EX_TOPMOST, L"AlicePopup", NULL,
            WS_POPUP, 0, 0, 220, 50, NULL, NULL, GetModuleHandle(NULL), NULL);
        SetLayeredWindowAttributes(g_popupWnd, 0, 245, LWA_ALPHA);
    }
    RECT rc; GetWindowRect(g_hWnd, &rc);
    SetWindowPos(g_popupWnd, NULL, rc.left + (rc.right - rc.left) / 2 - 110, rc.top - 60,
        220, 50, SWP_NOACTIVATE | SWP_SHOWWINDOW);
    HDC hdc = GetDC(g_popupWnd); HDC hm = CreateCompatibleDC(hdc);
    BITMAPINFO bi = {}; bi.bmiHeader.biSize = sizeof(BITMAPINFOHEADER);
    bi.bmiHeader.biWidth = 220; bi.bmiHeader.biHeight = -50;
    bi.bmiHeader.biPlanes = 1; bi.bmiHeader.biBitCount = 32; bi.bmiHeader.biCompression = BI_RGB;
    HBITMAP hB = CreateDIBSection(hdc, &bi, DIB_RGB_COLORS, NULL, NULL, 0);
    HGDIOBJ hOld = SelectObject(hm, hB);
    HBRUSH bg = CreateSolidBrush(RGB(20, 20, 35)); RECT full = { 0, 0, 220, 50 };
    FillRect(hm, &full, bg); DeleteObject(bg);
    SetBkMode(hm, TRANSPARENT); SetTextColor(hm, RGB(100, 255, 180));
    HFONT hf = CreateFontW(22, 0, 0, 0, FW_BOLD, 0, 0, 0, DEFAULT_CHARSET, 0, 0, CLEARTYPE_QUALITY, 0, L"Segoe UI");
    SelectObject(hm, hf); RECT tr = { 0, 0, 220, 50 };
    DrawTextW(hm, text, -1, &tr, DT_CENTER | DT_VCENTER);
    DeleteObject(hf); BitBlt(hdc, 0, 0, 220, 50, hm, 0, 0, SRCCOPY);
    SelectObject(hm, hOld); DeleteObject(hB); DeleteDC(hm); ReleaseDC(g_popupWnd, hdc);
    KillTimer(g_hWnd, 2);
    SetTimer(g_hWnd, 2, 3000, [](HWND h, UINT, UINT_PTR, DWORD) {
        if (g_popupWnd) ShowWindow(g_popupWnd, SW_HIDE); KillTimer(h, 2);
    });
}

static void ShowAnswerPopup(const wchar_t* text) {
    if (!g_popupWnd) {
        WNDCLASSEXW wc = { sizeof(wc) }; wc.lpfnWndProc = DefWindowProcW;
        wc.hInstance = GetModuleHandle(NULL); wc.hbrBackground = CreateSolidBrush(RGB(20, 20, 35));
        wc.lpszClassName = L"AlicePopup"; wc.hCursor = LoadCursor(NULL, IDC_ARROW);
        RegisterClassExW(&wc);
        g_popupWnd = CreateWindowExW(WS_EX_LAYERED | WS_EX_TOPMOST, L"AlicePopup", NULL,
            WS_POPUP, 0, 0, 100, 50, NULL, NULL, GetModuleHandle(NULL), NULL);
        SetLayeredWindowAttributes(g_popupWnd, 0, 245, LWA_ALPHA);
    }
    HDC hdc = GetDC(g_popupWnd);
    HFONT hf = CreateFontW(22, 0, 0, 0, FW_BOLD, 0, 0, 0, DEFAULT_CHARSET, 0, 0, CLEARTYPE_QUALITY, 0, L"Segoe UI");
    HGDIOBJ hfo = SelectObject(hdc, hf);
    SetBkMode(hdc, TRANSPARENT); SetTextColor(hdc, RGB(100, 255, 180));
    RECT trc = { 0, 0, 0, 0 }; DrawTextW(hdc, text, -1, &trc, DT_CALCRECT);
    int pw = trc.right - trc.left + 60; if (pw < 120) pw = 120;
    SelectObject(hdc, hfo); DeleteObject(hf); ReleaseDC(g_popupWnd, hdc);

    RECT rc; GetWindowRect(g_hWnd, &rc);
    SetWindowPos(g_popupWnd, NULL, rc.left + (rc.right - rc.left) / 2 - pw / 2,
        rc.top - 60, pw, 50, SWP_NOACTIVATE | SWP_SHOWWINDOW);

    hdc = GetDC(g_popupWnd); HDC hm = CreateCompatibleDC(hdc);
    BITMAPINFO bi = {}; bi.bmiHeader.biSize = sizeof(BITMAPINFOHEADER);
    bi.bmiHeader.biWidth = pw; bi.bmiHeader.biHeight = -50;
    bi.bmiHeader.biPlanes = 1; bi.bmiHeader.biBitCount = 32; bi.bmiHeader.biCompression = BI_RGB;
    HBITMAP hB = CreateDIBSection(hdc, &bi, DIB_RGB_COLORS, NULL, NULL, 0);
    HGDIOBJ hOld = SelectObject(hm, hB);
    HBRUSH bg = CreateSolidBrush(RGB(20, 20, 35)); RECT full = { 0, 0, pw, 50 };
    FillRect(hm, &full, bg); DeleteObject(bg);
    SetBkMode(hm, TRANSPARENT); SetTextColor(hm, RGB(100, 255, 180));
    hf = CreateFontW(22, 0, 0, 0, FW_BOLD, 0, 0, 0, DEFAULT_CHARSET, 0, 0, CLEARTYPE_QUALITY, 0, L"Segoe UI");
    SelectObject(hm, hf); trc = { 10, 0, pw - 10, 50 };
    DrawTextW(hm, text, -1, &trc, DT_CENTER | DT_VCENTER);
    DeleteObject(hf); BitBlt(hdc, 0, 0, pw, 50, hm, 0, 0, SRCCOPY);
    SelectObject(hm, hOld); DeleteObject(hB); DeleteDC(hm); ReleaseDC(g_popupWnd, hdc);
    KillTimer(g_hWnd, 2);
    SetTimer(g_hWnd, 2, 4000, [](HWND h, UINT, UINT_PTR, DWORD) {
        if (g_popupWnd) ShowWindow(g_popupWnd, SW_HIDE); KillTimer(h, 2);
    });
}

static void CALLBACK StatusTimerHide(HWND h, UINT, UINT_PTR, DWORD) {
    if (g_statusWnd) ShowWindow(g_statusWnd, SW_HIDE); KillTimer(h, 3);
}

static void ShowStatus(const wchar_t* text) {
    if (!g_statusWnd) {
        WNDCLASSEXW wc = { sizeof(wc) }; wc.lpfnWndProc = DefWindowProcW;
        wc.hInstance = GetModuleHandle(NULL); wc.hbrBackground = CreateSolidBrush(RGB(20, 20, 35));
        wc.lpszClassName = L"AliceStatus"; wc.hCursor = LoadCursor(NULL, IDC_ARROW);
        RegisterClassExW(&wc);
        g_statusWnd = CreateWindowExW(WS_EX_LAYERED | WS_EX_TOPMOST, L"AliceStatus", NULL,
            WS_POPUP, 0, 0, 350, 35, NULL, NULL, GetModuleHandle(NULL), NULL);
        SetLayeredWindowAttributes(g_statusWnd, 0, 220, LWA_ALPHA);
    }
    RECT rc; GetWindowRect(g_hWnd, &rc);
    SetWindowPos(g_statusWnd, NULL, rc.left + (rc.right - rc.left) / 2 - 175, rc.bottom + 5,
        350, 35, SWP_NOACTIVATE | SWP_SHOWWINDOW);
    HDC hdc = GetDC(g_statusWnd); HDC hm = CreateCompatibleDC(hdc);
    BITMAPINFO bi = {}; bi.bmiHeader.biSize = sizeof(BITMAPINFOHEADER);
    bi.bmiHeader.biWidth = 350; bi.bmiHeader.biHeight = -35;
    bi.bmiHeader.biPlanes = 1; bi.bmiHeader.biBitCount = 32; bi.bmiHeader.biCompression = BI_RGB;
    HBITMAP hB = CreateDIBSection(hdc, &bi, DIB_RGB_COLORS, NULL, NULL, 0);
    HGDIOBJ hOld = SelectObject(hm, hB);
    HBRUSH bg = CreateSolidBrush(RGB(20, 20, 35)); RECT full = { 0, 0, 350, 35 };
    FillRect(hm, &full, bg); DeleteObject(bg);
    SetBkMode(hm, TRANSPARENT); SetTextColor(hm, RGB(150, 150, 180));
    HFONT hf = CreateFontW(14, 0, 0, 0, FW_NORMAL, 0, 0, 0, DEFAULT_CHARSET, 0, 0, CLEARTYPE_QUALITY, 0, L"Segoe UI");
    SelectObject(hm, hf); RECT tr = { 5, 0, 345, 35 };
    DrawTextW(hm, text, -1, &tr, DT_LEFT | DT_VCENTER | DT_END_ELLIPSIS);
    DeleteObject(hf); BitBlt(hdc, 0, 0, 350, 35, hm, 0, 0, SRCCOPY);
    SelectObject(hm, hOld); DeleteObject(hB); DeleteDC(hm); ReleaseDC(g_statusWnd, hdc);
    KillTimer(g_hWnd, 3); SetTimer(g_hWnd, 3, 3000, StatusTimerHide);
}

/* ============ Main ============ */

static LRESULT CALLBACK WndProc(HWND hWnd, UINT msg, WPARAM wParam, LPARAM lParam) {
    switch (msg) {
    case WM_CREATE:
        CoInitializeEx(NULL, COINIT_APARTMENTTHREADED);
        CoCreateInstance(CLSID_WICImagingFactory, NULL, CLSCTX_INPROC_SERVER, IID_PPV_ARGS(&g_pWIC));
        ScanGifs(); LoadGif(); StartAnim();
        _beginthreadex(NULL, 0, SpeechThread, NULL, 0, NULL);
        return 0;
    case WM_POPUP_SHOW:
        ShowPopup(L"\x042f \x0442\x0443\x0442!"); return 0;
    case WM_STATUS_SHOW:
        ShowStatus((const wchar_t*)wParam); free((void*)wParam); return 0;
    case WM_ANSWER_SHOW:
        ShowAnswerPopup((const wchar_t*)wParam); free((void*)wParam); return 0;
    case WM_LBUTTONDOWN:
        ReleaseCapture(); SendMessage(hWnd, WM_NCLBUTTONDOWN, HTCAPTION, 0); return 0;
    case WM_MOUSEWHEEL: {
        if (!g_gifCount) return 0;
        int d = GET_WHEEL_DELTA_WPARAM(wParam);
        g_currentIdx = (g_currentIdx + (d > 0 ? -1 : 1) + g_gifCount) % g_gifCount;
        KillTimer(hWnd, 1); LoadGif(); StartAnim(); return 0;
    }
    case WM_RBUTTONUP: {
        HMENU hP = CreatePopupMenu(); HMENU hS = CreatePopupMenu(); HMENU hO = CreatePopupMenu();
        AppendMenuW(hS, MF_STRING, ID_SIZE_200, L"Small (200)");
        AppendMenuW(hS, MF_STRING, ID_SIZE_300, L"Medium (300)");
        AppendMenuW(hS, MF_STRING, ID_SIZE_450, L"Large (450)");
        AppendMenuW(hS, MF_STRING, ID_SIZE_600, L"Huge (600)");
        AppendMenuW(hP, MF_POPUP, (UINT_PTR)hS, L"Size");
        AppendMenuW(hO, MF_STRING, ID_OPEN_BROWSER, L"Browser");
        AppendMenuW(hO, MF_STRING, ID_OPEN_VALORANT, L"VALORANT");
        AppendMenuW(hO, MF_STRING, ID_OPEN_ADGUARD, L"AdGuard VPN");
        AppendMenuW(hO, MF_STRING, ID_OPEN_YANDEX, L"\x042f\x043d\x0434\x0435\x043a\x0441 \x041c\x0443\x0437\x044b\x043a\x0430");
        AppendMenuW(hP, MF_POPUP, (UINT_PTR)hO, L"Open");
        POINT pt = { GET_X_LPARAM(lParam), GET_Y_LPARAM(lParam) };
        ClientToScreen(hWnd, &pt);
        TrackPopupMenu(hP, TPM_RIGHTBUTTON, pt.x, pt.y, 0, hWnd, NULL);
        DestroyMenu(hP); return 0;
    }
    case WM_COMMAND:
        switch (LOWORD(wParam)) {
        case ID_SIZE_200: g_displaySize = 200; RenderFrame(); break;
        case ID_SIZE_300: g_displaySize = 300; RenderFrame(); break;
        case ID_SIZE_450: g_displaySize = 450; RenderFrame(); break;
        case ID_SIZE_600: g_displaySize = 600; RenderFrame(); break;
        case ID_OPEN_BROWSER: ShellExecuteW(NULL, L"open", L"https://www.google.com", NULL, NULL, SW_SHOWNORMAL); break;
        case ID_OPEN_VALORANT: { wchar_t b[MAX_PATH]; ExpandEnvironmentStringsW(L"C:\\Riot Games\\VALORANT\\live\\VALORANT.exe", b, MAX_PATH); ShellExecuteW(NULL, L"open", b, NULL, NULL, SW_SHOWNORMAL); break; }
        case ID_OPEN_ADGUARD: { wchar_t b[MAX_PATH]; ExpandEnvironmentStringsW(L"C:\\Program Files\\AdGuardVpn\\AdGuardVpn.exe", b, MAX_PATH); ShellExecuteW(NULL, L"open", b, NULL, NULL, SW_SHOWNORMAL); break; }
        case ID_OPEN_YANDEX: ShellExecuteW(NULL, L"open", L"%LOCALAPPDATA%\\Programs\\YandexMusic\\\x042f\x043d\x0434\x0435\x043a\x0441 \x041c\x0443\x0437\x044b\x043a\x0430.exe", NULL, NULL, SW_SHOWNORMAL); break;
        } return 0;
    case WM_KEYDOWN: if (wParam == VK_ESCAPE) DestroyWindow(hWnd); return 0;
    case WM_DESTROY:
        KillTimer(hWnd, 1); KillTimer(hWnd, 2); KillTimer(hWnd, 3);
        g_speechRunning = 0; Sleep(500);
        for (int i = 0; i < NUM_CMDS; i++)
            for (int r = 0; r < g_phraseCount[i]; r++)
                if (g_phraseMFCC[i][r]) freeMFCC(g_phraseMFCC[i][r], g_phraseFrames[i][r]);
        FreeGif();
        if (g_pWIC) { g_pWIC->Release(); g_pWIC = NULL; }
        CoUninitialize(); PostQuitMessage(0); return 0;
    }
    return DefWindowProcW(hWnd, msg, wParam, lParam);
}

int WINAPI wWinMain(HINSTANCE hInst, HINSTANCE, LPWSTR, int) {
    WNDCLASSEXW wc = { sizeof(wc) }; wc.style = CS_HREDRAW | CS_VREDRAW;
    wc.lpfnWndProc = WndProc; wc.hInstance = hInst;
    wc.hCursor = LoadCursor(NULL, IDC_ARROW); wc.lpszClassName = L"AliceGif";
    RegisterClassExW(&wc);
    g_winW = 380; g_winH = 380; RECT rc = { 0, 0, g_winW, g_winH };
    AdjustWindowRectEx(&rc, WS_POPUP, FALSE, WS_EX_LAYERED);
    g_hWnd = CreateWindowExW(WS_EX_LAYERED, L"AliceGif", L"Alice",
        WS_POPUP | WS_VISIBLE, CW_USEDEFAULT, CW_USEDEFAULT,
        rc.right - rc.left, rc.bottom - rc.top, NULL, NULL, hInst, NULL);
    MSG msg;
    while (GetMessageW(&msg, NULL, 0, 0)) { TranslateMessage(&msg); DispatchMessageW(&msg); }
    return (int)msg.wParam;
}
