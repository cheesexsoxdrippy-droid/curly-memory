/*
 * THE CITY: NO SIGNAL - Enhanced PSP / PPSSPP homebrew prototype
 *
 * Software ray-caster, procedural audio, stalking entity, evidence clues.
 * Build with PSPSDK:  make
 */
#include <pspkernel.h>
#include <pspdisplay.h>
#include <pspctrl.h>
#include <pspdebug.h>
#include <pspaudio.h>
#include <math.h>
#include <stdio.h>
#include <string.h>
#include <stdlib.h>

PSP_MODULE_INFO("THE_CITY_NO_SIGNAL", 0, 1, 0);
PSP_MAIN_THREAD_ATTR(THREAD_ATTR_USER | THREAD_ATTR_VFPU);

#define W 480
#define H 272
#define MAP_W 32
#define MAP_H 32
#define GPI 3.14159265358979323846f
#define FOV 1.0471975512f
#define MOVE_SPEED 0.060f
#define TURN_SPEED 0.043f
#define PLAYER_RADIUS 0.22f
#define AUDIO_SAMPLES 1024

/* Double-buffered VRAM (PSP line stride is always 512 pixels). */
#define VRAM_LINE 512
#define VRAM_FB_BYTES (VRAM_LINE * H * 4)

static unsigned int frame[W * H];
static float zbuf[W];
static unsigned char city[MAP_H][MAP_W];   /* 0 open, 1 wall, 2 clue, 3 recorded clue */
static unsigned int oldButtons = 0;
static float px = 3.5f, py = 3.5f, angle = 0.0f;
static float ex = 26.5f, ey = 26.5f;
static int flashlight = 1, paused = 0, stepTicks = 0;
static int radioTicks = 0, clueCount = 0, entityMood = 0;
static int drawPage = 0;
static short audioBuffer[AUDIO_SAMPLES] __attribute__((aligned(64)));
static char statusLine[112] = "RADIO: NO SIGNAL";
static char clueLine[180] = "The city has gone quiet.";
static char districtLine[48] = "NORTH RESIDENTIAL";
static unsigned int noiseSeed = 0x12345678;

static const char *clues[] = {
    "Apartment 04: dinner is still on the table. Every family photo is face-down.",
    "A child's drawing shows a tall, featureless shape outside the bedroom window.",
    "Emergency screen: CONTAINMENT FAILURE. DO NOT LOOK DIRECTLY AT IT.",
    "Police radio: 'We hear footsteps in rooms we already cleared.'",
    "A subway train is frozen here. A small stuffed animal rests on a seat.",
    "Rooftop notes: the telescope keeps turning toward the same dark tower.",
    "Office memo: evacuation order received 19 hours after the last employee vanished.",
    "Graffiti: IT'S ALREADY INSIDE."
};
#define CLUE_COUNT ((int)(sizeof(clues) / sizeof(clues[0])))

/* Clue positions (index matches clues[]). Chosen so none plug a doorway. */
static const int clueX[CLUE_COUNT] = { 8, 14, 22,  6, 16, 22,  8, 20 };
static const int clueY[CLUE_COUNT] = { 7,  8,  8, 16, 16, 16, 23, 23 };

/* ---------- exit callback (HOME button) ---------- */
static int exitCallback(int arg1, int arg2, void *common) {
    (void)arg1; (void)arg2; (void)common;
    sceKernelExitGame();
    return 0;
}
static int callbackThread(SceSize args, void *argp) {
    int cbid;
    (void)args; (void)argp;
    cbid = sceKernelCreateCallback("Exit Callback", exitCallback, NULL);
    sceKernelRegisterExitCallback(cbid);
    sceKernelSleepThreadCB();
    return 0;
}
static void setupExitCallback(void) {
    int thid = sceKernelCreateThread("update_thread", callbackThread, 0x11, 0xFA0, 0, NULL);
    if (thid >= 0) sceKernelStartThread(thid, 0, NULL);
}

/* ---------- helpers ---------- */
static unsigned int rgb(int r, int g, int b) {
    if (r < 0) { r = 0; } else if (r > 255) { r = 255; }
    if (g < 0) { g = 0; } else if (g > 255) { g = 255; }
    if (b < 0) { b = 0; } else if (b > 255) { b = 255; }
    return 0xFF000000u | ((unsigned int)r << 16) |
           ((unsigned int)g << 8) | (unsigned int)b;
}
static int inside(int x, int y) {
    return x >= 0 && y >= 0 && x < MAP_W && y < MAP_H;
}
/* Anything non-zero (walls AND clue blocks) is solid. */
static int blocked(float x, float y) {
    int mx = (int)floorf(x), my = (int)floorf(y);
    if (!inside(mx, my)) return 1;
    return city[my][mx] != 0;
}
/* Player collision with a radius so the camera never clips into walls. */
static int blockedR(float x, float y) {
    return blocked(x - PLAYER_RADIUS, y - PLAYER_RADIUS) ||
           blocked(x + PLAYER_RADIUS, y - PLAYER_RADIUS) ||
           blocked(x - PLAYER_RADIUS, y + PLAYER_RADIUS) ||
           blocked(x + PLAYER_RADIUS, y + PLAYER_RADIUS);
}
static void setCell(int x, int y, unsigned char v) {
    if (inside(x, y)) city[y][x] = v;
}
static int findClue(int x, int y) {
    int i;
    for (i = 0; i < CLUE_COUNT; ++i)
        if (clueX[i] == x && clueY[i] == y) return i;
    return -1;
}

/* Generate the street grid with enterable building interiors. */
static void buildCity(void) {
    int x, y, bx, by, i;
    for (y = 0; y < MAP_H; ++y)
        for (x = 0; x < MAP_W; ++x)
            city[y][x] = 1;

    /* Main roads and cross streets. */
    for (y = 1; y < MAP_H - 1; ++y)
        for (x = 1; x < MAP_W - 1; ++x)
            if (x == 2 || x == 3 || x == 10 || x == 11 ||
                x == 18 || x == 19 || x == 26 || x == 27 ||
                y == 2 || y == 3 || y == 10 || y == 11 ||
                y == 18 || y == 19 || y == 26 || y == 27)
                city[y][x] = 0;

    /* Building blocks (the bottom row is replaced by the hall below). */
    for (by = 5; by <= 13; by += 8) {
        for (bx = 5; bx <= 21; bx += 8) {
            int xx, yy;
            for (yy = by; yy < by + 5; ++yy)
                for (xx = bx; xx < bx + 5; ++xx)
                    city[yy][xx] = 0;
            for (xx = bx; xx < bx + 5; ++xx) {
                city[by][xx] = 1;
                city[by + 4][xx] = 1;
            }
            for (yy = by; yy < by + 5; ++yy) {
                city[yy][bx] = 1;
                city[yy][bx + 4] = 1;
            }
            /* West door: also carve the 1-tile gap outside it, otherwise the
             * door opens into solid wall and leads nowhere. */
            city[by + ((bx + by) % 3) + 1][bx] = 0;
            city[by + ((bx + by) % 3) + 1][bx - 1] = 0;
            /* South door onto the street. */
            city[by + 4][bx + 2] = 0;

            /* Interior partition with a gap in the middle. */
            city[by + 2][bx + 1] = 1;
            city[by + 2][bx + 3] = 1;
        }
    }

    /* Large south hall (x 5..24, y 21..25) with doors onto road y=26. */
    for (y = 21; y <= 25; ++y)
        for (x = 5; x <= 24; ++x)
            city[y][x] = (y == 21 || y == 25 || x == 5 || x == 24) ? 1 : 0;
    city[25][8] = 0; city[25][14] = 0; city[25][20] = 0;
    city[23][11] = 1; city[23][17] = 1;      /* pillars */

    /* Subway access corridor and station platform. */
    for (x = 12; x <= 24; ++x) {
        city[28][x] = 0;
        city[29][x] = 0;
    }

    /* Clue blocks. */
    for (i = 0; i < CLUE_COUNT; ++i)
        setCell(clueX[i], clueY[i], 2);
}

static void putPixel(int x, int y, unsigned int c) {
    if ((unsigned)x < W && (unsigned)y < H)
        frame[y * W + x] = c;
}

/* Line of sight between two points on the grid. */
static int lineOfSight(float x0, float y0, float x1, float y1) {
    float dx = x1 - x0, dy = y1 - y0;
    float d = sqrtf(dx * dx + dy * dy), t;
    if (d < 0.01f) return 1;
    for (t = 0.25f; t < d; t += 0.25f)
        if (blocked(x0 + dx / d * t, y0 + dy / d * t)) return 0;
    return 1;
}

/* DDA ray-caster: each screen column traces one ray through the city grid. */
static void renderWorld(void) {
    int x, y;
    const float tanHalf = tanf(FOV * 0.5f);
    for (y = 0; y < H / 2; ++y) {
        int shade = 3 + y / 30;
        unsigned int c = rgb(shade, shade + 1, shade + 4);
        for (x = 0; x < W; ++x) frame[y * W + x] = c;
    }
    for (y = H / 2; y < H; ++y) {
        int shade = 7 + (y - H / 2) / 10;
        unsigned int c = rgb(shade, shade, shade + 2);
        for (x = 0; x < W; ++x) frame[y * W + x] = c;
    }

    for (x = 0; x < W; ++x) {
        float cameraX = 2.0f * x / (float)W - 1.0f;
        float rayA = angle + atanf(cameraX * tanHalf);
        float rayX = cosf(rayA), rayY = sinf(rayA);
        int mapX = (int)floorf(px), mapY = (int)floorf(py);
        float deltaX = fabsf(1.0f / (rayX == 0 ? 0.00001f : rayX));
        float deltaY = fabsf(1.0f / (rayY == 0 ? 0.00001f : rayY));
        float sideX, sideY, dist, perpDist;
        int stepX, stepY, side = 0, hit = 0, wallType = 1, guard = 0;
        zbuf[x] = 1000.0f;
        if (rayX < 0) { stepX = -1; sideX = (px - mapX) * deltaX; }
        else { stepX = 1; sideX = (mapX + 1.0f - px) * deltaX; }
        if (rayY < 0) { stepY = -1; sideY = (py - mapY) * deltaY; }
        else { stepY = 1; sideY = (mapY + 1.0f - py) * deltaY; }

        /* Map is fully enclosed by walls, so this always terminates. */
        while (!hit && guard++ < 128) {
            if (sideX < sideY) { sideX += deltaX; mapX += stepX; side = 0; }
            else               { sideY += deltaY; mapY += stepY; side = 1; }
            if (!inside(mapX, mapY)) { hit = 1; wallType = 1; break; }
            if (city[mapY][mapX] != 0) { hit = 1; wallType = city[mapY][mapX]; }
        }
        if (!hit) continue;

        dist = (side == 0) ? (mapX - px + (1 - stepX) * 0.5f) / (rayX == 0 ? 0.00001f : rayX)
                           : (mapY - py + (1 - stepY) * 0.5f) / (rayY == 0 ? 0.00001f : rayY);
        /* Remove fish-eye: use distance perpendicular to the view plane. */
        perpDist = dist * cosf(rayA - angle);
        if (perpDist < 0.05f) perpDist = 0.05f;
        zbuf[x] = perpDist;
        {
            int wallH = (int)(H / perpDist);
            int top, bottom, y0, y1;
            float wallX = (side == 0) ? py + dist * rayY : px + dist * rayX;
            int texture = ((int)(wallX * 8.0f)) & 7;
            int base = (int)(68.0f / (1.0f + perpDist * 0.35f));
            float beam = 1.0f - fabsf(cameraX);
            if (wallH < 1) wallH = 1;
            top = H / 2 - wallH / 2;
            bottom = H / 2 + wallH / 2;
            if (side) base = base * 3 / 4;
            if (flashlight && beam > 0.48f) base += 15;
            if (base > 75) base = 75;
            if (wallType == 2) base += 4;

            /* Only loop over visible rows (walls pressed to the lens are huge). */
            y0 = top < 0 ? 0 : top;
            y1 = bottom > H ? H : bottom;
            for (y = y0; y < y1; ++y) {
                int localY = (y - top) * 16 / wallH;
                int shade = base;
                if ((localY == 3 || localY == 8 || localY == 13) && texture < 6) shade /= 2;
                if ((texture == 2 || texture == 5) && localY >= 4 && localY <= 10)
                    shade = (shade * 2) / 3;
                if (wallType == 2 && ((x + y) % 7 < 2)) shade += 12;
                frame[y * W + x] = rgb(shade, shade + 1, shade + 4);
            }
        }
    }

    /* Presence: incomplete silhouette, hidden behind walls via the z-buffer. */
    {
        float dx = ex - px, dy = ey - py;
        float distance = sqrtf(dx * dx + dy * dy);
        float relative = atan2f(dy, dx) - angle;
        while (relative > GPI) relative -= 2 * GPI;
        while (relative < -GPI) relative += 2 * GPI;
        if (distance < 11.0f && fabsf(relative) < 0.20f && distance > 2.8f) {
            float perp = distance * cosf(relative);
            int cx = W / 2 + (int)(tanf(relative) / tanHalf * (W / 2));
            int half = (int)(18.0f / perp);
            int top = H / 2 - (int)(72.0f / perp), bottom = H / 2 + (int)(72.0f / perp);
            for (x = cx - half; x <= cx + half; ++x) {
                if (x < 0 || x >= W || zbuf[x] < perp) continue;
                for (y = top; y < bottom; ++y)
                    if (((x + y + stepTicks) & 3) != 0)
                        putPixel(x, y, rgb(2, 2, 4));
            }
        }
    }

    /* Smooth vignette toward the screen edges. */
    for (y = 0; y < H; ++y) {
        int oy = abs(y - H / 2) - 85;
        for (x = 0; x < W; ++x) {
            int ox = abs(x - W / 2) - 150;
            int k = 0, k2 = 0, scale;
            unsigned int c;
            if (ox <= 0 && oy <= 0) continue;
            if (ox > 0) k = ox * 256 / 90;
            if (oy > 0) k2 = oy * 256 / 51;
            if (k2 > k) k = k2;
            if (k > 200) k = 200;
            scale = 256 - k;
            c = frame[y * W + x];
            frame[y * W + x] = 0xFF000000u |
                (((((c >> 16) & 255) * scale) >> 8) << 16) |
                (((((c >> 8) & 255) * scale) >> 8) << 8) |
                ((((c) & 255) * scale) >> 8);
        }
    }
}

/* Copy the software frame into the back buffer (uncached VRAM address). */
static void copyFrame(void) {
    unsigned int *dst = (unsigned int *)(0x44000000 + drawPage * VRAM_FB_BYTES);
    int y;
    for (y = 0; y < H; ++y)
        memcpy(dst + y * VRAM_LINE, frame + y * W, W * sizeof(unsigned int));
}

static void updateDistrict(void) {
    if (py < 9) strcpy(districtLine, "NORTH RESIDENTIAL");
    else if (px > 20 && py < 20) strcpy(districtLine, "EAST OFFICE DISTRICT");
    else if (py > 28) strcpy(districtLine, "UNDERGROUND / SUBWAY");
    else if (px < 12) strcpy(districtLine, "WEST INDUSTRIAL");
    else strcpy(districtLine, "CENTRAL CITY");
}

static void inspect(void) {
    float d;
    for (d = 0.3f; d <= 1.7f; d += 0.2f) {
        int mx = (int)floorf(px + cosf(angle) * d);
        int my = (int)floorf(py + sinf(angle) * d);
        int v, id;
        if (!inside(mx, my)) break;
        v = city[my][mx];
        if (v == 0) continue;
        if (v == 2 && (id = findClue(mx, my)) >= 0) {
            snprintf(clueLine, sizeof(clueLine), "%s", clues[id]);
            snprintf(statusLine, sizeof(statusLine), "FIELD EVIDENCE RECORDED");
            city[my][mx] = 3;
            clueCount++;
            return;
        }
        if (v == 3) {
            snprintf(statusLine, sizeof(statusLine), "ALREADY RECORDED");
            return;
        }
        break; /* ordinary wall */
    }
    snprintf(clueLine, sizeof(clueLine), "Dust covers everything. Something moved when the light turned away.");
    snprintf(statusLine, sizeof(statusLine), "NO INTERACTABLE CLUE");
}

static void useRadio(void) {
    static const char *messages[] = {
        "RADIO: [STATIC] ...unit 7, do you copy?",
        "RADIO: ...the streets are empty. We are not alone.",
        "RADIO: ...do not follow the footsteps underground.",
        "RADIO: [BREATHING] ...you should not have come back.",
        "RADIO: ...signal source is directly behind you..."
    };
    radioTicks++;
    snprintf(statusLine, sizeof(statusLine), "%s", messages[radioTicks % 5]);
}

/* Generated drone with occasional noise pulses. Uses its own sample counter so
 * the waveform is continuous (no clicks) and keeps playing while paused. */
static int audioThread(SceSize args, void *argp) {
    int i, ch;
    unsigned int sampleCounter = 0;
    (void)args; (void)argp;
    ch = sceAudioChReserve(-1, AUDIO_SAMPLES, PSP_AUDIO_FORMAT_MONO);
    if (ch < 0) return 0;
    while (1) {
        for (i = 0; i < AUDIO_SAMPLES; ++i, ++sampleCounter) {
            float t = (float)(sampleCounter % 2000000u) * 0.018f;
            int hum = (int)(sinf(t) * 650.0f + sinf(t * 0.37f) * 380.0f);
            int noise, pulse;
            noiseSeed = noiseSeed * 1664525u + 1013904223u;
            noise = ((int)((noiseSeed >> 20) & 0x7ff) - 1024);
            pulse = ((sampleCounter / 40000u) % 4 == 0 && (sampleCounter % 240) < 5) ? noise / 2 : 0;
            audioBuffer[i] = (short)(hum + noise / 9 + pulse);
        }
        sceAudioOutputBlocking(ch, PSP_AUDIO_VOLUME_MAX / 3, audioBuffer);
    }
    return 0;
}

/* Try to move the entity by (mx,my), sliding along walls. */
static int entityMove(float mx, float my) {
    int moved = 0;
    if (!blocked(ex + mx, ey)) { ex += mx; moved = 1; }
    if (!blocked(ex, ey + my)) { ey += my; moved = 1; }
    return moved;
}

static void updateEntity(void) {
    float dx = px - ex, dy = py - ey;
    float d = sqrtf(dx * dx + dy * dy);
    if (d < 0.001f) return;

    /* Acts every ~1.6 s. Being looked at (with clear line of sight) makes it
     * retreat; otherwise it creeps toward the player. */
    if (stepTicks % 95 == 0) {
        float toEntity = atan2f(ey - py, ex - px) - angle;
        while (toEntity > GPI) toEntity -= 2 * GPI;
        while (toEntity < -GPI) toEntity += 2 * GPI;

        if (fabsf(toEntity) < 0.42f && d < 13.0f && lineOfSight(px, py, ex, ey)) {
            entityMood = 1;
            entityMove(-(dx / d) * 1.4f, -(dy / d) * 1.4f);   /* away from player */
            snprintf(statusLine, sizeof(statusLine), "THE FOOTSTEPS STOP WHEN YOU TURN.");
        } else if (d > 3.6f) {
            /* Try straight at the player, then angled detours so it doesn't
             * get stuck on the first wall it meets. */
            static const float turns[5] = { 0.0f, 0.8f, -0.8f, 1.6f, -1.6f };
            float base = atan2f(dy, dx);
            int i;
            for (i = 0; i < 5; ++i) {
                float a = base + turns[i];
                if (entityMove(cosf(a) * 0.34f, sinf(a) * 0.34f)) break;
            }
            entityMood = 2;
        } else {
            entityMood = 3;
            snprintf(statusLine, sizeof(statusLine), "A COLD DRAFT PASSES THROUGH THE ROOM.");
        }
    }
    if (blocked(ex, ey)) { ex = 26.5f; ey = 26.5f; }
}

static void printWrapped(int row, const char *s) {
    char line[64];
    int len = (int)strlen(s), pos = 0;
    while (pos < len && row < 10) {
        int n = len - pos;
        if (n > 62) n = 62;
        memcpy(line, s + pos, n);
        line[n] = 0;
        pspDebugScreenSetXY(1, row++);
        pspDebugScreenPrintf("%s", line);
        pos += n;
    }
}

static void drawHud(void) {
    pspDebugScreenSetTextColor(0xFFB5BBC4);
    pspDebugScreenSetXY(1, 1);
    pspDebugScreenPrintf("THE CITY: NO SIGNAL");
    pspDebugScreenSetXY(1, 2);
    pspDebugScreenPrintf("%s", districtLine);
    pspDebugScreenSetXY(1, 3);
    pspDebugScreenPrintf("FLASHLIGHT: %s  [UNLIMITED]", flashlight ? "ON" : "OFF");
    pspDebugScreenSetXY(1, 4);
    pspDebugScreenPrintf("%s", statusLine);
    pspDebugScreenSetXY(1, 31);
    pspDebugScreenPrintf("D-PAD MOVE  ANALOG TURN  X INSPECT  [] LIGHT  TRIANGLE RADIO");
    pspDebugScreenSetXY(1, 32);
    pspDebugScreenPrintf("START PAUSE  |  EVIDENCE: %d/%d", clueCount, CLUE_COUNT);
    pspDebugScreenSetTextColor(0xFF9299A3);
    printWrapped(6, clueLine);
}

#ifndef CITY_TEST_HARNESS
int main(void) {
    SceCtrlData pad;
    int audioTid;
    setupExitCallback();
    pspDebugScreenInit();
    pspDebugScreenEnableBackColor(0);   /* transparent text over the scene */
    sceCtrlSetSamplingCycle(0);
    sceCtrlSetSamplingMode(PSP_CTRL_MODE_ANALOG);
    buildCity();

    audioTid = sceKernelCreateThread("CityAmbientAudio", audioThread, 0x18, 0x4000, PSP_THREAD_ATTR_USER, NULL);
    if (audioTid >= 0) sceKernelStartThread(audioTid, 0, NULL);

    while (1) {
        unsigned int pressed;
        sceCtrlReadBufferPositive(&pad, 1);
        pressed = pad.Buttons & ~oldButtons;
        oldButtons = pad.Buttons;

        if (pressed & PSP_CTRL_START) paused = !paused;

        if (!paused) {
            float forward = 0.0f, strafe = 0.0f;
            if (pad.Buttons & PSP_CTRL_UP) forward += MOVE_SPEED;
            if (pad.Buttons & PSP_CTRL_DOWN) forward -= MOVE_SPEED;
            if (pad.Buttons & PSP_CTRL_LEFT) strafe -= MOVE_SPEED;
            if (pad.Buttons & PSP_CTRL_RIGHT) strafe += MOVE_SPEED;
            if (forward != 0.0f && strafe != 0.0f) { forward *= 0.7071f; strafe *= 0.7071f; }
            if (pad.Lx < 105) angle -= TURN_SPEED;
            if (pad.Lx > 150) angle += TURN_SPEED;

            {
                float nx = px + cosf(angle) * forward - sinf(angle) * strafe;
                float ny = py + sinf(angle) * forward + cosf(angle) * strafe;
                if (!blockedR(nx, py)) px = nx;
                if (!blockedR(px, ny)) py = ny;
            }

            if (pressed & PSP_CTRL_SQUARE) flashlight = !flashlight;
            if (pressed & PSP_CTRL_CROSS) inspect();
            if (pressed & PSP_CTRL_TRIANGLE) useRadio();

            stepTicks++;
            updateEntity();
            updateDistrict();

            if (stepTicks % 620 == 0)
                snprintf(statusLine, sizeof(statusLine), "A DOOR CREAKS SOMEWHERE BEHIND YOU.");
            if (stepTicks % 1100 == 0)
                snprintf(statusLine, sizeof(statusLine), "RADIO: [STATIC] ...IT IS STILL HERE...");
        }

        /* Render into the hidden page, draw HUD on top, then flip. */
        renderWorld();
        copyFrame();
        pspDebugScreenSetOffset(drawPage * VRAM_FB_BYTES);
        drawHud();
        if (paused) {
            pspDebugScreenSetXY(18, 15);
            pspDebugScreenSetTextColor(0xFFD0D3D8);
            pspDebugScreenPrintf("PAUSED - PRESS START");
        }

        sceDisplayWaitVblankStart();
        sceDisplaySetFrameBuf((void *)(0x04000000 + drawPage * VRAM_FB_BYTES),
                              VRAM_LINE, PSP_DISPLAY_PIXEL_FORMAT_8888,
                              PSP_DISPLAY_SETBUF_NEXTFRAME);
        drawPage ^= 1;
    }
    return 0;
}
#endif
