/*
 * Host-side harness for the decoder. For each (source, target) pair, runs
 * xdelta3 -e -S none to produce a VCDIFF, hands it to our decoder, and
 * compares the decoded output to the original target.
 *
 * Not part of the verified code; regular C99.
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <fcntl.h>
#include <sys/wait.h>

extern int vcdiff_decode(unsigned char *patch, unsigned int patch_len,
                         unsigned char *src, unsigned int src_len,
                         unsigned char *out, unsigned int out_cap,
                         unsigned int *out_len);

static int write_file(const char *path, const unsigned char *data, size_t len)
{
    FILE *f = fopen(path, "wb");
    if (!f) return -1;
    size_t w = fwrite(data, 1, len, f);
    fclose(f);
    return (w == len) ? 0 : -1;
}

static int read_file(const char *path, unsigned char *buf, size_t cap, size_t *out_len)
{
    FILE *f = fopen(path, "rb");
    if (!f) return -1;
    size_t n = fread(buf, 1, cap, f);
    fclose(f);
    *out_len = n;
    return 0;
}

static int run_xdelta3_encode(const char *src_path, const char *tgt_path,
                              const char *vcdiff_path, int have_source)
{
    pid_t pid = fork();
    if (pid == 0) {
        int devnull = open("/dev/null", O_WRONLY);
        if (devnull >= 0) dup2(devnull, 2);
        if (have_source) {
            execlp("xdelta3", "xdelta3",
                   "-e", "-S", "none", "-A=", "-f",
                   "-s", src_path, tgt_path, vcdiff_path, (char *)NULL);
        } else {
            execlp("xdelta3", "xdelta3",
                   "-e", "-S", "none", "-A=", "-f",
                   tgt_path, vcdiff_path, (char *)NULL);
        }
        _exit(127);
    }
    if (pid < 0) return -1;
    int status = 0;
    if (waitpid(pid, &status, 0) < 0) return -1;
    if (!WIFEXITED(status) || WEXITSTATUS(status) != 0)
        return WEXITSTATUS(status);
    return 0;
}

static int round_trip(const char *name,
                      const unsigned char *src, size_t src_len,
                      const unsigned char *target, size_t target_len)
{
    const char *src_path = "/tmp/cdelta_dec_src";
    const char *tgt_path = "/tmp/cdelta_dec_tgt";
    const char *vpath    = "/tmp/cdelta_dec_patch.vcdiff";
    int have_source = (src != NULL);

    if (have_source) {
        if (write_file(src_path, src, src_len) != 0) return 1;
    }
    if (write_file(tgt_path, target, target_len) != 0) return 1;
    unlink(vpath);

    int rc = run_xdelta3_encode(have_source ? src_path : NULL,
                                tgt_path, vpath, have_source);
    if (rc != 0) {
        fprintf(stderr, "[%s] xdelta3 -e failed (%d)\n", name, rc);
        return 1;
    }

    unsigned char patch[131072];
    size_t patch_len = 0;
    if (read_file(vpath, patch, sizeof(patch), &patch_len) != 0) {
        fprintf(stderr, "[%s] read vcdiff failed\n", name);
        return 1;
    }

    unsigned char out[131072];
    unsigned int out_len = 0;
    int drc = vcdiff_decode(patch, (unsigned int)patch_len,
                            have_source ? (unsigned char *)src : NULL,
                            (unsigned int)src_len,
                            out, sizeof(out), &out_len);
    if (drc != 0) {
        fprintf(stderr, "[%s] vcdiff_decode error %d (patch=%zu bytes)\n",
                name, drc, patch_len);
        return 1;
    }
    if (out_len != target_len || memcmp(out, target, target_len) != 0) {
        fprintf(stderr, "[%s] MISMATCH: got %u bytes, expected %zu\n",
                name, out_len, target_len);
        size_t n = out_len < target_len ? out_len : target_len;
        size_t firstdiff = 0;
        for (; firstdiff < n; firstdiff++)
            if (out[firstdiff] != target[firstdiff]) break;
        fprintf(stderr, "   first diff at byte %zu\n", firstdiff);
        return 1;
    }
    printf("[%s] OK  (src=%zu tgt=%zu patch=%zu)\n",
           name, src_len, target_len, patch_len);
    return 0;
}

int main(void)
{
    int failures = 0;

    /* ---------- no-source cases (pure ADD) ---------- */
    failures += round_trip("ns-empty", NULL, 0,
                           (const unsigned char *)"", 0);
    failures += round_trip("ns-one", NULL, 0,
                           (const unsigned char *)"X", 1);
    failures += round_trip("ns-hello", NULL, 0,
                           (const unsigned char *)"hello world", 11);

    /* ---------- with source ---------- */
    const char *sa = "the quick brown fox jumps over the lazy dog";
    const char *ta = "the quick brown fox jumps over the lazy cat";
    failures += round_trip("src-fox", (const unsigned char *)sa, strlen(sa),
                           (const unsigned char *)ta, strlen(ta));

    /* identical src/tgt */
    const char *sb = "this exact string";
    failures += round_trip("src-identical",
                           (const unsigned char *)sb, strlen(sb),
                           (const unsigned char *)sb, strlen(sb));

    /* target is a prefix of source */
    const char *sc = "abcdefghijklmnopqrstuvwxyz";
    failures += round_trip("src-prefix",
                           (const unsigned char *)sc, strlen(sc),
                           (const unsigned char *)sc, 10);

    /* target is source reversed — should need ADDs */
    {
        unsigned char src[32];
        unsigned char tgt[32];
        for (size_t i = 0; i < 32; i++) src[i] = (unsigned char)('a' + i);
        for (size_t i = 0; i < 32; i++) tgt[i] = src[31 - i];
        failures += round_trip("src-reversed", src, 32, tgt, 32);
    }

    /* larger repeating pattern (should trigger RUN/COPY) */
    {
        unsigned char src[2048];
        unsigned char tgt[2048];
        for (size_t i = 0; i < 2048; i++) src[i] = (unsigned char)((i * 31) & 0xFF);
        memcpy(tgt, src, 2048);
        /* Mutate a few bytes */
        for (size_t i = 100; i < 110; i++) tgt[i] = (unsigned char)(i & 0xFF);
        failures += round_trip("src-mostly-equal", src, 2048, tgt, 2048);
    }

    /* all-zeros target, no source (RUN-friendly) */
    {
        unsigned char tgt[1024] = {0};
        failures += round_trip("ns-zeros", NULL, 0, tgt, 1024);
    }

    /* all-zeros target with an unrelated source */
    {
        unsigned char src[512];
        unsigned char tgt[1024] = {0};
        for (size_t i = 0; i < 512; i++) src[i] = (unsigned char)(i & 0xFF);
        failures += round_trip("src-zeros", src, 512, tgt, 1024);
    }

    if (failures == 0) {
        printf("\nAll round-trips OK.\n");
        return 0;
    }
    fprintf(stderr, "\n%d failures.\n", failures);
    return 1;
}
