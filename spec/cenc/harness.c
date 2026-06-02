/*
 * Host-side harness: runs vcdiff_encode on a set of target buffers,
 * writes the resulting VCDIFF to disk, and spawns `xdelta3 -d` to verify
 * the decoded output matches the original target.
 *
 * Not part of the verified code; regular C99.
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <fcntl.h>
#include <sys/wait.h>

extern unsigned int vcdiff_encode(unsigned char *out, unsigned int out_cap,
                                  unsigned char *src, unsigned int src_len,
                                  unsigned char *tgt, unsigned int tgt_len,
                                  unsigned int *head,
                                  unsigned int *next_arr,
                                  unsigned char *pending, unsigned int pending_cap,
                                  unsigned char *data_sec, unsigned int data_cap,
                                  unsigned char *inst_sec, unsigned int inst_cap,
                                  unsigned char *addr_sec, unsigned int addr_cap);

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

static int run_xdelta3_decode(const char *vcdiff_path, const char *out_path)
{
    /* xdelta3 -d -f -s /dev/null <vcdiff_path> <out_path> */
    pid_t pid = fork();
    if (pid == 0) {
        /* Silence xdelta3. */
        int devnull = open("/dev/null", O_WRONLY);
        if (devnull >= 0) {
            dup2(devnull, 2);
        }
        execlp("xdelta3", "xdelta3", "-d", "-f",
               "-s", "/dev/null",
               vcdiff_path, out_path, (char *)NULL);
        _exit(127);
    }
    if (pid < 0) return -1;
    int status = 0;
    if (waitpid(pid, &status, 0) < 0) return -1;
    if (!WIFEXITED(status) || WEXITSTATUS(status) != 0) {
        return WEXITSTATUS(status);
    }
    return 0;
}

static int round_trip(const char *name,
                      const unsigned char *target, size_t target_len)
{
    unsigned char out[65536];
    unsigned int head[65536];
    unsigned int next_arr[1];
    unsigned char pending[65536];
    unsigned char data[65536 + 64];
    unsigned char inst[65536 + 64];
    unsigned char addr[65536 + 64];
    unsigned int out_len;
    if (target_len > 65536U) {
        fprintf(stderr, "[%s] target too large for harness scratch\n", name);
        return 1;
    }
    out_len = vcdiff_encode(out, sizeof(out),
                            (unsigned char *)0, 0U,
                            (unsigned char *)target, (unsigned int)target_len,
                            head,
                            next_arr,
                            pending, 65536U,
                            data, 65536U + 64U,
                            inst, 65536U + 64U,
                            addr, 65536U + 64U);
    if (out_len == 0) {
        fprintf(stderr, "[%s] encode failed (buffer full)\n", name);
        return 1;
    }

    const char *vpath = "/tmp/cdelta_harness.vcdiff";
    const char *dpath = "/tmp/cdelta_harness.decoded";
    if (write_file(vpath, out, out_len) != 0) {
        fprintf(stderr, "[%s] write vcdiff failed\n", name);
        return 1;
    }
    /* Ensure decoded file doesn't exist from previous run. */
    unlink(dpath);

    int rc = run_xdelta3_decode(vpath, dpath);
    if (rc != 0) {
        fprintf(stderr, "[%s] xdelta3 -d failed (exit %d)\n", name, rc);
        return 1;
    }

    unsigned char got[65536];
    size_t got_len = 0;
    if (read_file(dpath, got, sizeof(got), &got_len) != 0) {
        fprintf(stderr, "[%s] reading decoded file failed\n", name);
        return 1;
    }
    if (got_len != target_len || memcmp(got, target, target_len) != 0) {
        fprintf(stderr, "[%s] MISMATCH: decoded %zu bytes, expected %zu\n",
                name, got_len, target_len);
        return 1;
    }
    printf("[%s] OK  (target=%zu bytes, vcdiff=%u bytes)\n",
           name, target_len, out_len);
    return 0;
}

int main(void)
{
    int failures = 0;

    /* Case 1: empty target */
    failures += round_trip("empty", (const unsigned char *)"", 0);

    /* Case 2: single byte */
    failures += round_trip("one-byte", (const unsigned char *)"X", 1);

    /* Case 3: "hello world" */
    failures += round_trip("hello",
                           (const unsigned char *)"hello world", 11);

    /* Case 4: 127 bytes (varint boundary) */
    {
        unsigned char buf[127];
        for (size_t i = 0; i < sizeof(buf); i++) {
            buf[i] = (unsigned char)(i & 0xFF);
        }
        failures += round_trip("len-127", buf, sizeof(buf));
    }

    /* Case 5: 128 bytes (varint boundary: now 2 bytes) */
    {
        unsigned char buf[128];
        for (size_t i = 0; i < sizeof(buf); i++) {
            buf[i] = (unsigned char)((i * 7) & 0xFF);
        }
        failures += round_trip("len-128", buf, sizeof(buf));
    }

    /* Case 6: 16384 bytes (varint boundary: 3 bytes) */
    {
        unsigned char buf[16384];
        for (size_t i = 0; i < sizeof(buf); i++) {
            buf[i] = (unsigned char)((i * 131) & 0xFF);
        }
        failures += round_trip("len-16384", buf, sizeof(buf));
    }

    /* Case 7: all zeros */
    {
        unsigned char buf[1024];
        memset(buf, 0, sizeof(buf));
        failures += round_trip("zeros", buf, sizeof(buf));
    }

    /* Case 8: all 0xFF */
    {
        unsigned char buf[1024];
        memset(buf, 0xFF, sizeof(buf));
        failures += round_trip("ones", buf, sizeof(buf));
    }

    if (failures == 0) {
        printf("\nAll %d round-trips OK.\n", 8);
        return 0;
    }
    fprintf(stderr, "\n%d failures.\n", failures);
    return 1;
}
