/*
 * Minimal VCDIFF decoder (RFC 3284, simplified):
 *   - Default code table (§5.4), embedded.
 *   - VCD_SELF / VCD_HERE / VCD_NEAR / VCD_SAME addressing (default s_near=4,
 *     s_same=3), with address cache.
 *   - Window indicators: 0x00 (no source) and VCD_SOURCE (0x01), optionally
 *     VCD_ADLER32. VCD_TARGET (0x02) is rejected.
 *   - Delta indicator must be 0 (no secondary compression).
 *   - Single window only.
 *
 * Written in the AutoCorres C subset: no function pointers, no variadic,
 * no longjmp, restricted pointer arithmetic (indexing only), no pointers
 * to locals (helpers communicate via struct returns).
 *
 * Error codes (returned as signed int):
 *    0        — success
 *   negative  — decode error
 */

#define VCD_OK            0
#define VCD_ERR_TRUNC    -1
#define VCD_ERR_MAGIC    -2
#define VCD_ERR_HDR      -3
#define VCD_ERR_WIN      -4
#define VCD_ERR_DI       -5
#define VCD_ERR_OPCODE   -6
#define VCD_ERR_MODE     -7
#define VCD_ERR_SIZE     -8
#define VCD_ERR_OVERRUN  -9
#define VCD_ERR_SRC      -10
#define VCD_ERR_VARINT   -11
#define VCD_ERR_OUTCAP   -12
#define VCD_ERR_SRCNEED  -13

/* Address cache: default s_near=4, s_same=3. */
#define NEAR_SZ 4U
#define SAME_SZ 3U

/* Instruction types. */
#define OP_NOOP 0U
#define OP_ADD  1U
#define OP_RUN  2U
#define OP_COPY 3U

/* ---------- Result structs ---------- */
/*
 * All parse helpers return a `pr_t`:
 *   err == 0 : success; pos is new cursor; val is the parsed value (byte
 *              or varint).
 *   err <  0 : failure; pos / val undefined.
 */
struct pr_t {
    unsigned int pos;
    unsigned int val;
    int err;
};

/* Address-decode result: same shape plus an updated near_ptr. */
struct ar_t {
    unsigned int pos;
    unsigned int addr;
    unsigned int near_ptr;
    int err;
};

/* ---------- Input cursor helpers ---------- */

static struct pr_t read_byte(unsigned char *buf, unsigned int len,
                             unsigned int pos)
{
    struct pr_t r;
    if (pos >= len) {
        r.pos = pos;
        r.val = 0U;
        r.err = VCD_ERR_TRUNC;
        return r;
    }
    r.pos = pos + 1U;
    r.val = (unsigned int)buf[pos];
    r.err = VCD_OK;
    return r;
}

/* Big-endian 7-bit-per-byte VCDIFF varint, bounded to 32 bits. */
static struct pr_t read_varint(unsigned char *buf, unsigned int len,
                               unsigned int pos)
{
    struct pr_t r;
    unsigned int v = 0U;
    unsigned int i = 0U;
    unsigned int cur = pos;
    while (i < 5U) {
        unsigned char b;
        if (cur >= len) {
            r.pos = cur;
            r.val = 0U;
            r.err = VCD_ERR_TRUNC;
            return r;
        }
        b = buf[cur];
        cur = cur + 1U;
        if (i == 4U && (v & 0xFE000000U) != 0U) {
            r.pos = cur;
            r.val = 0U;
            r.err = VCD_ERR_VARINT;
            return r;
        }
        v = (v << 7) | (unsigned int)(b & 0x7FU);
        if ((b & 0x80U) == 0U) {
            r.pos = cur;
            r.val = v;
            r.err = VCD_OK;
            return r;
        }
        i = i + 1U;
    }
    r.pos = cur;
    r.val = 0U;
    r.err = VCD_ERR_VARINT;
    return r;
}

/* ---------- Default code table ---------- */

static unsigned char code_tbl[256][6];
static unsigned int code_tbl_built = 0U;

/* Address cache state. File-scope rather than stack-local to keep the
 * AutoCorres heap-lift phase tractable (no pointers into caller stack). */
static unsigned int near_arr[NEAR_SZ];
static unsigned int same_arr[SAME_SZ * 256U];

static void build_code_table(void)
{
    unsigned int i;
    unsigned int idx;
    unsigned int mode;
    unsigned int size;
    unsigned int add_size;
    unsigned int copy_size;

    for (i = 0U; i < 256U; i = i + 1U) {
        code_tbl[i][0] = (unsigned char)OP_NOOP;
        code_tbl[i][1] = (unsigned char)0U;
        code_tbl[i][2] = (unsigned char)0U;
        code_tbl[i][3] = (unsigned char)OP_NOOP;
        code_tbl[i][4] = (unsigned char)0U;
        code_tbl[i][5] = (unsigned char)0U;
    }

    code_tbl[0][0] = (unsigned char)OP_RUN;

    for (i = 0U; i < 18U; i = i + 1U) {
        code_tbl[1U + i][0] = (unsigned char)OP_ADD;
        code_tbl[1U + i][1] = (unsigned char)i;
    }

    idx = 19U;
    for (mode = 0U; mode < 9U; mode = mode + 1U) {
        code_tbl[idx][0] = (unsigned char)OP_COPY;
        code_tbl[idx][1] = (unsigned char)0U;
        code_tbl[idx][2] = (unsigned char)mode;
        idx = idx + 1U;
        for (size = 4U; size < 19U; size = size + 1U) {
            code_tbl[idx][0] = (unsigned char)OP_COPY;
            code_tbl[idx][1] = (unsigned char)size;
            code_tbl[idx][2] = (unsigned char)mode;
            idx = idx + 1U;
        }
    }

    for (mode = 0U; mode < 6U; mode = mode + 1U) {
        for (add_size = 1U; add_size < 5U; add_size = add_size + 1U) {
            for (copy_size = 4U; copy_size < 7U; copy_size = copy_size + 1U) {
                code_tbl[idx][0] = (unsigned char)OP_ADD;
                code_tbl[idx][1] = (unsigned char)add_size;
                code_tbl[idx][2] = (unsigned char)0U;
                code_tbl[idx][3] = (unsigned char)OP_COPY;
                code_tbl[idx][4] = (unsigned char)copy_size;
                code_tbl[idx][5] = (unsigned char)mode;
                idx = idx + 1U;
            }
        }
    }

    for (mode = 6U; mode < 9U; mode = mode + 1U) {
        for (add_size = 1U; add_size < 5U; add_size = add_size + 1U) {
            code_tbl[idx][0] = (unsigned char)OP_ADD;
            code_tbl[idx][1] = (unsigned char)add_size;
            code_tbl[idx][2] = (unsigned char)0U;
            code_tbl[idx][3] = (unsigned char)OP_COPY;
            code_tbl[idx][4] = (unsigned char)4U;
            code_tbl[idx][5] = (unsigned char)mode;
            idx = idx + 1U;
        }
    }

    for (mode = 0U; mode < 9U; mode = mode + 1U) {
        code_tbl[idx][0] = (unsigned char)OP_COPY;
        code_tbl[idx][1] = (unsigned char)4U;
        code_tbl[idx][2] = (unsigned char)mode;
        code_tbl[idx][3] = (unsigned char)OP_ADD;
        code_tbl[idx][4] = (unsigned char)1U;
        code_tbl[idx][5] = (unsigned char)0U;
        idx = idx + 1U;
    }

    code_tbl_built = 1U;
}

/* ---------- Address decoding ---------- */
/*
 * near_arr (4 slots) and same_arr (3*256 slots) are passed in as plain
 * arrays. The caller owns them on the stack; this function reads and
 * updates them in place. near_ptr is passed by value and returned in the
 * result struct so the function has no pointers to locals of its caller
 * beyond the arrays themselves.
 */
static struct ar_t decode_address(unsigned char *patch,
                                  unsigned int addr_end,
                                  unsigned int pos,
                                  unsigned int here,
                                  unsigned int mode,
                                  unsigned int near_ptr)
{
    struct ar_t r;
    struct pr_t p;
    unsigned int addr;

    r.near_ptr = near_ptr;

    if (mode == 0U) {
        p = read_varint(patch, addr_end, pos);
        if (p.err != VCD_OK) {
            r.pos = p.pos; r.addr = 0U; r.err = p.err; return r;
        }
        addr = p.val;
        r.pos = p.pos;
    } else if (mode == 1U) {
        p = read_varint(patch, addr_end, pos);
        if (p.err != VCD_OK) {
            r.pos = p.pos; r.addr = 0U; r.err = p.err; return r;
        }
        if (p.val > here) {
            r.pos = p.pos; r.addr = 0U; r.err = VCD_ERR_SRC; return r;
        }
        addr = here - p.val;
        r.pos = p.pos;
    } else if (mode < 2U + NEAR_SZ) {
        p = read_varint(patch, addr_end, pos);
        if (p.err != VCD_OK) {
            r.pos = p.pos; r.addr = 0U; r.err = p.err; return r;
        }
        addr = near_arr[mode - 2U] + p.val;
        r.pos = p.pos;
    } else if (mode < 2U + NEAR_SZ + SAME_SZ) {
        struct pr_t pb;
        unsigned int slot;
        pb = read_byte(patch, addr_end, pos);
        if (pb.err != VCD_OK) {
            r.pos = pb.pos; r.addr = 0U; r.err = pb.err; return r;
        }
        slot = (mode - 2U - NEAR_SZ) * 256U + pb.val;
        addr = same_arr[slot];
        r.pos = pb.pos;
    } else {
        r.pos = pos; r.addr = 0U; r.err = VCD_ERR_MODE; return r;
    }

    near_arr[r.near_ptr] = addr;
    r.near_ptr = (r.near_ptr + 1U) % NEAR_SZ;
    same_arr[addr % (SAME_SZ * 256U)] = addr;

    r.addr = addr;
    r.err = VCD_OK;
    return r;
}

/* ---------- Main decoder ---------- */

int vcdiff_decode(unsigned char *patch, unsigned int patch_len,
                  unsigned char *src, unsigned int src_len,
                  unsigned char *out, unsigned int out_cap,
                  unsigned int *out_len)
{
    unsigned int pos;
    unsigned int win_ind;
    unsigned int src_seg_len;
    unsigned int src_seg_off;
    unsigned int dlen;
    unsigned int delta_start;
    unsigned int tgt_len;
    unsigned int data_len;
    unsigned int inst_len;
    unsigned int addr_len;
    unsigned int adler_len;
    unsigned int consumed;
    unsigned int remaining;
    unsigned int data_pos;
    unsigned int inst_pos;
    unsigned int addr_pos;
    unsigned int data_cursor;
    unsigned int inst_cursor;
    unsigned int addr_cursor;
    unsigned int data_end;
    unsigned int inst_end;
    unsigned int addr_end;
    unsigned int tgt_pos;
    unsigned int i;
    unsigned char hi;
    struct pr_t p;
    unsigned int near_ptr;

    *out_len = 0U;

    /* Header: D6 C3 C4 00 Hdr_Indicator */
    if (patch_len < 5U) {
        return VCD_ERR_TRUNC;
    }
    if (patch[0] != (unsigned char)0xD6U) return VCD_ERR_MAGIC;
    if (patch[1] != (unsigned char)0xC3U) return VCD_ERR_MAGIC;
    if (patch[2] != (unsigned char)0xC4U) return VCD_ERR_MAGIC;
    if (patch[3] != (unsigned char)0x00U) return VCD_ERR_MAGIC;

    hi = patch[4];
    if ((hi & 0x03U) != 0U) return VCD_ERR_HDR;
    pos = 5U;

    if ((hi & 0x04U) != 0U) {
        unsigned int app_len;
        p = read_varint(patch, patch_len, pos);
        if (p.err != VCD_OK) return p.err;
        pos = p.pos;
        app_len = p.val;
        if (app_len > patch_len - pos) return VCD_ERR_TRUNC;
        pos = pos + app_len;
    }

    if (code_tbl_built == 0U) {
        build_code_table();
    }

    near_ptr = 0U;
    for (i = 0U; i < NEAR_SZ; i = i + 1U) near_arr[i] = 0U;
    for (i = 0U; i < SAME_SZ * 256U; i = i + 1U) same_arr[i] = 0U;

    p = read_byte(patch, patch_len, pos);
    if (p.err != VCD_OK) return p.err;
    pos = p.pos;
    win_ind = p.val;

    if ((win_ind & 0x02U) != 0U) return VCD_ERR_WIN;
    if ((win_ind & ~(0x01U | 0x04U)) != 0U) return VCD_ERR_WIN;

    src_seg_len = 0U;
    src_seg_off = 0U;
    if ((win_ind & 0x01U) != 0U) {
        if (src == (unsigned char *)0) return VCD_ERR_SRCNEED;
        p = read_varint(patch, patch_len, pos);
        if (p.err != VCD_OK) return p.err;
        pos = p.pos;
        src_seg_len = p.val;
        p = read_varint(patch, patch_len, pos);
        if (p.err != VCD_OK) return p.err;
        pos = p.pos;
        src_seg_off = p.val;
        if (src_seg_off > src_len) return VCD_ERR_SRC;
        if (src_seg_len > src_len - src_seg_off) return VCD_ERR_SRC;
    }

    p = read_varint(patch, patch_len, pos);
    if (p.err != VCD_OK) return p.err;
    pos = p.pos;
    dlen = p.val;
    delta_start = pos;
    if (dlen > patch_len - pos) return VCD_ERR_TRUNC;

    p = read_varint(patch, patch_len, pos);
    if (p.err != VCD_OK) return p.err;
    pos = p.pos;
    tgt_len = p.val;
    if (tgt_len > out_cap) return VCD_ERR_OUTCAP;

    p = read_byte(patch, patch_len, pos);
    if (p.err != VCD_OK) return p.err;
    pos = p.pos;
    if (p.val != 0U) return VCD_ERR_DI;

    p = read_varint(patch, patch_len, pos);
    if (p.err != VCD_OK) return p.err;
    pos = p.pos;
    data_len = p.val;

    p = read_varint(patch, patch_len, pos);
    if (p.err != VCD_OK) return p.err;
    pos = p.pos;
    inst_len = p.val;

    p = read_varint(patch, patch_len, pos);
    if (p.err != VCD_OK) return p.err;
    pos = p.pos;
    addr_len = p.val;

    adler_len = 0U;
    if ((win_ind & 0x04U) != 0U) adler_len = 4U;

    consumed = pos - delta_start;
    if (dlen < consumed) return VCD_ERR_SIZE;
    remaining = dlen - consumed;
    if (remaining != data_len + inst_len + addr_len + adler_len) {
        return VCD_ERR_SIZE;
    }

    pos = pos + adler_len;

    data_pos = pos;
    inst_pos = data_pos + data_len;
    addr_pos = inst_pos + inst_len;

    data_cursor = data_pos;
    inst_cursor = inst_pos;
    addr_cursor = addr_pos;
    data_end = data_pos + data_len;
    inst_end = inst_pos + inst_len;
    addr_end = addr_pos + addr_len;
    tgt_pos = 0U;

    while (inst_cursor < inst_end) {
        unsigned int op;
        unsigned int which;

        p = read_byte(patch, inst_end, inst_cursor);
        if (p.err != VCD_OK) return p.err;
        inst_cursor = p.pos;
        op = p.val;

        for (which = 0U; which < 2U; which = which + 1U) {
            unsigned int base = which * 3U;
            unsigned int typ = (unsigned int)code_tbl[op][base + 0U];
            unsigned int sz  = (unsigned int)code_tbl[op][base + 1U];
            unsigned int md  = (unsigned int)code_tbl[op][base + 2U];

            if (typ == OP_NOOP) continue;

            if (sz == 0U) {
                p = read_varint(patch, inst_end, inst_cursor);
                if (p.err != VCD_OK) return p.err;
                inst_cursor = p.pos;
                sz = p.val;
            }

            if (tgt_pos + sz > tgt_len) return VCD_ERR_OVERRUN;

            if (typ == OP_ADD) {
                unsigned int j;
                if (sz > data_end - data_cursor) return VCD_ERR_TRUNC;
                for (j = 0U; j < sz; j = j + 1U) {
                    out[tgt_pos + j] = patch[data_cursor + j];
                }
                data_cursor = data_cursor + sz;
                tgt_pos = tgt_pos + sz;
            } else if (typ == OP_RUN) {
                unsigned char fill;
                unsigned int j;
                if (data_cursor >= data_end) return VCD_ERR_TRUNC;
                fill = patch[data_cursor];
                data_cursor = data_cursor + 1U;
                for (j = 0U; j < sz; j = j + 1U) {
                    out[tgt_pos + j] = fill;
                }
                tgt_pos = tgt_pos + sz;
            } else {
                /* COPY */
                unsigned int here_addr = src_seg_len + tgt_pos;
                struct ar_t ar;
                unsigned int j;
                ar = decode_address(patch, addr_end, addr_cursor, here_addr,
                                    md, near_ptr);
                if (ar.err != VCD_OK) return ar.err;
                addr_cursor = ar.pos;
                near_ptr = ar.near_ptr;
                if (ar.addr >= here_addr) return VCD_ERR_SRC;
                for (j = 0U; j < sz; j = j + 1U) {
                    unsigned int a = ar.addr + j;
                    unsigned char byte;
                    if (a < src_seg_len) {
                        byte = src[src_seg_off + a];
                    } else {
                        unsigned int tgt_rel = a - src_seg_len;
                        if (tgt_rel >= tgt_pos + j) return VCD_ERR_SRC;
                        byte = out[tgt_rel];
                    }
                    out[tgt_pos + j] = byte;
                }
                tgt_pos = tgt_pos + sz;
            }
        }
    }

    if (tgt_pos != tgt_len) return VCD_ERR_SIZE;
    if (data_cursor != data_end) return VCD_ERR_SIZE;
    if (addr_cursor != addr_end) return VCD_ERR_SIZE;

    *out_len = tgt_pos;
    return VCD_OK;
}
