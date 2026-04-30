/*
 * VCDIFF encoder (RFC 3284, simplified):
 *   - Single window
 *   - VCD_SOURCE (source offset 0, length = src_len) when src_len > 0,
 *     otherwise Win_Indicator=0
 *   - Default code table (§5.4), default address cache (s_near=4, s_same=3)
 *   - No secondary compression, no adler32, no application header
 *
 * Matches the feature set our decoder in ../decoder/vcdiff_dec.c accepts.
 *
 * Strategy: 4-byte rolling hash + chained buckets over the source, greedy
 * match with chain cap, pending-ADD buffer with RUN detection, address
 * encoding via SELF/HERE/NEAR/SAME (picking the cheapest per match), and
 * opcode fusion for ADD(1..4)+COPY(4..6) where the code table allows.
 *
 * Written in the AutoCorres C subset: no function pointers, no variadics,
 * no longjmp, helpers communicate via struct returns, caches and tables
 * are file-scope arrays.
 */

#define HASH_BITS    16U
#define HASH_SIZE    (1U << HASH_BITS)
#define HASH_MASK    (HASH_SIZE - 1U)
#define NO_ENTRY     0xFFFFFFFFU
#define MAX_CHAIN    16U
#define MIN_MATCH    4U
#define MIN_RUN      4U

#define NEAR_SZ      4U
#define SAME_SZ      3U
#define SAME_BUCKETS (SAME_SZ * 256U)

#define ENC_OK       0U
#define ENC_OVERFLOW 1U

/* ---------- File-scope state (AutoCorres friendly) ---------- */

/* Hash index over the source. Caller sizes `head` to HASH_SIZE and
 * `next_arr` to >= src_len. We keep them file-scope so callers can pass
 * them as plain pointers; sizing is enforced by the caller. */
static unsigned int head_arr[HASH_SIZE];

/* Address cache (mirrors the decoder's state). */
static unsigned int near_arr[NEAR_SZ];
static unsigned int near_ptr;
static unsigned int same_arr[SAME_BUCKETS];

/* ---------- Struct returns ---------- */

struct wr_t {
    unsigned int pos;
    unsigned int err;
};

struct match_t {
    unsigned int pos;   /* source position */
    unsigned int len;   /* match length; 0 if no match */
};

struct op_t {
    unsigned int op;            /* opcode byte */
    unsigned int needs_size;    /* 1 if a size varint must follow */
};

struct mode_t {
    unsigned int mode;   /* 0..8 */
    unsigned int arg;    /* varint value (modes 0..5) or 1-byte slot (6..8) */
};

/* ---------- Varint ---------- */

static unsigned int varint_size(unsigned int v)
{
    unsigned int n = 1U;
    unsigned int x = v >> 7;
    while (x != 0U) {
        n = n + 1U;
        x = x >> 7;
    }
    return n;
}

static struct wr_t write_varint(unsigned char *buf, unsigned int cap,
                                unsigned int pos, unsigned int v)
{
    struct wr_t r;
    unsigned int n = varint_size(v);
    unsigned int i = 0U;
    if (n > cap - pos) {
        r.pos = pos; r.err = ENC_OVERFLOW; return r;
    }
    while (i < n) {
        unsigned int shift = 7U * (n - 1U - i);
        unsigned char byte = (unsigned char)((v >> shift) & 0x7FU);
        if (i + 1U < n) byte = (unsigned char)(byte | 0x80U);
        buf[pos + i] = byte;
        i = i + 1U;
    }
    r.pos = pos + n; r.err = ENC_OK;
    return r;
}

static struct wr_t write_byte(unsigned char *buf, unsigned int cap,
                              unsigned int pos, unsigned char b)
{
    struct wr_t r;
    if (pos >= cap) {
        r.pos = pos; r.err = ENC_OVERFLOW; return r;
    }
    buf[pos] = b;
    r.pos = pos + 1U; r.err = ENC_OK;
    return r;
}

static struct wr_t write_bytes(unsigned char *buf, unsigned int cap,
                               unsigned int pos,
                               unsigned char *src, unsigned int src_off,
                               unsigned int len)
{
    struct wr_t r;
    unsigned int i = 0U;
    if (len > cap - pos) {
        r.pos = pos; r.err = ENC_OVERFLOW; return r;
    }
    while (i < len) {
        buf[pos + i] = src[src_off + i];
        i = i + 1U;
    }
    r.pos = pos + len; r.err = ENC_OK;
    return r;
}

/* ---------- Hash index ---------- */

static unsigned int hash4(unsigned char *buf, unsigned int pos)
{
    /* Multiplicative 4-byte hash matching fdelta; any decent spread works. */
    unsigned int v = ((unsigned int)buf[pos])
                   | ((unsigned int)buf[pos + 1U] << 8)
                   | ((unsigned int)buf[pos + 2U] << 16)
                   | ((unsigned int)buf[pos + 3U] << 24);
    return v * 2654435761U;
}

static void build_index(unsigned char *src, unsigned int src_len,
                        unsigned int *next_arr)
{
    unsigned int i;
    for (i = 0U; i < HASH_SIZE; i = i + 1U) {
        head_arr[i] = NO_ENTRY;
    }
    if (src_len < MIN_MATCH) return;
    /* Walk source in reverse so the chain ends up in increasing position
     * order, like fdelta. Matching position order doesn't matter for
     * correctness — only for which of several candidates we pick first. */
    i = src_len - MIN_MATCH + 1U;
    while (i > 0U) {
        unsigned int p = i - 1U;
        unsigned int h = hash4(src, p) & HASH_MASK;
        next_arr[p] = head_arr[h];
        head_arr[h] = p;
        i = i - 1U;
    }
}

static unsigned int common_prefix(unsigned char *a, unsigned int a_pos, unsigned int a_end,
                                  unsigned char *b, unsigned int b_pos, unsigned int b_end)
{
    unsigned int n = 0U;
    unsigned int amax = a_end - a_pos;
    unsigned int bmax = b_end - b_pos;
    unsigned int lim = amax < bmax ? amax : bmax;
    while (n < lim && a[a_pos + n] == b[b_pos + n]) {
        n = n + 1U;
    }
    return n;
}

static struct match_t find_best_match(unsigned char *src, unsigned int src_len,
                                      unsigned char *tgt, unsigned int tgt_len,
                                      unsigned int tp, unsigned int *next_arr)
{
    struct match_t best;
    unsigned int cand;
    unsigned int checked = 0U;
    unsigned int best_len = 0U;
    unsigned int best_pos = 0U;

    best.pos = 0U; best.len = 0U;
    if (src_len < MIN_MATCH) return best;
    if (tgt_len - tp < MIN_MATCH) return best;

    cand = head_arr[hash4(tgt, tp) & HASH_MASK];
    while (cand != NO_ENTRY && checked < MAX_CHAIN) {
        if (cand + MIN_MATCH <= src_len) {
            unsigned int l = common_prefix(src, cand, src_len,
                                           tgt, tp, tgt_len);
            if (l >= MIN_MATCH && l > best_len) {
                best_len = l;
                best_pos = cand;
            }
        }
        cand = next_arr[cand];
        checked = checked + 1U;
    }
    best.pos = best_pos;
    best.len = best_len;
    return best;
}

/* ---------- Address cache ---------- */

static void cache_reset(void)
{
    unsigned int i;
    near_ptr = 0U;
    for (i = 0U; i < NEAR_SZ; i = i + 1U) near_arr[i] = 0U;
    for (i = 0U; i < SAME_BUCKETS; i = i + 1U) same_arr[i] = 0U;
}

static void cache_update(unsigned int addr)
{
    near_arr[near_ptr] = addr;
    near_ptr = (near_ptr + 1U) % NEAR_SZ;
    same_arr[addr % SAME_BUCKETS] = addr;
}

/* Pick the cheapest address mode for `addr` given `here`. Returns the
 * mode (0..8) and the encoded value (varint for 0..5, byte for 6..8).
 * SAME is only selected when the bucket already holds `addr` *and*
 * `addr != 0`, because the cache is zero-initialised and we must not
 * false-match on an untouched bucket. */
static struct mode_t best_mode(unsigned int addr, unsigned int here)
{
    struct mode_t r;
    unsigned int best_mode_v = 0U;
    unsigned int best_sz;
    unsigned int best_arg = addr;
    unsigned int i;

    best_sz = varint_size(addr);

    if (here > addr) {
        unsigned int d = here - addr;
        unsigned int s = varint_size(d);
        if (s < best_sz) { best_sz = s; best_mode_v = 1U; best_arg = d; }
    }

    for (i = 0U; i < NEAR_SZ; i = i + 1U) {
        unsigned int base = near_arr[i];
        if (addr >= base) {
            unsigned int d = addr - base;
            unsigned int s = varint_size(d);
            if (s < best_sz) {
                best_sz = s;
                best_mode_v = 2U + i;
                best_arg = d;
            }
        }
    }

    if (addr != 0U) {
        for (i = 0U; i < SAME_SZ; i = i + 1U) {
            unsigned int slot = i * 256U + (addr % 256U);
            if (same_arr[slot] == addr) {
                if (1U < best_sz) {
                    best_sz = 1U;
                    best_mode_v = 2U + NEAR_SZ + i;
                    best_arg = addr % 256U;
                }
            }
        }
    }

    r.mode = best_mode_v;
    r.arg = best_arg;
    return r;
}

static struct wr_t emit_address(unsigned char *addr_buf, unsigned int addr_cap,
                                unsigned int addr_pos,
                                struct mode_t m)
{
    if (m.mode < 2U + NEAR_SZ) {
        return write_varint(addr_buf, addr_cap, addr_pos, m.arg);
    }
    return write_byte(addr_buf, addr_cap, addr_pos, (unsigned char)m.arg);
}

/* ---------- Opcode helpers ---------- */

static struct op_t single_add_opcode(unsigned int sz)
{
    struct op_t r;
    if (sz >= 1U && sz <= 17U) {
        r.op = 1U + sz;        /* opcodes 2..18 */
        r.needs_size = 0U;
    } else {
        r.op = 1U;             /* opcode 1 = ADD size-varint */
        r.needs_size = 1U;
    }
    return r;
}

static struct op_t single_copy_opcode(unsigned int sz, unsigned int mode)
{
    struct op_t r;
    unsigned int base = 19U + mode * 16U;   /* per-mode block */
    if (sz >= 4U && sz <= 18U) {
        r.op = base - 3U + sz; /* size 4 → base+1; size 18 → base+15 */
        r.needs_size = 0U;
    } else {
        r.op = base;           /* varint size */
        r.needs_size = 1U;
    }
    return r;
}

/* ADD(1..4) + COPY(4..6 mode 0..5, or 4 mode 6..8). Returns opcode or 0
 * if the combination isn't representable in the default table. */
static unsigned int add_copy_opcode(unsigned int add_sz, unsigned int copy_sz,
                                    unsigned int mode)
{
    if (add_sz < 1U || add_sz > 4U) return 0U;
    if (mode <= 5U) {
        if (copy_sz >= 4U && copy_sz <= 6U) {
            return 163U + mode * 12U
                 + (add_sz - 1U) * 3U
                 + (copy_sz - 4U);
        }
    } else if (mode <= 8U) {
        if (copy_sz == 4U) {
            return 235U + (mode - 6U) * 4U + (add_sz - 1U);
        }
    }
    return 0U;
}

/* ---------- Emit helpers ---------- */

/* Two-cursor state for the three output sections. We pass cursors in and
 * return updated cursors via struct, avoiding &local pointers. */
struct sections_t {
    unsigned int data_pos;
    unsigned int inst_pos;
    unsigned int addr_pos;
    unsigned int err;
};

static struct sections_t emit_add(struct sections_t s,
                                  unsigned char *data, unsigned int data_cap,
                                  unsigned char *inst, unsigned int inst_cap,
                                  unsigned char *pending, unsigned int off,
                                  unsigned int sz)
{
    struct op_t op = single_add_opcode(sz);
    struct wr_t w;

    w = write_byte(inst, inst_cap, s.inst_pos, (unsigned char)op.op);
    if (w.err != ENC_OK) { s.err = w.err; return s; }
    s.inst_pos = w.pos;

    if (op.needs_size) {
        w = write_varint(inst, inst_cap, s.inst_pos, sz);
        if (w.err != ENC_OK) { s.err = w.err; return s; }
        s.inst_pos = w.pos;
    }
    w = write_bytes(data, data_cap, s.data_pos, pending, off, sz);
    if (w.err != ENC_OK) { s.err = w.err; return s; }
    s.data_pos = w.pos;
    return s;
}

static struct sections_t emit_run(struct sections_t s,
                                  unsigned char *data, unsigned int data_cap,
                                  unsigned char *inst, unsigned int inst_cap,
                                  unsigned char fill, unsigned int sz)
{
    struct wr_t w;
    w = write_byte(inst, inst_cap, s.inst_pos, (unsigned char)0U); /* opcode 0 */
    if (w.err != ENC_OK) { s.err = w.err; return s; }
    s.inst_pos = w.pos;
    w = write_varint(inst, inst_cap, s.inst_pos, sz);
    if (w.err != ENC_OK) { s.err = w.err; return s; }
    s.inst_pos = w.pos;
    w = write_byte(data, data_cap, s.data_pos, fill);
    if (w.err != ENC_OK) { s.err = w.err; return s; }
    s.data_pos = w.pos;
    return s;
}

/* Flush `pending[0..len)` splitting out RUNs of length >= MIN_RUN. */
static struct sections_t flush_pending(struct sections_t s,
                                       unsigned char *data, unsigned int data_cap,
                                       unsigned char *inst, unsigned int inst_cap,
                                       unsigned char *pending, unsigned int len)
{
    unsigned int i = 0U;
    unsigned int add_start = 0U;
    while (i < len) {
        unsigned char b = pending[i];
        unsigned int j = i + 1U;
        while (j < len && pending[j] == b) j = j + 1U;
        if (j - i >= MIN_RUN) {
            if (i > add_start) {
                s = emit_add(s, data, data_cap, inst, inst_cap,
                             pending, add_start, i - add_start);
                if (s.err != ENC_OK) return s;
            }
            s = emit_run(s, data, data_cap, inst, inst_cap, b, j - i);
            if (s.err != ENC_OK) return s;
            i = j;
            add_start = j;
        } else {
            i = j;
        }
    }
    if (len > add_start) {
        s = emit_add(s, data, data_cap, inst, inst_cap,
                     pending, add_start, len - add_start);
    }
    return s;
}

/* Emit a COPY. `addr` is the absolute combined-window address. */
static struct sections_t emit_copy(struct sections_t s,
                                   unsigned char *inst, unsigned int inst_cap,
                                   unsigned char *addr_buf, unsigned int addr_cap,
                                   unsigned int addr, unsigned int here,
                                   unsigned int len)
{
    struct mode_t m = best_mode(addr, here);
    struct op_t op = single_copy_opcode(len, m.mode);
    struct wr_t w;

    w = write_byte(inst, inst_cap, s.inst_pos, (unsigned char)op.op);
    if (w.err != ENC_OK) { s.err = w.err; return s; }
    s.inst_pos = w.pos;

    if (op.needs_size) {
        w = write_varint(inst, inst_cap, s.inst_pos, len);
        if (w.err != ENC_OK) { s.err = w.err; return s; }
        s.inst_pos = w.pos;
    }
    w = emit_address(addr_buf, addr_cap, s.addr_pos, m);
    if (w.err != ENC_OK) { s.err = w.err; return s; }
    s.addr_pos = w.pos;

    cache_update(addr);
    return s;
}

/* Emit fused ADD+COPY when applicable, else separate. Returns 1 if fused,
 * 0 if the caller should flush+emit separately. */
struct fused_t {
    struct sections_t s;
    unsigned int fused;
};

static struct fused_t try_emit_add_copy(struct sections_t s,
                                        unsigned char *data, unsigned int data_cap,
                                        unsigned char *inst, unsigned int inst_cap,
                                        unsigned char *addr_buf, unsigned int addr_cap,
                                        unsigned char *pending, unsigned int pend_len,
                                        unsigned int addr, unsigned int here,
                                        unsigned int copy_len)
{
    struct fused_t f;
    struct mode_t m;
    unsigned int op;
    struct wr_t w;
    f.s = s; f.fused = 0U;

    if (pend_len < 1U || pend_len > 4U) return f;
    if (copy_len < 4U) return f;
    /* The fused table only supports copy_len ≤ 6 (mode 0..5) or == 4
     * (mode 6..8). We don't precompute mode here because we want
     * best_mode to pick — but best_mode's output mode may not match a
     * fused-table row, in which case we fall back. */
    m = best_mode(addr, here);
    {
        unsigned int csz = copy_len;
        /* Cap the fused COPY size to the table's max for the chosen mode. */
        if (m.mode <= 5U) {
            if (csz > 6U) csz = 6U;
        } else {
            if (csz != 4U) return f;
        }
        op = add_copy_opcode(pend_len, csz, m.mode);
        if (op == 0U) return f;

        /* Check that fusing actually saves space. A separate flush+COPY
         * would need: add_inst_bytes (1 or 2) + copy_inst_bytes (1) +
         * maybe copy_size_varint. Fused is 1 inst byte. We always save at
         * least 1 byte in the inst section, so always prefer the fusion
         * when it's representable. */
        w = write_byte(inst, inst_cap, f.s.inst_pos, (unsigned char)op);
        if (w.err != ENC_OK) { f.s.err = w.err; return f; }
        f.s.inst_pos = w.pos;
        w = write_bytes(data, data_cap, f.s.data_pos, pending, 0U, pend_len);
        if (w.err != ENC_OK) { f.s.err = w.err; return f; }
        f.s.data_pos = w.pos;
        w = emit_address(addr_buf, addr_cap, f.s.addr_pos, m);
        if (w.err != ENC_OK) { f.s.err = w.err; return f; }
        f.s.addr_pos = w.pos;

        cache_update(addr);
        f.fused = 1U;
        /* If csz < copy_len, the caller still needs to cover the remaining
         * bytes. We return fused=1 and signal the consumed count via a
         * convention: actual consumed copy bytes = csz. To keep the
         * interface simple we just cap at 6 and the caller handles any
         * tail via a follow-up emit. Since csz ≤ copy_len ≤ table-max,
         * we report csz through a side-channel: encode_window reads
         * f.s.data_pos - pre_data_pos (= pend_len) and derives the copy
         * length from the opcode — simpler to just pass csz back. */
        f.fused = csz; /* reuse the field as "bytes of COPY consumed" */
        return f;
    }
}

/* ---------- Main encode ---------- */

static struct sections_t encode_window(unsigned char *src, unsigned int src_len,
                                       unsigned char *tgt, unsigned int tgt_len,
                                       unsigned int *next_arr,
                                       unsigned char *data, unsigned int data_cap,
                                       unsigned char *inst, unsigned int inst_cap,
                                       unsigned char *addr_buf, unsigned int addr_cap,
                                       unsigned char *pending, unsigned int pending_cap)
{
    struct sections_t s;
    unsigned int tp = 0U;
    unsigned int pend_len = 0U;

    s.data_pos = 0U;
    s.inst_pos = 0U;
    s.addr_pos = 0U;
    s.err = ENC_OK;

    cache_reset();

    while (tp < tgt_len) {
        struct match_t m = find_best_match(src, src_len, tgt, tgt_len, tp,
                                           next_arr);
        if (m.len < MIN_MATCH) {
            if (pend_len >= pending_cap) { s.err = ENC_OVERFLOW; return s; }
            pending[pend_len] = tgt[tp];
            pend_len = pend_len + 1U;
            tp = tp + 1U;
            continue;
        }
        {
            unsigned int here = src_len + tp;
            struct fused_t f;
            /* Try ADD(pending)+COPY fusion first. */
            f = try_emit_add_copy(s, data, data_cap, inst, inst_cap,
                                  addr_buf, addr_cap,
                                  pending, pend_len, m.pos, here, m.len);
            if (f.s.err != ENC_OK) return f.s;
            if (f.fused != 0U) {
                unsigned int consumed = f.fused;
                s = f.s;
                pend_len = 0U;
                tp = tp + consumed;
                /* If the match was longer than the fused COPY could cover,
                 * emit the remainder as a plain COPY (same source
                 * address + consumed). */
                if (consumed < m.len) {
                    unsigned int rem = m.len - consumed;
                    unsigned int rem_addr = m.pos + consumed;
                    unsigned int rem_here = src_len + tp;
                    s = emit_copy(s, inst, inst_cap, addr_buf, addr_cap,
                                  rem_addr, rem_here, rem);
                    if (s.err != ENC_OK) return s;
                    tp = tp + rem;
                }
                continue;
            }
            /* No fusion: flush pending then emit a plain COPY. */
            if (pend_len > 0U) {
                s = flush_pending(s, data, data_cap, inst, inst_cap,
                                  pending, pend_len);
                if (s.err != ENC_OK) return s;
                pend_len = 0U;
            }
            s = emit_copy(s, inst, inst_cap, addr_buf, addr_cap,
                          m.pos, here, m.len);
            if (s.err != ENC_OK) return s;
            tp = tp + m.len;
        }
    }

    if (pend_len > 0U) {
        s = flush_pending(s, data, data_cap, inst, inst_cap,
                          pending, pend_len);
    }
    return s;
}

/* ---------- Top-level ---------- */

/* Serialize the 5-byte header, window indicator, source-segment descriptor
 * (if any), delta header, and the three sections. Returns bytes written,
 * or 0 on overflow / inconsistency. */
static unsigned int serialize(unsigned char *out, unsigned int out_cap,
                              unsigned int src_len,
                              unsigned int tgt_len,
                              unsigned char *data, unsigned int data_len,
                              unsigned char *inst, unsigned int inst_len,
                              unsigned char *addr_buf, unsigned int addr_len)
{
    struct wr_t w;
    unsigned int pos = 0U;
    unsigned int has_src = (src_len > 0U) ? 1U : 0U;
    unsigned int win_ind = has_src ? 0x01U : 0x00U;
    unsigned int vs_tgt  = varint_size(tgt_len);
    unsigned int vs_data = varint_size(data_len);
    unsigned int vs_inst = varint_size(inst_len);
    unsigned int vs_addr = varint_size(addr_len);
    unsigned int dlen    = vs_tgt + 1U + vs_data + vs_inst + vs_addr
                         + data_len + inst_len + addr_len;

#define STEP(expr) do { \
    w = (expr); \
    if (w.err != ENC_OK) return 0U; \
    pos = w.pos; \
} while (0)

    STEP(write_byte(out, out_cap, pos, 0xD6U));
    STEP(write_byte(out, out_cap, pos, 0xC3U));
    STEP(write_byte(out, out_cap, pos, 0xC4U));
    STEP(write_byte(out, out_cap, pos, 0x00U));
    STEP(write_byte(out, out_cap, pos, 0x00U));

    STEP(write_byte(out, out_cap, pos, (unsigned char)win_ind));

    if (has_src) {
        STEP(write_varint(out, out_cap, pos, src_len));
        STEP(write_varint(out, out_cap, pos, 0U));
    }

    STEP(write_varint(out, out_cap, pos, dlen));
    STEP(write_varint(out, out_cap, pos, tgt_len));
    STEP(write_byte(out, out_cap, pos, 0x00U));   /* delta indicator */
    STEP(write_varint(out, out_cap, pos, data_len));
    STEP(write_varint(out, out_cap, pos, inst_len));
    STEP(write_varint(out, out_cap, pos, addr_len));

    STEP(write_bytes(out, out_cap, pos, data, 0U, data_len));
    STEP(write_bytes(out, out_cap, pos, inst, 0U, inst_len));
    STEP(write_bytes(out, out_cap, pos, addr_buf, 0U, addr_len));

    return pos;
#undef STEP
}

/* Public entrypoint.
 *
 * Caller-provided scratch buffer sizes:
 *   next_arr : >= src_len (or >= 1 if src_len == 0; pass any non-null ptr)
 *   pending  : >= tgt_len  (+1 for the tail byte of a degenerate case)
 *   data_sec, inst_sec, addr_sec : each tgt_len + 64 bytes is enough.
 *   out      : tgt_len + src_len-ish; a safe cap is tgt_len * 2 + 1024.
 *
 * Returns bytes written to `out` on success, or 0 on any overflow. */
unsigned int vcdiff_encode(unsigned char *out, unsigned int out_cap,
                           unsigned char *src, unsigned int src_len,
                           unsigned char *tgt, unsigned int tgt_len,
                           unsigned int *next_arr,
                           unsigned char *pending, unsigned int pending_cap,
                           unsigned char *data_sec, unsigned int data_cap,
                           unsigned char *inst_sec, unsigned int inst_cap,
                           unsigned char *addr_sec, unsigned int addr_cap)
{
    struct sections_t s;

    if (pending_cap < tgt_len) return 0U;

    build_index(src, src_len, next_arr);

    s = encode_window(src, src_len, tgt, tgt_len, next_arr,
                      data_sec, data_cap,
                      inst_sec, inst_cap,
                      addr_sec, addr_cap,
                      pending, pending_cap);
    if (s.err != ENC_OK) return 0U;

    return serialize(out, out_cap, src_len, tgt_len,
                     data_sec, s.data_pos,
                     inst_sec, s.inst_pos,
                     addr_sec, s.addr_pos);
}

/* ---------- Backwards-compat shim ---------- */
/* The old harness + Rust wrapper may still reference `vcdiff_encode_add`.
 * Keep a thin wrapper so the existing round-trip tests compile. It
 * degenerates to an encode with src_len=0. Callers must provide the
 * same scratch recipe. */
unsigned int vcdiff_encode_add(unsigned char *out, unsigned int out_cap,
                               unsigned char *target, unsigned int target_len)
{
    /* The old API had no scratch. For use from the legacy harness only:
     * allocate static scratch sized to a modest bound. If target_len
     * exceeds it, the caller should switch to vcdiff_encode. */
    static unsigned int s_next[4];
    static unsigned char s_pending[65536];
    static unsigned char s_data[65536 + 64];
    static unsigned char s_inst[65536 + 64];
    static unsigned char s_addr[65536 + 64];
    if (target_len > 65536U) return 0U;
    return vcdiff_encode(out, out_cap,
                         (unsigned char *)0, 0U,
                         target, target_len,
                         s_next,
                         s_pending, 65536U,
                         s_data, 65536U + 64U,
                         s_inst, 65536U + 64U,
                         s_addr, 65536U + 64U);
}
