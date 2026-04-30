/*
 * Minimal VCDIFF encoder (RFC 3284, simplified):
 *   - Single window
 *   - No source segment (VCD_SOURCE/VCD_TARGET both unset)
 *   - One ADD instruction for the entire target (default code table opcode 1
 *     with an explicit size varint)
 *   - No secondary compression, no application header
 *
 * Output layout:
 *   Header        : D6 C3 C4 00 00
 *   Window:
 *     Win_Indicator           : 00
 *     Delta_Encoding_Length   : varint
 *     Target_Window_Length    : varint (= target_len)
 *     Delta_Indicator         : 00
 *     Data_Section_Length     : varint (= target_len)
 *     Inst_Section_Length     : varint (= 1 + varint_size(target_len))
 *     Addr_Section_Length     : varint (= 0)
 *     Data section            : target bytes
 *     Inst section            : 01 <varint(target_len)>
 *     Addr section            : (empty)
 *
 * Written in the AutoCorres2 C subset: no function pointers, no variadic,
 * no longjmp, restricted pointer arithmetic (indexing only).
 */

unsigned int vcdiff_varint_size(unsigned int v)
{
    unsigned int n = 1U;
    unsigned int x = v >> 7;
    while (x != 0U) {
        n = n + 1U;
        x = x >> 7;
    }
    return n;
}

unsigned int vcdiff_varint_write(unsigned char *out, unsigned int v)
{
    unsigned int n = vcdiff_varint_size(v);
    unsigned int i = 0U;
    while (i < n) {
        unsigned int shift = 7U * (n - 1U - i);
        unsigned char byte = (unsigned char)((v >> shift) & 0x7fU);
        if (i + 1U < n) {
            byte = (unsigned char)(byte | 0x80U);
        }
        out[i] = byte;
        i = i + 1U;
    }
    return n;
}

/*
 * Returns the number of bytes written into `out` on success, or 0 on
 * failure (buffer too small).
 *
 * Caller must ensure out != target (the encoder does not alias-check).
 */
unsigned int vcdiff_encode_add(unsigned char *out, unsigned int out_cap,
                               unsigned char *target, unsigned int target_len)
{
    unsigned int vn = vcdiff_varint_size(target_len);
    unsigned int inst_len = 1U + vn;

    /* Delta encoding length covers: target window length varint,
     * delta indicator, three section-length varints, and the three
     * sections themselves. */
    unsigned int dlen = vn              /* target window length */
                      + 1U              /* delta indicator */
                      + vn              /* data section length */
                      + vcdiff_varint_size(inst_len)
                      + 1U              /* addr section length varint for 0 */
                      + target_len
                      + inst_len;       /* no addr section bytes */

    unsigned int vdlen = vcdiff_varint_size(dlen);

    /* Total size = 5-byte header + 1-byte window indicator
     *            + varint(dlen) + dlen */
    unsigned int total = 5U + 1U + vdlen + dlen;

    unsigned int pos = 0U;
    unsigned int i = 0U;

    if (total > out_cap) {
        return 0U;
    }

    /* Header: magic + version 0 + header indicator 0 */
    out[0] = (unsigned char)0xD6U;
    out[1] = (unsigned char)0xC3U;
    out[2] = (unsigned char)0xC4U;
    out[3] = (unsigned char)0x00U;
    out[4] = (unsigned char)0x00U;
    pos = 5U;

    /* Window indicator: no source, no target */
    out[pos] = (unsigned char)0x00U;
    pos = pos + 1U;

    /* Delta encoding length */
    pos = pos + vcdiff_varint_write(out + pos, dlen);

    /* Target window length */
    pos = pos + vcdiff_varint_write(out + pos, target_len);

    /* Delta indicator */
    out[pos] = (unsigned char)0x00U;
    pos = pos + 1U;

    /* Data section length */
    pos = pos + vcdiff_varint_write(out + pos, target_len);

    /* Instructions section length */
    pos = pos + vcdiff_varint_write(out + pos, inst_len);

    /* Addresses section length */
    pos = pos + vcdiff_varint_write(out + pos, 0U);

    /* Data section: raw target bytes */
    while (i < target_len) {
        out[pos + i] = target[i];
        i = i + 1U;
    }
    pos = pos + target_len;

    /* Instructions section: opcode 01 (ADD, size follows) + varint(size) */
    out[pos] = (unsigned char)0x01U;
    pos = pos + 1U;
    pos = pos + vcdiff_varint_write(out + pos, target_len);

    /* No addresses section. */

    return pos;
}
