#!/usr/bin/env python3
"""Makes the JPEG test corpus and its reference outputs (phase-6.md item 6.5).

Usage, on Linux with libjpeg-turbo's runtime library (`libjpeg.so.8`) and a
checkout of libjpeg-turbo at the pinned tag for its `testimages/`:

    python3 scripts/jpeg-reference.py LIBJPEG_TURBO_CHECKOUT OUT_DIR

It writes, into `OUT_DIR`:

- `testorig.ref`, `testimgint.ref`: libjpeg-turbo's output for two of its
  own test images (`testimages/testorig.jpg`, `testimgint.jpg`);
- `corpus.pack`: JPEG files this script encodes from
  `testimages/testorig.ppm` (every sampling ratio, restart intervals,
  non-interleaved scans, RGB, CMYK and YCCK, extended sequential, 16-bit
  quantization tables, EXIF orientations, awkward sizes) each followed by
  libjpeg-turbo's output for it.

Both come from the same decoder, driven through ctypes: the installed
libjpeg-turbo (Ubuntu 24.04's `libjpeg-turbo8` 2.1.5-2ubuntu2, built with
the libjpeg 8 API), with its defaults (`jpeg_read_header`,
`jpeg_start_decompress`, `jpeg_read_scanlines`: the integer `ISLOW` IDCT,
fancy upsampling, output colour space as `default_decompress_parms` picks
it). The plan asked for a build of the pinned 3.2.1 sources; building them
was not possible in the session that wrote this (see
`crates/clazel-jpeg/README.md`), so the pin is the version below, and the
outputs should be regenerated against 3.2.1 when it can be built.

Reference file format (`.ref`, and the second part of each corpus record):
`width` and `height` as 4-byte little-endian integers, the number of
channels (1, 3 or 4) as a byte, then the samples row by row, as libjpeg
returns them (gray, RGB or CMYK as the library's output colour space is).

Pack format: records of `name length` (1 byte), the name, the JPEG's
length (4 bytes little-endian), the JPEG, the reference's length (4 bytes
little-endian) and the reference (length 0: libjpeg-turbo refuses the file
or it is not one this decoder reads).

The encoder is a plain float DCT with the standard Annex K tables; it is
here only to make varied valid files, and is not part of the tested code.
"""

import ctypes
import math
import os
import struct
import sys

# ---------------------------------------------------------------- reference

LIB = ctypes.CDLL("libjpeg.so.8")


class ErrMgr(ctypes.Structure):
    _fields_ = [
        ("error_exit", ctypes.c_void_p),
        ("emit_message", ctypes.c_void_p),
        ("output_message", ctypes.c_void_p),
        ("format_message", ctypes.c_void_p),
        ("reset_error_mgr", ctypes.c_void_p),
        ("msg_code", ctypes.c_int),
        ("msg_parm", ctypes.c_char * 80),  # a union of int[8] and char[80]
        ("trace_level", ctypes.c_int),
        ("num_warnings", ctypes.c_long),
        ("jpeg_message_table", ctypes.c_void_p),
        ("last_jpeg_message", ctypes.c_int),
        ("addon_message_table", ctypes.c_void_p),
        ("first_addon_message", ctypes.c_int),
        ("last_addon_message", ctypes.c_int),
    ]


_CB = ctypes.CFUNCTYPE(None, ctypes.c_void_p)
_ERR = ErrMgr()
LIB.jpeg_std_error.restype = ctypes.c_void_p
LIB.jpeg_std_error(ctypes.byref(_ERR))


def _raise(_cinfo):
    # libjpeg expects error_exit never to return (it longjmps in C); an
    # exception cannot unwind through it, so stop. `ref_bytes` only calls the
    # library for files it has checked, so this is a bug of the script.
    print("libjpeg error", _ERR.msg_code, file=sys.stderr)
    os._exit(2)


_RAISE = _CB(_raise)
_ERR.error_exit = ctypes.cast(_RAISE, ctypes.c_void_p).value

# Offsets in struct jpeg_decompress_struct of the libjpeg 8 API, LP64
# (656 bytes; the library checks the size).
OFF = dict(
    image_width=48,
    image_height=52,
    num_components=56,
    out_color_space=64,
    dct_method=96,
    do_fancy_upsampling=100,
    output_width=136,
    output_height=140,
    output_components=148,
)


def _rd(buf, key):
    return struct.unpack_from("<I", buf, OFF[key])[0]


def reference(data):
    """libjpeg-turbo's output for `data`: (width, height, channels, samples)."""
    buf = ctypes.create_string_buffer(656)
    struct.pack_into("<Q", buf, 0, ctypes.addressof(_ERR))
    LIB.jpeg_CreateDecompress(buf, 80, 656)
    try:
        src = ctypes.create_string_buffer(data, len(data))
        LIB.jpeg_mem_src(buf, src, ctypes.c_ulong(len(data)))
        LIB.jpeg_read_header(buf, 1)
        # The defaults the decoder under test copies.
        assert _rd(buf, "dct_method") == 0, "default DCT is not ISLOW"
        assert _rd(buf, "do_fancy_upsampling") == 1
        LIB.jpeg_start_decompress(buf)
        w, h, c = _rd(buf, "output_width"), _rd(buf, "output_height"), _rd(buf, "output_components")
        out = bytearray()
        row = ctypes.create_string_buffer(w * c)
        rp = (ctypes.c_void_p * 1)(ctypes.addressof(row))
        for _ in range(h):
            assert LIB.jpeg_read_scanlines(buf, rp, 1) == 1
            out += row.raw
        LIB.jpeg_finish_decompress(buf)
        return w, h, c, bytes(out)
    finally:
        LIB.jpeg_destroy_decompress(buf)


def sof(data):
    """The marker and precision of the first SOF of `data`, or None."""
    i = 2
    while i + 4 <= len(data) and data[i] == 0xFF:
        m = data[i + 1]
        if 0xC0 <= m <= 0xCF and m not in (0xC4, 0xC8, 0xCC):
            return m, data[i + 4]
        if m == 0xDA:
            return None
        i += 2 + struct.unpack(">H", data[i + 2:i + 4])[0]
    return None


def ref_bytes(data):
    """The reference for `data`, empty if it is not a baseline or extended
    sequential, 8-bit, Huffman file (what libjpeg-turbo built for 8-bit
    samples decodes, and the decoder under test reads)."""
    found = sof(data)
    if found is None or found[0] not in (0xC0, 0xC1) or found[1] != 8:
        return b""
    w, h, c, out = reference(data)
    return struct.pack("<IIB", w, h, c) + out


# ------------------------------------------------------------------ encoder

ZIGZAG = [
    0, 1, 8, 16, 9, 2, 3, 10, 17, 24, 32, 25, 18, 11, 4, 5, 12, 19, 26, 33, 40, 48, 41, 34, 27,
    20, 13, 6, 7, 14, 21, 28, 35, 42, 49, 56, 57, 50, 43, 36, 29, 22, 15, 23, 30, 37, 44, 51, 58,
    59, 52, 45, 38, 31, 39, 46, 53, 60, 61, 54, 47, 55, 62, 63,
]

# T.81 Annex K.1, Tables K.1 and K.2, natural order.
Q_LUM = [
    16, 11, 10, 16, 24, 40, 51, 61, 12, 12, 14, 19, 26, 58, 60, 55, 14, 13, 16, 24, 40, 57, 69,
    56, 14, 17, 22, 29, 51, 87, 80, 62, 18, 22, 37, 56, 68, 109, 103, 77, 24, 35, 55, 64, 81,
    104, 113, 92, 49, 64, 78, 87, 103, 121, 120, 101, 72, 92, 95, 98, 112, 100, 103, 99,
]
Q_CHR = [
    17, 18, 24, 47, 99, 99, 99, 99, 18, 21, 26, 66, 99, 99, 99, 99, 24, 26, 56, 99, 99, 99, 99,
    99, 47, 66, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99,
    99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99,
]

# T.81 Annex K.3.3, Tables K.3 to K.6.
DC_L = ([0, 1, 5, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0], list(range(12)))
DC_C = ([0, 3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0], list(range(12)))
AC_L = (
    [0, 2, 1, 3, 3, 2, 4, 3, 5, 5, 4, 4, 0, 0, 1, 0x7D],
    [
        0x01, 0x02, 0x03, 0x00, 0x04, 0x11, 0x05, 0x12, 0x21, 0x31, 0x41, 0x06, 0x13, 0x51, 0x61,
        0x07, 0x22, 0x71, 0x14, 0x32, 0x81, 0x91, 0xA1, 0x08, 0x23, 0x42, 0xB1, 0xC1, 0x15, 0x52,
        0xD1, 0xF0, 0x24, 0x33, 0x62, 0x72, 0x82, 0x09, 0x0A, 0x16, 0x17, 0x18, 0x19, 0x1A, 0x25,
        0x26, 0x27, 0x28, 0x29, 0x2A, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39, 0x3A, 0x43, 0x44, 0x45,
        0x46, 0x47, 0x48, 0x49, 0x4A, 0x53, 0x54, 0x55, 0x56, 0x57, 0x58, 0x59, 0x5A, 0x63, 0x64,
        0x65, 0x66, 0x67, 0x68, 0x69, 0x6A, 0x73, 0x74, 0x75, 0x76, 0x77, 0x78, 0x79, 0x7A, 0x83,
        0x84, 0x85, 0x86, 0x87, 0x88, 0x89, 0x8A, 0x92, 0x93, 0x94, 0x95, 0x96, 0x97, 0x98, 0x99,
        0x9A, 0xA2, 0xA3, 0xA4, 0xA5, 0xA6, 0xA7, 0xA8, 0xA9, 0xAA, 0xB2, 0xB3, 0xB4, 0xB5, 0xB6,
        0xB7, 0xB8, 0xB9, 0xBA, 0xC2, 0xC3, 0xC4, 0xC5, 0xC6, 0xC7, 0xC8, 0xC9, 0xCA, 0xD2, 0xD3,
        0xD4, 0xD5, 0xD6, 0xD7, 0xD8, 0xD9, 0xDA, 0xE1, 0xE2, 0xE3, 0xE4, 0xE5, 0xE6, 0xE7, 0xE8,
        0xE9, 0xEA, 0xF1, 0xF2, 0xF3, 0xF4, 0xF5, 0xF6, 0xF7, 0xF8, 0xF9, 0xFA,
    ],
)
AC_C = (
    [0, 2, 1, 2, 4, 4, 3, 4, 7, 5, 4, 4, 0, 1, 2, 0x77],
    [
        0x00, 0x01, 0x02, 0x03, 0x11, 0x04, 0x05, 0x21, 0x31, 0x06, 0x12, 0x41, 0x51, 0x07, 0x61,
        0x71, 0x13, 0x22, 0x32, 0x81, 0x08, 0x14, 0x42, 0x91, 0xA1, 0xB1, 0xC1, 0x09, 0x23, 0x33,
        0x52, 0xF0, 0x15, 0x62, 0x72, 0xD1, 0x0A, 0x16, 0x24, 0x34, 0xE1, 0x25, 0xF1, 0x17, 0x18,
        0x19, 0x1A, 0x26, 0x27, 0x28, 0x29, 0x2A, 0x35, 0x36, 0x37, 0x38, 0x39, 0x3A, 0x43, 0x44,
        0x45, 0x46, 0x47, 0x48, 0x49, 0x4A, 0x53, 0x54, 0x55, 0x56, 0x57, 0x58, 0x59, 0x5A, 0x63,
        0x64, 0x65, 0x66, 0x67, 0x68, 0x69, 0x6A, 0x73, 0x74, 0x75, 0x76, 0x77, 0x78, 0x79, 0x7A,
        0x82, 0x83, 0x84, 0x85, 0x86, 0x87, 0x88, 0x89, 0x8A, 0x92, 0x93, 0x94, 0x95, 0x96, 0x97,
        0x98, 0x99, 0x9A, 0xA2, 0xA3, 0xA4, 0xA5, 0xA6, 0xA7, 0xA8, 0xA9, 0xAA, 0xB2, 0xB3, 0xB4,
        0xB5, 0xB6, 0xB7, 0xB8, 0xB9, 0xBA, 0xC2, 0xC3, 0xC4, 0xC5, 0xC6, 0xC7, 0xC8, 0xC9, 0xCA,
        0xD2, 0xD3, 0xD4, 0xD5, 0xD6, 0xD7, 0xD8, 0xD9, 0xDA, 0xE2, 0xE3, 0xE4, 0xE5, 0xE6, 0xE7,
        0xE8, 0xE9, 0xEA, 0xF2, 0xF3, 0xF4, 0xF5, 0xF6, 0xF7, 0xF8, 0xF9, 0xFA,
    ],
)

# Every table must hold exactly the symbols the encoder can produce.
_AC_SYMS = {0x00, 0xF0} | {(r << 4) | s for r in range(16) for s in range(1, 11)}
for _bits, _vals in (AC_L, AC_C):
    assert sum(_bits) == len(_vals) == 162 and set(_vals) == _AC_SYMS


def huff_codes(table):
    """symbol -> (code, length), T.81 Figures C.1 and C.2."""
    bits, vals = table
    codes, code, k = {}, 0, 0
    for length in range(1, 17):
        for _ in range(bits[length - 1]):
            codes[vals[k]] = (code, length)
            code += 1
            k += 1
        code <<= 1
    return codes


COS = [[math.cos((2 * x + 1) * u * math.pi / 16) for x in range(8)] for u in range(8)]
CU = [1 / math.sqrt(2)] + [1.0] * 7


def fdct(block):
    """T.81 A.3.3 forward DCT of an 8x8 block (list of 64 level-shifted samples)."""
    tmp = [[0.0] * 8 for _ in range(8)]
    for y in range(8):
        for u in range(8):
            tmp[y][u] = 0.5 * CU[u] * sum(block[y * 8 + x] * COS[u][x] for x in range(8))
    out = [0.0] * 64
    for u in range(8):
        for v in range(8):
            out[v * 8 + u] = 0.5 * CU[v] * sum(tmp[y][u] * COS[v][y] for y in range(8))
    return out


def scale_q(table, quality):
    s = 5000 // quality if quality < 50 else 200 - quality * 2
    return [max(1, min(255, (q * s + 50) // 100)) for q in table]


class Bits:
    def __init__(self):
        self.out = bytearray()
        self.acc = 0
        self.n = 0

    def put(self, code, length):
        self.acc = (self.acc << length) | code
        self.n += length
        while self.n >= 8:
            b = (self.acc >> (self.n - 8)) & 0xFF
            self.out.append(b)
            if b == 0xFF:
                self.out.append(0)
            self.n -= 8
        self.acc &= (1 << self.n) - 1

    def flush(self):
        if self.n:
            self.put((1 << (8 - self.n)) - 1, 8 - self.n)


def size_of(v):
    return abs(v).bit_length()


def bits_of(v, s):
    return v if v >= 0 else v + (1 << s) - 1


def encode_block(bits, q, coef, pred, dc_codes, ac_codes):
    """Encodes one quantized block (zigzag list); returns the new predictor."""
    diff = coef[0] - pred
    s = size_of(diff)
    bits.put(*dc_codes[s])
    if s:
        bits.put(bits_of(diff, s), s)
    run = 0
    last = max((k for k in range(1, 64) if coef[k]), default=0)
    for k in range(1, last + 1):
        v = coef[k]
        if v == 0:
            run += 1
            continue
        while run > 15:
            bits.put(*ac_codes[0xF0])
            run -= 16
        s = size_of(v)
        bits.put(*ac_codes[(run << 4) | s])
        bits.put(bits_of(v, s), s)
        run = 0
    if last < 63:
        bits.put(*ac_codes[0x00])
    return coef[0]


def seg(marker, body):
    return bytes([0xFF, marker]) + struct.pack(">H", len(body) + 2) + body


def exif_app1(orientation, big=False):
    bo = ">" if big else "<"
    tiff = (b"MM" if big else b"II") + struct.pack(bo + "HI", 42, 8)
    tiff += struct.pack(bo + "H", 1) + struct.pack(bo + "HHIHH", 0x0112, 3, 1, orientation, 0)
    tiff += struct.pack(bo + "I", 0)
    return seg(0xE1, b"Exif\0\0" + tiff)


def encode(planes, *, h, v, restart=0, interleaved=True, jfif=True, adobe=None, sof=0,
           wide_q=False, orientation=None, big_exif=False, quality=75, tq=None, ids=None,
           tables=None):
    """planes: list of full-resolution 2-D lists (rows of ints 0..255), already
    in the colour space to code. h, v: sampling factors per component."""
    n = len(planes)
    height, width = len(planes[0]), len(planes[0][0])
    hmax, vmax = max(h), max(v)
    tq = tq or [0 if i in (0, 3) else 1 for i in range(n)]
    td = [0 if i in (0, 3) else 1 for i in range(n)]
    ids = ids or list(range(1, n + 1))
    qtabs = [scale_q(Q_LUM, quality), scale_q(Q_CHR, quality)]
    if wide_q:
        qtabs = [[min(65535, q * 3 + 300) for q in t] for t in qtabs]
    dc_codes = [huff_codes(DC_L), huff_codes(DC_C)]
    ac_codes = [huff_codes(AC_L), huff_codes(AC_C)]
    mcus_x = -(-width // (8 * hmax))
    mcus_y = -(-height // (8 * vmax))
    # Downsample (box average) and pad every plane to whole MCUs.
    comp = []
    for i in range(n):
        fx, fy = hmax // h[i], vmax // v[i]
        cw, ch = -(-width * h[i] // hmax), -(-height * v[i] // vmax)
        bw, bh = mcus_x * h[i], mcus_y * v[i]
        small = []
        for y in range(bh * 8):
            row = []
            for x in range(bw * 8):
                sy, sx = min(y, ch - 1), min(x, cw - 1)
                tot = cnt = 0
                for dy in range(fy):
                    for dx in range(fx):
                        py, px = min(sy * fy + dy, height - 1), min(sx * fx + dx, width - 1)
                        tot += planes[i][py][px]
                        cnt += 1
                row.append((tot + cnt // 2) // cnt)
            small.append(row)
        comp.append((small, cw, ch, bw, bh))

    def block_coefs(i, bx, by):
        small = comp[i][0]
        blk = [small[by * 8 + r][bx * 8 + c] - 128 for r in range(8) for c in range(8)]
        d = fdct(blk)
        q = qtabs[tq[i]]
        return [int(round(d[ZIGZAG[k]] / q[ZIGZAG[k]])) for k in range(64)]

    out = bytearray(b"\xFF\xD8")
    if jfif:
        out += seg(0xE0, b"JFIF\0" + bytes([1, 2, 0]) + struct.pack(">HH", 1, 1) + b"\0\0")
    if adobe is not None:
        out += seg(0xEE, b"Adobe" + struct.pack(">HHHB", 100, 0, 0, adobe))
    if orientation is not None:
        out += exif_app1(orientation, big_exif)
    out += seg(0xFE, b"made by scripts/jpeg-reference.py")
    for t in range(2):
        body = bytearray()
        q = qtabs[t]
        if wide_q:
            body.append(0x10 | t)
            for k in range(64):
                body += struct.pack(">H", q[ZIGZAG[k]])
        else:
            body.append(t)
            body += bytes(q[ZIGZAG[k]] for k in range(64))
        out += seg(0xDB, bytes(body))
    out += bytes([0xFF, 0xC0 + sof])
    sof_body = struct.pack(">BHHB", 8, height, width, n)
    for i in range(n):
        sof_body += bytes([ids[i], (h[i] << 4) | v[i], tq[i]])
    out += struct.pack(">H", len(sof_body) + 2) + sof_body
    for cls, tabs in ((0, (DC_L, DC_C)), (1, (AC_L, AC_C))):
        for t in range(2):
            bits, vals = tabs[t]
            out += seg(0xC4, bytes([(cls << 4) | t]) + bytes(bits) + bytes(vals))
    if restart:
        out += seg(0xDD, struct.pack(">H", restart))

    def scan(order, blocks_of):
        """order: component indexes; blocks_of(mcu) -> list of (comp, bx, by)."""
        body = bytes([len(order)]) + b"".join(bytes([ids[i], (td[i] << 4) | td[i]]) for i in order)
        body += bytes([0, 63, 0])
        s = bytearray(seg(0xDA, body))
        bits = Bits()
        preds = {i: 0 for i in order}
        total = len(blocks_of)
        rst = 0
        for m, blks in enumerate(blocks_of):
            if restart and m and m % restart == 0:
                bits.flush()
                s += bits.out
                s += bytes([0xFF, 0xD0 + rst])
                rst = (rst + 1) & 7
                bits = Bits()
                preds = {i: 0 for i in order}
            for (i, bx, by) in blks:
                preds[i] = encode_block(bits, None, block_coefs(i, bx, by), preds[i],
                                        dc_codes[td[i]], ac_codes[td[i]])
        bits.flush()
        s += bits.out
        return bytes(s)

    if interleaved:
        mcus = []
        for my in range(mcus_y):
            for mx in range(mcus_x):
                blks = []
                for i in range(n):
                    for by in range(v[i]):
                        for bx in range(h[i]):
                            blks.append((i, mx * h[i] + bx, my * v[i] + by))
                mcus.append(blks)
        out += scan(list(range(n)), mcus)
    else:
        for i in range(n):
            _, cw, ch, bw, bh = comp[i]
            mcus = [[(i, bx, by)] for by in range(-(-ch // 8)) for bx in range(-(-cw // 8))]
            out += scan([i], mcus)
    out += b"\xFF\xD9"
    return bytes(out)


# -------------------------------------------------------------------- images


def read_ppm(path):
    with open(path, "rb") as f:
        data = f.read()
    parts = data.split(b"\n", 3)
    assert parts[0] == b"P6"
    w, h = map(int, parts[1].split())
    assert parts[2] == b"255"
    px = parts[3]
    return w, h, [[tuple(px[(y * w + x) * 3:(y * w + x) * 3 + 3]) for x in range(w)] for y in range(h)]


def crop(img, w, h, x0=0, y0=0):
    return [row[x0:x0 + w] for row in img[y0:y0 + h]]


def to_ycc(img):
    ys, cbs, crs = [], [], []
    for row in img:
        yr, br, rr = [], [], []
        for (r, g, b) in row:
            yr.append(min(255, max(0, round(0.299 * r + 0.587 * g + 0.114 * b))))
            br.append(min(255, max(0, round(-0.168736 * r - 0.331264 * g + 0.5 * b + 128))))
            rr.append(min(255, max(0, round(0.5 * r - 0.418688 * g - 0.081312 * b + 128))))
        ys.append(yr)
        cbs.append(br)
        crs.append(rr)
    return [ys, cbs, crs]


def to_rgb(img):
    return [[[p[c] for p in row] for row in img] for c in range(3)]


def to_gray(img):
    return [[[min(255, round(0.299 * r + 0.587 * g + 0.114 * b)) for (r, g, b) in row] for row in img]]


def k_plane(img):
    """A fourth plane: a diagonal gradient with a pattern, so K matters."""
    hh, ww = len(img), len(img[0])
    return [[(255 * (x + y) // (ww + hh) + (40 if (x // 3 + y // 5) % 2 else 0)) % 256
             for x in range(ww)] for y in range(hh)]


def to_cmyk(img):
    return to_rgb(img) + [k_plane(img)]


def to_ycck(img):
    inv = [[(255 - r, 255 - g, 255 - b) for (r, g, b) in row] for row in img]
    return to_ycc(inv) + [k_plane(img)]


SAMPLINGS = {
    "444": ([1, 1, 1], [1, 1, 1]),
    "422": ([2, 1, 1], [1, 1, 1]),
    "420": ([2, 1, 1], [2, 1, 1]),
    "440": ([1, 1, 1], [2, 1, 1]),
    "411": ([4, 1, 1], [1, 1, 1]),
    "410": ([4, 1, 1], [2, 1, 1]),
    "422v": ([1, 1, 1], [1, 2, 2]),
    "mixed": ([2, 1, 2], [2, 1, 1]),
    "h3": ([4, 2, 1], [1, 1, 1]),
}


def main():
    ljt, out_dir = sys.argv[1], sys.argv[2]
    os.makedirs(out_dir, exist_ok=True)
    testimages = os.path.join(ljt, "testimages")
    # libjpeg-turbo's own images.
    for name in ("testorig", "testimgint"):
        data = open(os.path.join(testimages, name + ".jpg"), "rb").read()
        open(os.path.join(out_dir, name + ".ref"), "wb").write(ref_bytes(data))
    w, h, img = read_ppm(os.path.join(testimages, "testorig.ppm"))
    corpus = []

    def add(name, data):
        corpus.append((name, data, ref_bytes(data)))

    # Full-size images: the sampling ratios, restart intervals, scan layouts.
    ycc = to_ycc(img)
    for s in ("444", "422", "420", "440", "411", "410"):
        hh, vv = SAMPLINGS[s]
        add(f"full-{s}", encode(ycc, h=hh, v=vv))
    hh, vv = SAMPLINGS["420"]
    add("full-420-restart-7", encode(ycc, h=hh, v=vv, restart=7))
    add("full-420-noninterleaved", encode(ycc, h=hh, v=vv, interleaved=False))
    add("full-gray", encode(to_gray(img), h=[1], v=[1], jfif=True))
    add("full-rgb-adobe", encode(to_rgb(img), h=[1, 1, 1], v=[1, 1, 1], jfif=False, adobe=0,
                                 tq=[0, 0, 0]))
    add("full-cmyk-adobe", encode(to_cmyk(img), h=[1] * 4, v=[1] * 4, jfif=False, adobe=0,
                                  tq=[0, 0, 0, 0]))
    add("full-ycck-adobe-420", encode(to_ycck(img), h=[2, 1, 1, 2], v=[2, 1, 1, 2], jfif=False,
                                      adobe=2))
    # Small and awkward sizes through every sampling.
    sizes = [(1, 1), (2, 3), (3, 2), (5, 7), (8, 8), (9, 9), (16, 16), (17, 15), (31, 33), (37, 23)]
    for (cw, ch) in sizes:
        small = crop(img, cw, ch, 20, 10)
        sycc = to_ycc(small)
        for s in ("444", "422", "420", "440", "411", "410", "422v", "mixed", "h3"):
            hh, vv = SAMPLINGS[s]
            add(f"{cw}x{ch}-{s}", encode(sycc, h=hh, v=vv))
        add(f"{cw}x{ch}-gray", encode(to_gray(small), h=[1], v=[1]))
    small = crop(img, 37, 23, 40, 30)
    sycc = to_ycc(small)
    add("37x23-420-restart-1", encode(sycc, h=[2, 1, 1], v=[2, 1, 1], restart=1))
    add("37x23-420-restart-3-noninterleaved",
        encode(sycc, h=[2, 1, 1], v=[2, 1, 1], restart=3, interleaved=False))
    add("37x23-444-sof1", encode(sycc, h=[1] * 3, v=[1] * 3, sof=1))
    add("37x23-444-wide-q", encode(sycc, h=[1] * 3, v=[1] * 3, wide_q=True, sof=1))
    add("37x23-420-q100", encode(sycc, h=[2, 1, 1], v=[2, 1, 1], quality=100))
    add("37x23-420-q10", encode(sycc, h=[2, 1, 1], v=[2, 1, 1], quality=10))
    add("37x23-rgb-ids", encode(to_rgb(small), h=[1] * 3, v=[1] * 3, jfif=False, ids=[82, 71, 66],
                                tq=[0, 0, 0]))
    add("37x23-cmyk-420", encode(to_cmyk(small), h=[2, 1, 1, 2], v=[2, 1, 1, 2], jfif=False,
                                 adobe=0, tq=[0, 0, 0, 0]))
    add("37x23-ycck-444", encode(to_ycck(small), h=[1] * 4, v=[1] * 4, jfif=False, adobe=2))
    add("37x23-cmyk-noadobe", encode(to_cmyk(small), h=[1] * 4, v=[1] * 4, jfif=False,
                                     tq=[0, 0, 0, 0]))
    add("37x23-ycc-noadobe-nojfif", encode(sycc, h=[2, 1, 1], v=[2, 1, 1], jfif=False))
    add("37x23-ycc-adobe-1", encode(sycc, h=[2, 1, 1], v=[2, 1, 1], jfif=False, adobe=1))
    for o in range(1, 9):
        add(f"37x23-420-orient-{o}",
            encode(sycc, h=[2, 1, 1], v=[2, 1, 1], orientation=o, big_exif=bool(o % 2)))
    # Refused by this decoder, and by libjpeg-turbo with an error or not:
    # nothing to compare, the test only needs a refusal (see the test).
    with open(os.path.join(out_dir, "corpus.pack"), "wb") as f:
        for (name, data, ref) in corpus:
            nb = name.encode()
            f.write(bytes([len(nb)]) + nb)
            f.write(struct.pack("<I", len(data)) + data)
            f.write(struct.pack("<I", len(ref)) + ref)
    print(f"{len(corpus)} corpus files")


if __name__ == "__main__":
    main()
