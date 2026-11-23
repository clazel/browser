#!/usr/bin/env python3
"""Makes the progressive JPEG test files (phase-6.md item 6.6).

Usage, on Linux with libjpeg-turbo's runtime library (`libjpeg.so.8`), its
`jpegtran` (Ubuntu's `libjpeg-turbo-progs`, 2.1.5-2ubuntu2: `apt-get download
libjpeg-turbo-progs`, then `dpkg -x`), run from the repository root:

    python3 scripts/jpeg-progressive.py JPEGTRAN OUT_DIR

It reads the baseline files of the 6.5 suites (`testorig.jpg` and
`testimgint.jpg` of `crates/clazel-jpeg/tests/data/libjpeg-turbo-testimages/`
and every file of `.../jpeg-corpus/corpus.pack` that libjpeg-turbo reads),
turns each into progressive files with `jpegtran` (a lossless transcoding: the
quantized coefficients stay the same, so libjpeg-turbo's output for the
progressive file must equal its output for the baseline one, which this
script checks with the library for every file it writes), and writes into
`OUT_DIR`:

- `progressive.pack`: the progressive files, in the pack format of
  `jpeg-reference.py` with an empty reference (the test compares each with the
  reference of its baseline original, named after the `/`); the name is
  `VARIANT/ORIGINAL`, the variants being
  - `default`: `jpegtran -progressive` (libjpeg's `jpeg_simple_progression`:
    spectral selection and successive approximation, DC and AC refinement),
  - `restart`: the same with a restart interval of 3 blocks,
  - `libjpeg-turbo-scan`: `-scans test.scan`, the script of libjpeg-turbo's
    own `testimages/test.scan` (vendored beside the pack), for the files
    with three components,
  - `spectral`: DC, then AC in bands 1 to 5 and 6 to 63 with no successive
    approximation (made by this script for the component count),
  - `successive`: DC at `Al` 3 refined one bit at a time, AC bands 1 to 9
    from `Al` 2 and 10 to 63 from `Al` 1 refined likewise (made by this
    script).

  A variant libjpeg refuses for a file (a script for three components over a
  gray file) is left out.

The files are not a different image from the baseline ones: they hold the
same coefficients in a different order, so the references stay those of the
6.5 suites.
"""

import importlib.util
import os
import struct
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location("jpeg_reference", os.path.join(HERE, "jpeg-reference.py"))
jr = importlib.util.module_from_spec(spec)
spec.loader.exec_module(jr)

DATA = os.path.join(HERE, "..", "crates", "clazel-jpeg", "tests", "data")


def read_pack(path):
    out = []
    b = open(path, "rb").read()
    at = 0
    while at < len(b):
        n = b[at]
        name = b[at + 1:at + 1 + n].decode()
        at += 1 + n
        (jl,) = struct.unpack_from("<I", b, at)
        jpeg = b[at + 4:at + 4 + jl]
        at += 4 + jl
        (rl,) = struct.unpack_from("<I", b, at)
        ref = b[at + 4:at + 4 + rl]
        at += 4 + rl
        out.append((name, jpeg, ref))
    return out


def components(jpeg):
    """The component count of the first SOF."""
    i = 2
    while i + 4 <= len(jpeg) and jpeg[i] == 0xFF:
        m = jpeg[i + 1]
        if 0xC0 <= m <= 0xCF and m not in (0xC4, 0xC8, 0xCC):
            return jpeg[i + 9]
        i += 2 + struct.unpack(">H", jpeg[i + 2:i + 4])[0]
    return 0


def script(kind, n):
    """A scan script (jpegtran's `-scans` syntax) for `n` components."""
    all_c = " ".join(str(c) for c in range(n))
    each = range(n)
    lines = []
    if kind == "spectral":
        lines.append(f"{all_c}: 0 0 0 0;")
        for c in each:
            lines.append(f"{c}: 1 5 0 0;")
        for c in each:
            lines.append(f"{c}: 6 63 0 0;")
    elif kind == "successive":
        lines.append(f"{all_c}: 0 0 0 3;")
        for c in each:
            lines.append(f"{c}: 1 9 0 2;")
        for c in each:
            lines.append(f"{c}: 10 63 0 1;")
        lines.append(f"{all_c}: 0 0 3 2;")
        for c in each:
            lines.append(f"{c}: 1 9 2 1;")
        lines.append(f"{all_c}: 0 0 2 1;")
        for c in each:
            lines.append(f"{c}: 10 63 1 0;")
        for c in each:
            lines.append(f"{c}: 1 9 1 0;")
        lines.append(f"{all_c}: 0 0 1 0;")
    return "\n".join(lines) + "\n"


def transcode(jpegtran, jpeg, args, tmp):
    src = os.path.join(tmp, "in.jpg")
    dst = os.path.join(tmp, "out.jpg")
    open(src, "wb").write(jpeg)
    if os.path.exists(dst):
        os.remove(dst)
    r = subprocess.run([jpegtran, "-copy", "all", *args, "-outfile", dst, src],
                       capture_output=True)
    if r.returncode != 0 or not os.path.exists(dst):
        return None
    return open(dst, "rb").read()


def main():
    jpegtran, out_dir = sys.argv[1], sys.argv[2]
    os.makedirs(out_dir, exist_ok=True)
    originals = [
        ("testorig.jpg", open(os.path.join(DATA, "libjpeg-turbo-testimages", "testorig.jpg"), "rb").read()),
        ("testimgint.jpg", open(os.path.join(DATA, "libjpeg-turbo-testimages", "testimgint.jpg"), "rb").read()),
    ]
    for (name, jpeg, ref) in read_pack(os.path.join(DATA, "jpeg-corpus", "corpus.pack")):
        if ref:
            originals.append((name, jpeg))
    test_scan = os.path.join(DATA, "jpeg-progressive", "test.scan")
    out = []
    counts = {}
    with tempfile.TemporaryDirectory() as tmp:
        for (name, jpeg) in originals:
            n = components(jpeg)
            want = jr.reference(jpeg)
            variants = [
                ("default", ["-progressive"]),
                ("restart", ["-progressive", "-restart", "3B"]),
            ]
            if n == 3:
                variants.append(("libjpeg-turbo-scan", ["-scans", test_scan]))
            for kind in ("spectral", "successive"):
                p = os.path.join(tmp, kind + ".scan")
                open(p, "w").write(script(kind, n))
                variants.append((kind, ["-scans", p]))
            for (vname, args) in variants:
                prog = transcode(jpegtran, jpeg, args, tmp)
                if prog is None:
                    counts[vname + " (refused)"] = counts.get(vname + " (refused)", 0) + 1
                    continue
                found = jr.sof(prog)
                assert found is not None and found[0] == 0xC2, (name, vname, found)
                got = jr.reference(prog)
                assert got == want, f"{vname}/{name}: libjpeg decodes the progressive file differently"
                out.append((f"{vname}/{name}", prog))
                counts[vname] = counts.get(vname, 0) + 1
    with open(os.path.join(out_dir, "progressive.pack"), "wb") as f:
        for (name, data) in out:
            nb = name.encode()
            assert len(nb) < 256
            f.write(bytes([len(nb)]) + nb)
            f.write(struct.pack("<I", len(data)) + data)
            f.write(struct.pack("<I", 0))
    print(len(out), "progressive files", counts)


if __name__ == "__main__":
    main()
