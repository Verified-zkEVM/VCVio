#!/usr/bin/env python3
"""Compare whole Foundation algorithms with Lean cores and independent vectors.

These checks execute the original pinned source through Cryptol. They do not
execute the imported JSON AST or establish a source/implementation theorem.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile
import time
import zlib

from export_references import verify_checkout
from extract_foundation import CRYPTOL, FOUNDATION, ROOT

LEAN = ROOT.parents[1] / ".lake/build/bin/cryptol-interop"
ALGORITHMS = ["sha224", "sha256", "sha384", "sha512", "sha512_224", "sha512_256",
              "sha3_224", "sha3_256", "sha3_384", "sha3_512", "shake128", "shake256"]


def bits(data):
    return f"(join ({list(data)} : [{len(data)}][8]))"


def core(algorithm, data, length):
    result = subprocess.check_output([
        str(LEAN), "foundation", "hash", algorithm, json.dumps(list(data)), str(length)],
        text=True, timeout=30)
    return bytes(json.loads(result))


def oracle(algorithm, data, length):
    name = algorithm.replace("shake", "shake_")
    try:
        h = hashlib.new(name, data)
    except ValueError:
        # Apple's system Python omits SHA-512/t; OpenSSL exposes both variants.
        if algorithm not in ("sha512_224", "sha512_256"):
            raise
        return subprocess.check_output(["openssl", "dgst", "-" + algorithm.replace("_", "-"),
                                        "-binary"], input=data, timeout=30)
    return h.digest(length) if algorithm.startswith("shake") else h.digest()


def hash_cases():
    cases = []
    for i, algorithm in enumerate(ALGORITHMS):
        rate = (64 if i < 2 else 128) if i < 6 else [144, 136, 104, 72, 168, 136][i - 6]
        lengths = sorted({0, 3, rate - 1, rate, rate + 1,
                          *([rate - 9, rate - 8] if i < 6 else [])})
        for size in lengths:
            data = b"abc" if size == 3 else bytes((j * 73 + 19) % 256 for j in range(size))
            output_lengths = [0, 32, rate + 1] if i >= 10 else [0]
            for length in output_lengths:
                result = core(algorithm, data, length)
                assert result == oracle(algorithm, data, length), (algorithm, size, length)
                function = f"R{i}::hash" if i < 10 else \
                    f"R10::SHAKE{128 if i == 10 else 256}`{{DigestSize={8 * length}}}"
                expression = f"({function} {bits(data)}) == {bits(result)}"
                cases.append((f"{algorithm}/{size}/{len(result)}", expression))
    return cases


def additional_cases():
    cases = []
    # RawSHAKE with the two preceding domain bits is SHAKE. The adapter explicitly
    # handles Foundation's per-byte bit order, including the final partial byte.
    for strength in (128, 256):
        data = b"abc"
        expected = oracle(f"shake{strength}", data, 32)
        message = f"R11::bitReordering (R11::bitReordering {bits(data)} # 0b11)"
        cases.append((f"rawshake{strength}/domain-extension",
                      f"R10::RawSHAKE{strength}`{{DigestSize=256}} ({message}) == {bits(expected)}"))
    for data in (b"", b"abc", bytes(range(137))):
        expected = core("keccak256", data, 32)
        cases.append((f"keccak256/{len(data)}",
                      f"R11::bitReordering (R11::Keccak`{{c=512,d=256}} "
                      f"(R11::bitReordering {bits(data)})) == {bits(expected)}"))
    for data in (b"", bytes([0x12, 0x34, 0x56])):
        reversed_bits = bytes(int(f"{b:08b}"[::-1], 2) for b in data)
        cases.append((f"bit-reordering/{len(data)}",
                      f"R11::bitReordering {bits(data)} == {bits(reversed_bits)}"))
    # FIPS 197 Appendix C examples, with the key bytes in ascending order.
    plain = "00112233445566778899aabbccddeeff"
    vectors = {128: "69c4e0d86a7b0430d8cdb78070b4c55a",
               192: "dda97ca4864cdfe06eaf70a0ec0d7191",
               256: "8ea2b7ca516745bfeafc49904b496089"}
    for width, cipher in vectors.items():
        key = bytes(range(width // 8)).hex()
        for direction, src, dst in (("Encrypt", plain, cipher), ("Decrypt", cipher, plain)):
            cases.append((f"aes{width}-{direction.lower()}",
                          f"R13::AES{width}.{direction} 0x{key} 0x{src} == 0x{dst}"))
    for data in (b"", b"123456789", bytes(range(33))):
        cases.append((f"crc32/{len(data)}", f"R14::CRC {bits(data)} == {zlib.crc32(data)}"))
        for split in sorted({0, len(data) // 2, len(data)}):
            cases.append((f"crc32-update/{len(data)}/{split}",
                          f"R14::CRCUpdateCorrect {bits(data[:split])} {bits(data[split:])}"))
    chunks = [bytes([0, 1]), bytes([2, 3]), bytes([4, 5])]
    running = [zlib.crc32(b"".join(chunks[:i])) for i in (1, 2, 3)]
    cases.append(("crc32-running/3/2",
                  "R14::CRCRunning [" + ",".join(bits(c) for c in chunks) + "] == " + str(running)))
    for width in (0, 1, 2, 8, 32, 64):
        # One nonuniform state catches x/y transposition; the zero width checks empty lanes.
        value = sum(1 << i for i in range(25 * width) if (i * 17 + 3) % 11 < 5)
        source = f"({value} : [{25 * width}])"
        cases.append((f"keccak-codec/{width}",
                      f"R12::toStatetoStringProp`{{{width}}} {source} /\\ "
                      f"R12::toStringtoStateProp`{{{width}}} (R12::toState {source})"))
    cases.append(("keccak-theta-negative-index/1",
                  "~((Theta::θ`{1} zero) @ 0 @ 0 @ 0)"))
    return cases


def check_external(cryptol, foundation, source, cases, mode, timeout):
    env = dict(os.environ)
    env["PATH"] = str(cryptol.parent) + os.pathsep + env.get("PATH", "")
    reports = []
    for label, expression in cases:
        start = time.monotonic()
        command = (":eval " if mode == "reference" else "") + f"({expression})"
        result = subprocess.run([str(cryptol), "--ignore-cryptolrc", "--color=none", "-e",
                                 "-c", f":load {source}", "-c", command],
                                cwd=foundation, env=env, text=True, capture_output=True,
                                timeout=timeout)
        output = result.stdout + result.stderr
        # Reference.lhs uses signed remainder for Integer. Foundation's theta
        # uses (x-1)%5 at x=0, so these source computations return an index error.
        discrepancy = mode == "reference" and \
            label.startswith(("sha3_", "shake", "rawshake", "keccak256/",
                              "keccak-theta-negative-index/"))
        expected = r"^invalid sequence index: -1$" if discrepancy else r"^True$"
        if result.returncode or not re.search(expected, output, re.MULTILINE) or \
                re.search(r"\[error\]|parse error|type error|Run-time error", output, re.IGNORECASE):
            raise AssertionError(f"{mode} {label}: {output}")
        status = "documented-index-error" if discrepancy else "agreed"
        reports.append({"case": label, "mode": mode, "status": status,
                        "milliseconds": round(1000 * (time.monotonic() - start))})
        print(f"{mode}: {label} {status}", flush=True)
    return reports


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cryptol", type=Path)
    parser.add_argument("--foundation", type=Path)
    parser.add_argument("--report", type=Path)
    args = parser.parse_args()
    hashes = hash_cases()
    report = {"core_hash_cases": len(hashes), "foundation_revision": FOUNDATION,
              "cryptol_revision": CRYPTOL, "observations": [],
              "meaning": "Whole-algorithm executable comparisons; no imported-AST certificate"}
    print(f"{len(hashes)} whole-hash Lean/hashlib/OpenSSL comparisons passed", flush=True)
    # Malformed input is rejected rather than reduced modulo 256.
    for algorithm, data, length in (("sha256", "[256]", "0"),
                                    ("sha256", "[-1]", "0"),
                                    ("unknown", "[]", "0"),
                                    ("shake128", "[]", "-1")):
        bad = subprocess.run([str(LEAN), "foundation", "hash", algorithm, data, length],
                             text=True, capture_output=True, timeout=30)
        assert bad.returncode != 0 and not bad.stdout
    if args.cryptol:
        if not args.foundation:
            parser.error("--cryptol requires --foundation")
        cryptol, foundation = args.cryptol.resolve(), args.foundation.resolve()
        verify_checkout(foundation, FOUNDATION)
        version = subprocess.check_output([str(cryptol), "--version"], text=True)
        assert "Cryptol 3.6.0" in version and f"Git commit {CRYPTOL}" in version
        manifest = json.loads((ROOT / "artifacts/references/manifest.json").read_text())
        entry = (ROOT / "artifacts/references/FoundationReferences.cry").read_bytes()
        assert hashlib.sha256(entry).hexdigest() == manifest["entry_sha256"]
        with tempfile.TemporaryDirectory(prefix="cryptol-whole-reference-") as temporary:
            source = Path(temporary) / "FoundationReferences.cry"
            source.write_text(entry.decode().replace("module FoundationReferences where",
                "module FoundationReferences where\n"
                "import algorithms::Keccak::StepMappings as Theta"))
            extra = additional_cases()
            report["observations"] += check_external(
                cryptol, foundation, source, hashes + extra, "normal", 60)
            # The reference pass uses a smaller set, still covering every hash,
            # all AES key sizes/directions, CRC updates, and all codec widths.
            reference = [case for case in hashes if case[0].split("/")[1:] == ["3", "32"]
                         or (case[0].split("/")[1] == "0" and
                             not case[0].startswith("shake"))]
            report["observations"] += check_external(
                cryptol, foundation, source, reference + extra, "reference", 60)
    if args.report:
        args.report.parent.mkdir(parents=True, exist_ok=True)
        args.report.write_text(json.dumps(report, indent=2) + "\n")


if __name__ == "__main__":
    main()
