#!/usr/bin/env python3
"""Generate and verify the compact, lossless SLH-DSA ACVP sample corpus.

The input is the six prompt/expected-results JSON files in the pinned NIST
ACVP-Server checkout.  The output is deterministic and retains every byte-valued
test field, every expected result, and all group metadata needed to dispatch a
test.  JSON is deliberately not committed for the large signature suites: hex
would double the already incompressible signature payload.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import struct
import subprocess
from pathlib import Path
from typing import Any


SERVER_REPOSITORY = "https://github.com/usnistgov/ACVP-Server"
SERVER_COMMIT = "975de31eb83d87039ec88934fdc47d8c312b892d"
SERVER_RELEASE = "v1.1.0.43"
MAGIC = b"VCVSLH1\x00"
FORMAT_VERSION = 1
MODES = {"keyGen": 1, "sigGen": 2, "sigVer": 3}
INTERFACES = {None: 0, "internal": 1, "external": 2}
PREHASHES = {None: 0, "pure": 1, "preHash": 2}
DETERMINISTIC = {None: 0, False: 1, True: 2}
HASHES = {
    None: 0,
    "SHA2-224": 1,
    "SHA2-256": 2,
    "SHA2-384": 3,
    "SHA2-512": 4,
    "SHA2-512/224": 5,
    "SHA2-512/256": 6,
    "SHA3-224": 7,
    "SHA3-256": 8,
    "SHA3-384": 9,
    "SHA3-512": 10,
    "SHAKE-128": 11,
    "SHAKE-256": 12,
}

# name, n, public-key bytes, secret-key bytes, signature bytes
PARAMETERS = [
    ("SLH-DSA-SHA2-128s", 16, 32, 64, 7856),
    ("SLH-DSA-SHAKE-128s", 16, 32, 64, 7856),
    ("SLH-DSA-SHA2-128f", 16, 32, 64, 17088),
    ("SLH-DSA-SHAKE-128f", 16, 32, 64, 17088),
    ("SLH-DSA-SHA2-192s", 24, 48, 96, 16224),
    ("SLH-DSA-SHAKE-192s", 24, 48, 96, 16224),
    ("SLH-DSA-SHA2-192f", 24, 48, 96, 35664),
    ("SLH-DSA-SHAKE-192f", 24, 48, 96, 35664),
    ("SLH-DSA-SHA2-256s", 32, 64, 128, 29792),
    ("SLH-DSA-SHAKE-256s", 32, 64, 128, 29792),
    ("SLH-DSA-SHA2-256f", 32, 64, 128, 49856),
    ("SLH-DSA-SHAKE-256f", 32, 64, 128, 49856),
]
PARAMETER_INDEX = {row[0]: index for index, row in enumerate(PARAMETERS)}
EXPECTED = {
    "keyGen": {"groups": 12, "tests": 120},
    "sigGen": {"groups": 72, "tests": 624},
    "sigVer": {"groups": 36, "tests": 504, "positive": 72, "negative": 432},
}
SOURCE_FILES = {
    "keyGen": (
        "gen-val/json-files/SLH-DSA-keyGen-FIPS205/prompt.json",
        "gen-val/json-files/SLH-DSA-keyGen-FIPS205/expectedResults.json",
    ),
    "sigGen": (
        "gen-val/json-files/SLH-DSA-sigGen-FIPS205/prompt.json",
        "gen-val/json-files/SLH-DSA-sigGen-FIPS205/expectedResults.json",
    ),
    "sigVer": (
        "gen-val/json-files/SLH-DSA-sigVer-FIPS205/prompt.json",
        "gen-val/json-files/SLH-DSA-sigVer-FIPS205/expectedResults.json",
    ),
}
SOURCE_DIGESTS = {
    "gen-val/json-files/SLH-DSA-keyGen-FIPS205/prompt.json":
        (32454, "bce170976f257ee3dfc8c54ea46722ccb553539847daa6d8048f0216cc28b51c"),
    "gen-val/json-files/SLH-DSA-keyGen-FIPS205/expectedResults.json":
        (45192, "f35f74b6676d6b369c87e88c36698f28c14d5929d31e507d910288c69258afee"),
    "gen-val/json-files/SLH-DSA-sigGen-FIPS205/prompt.json":
        (5512830, "afa673eacdf0aec53512a159159b7632684adfcd0d88f8640a7f6f5796aacdc8"),
    "gen-val/json-files/SLH-DSA-sigGen-FIPS205/expectedResults.json":
        (32595492, "71e8e0f7e4b0cfd1747314299204d9d4d50968d200a4ae873921eaa7aabeaad1"),
    "gen-val/json-files/SLH-DSA-sigVer-FIPS205/prompt.json":
        (30513796, "4e7beb1233e47baa0acdd36417c66c45811aa40a4e32ffdb1a35d93b13b289fb"),
    "gen-val/json-files/SLH-DSA-sigVer-FIPS205/expectedResults.json":
        (39216, "259f5e2a0665de0adc0fefa45b5db3a2a6ed13c3c44d14bdaf64a80aee12c687"),
}


class CorpusError(Exception):
    """A fail-closed source, encoding, or verification error."""


def require(condition: bool, message: str) -> None:
    if not condition:
        raise CorpusError(message)


def strict_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    out: dict[str, Any] = {}
    for key, value in pairs:
        require(key not in out, f"duplicate JSON key {key!r}")
        out[key] = value
    return out


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def load_source(root: Path, relative: str) -> dict[str, Any]:
    path = root / relative
    try:
        raw = path.read_bytes()
    except OSError as error:
        raise CorpusError(f"cannot read {path}: {error}") from error
    require((len(raw), sha256(raw)) == SOURCE_DIGESTS[relative],
            f"pinned source mismatch: {relative}")
    try:
        value = json.loads(raw, object_pairs_hook=strict_object)
    except (UnicodeError, json.JSONDecodeError) as error:
        raise CorpusError(f"invalid strict JSON in {relative}: {error}") from error
    require(isinstance(value, dict), f"top-level object required: {relative}")
    return value


def exact_keys(value: dict[str, Any], keys: set[str], label: str) -> None:
    require(set(value) == keys, f"{label}: keys differ: {set(value) ^ keys}")


def hex_bytes(value: Any, label: str) -> bytes:
    require(isinstance(value, str) and len(value) % 2 == 0, f"{label}: even hex required")
    try:
        return bytes.fromhex(value)
    except ValueError as error:
        raise CorpusError(f"{label}: invalid hex") from error


def u8(value: int) -> bytes:
    require(0 <= value <= 0xFF, f"u8 overflow: {value}")
    return struct.pack(">B", value)


def u16(value: int) -> bytes:
    require(0 <= value <= 0xFFFF, f"u16 overflow: {value}")
    return struct.pack(">H", value)


def u32(value: int) -> bytes:
    require(0 <= value <= 0xFFFFFFFF, f"u32 overflow: {value}")
    return struct.pack(">I", value)


def blob(value: bytes) -> bytes:
    return u32(len(value)) + value


def option_blob(value: bytes | None) -> bytes:
    return u8(value is not None) + (blob(value) if value is not None else b"")


def validate_top(document: dict[str, Any], mode: str, label: str) -> None:
    exact_keys(document, {"vsId", "algorithm", "mode", "revision", "isSample", "testGroups"}, label)
    require(document["vsId"] == 53, f"{label}: vsId")
    require(document["algorithm"] == "SLH-DSA", f"{label}: algorithm")
    require(document["mode"] == mode, f"{label}: mode")
    require(document["revision"] == "FIPS205", f"{label}: revision")
    require(document["isSample"] is True, f"{label}: isSample")
    require(isinstance(document["testGroups"], list), f"{label}: testGroups")


def result_map(document: dict[str, Any], mode: str) -> dict[tuple[int, int], dict[str, Any]]:
    out: dict[tuple[int, int], dict[str, Any]] = {}
    for group in document["testGroups"]:
        exact_keys(group, {"tgId", "tests"}, f"{mode} result group")
        require(isinstance(group["tests"], list), f"{mode}: result tests")
        for test in group["tests"]:
            expected = {
                "keyGen": {"tcId", "pk", "sk"},
                "sigGen": {"tcId", "signature"},
                "sigVer": {"tcId", "testPassed"},
            }[mode]
            exact_keys(test, expected, f"{mode} result test")
            key = (group["tgId"], test["tcId"])
            require(key not in out, f"{mode}: duplicate result id {key}")
            out[key] = test
    return out


def encode_mode(root: Path, mode: str) -> tuple[bytes, dict[str, int]]:
    prompt_relative, result_relative = SOURCE_FILES[mode]
    prompt = load_source(root, prompt_relative)
    results = load_source(root, result_relative)
    validate_top(prompt, mode, "prompt")
    validate_top(results, mode, "results")
    lookup = result_map(results, mode)
    groups = prompt["testGroups"]
    require(len(groups) == EXPECTED[mode]["groups"], f"{mode}: group count")
    out = bytearray()
    out += u8(MODES[mode]) + u32(prompt["vsId"]) + u16(len(groups))
    out += u32(EXPECTED[mode]["tests"])
    seen_results: set[tuple[int, int]] = set()
    next_tc = 1
    positive = 0
    negative = 0
    payload_bytes = 0
    for expected_tg, group in enumerate(groups, 1):
        base = {"tgId", "testType", "parameterSet", "tests"}
        if mode == "sigGen":
            base |= {"deterministic", "signatureInterface"}
        elif mode == "sigVer":
            base |= {"signatureInterface"}
        interface = group.get("signatureInterface")
        if interface == "external":
            base.add("preHash")
        exact_keys(group, base, f"{mode} group {expected_tg}")
        require(group["tgId"] == expected_tg, f"{mode}: noncanonical tgId")
        require(group["testType"] == "AFT", f"{mode}: testType")
        require(group["parameterSet"] in PARAMETER_INDEX, f"{mode}: parameterSet")
        require(interface in INTERFACES, f"{mode}: signatureInterface")
        prehash = group.get("preHash")
        require(prehash in PREHASHES, f"{mode}: preHash")
        deterministic = group.get("deterministic")
        require(deterministic in DETERMINISTIC, f"{mode}: deterministic")
        tests = group["tests"]
        require(isinstance(tests, list) and tests, f"{mode}: nonempty tests")
        parameter_index = PARAMETER_INDEX[group["parameterSet"]]
        _name, n, pk_len, sk_len, sig_len = PARAMETERS[parameter_index]
        out += u32(group["tgId"]) + u8(1) + u8(parameter_index)
        out += u8(INTERFACES[interface]) + u8(PREHASHES[prehash])
        out += u8(DETERMINISTIC[deterministic]) + u16(len(tests))
        for test in tests:
            require(test.get("tcId") == next_tc, f"{mode}: tcId sequence at {next_tc}")
            key = (group["tgId"], test["tcId"])
            require(key in lookup and key not in seen_results, f"{mode}: missing/duplicate result {key}")
            result = lookup[key]
            seen_results.add(key)
            out += u32(test["tcId"])
            if mode == "keyGen":
                exact_keys(test, {"tcId", "skSeed", "skPrf", "pkSeed"}, "keyGen test")
                values = [hex_bytes(test[name], name) for name in ("skSeed", "skPrf", "pkSeed")]
                require(all(len(value) == n for value in values), "keyGen: seed width")
                pk = hex_bytes(result["pk"], "pk")
                sk = hex_bytes(result["sk"], "sk")
                require(len(pk) == pk_len and len(sk) == sk_len, "keyGen: result width")
                for value in [*values, pk, sk]:
                    out += blob(value)
                    payload_bytes += len(value)
            elif mode == "sigGen":
                keys = {"tcId", "sk", "message"}
                if interface == "external":
                    keys.add("context")
                if prehash == "preHash":
                    keys.add("hashAlg")
                if deterministic is False:
                    keys.add("additionalRandomness")
                exact_keys(test, keys, "sigGen test")
                sk = hex_bytes(test["sk"], "sk")
                message = hex_bytes(test["message"], "message")
                context = hex_bytes(test["context"], "context") if "context" in test else None
                randomness = (hex_bytes(test["additionalRandomness"], "additionalRandomness")
                              if "additionalRandomness" in test else None)
                hash_alg = test.get("hashAlg")
                signature = hex_bytes(result["signature"], "signature")
                require(len(sk) == sk_len, "sigGen: sk width")
                require(0 < len(message) <= 8192, "sigGen: message width")
                require(context is None or len(context) <= 255, "sigGen: context width")
                require(hash_alg in HASHES and ((hash_alg is not None) == (prehash == "preHash")),
                        "sigGen: hash conditional")
                require((randomness is not None) == (deterministic is False),
                        "sigGen: randomness conditional")
                require(randomness is None or len(randomness) == n, "sigGen: randomness width")
                require(len(signature) == sig_len, "sigGen: signature width")
                out += blob(sk) + blob(message) + option_blob(context)
                out += u8(HASHES[hash_alg]) + option_blob(randomness) + blob(signature)
                payload_bytes += sum(len(value) for value in [sk, message, signature])
                payload_bytes += len(context or b"") + len(randomness or b"")
            else:
                keys = {"tcId", "pk", "message", "signature"}
                if interface == "external":
                    keys.add("context")
                if prehash == "preHash":
                    keys.add("hashAlg")
                exact_keys(test, keys, "sigVer test")
                pk = hex_bytes(test["pk"], "pk")
                message = hex_bytes(test["message"], "message")
                context = hex_bytes(test["context"], "context") if "context" in test else None
                hash_alg = test.get("hashAlg")
                signature = hex_bytes(test["signature"], "signature")
                passed = result["testPassed"]
                require(len(pk) == pk_len, "sigVer: pk width")
                require(0 < len(message) <= 8192, "sigVer: message width")
                require(context is None or len(context) <= 255, "sigVer: context width")
                require(hash_alg in HASHES and ((hash_alg is not None) == (prehash == "preHash")),
                        "sigVer: hash conditional")
                require(len(signature) in {sig_len - 1, sig_len, sig_len + 1},
                        "sigVer: signature mutation width")
                require(isinstance(passed, bool), "sigVer: boolean result")
                require(not passed or len(signature) == sig_len, "sigVer: positive noncanonical signature")
                out += blob(pk) + blob(message) + option_blob(context)
                out += u8(HASHES[hash_alg]) + blob(signature) + u8(passed)
                payload_bytes += sum(len(value) for value in [pk, message, signature])
                payload_bytes += len(context or b"")
                positive += int(passed)
                negative += int(not passed)
            next_tc += 1
    require(next_tc - 1 == EXPECTED[mode]["tests"], f"{mode}: test count")
    require(seen_results == set(lookup), f"{mode}: unpaired expected result")
    if mode == "sigVer":
        require((positive, negative) == (72, 432), "sigVer: verdict counts")
    return bytes(out), {
        "groups": len(groups),
        "tests": next_tc - 1,
        "payloadBytes": payload_bytes,
        **({"positive": positive, "negative": negative} if mode == "sigVer" else {}),
    }


def build(root: Path) -> tuple[bytes, dict[str, Any]]:
    try:
        head = subprocess.run(["git", "-C", str(root), "rev-parse", "HEAD"], check=True,
                              capture_output=True, text=True, timeout=15).stdout.strip()
    except (OSError, subprocess.SubprocessError) as error:
        raise CorpusError(f"cannot inspect source checkout: {error}") from error
    require(head == SERVER_COMMIT, f"source checkout commit {head} != {SERVER_COMMIT}")
    encoded = bytearray(MAGIC + u16(FORMAT_VERSION) + u16(3))
    counts: dict[str, Any] = {}
    for mode in ("keyGen", "sigGen", "sigVer"):
        section, measurement = encode_mode(root, mode)
        encoded += section
        counts[mode] = measurement
    binary = bytes(encoded)
    manifest = {
        "schemaVersion": 1,
        "format": "VCVio SLH-DSA ACVP lossless binary corpus v1",
        "source": {
            "repository": SERVER_REPOSITORY,
            "commit": SERVER_COMMIT,
            "release": SERVER_RELEASE,
            "files": [
                {"path": path, "size": size, "sha256": digest}
                for path, (size, digest) in SOURCE_DIGESTS.items()
            ],
        },
        "generationCommand": (
            "python3 scripts/slhdsa/generate-acvp-corpus.py "
            "--source-root /path/to/pinned/ACVP-Server --write"
        ),
        "encoding": {
            "byteOrder": "big-endian",
            "lengthPrefix": "unsigned 32-bit bytes",
            "optionEncoding": "one-byte presence tag followed by value when present",
            "preserves": [
                "skSeed", "skPrf", "pkSeed", "pk", "sk", "message", "context",
                "hashAlg", "additionalRandomness", "signature", "testPassed",
                "vsId", "tgId", "tcId", "testType", "parameterSet",
                "signatureInterface", "preHash", "deterministic",
            ],
        },
        "measurements": counts,
        "output": {"path": "HashSigTest/SLHDSA/ACVP/fixtures/corpus.bin",
                   "size": len(binary), "sha256": sha256(binary)},
    }
    return binary, manifest


def canonical_json(value: Any) -> bytes:
    return (json.dumps(value, indent=2, ensure_ascii=True) + "\n").encode()


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--source-root", type=Path, required=True)
    action = parser.add_mutually_exclusive_group(required=True)
    action.add_argument("--write", action="store_true")
    action.add_argument("--check", action="store_true")
    parser.add_argument("--output", type=Path,
                        default=Path("HashSigTest/SLHDSA/ACVP/fixtures/corpus.bin"))
    parser.add_argument("--manifest", type=Path,
                        default=Path("HashSigTest/SLHDSA/ACVP/fixtures/corpus-manifest.json"))
    args = parser.parse_args()
    try:
        binary, manifest = build(args.source_root.resolve())
        manifest_bytes = canonical_json(manifest)
        if args.write:
            args.output.parent.mkdir(parents=True, exist_ok=True)
            args.output.write_bytes(binary)
            args.manifest.write_bytes(manifest_bytes)
            print(f"wrote {args.output}: {len(binary)} bytes, sha256 {sha256(binary)}")
            print(f"wrote {args.manifest}: {len(manifest_bytes)} bytes")
        else:
            require(args.output.read_bytes() == binary, f"generated corpus differs: {args.output}")
            require(args.manifest.read_bytes() == manifest_bytes,
                    f"generated manifest differs: {args.manifest}")
            print(f"SLH-DSA ACVP corpus provenance: PASS ({len(binary)} bytes, {sha256(binary)})")
        return 0
    except (CorpusError, OSError) as error:
        print(f"SLH-DSA ACVP corpus provenance: FAIL: {error}")
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
