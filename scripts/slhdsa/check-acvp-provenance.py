#!/usr/bin/env python3
"""Verify the committed SLH-DSA ACVP evidence without using the network."""

from __future__ import annotations

import copy
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[2]
FIXTURE_ROOT = REPO_ROOT / "HashSigTest" / "SLHDSA" / "ACVP" / "fixtures"
SERVER_COMMIT = "975de31eb83d87039ec88934fdc47d8c312b892d"
SERVER_RELEASE = "v1.1.0.43"
SERVER_COMPATIBILITY_COMMIT = "85f8742965b2691862079172982683757d8d91db"
SERVER_COMPATIBILITY_RELEASE = "v1.1.0.38"
PROTOCOL_COMMIT = "892fd14710f3a7edbea230d0aecc5511e0257f8e"
PROTOCOL_DOCUMENT = "draft-livelsberger-acvp-slh-dsa-01"
PROTOCOL_DOCUMENT_DATE = "2024-06-25"
SP800_PROFILE_ID = "SP800-230-IPD-6SET"
LEGACY_CURRENT_CODE_PROFILE_ID = "LEGACY-SHA2-128-24"
PROTOCOL_ROOT_ARTIFACT = (
    "src/draft-livelsberger-acvp-slh-dsa.adoc",
    2258,
    "d9c7088a6bb0531b2a5ab65104f467a7abe0e5ffc4d22f8ec1b7b90978d7d061",
)
PROTOCOL_COMPOSITE_SHA256 = (
    "bc38ec528afcaa7f6a8155fd75a7612166203c789a540c0ac42e860a04c40a54"
)

PARAMETER_SETS = [
    "SLH-DSA-SHA2-128s",
    "SLH-DSA-SHAKE-128s",
    "SLH-DSA-SHA2-128f",
    "SLH-DSA-SHAKE-128f",
    "SLH-DSA-SHA2-192s",
    "SLH-DSA-SHAKE-192s",
    "SLH-DSA-SHA2-192f",
    "SLH-DSA-SHAKE-192f",
    "SLH-DSA-SHA2-256s",
    "SLH-DSA-SHAKE-256s",
    "SLH-DSA-SHA2-256f",
    "SLH-DSA-SHAKE-256f",
]

HASH_ALGORITHMS = [
    "SHA2-224",
    "SHA2-256",
    "SHA2-384",
    "SHA2-512",
    "SHA2-512/224",
    "SHA2-512/256",
    "SHA3-224",
    "SHA3-256",
    "SHA3-384",
    "SHA3-512",
    "SHAKE-128",
    "SHAKE-256",
]

SP800_IPD_PARAMETER_SETS = [
    {"name": "SLH-DSA-SHA2-128-24", "family": "SHA2", "n": 16, "h": 22,
     "d": 1, "hp": 22, "a": 24, "k": 6, "lgw": 2, "m": 21, "category": 1,
     "public_key_bytes": 32, "signature_bytes": 3856},
    {"name": "SLH-DSA-SHAKE-128-24", "family": "SHAKE", "n": 16, "h": 22,
     "d": 1, "hp": 22, "a": 24, "k": 6, "lgw": 2, "m": 21, "category": 1,
     "public_key_bytes": 32, "signature_bytes": 3856},
    {"name": "SLH-DSA-SHA2-192-24", "family": "SHA2", "n": 24, "h": 21,
     "d": 1, "hp": 21, "a": 25, "k": 9, "lgw": 3, "m": 32, "category": 3,
     "public_key_bytes": 48, "signature_bytes": 7752},
    {"name": "SLH-DSA-SHAKE-192-24", "family": "SHAKE", "n": 24, "h": 21,
     "d": 1, "hp": 21, "a": 25, "k": 9, "lgw": 3, "m": 32, "category": 3,
     "public_key_bytes": 48, "signature_bytes": 7752},
    {"name": "SLH-DSA-SHA2-256-24", "family": "SHA2", "n": 32, "h": 21,
     "d": 1, "hp": 21, "a": 25, "k": 12, "lgw": 2, "m": 41, "category": 5,
     "public_key_bytes": 64, "signature_bytes": 14944},
    {"name": "SLH-DSA-SHAKE-256-24", "family": "SHAKE", "n": 32, "h": 21,
     "d": 1, "hp": 21, "a": 25, "k": 12, "lgw": 2, "m": 41, "category": 5,
     "public_key_bytes": 64, "signature_bytes": 14944},
]

SAMPLE_SUITE_MEASUREMENTS = {
    "source": "ACVP-Server sample prompt.json and expectedResults.json files at the pinned commit",
    "keyGen": {"groups": 12, "tests": 120},
    "sigGen": {"groups": 72, "tests": 624},
    "sigVer": {
        "groups": 36, "tests": 504, "positive": 72, "negative": 432,
    },
}

SERVER_ARTIFACTS = [
    ("gen-val/json-files/SLH-DSA-keyGen-FIPS205/registration.json", 438, "dfbf8116cb108209bc8fe539ec460dcda7036336ff460e4b0d9cf55c464fca08"),
    ("gen-val/json-files/SLH-DSA-keyGen-FIPS205/prompt.json", 32454, "bce170976f257ee3dfc8c54ea46722ccb553539847daa6d8048f0216cc28b51c"),
    ("gen-val/json-files/SLH-DSA-keyGen-FIPS205/internalProjection.json", 75294, "d7c53a1b6450087047b57aae83a5a51a0ac89ecdb23ebe071e83fbb69ae9d920"),
    ("gen-val/json-files/SLH-DSA-keyGen-FIPS205/expectedResults.json", 45192, "f35f74b6676d6b369c87e88c36698f28c14d5929d31e507d910288c69258afee"),
    ("gen-val/json-files/SLH-DSA-keyGen-FIPS205/validation.json", 6792, "df6726b334e4ab0ce0b48f716a423bd2b4366cea589d2878ff3023ba11494da9"),
    ("gen-val/json-files/SLH-DSA-sigGen-FIPS205/registration.json", 1776, "f7db21f297028ae806a07b482a7bad73e49c8df2bf0dec492786c1313ba9fa72"),
    ("gen-val/json-files/SLH-DSA-sigGen-FIPS205/prompt.json", 5512830, "afa673eacdf0aec53512a159159b7632684adfcd0d88f8640a7f6f5796aacdc8"),
    ("gen-val/json-files/SLH-DSA-sigGen-FIPS205/internalProjection.json", 38178342, "62b42e7c27fda5de8a94aba2943ae413b59b6ea08141f3bc035b1eceae235dba"),
    ("gen-val/json-files/SLH-DSA-sigGen-FIPS205/expectedResults.json", 32595492, "71e8e0f7e4b0cfd1747314299204d9d4d50968d200a4ae873921eaa7aabeaad1"),
    ("gen-val/json-files/SLH-DSA-sigGen-FIPS205/validation.json", 35520, "4b3e13ff387d2b491b94a60f78b09d7c0d568154061773cb6d8faf6b28b448fc"),
    ("gen-val/json-files/SLH-DSA-sigVer-FIPS205/registration.json", 1730, "afe3475e0e0f2680daf0f6b908832e8f0649f2dc6909b5df6be78802f09e5dde"),
    ("gen-val/json-files/SLH-DSA-sigVer-FIPS205/prompt.json", 30513796, "4e7beb1233e47baa0acdd36417c66c45811aa40a4e32ffdb1a35d93b13b289fb"),
    ("gen-val/json-files/SLH-DSA-sigVer-FIPS205/internalProjection.json", 30731848, "a013fc2104f4ed4799d96d51141f65b965969b2cf10646626a021b6d456ce792"),
    ("gen-val/json-files/SLH-DSA-sigVer-FIPS205/expectedResults.json", 39216, "259f5e2a0665de0adc0fefa45b5db3a2a6ed13c3c44d14bdaf64a80aee12c687"),
    ("gen-val/json-files/SLH-DSA-sigVer-FIPS205/validation.json", 28680, "83335f44c1b91d90258da79e398eb7370e06b1eb2dd94279da01fffba64a54ee"),
]

PROTOCOL_ARTIFACTS = [
    ("src/slh-dsa/sections/03-supported.adoc", 287, "d92d036162464cda211b458ef214de0cfac49642cd6a51ba6df9cb5e0bdf6355"),
    ("src/slh-dsa/sections/04-testtypes.adoc", 4788, "4528cb13bd80da55cac571723c0aa7e4729f401b1c97b583d1c5e9099908c570"),
    ("src/slh-dsa/sections/05-capabilities.adoc", 800, "b9d0ca1b5c773a056d1837373ee212f9f155367dedbad7d83f32f090952dd605"),
    ("src/slh-dsa/sections/05-slh-dsa-keygen-capabilities.adoc", 1638, "09568244b74d1b6fe2250544526859be669b38222357b3bc24f891d880b1bc12"),
    ("src/slh-dsa/sections/05-slh-dsa-siggen-capabilities.adoc", 3690, "644b863cfb3fedca6db12f2deaa70074c1e4c9f710a9bf615227f9d44d2cffb7"),
    ("src/slh-dsa/sections/05-slh-dsa-sigver-capabilities.adoc", 3396, "24c235b4b3d7e4b3db79207f2416c33c9c942da40035976789ad534f4f89fafd"),
    ("src/slh-dsa/sections/06-slh-dsa-keygen-test-vectors.adoc", 2581, "8001e6b79a3b446bab0d42876c494031327e85f04646c21712c8fc34988fe966"),
    ("src/slh-dsa/sections/06-slh-dsa-siggen-test-vectors.adoc", 4692, "d07f8c3291d7787b118c8804294258549723342a57b1290fb923e49333c6ea15"),
    ("src/slh-dsa/sections/06-slh-dsa-sigver-test-vectors.adoc", 5095, "08740e1b04d5de7124b05a99f3b9ebdfbb93231ff3a126f4f5316755a0702bfd"),
    ("src/slh-dsa/sections/06-test-vectors.adoc", 1527, "acede1bd43f0c9230fe42c550660855c5d26121dbb1c755e5e16f63017d7cf4e"),
    ("src/slh-dsa/sections/07-responses.adoc", 1204, "f47fc9df4269faa50b0e7afabe13aabd487db0a648e2fc0fb086994122f5ee5a"),
    ("src/slh-dsa/sections/07-slh-dsa-keygen-responses.adoc", 1099, "e83fdda88d9691f8eff65c5827ac43fe666751e69f57f74c9dd39a246f228283"),
    ("src/slh-dsa/sections/07-slh-dsa-siggen-responses.adoc", 1035, "f858107c8fa775bb14f7824016de4e55d276c341a06b952a8b43b6ea438a643e"),
    ("src/slh-dsa/sections/07-slh-dsa-sigver-responses.adoc", 1046, "786247baefdb39a3c014b6542a9e93c4ddc3a9f49194e49615c4174089e1a52e"),
    ("src/slh-dsa/sections/98-references.adoc", 1092, "b127d1e0d713365b797b12fe167e693c1a113641fd56d2084ded37adf8cf8042"),
]

COMMITTED_ARTIFACTS = {
    "HashSigTest/SLHDSA/ACVP/fixtures/NOTICE-NIST.txt":
        (2704, "9f794a8f136aa701c1d4670a49beed6d3d0cf9cabf0389727ab732137da709a7"),
    "HashSigTest/SLHDSA/ACVP/fixtures/keygen-expected.json":
        (45193, "81143b49c1bf125edf0c8cf357e53aaa4049c1de8482b20473e3fdf4067e0f01"),
    "HashSigTest/SLHDSA/ACVP/fixtures/keygen-prompt.json":
        (32455, "0274937fbc03feb2eeca572c99f8db2407bf2412e301753a54e0d3cdea77b73a"),
    "HashSigTest/SLHDSA/ACVP/fixtures/keygen-registration.json":
        (439, "3c20a6681eff583389cf392975a61ba43e1e33a310378c2232dac872996e91a6"),
    "HashSigTest/SLHDSA/ACVP/fixtures/positive-prehash-coverage.json":
        (18808, "c5b098163806dd27f028e57135df9ca6686024650d9b2392f2281d149e7db04c"),
    "HashSigTest/SLHDSA/ACVP/fixtures/siggen-registration.json":
        (1777, "69b584f1a19adddf8e5381a7ba1e7a164b4b68efab7aa64f9a2dde86a97cf0f8"),
    "HashSigTest/SLHDSA/ACVP/fixtures/siggen-schema-slice.json":
        (146774, "3912e38aadd777c780cfab8d28dbc95c1f9a5f20970308a8daddacc377022699"),
    "HashSigTest/SLHDSA/ACVP/fixtures/sigver-registration.json":
        (1731, "275adf4d16f9c2adc648ecb3598d4f96062758e332469897705f68bc550892bc"),
    "HashSigTest/SLHDSA/ACVP/fixtures/sigver-schema-slice.json":
        (155072, "91126fa396b595d1940a50c91ede34eb3c3b4b22463dddaea5d875047214688f"),
}

EXACT_COPY_MAP = {
    "HashSigTest/SLHDSA/ACVP/fixtures/keygen-registration.json":
        "gen-val/json-files/SLH-DSA-keyGen-FIPS205/registration.json",
    "HashSigTest/SLHDSA/ACVP/fixtures/siggen-registration.json":
        "gen-val/json-files/SLH-DSA-sigGen-FIPS205/registration.json",
    "HashSigTest/SLHDSA/ACVP/fixtures/sigver-registration.json":
        "gen-val/json-files/SLH-DSA-sigVer-FIPS205/registration.json",
    "HashSigTest/SLHDSA/ACVP/fixtures/keygen-prompt.json":
        "gen-val/json-files/SLH-DSA-keyGen-FIPS205/prompt.json",
    "HashSigTest/SLHDSA/ACVP/fixtures/keygen-expected.json":
        "gen-val/json-files/SLH-DSA-keyGen-FIPS205/expectedResults.json",
}

COMMITTED_DERIVATIONS = {
    **{path: ("exact-json-copy-final-lf-normalized", source_path)
       for path, source_path in EXACT_COPY_MAP.items()},
    "HashSigTest/SLHDSA/ACVP/fixtures/siggen-schema-slice.json":
        ("projection", "gen-val/json-files/SLH-DSA-sigGen-FIPS205/{prompt.json,expectedResults.json}"),
    "HashSigTest/SLHDSA/ACVP/fixtures/sigver-schema-slice.json":
        ("projection", "gen-val/json-files/SLH-DSA-sigVer-FIPS205/{prompt.json,expectedResults.json}"),
    "HashSigTest/SLHDSA/ACVP/fixtures/positive-prehash-coverage.json":
        ("derived-matrix", "gen-val/json-files/SLH-DSA-sigVer-FIPS205/{prompt.json,expectedResults.json}"),
    "HashSigTest/SLHDSA/ACVP/fixtures/NOTICE-NIST.txt":
        ("notice", "README.md#license"),
}

SIGGEN_CASES = [
    {"shape": "external-pure-deterministic", "tgId": 19, "tcId": 157},
    {"shape": "external-preHash-deterministic", "tgId": 20, "tcId": 164},
    {"shape": "internal-deterministic", "tgId": 31, "tcId": 271},
    {"shape": "external-pure-randomized", "tgId": 55, "tcId": 469},
    {"shape": "external-preHash-randomized", "tgId": 56, "tcId": 476},
    {"shape": "internal-randomized", "tgId": 67, "tcId": 583},
]

SIGVER_CASES = [
    {"shape": "external-pure-exact-length-invalid", "tgId": 19, "tcId": 253},
    {"shape": "external-pure-one-byte-short-invalid", "tgId": 19, "tcId": 256},
    {"shape": "external-pure-one-byte-long-invalid", "tgId": 19, "tcId": 257},
    {"shape": "external-pure-valid", "tgId": 19, "tcId": 258},
    {"shape": "external-preHash-valid", "tgId": 20, "tcId": 268},
    {"shape": "internal-valid", "tgId": 31, "tcId": 422},
]

POSITIVE_PAIRS = {
    ("SLH-DSA-SHA2-128f", "SHA3-384"): (2, 19),
    ("SLH-DSA-SHA2-128f", "SHA2-256"): (2, 25),
    ("SLH-DSA-SHA2-192f", "SHA2-512"): (4, 52),
    ("SLH-DSA-SHA2-192f", "SHA2-512/224"): (4, 53),
    ("SLH-DSA-SHA2-256f", "SHA2-224"): (6, 72),
    ("SLH-DSA-SHA2-256f", "SHA2-384"): (6, 84),
    ("SLH-DSA-SHAKE-128f", "SHA3-512"): (8, 107),
    ("SLH-DSA-SHAKE-128f", "SHA2-512/256"): (8, 111),
    ("SLH-DSA-SHAKE-192f", "SHA3-512"): (10, 129),
    ("SLH-DSA-SHAKE-192f", "SHA3-384"): (10, 139),
    ("SLH-DSA-SHAKE-256f", "SHA2-224"): (12, 167),
    ("SLH-DSA-SHAKE-256f", "SHA2-256"): (12, 168),
    ("SLH-DSA-SHA2-128s", "SHA2-512"): (20, 268),
    ("SLH-DSA-SHA2-128s", "SHAKE-256"): (20, 271),
    ("SLH-DSA-SHA2-192s", "SHA2-512/256"): (22, 302),
    ("SLH-DSA-SHA2-192s", "SHA2-256"): (22, 307),
    ("SLH-DSA-SHA2-256s", "SHA3-384"): (24, 328),
    ("SLH-DSA-SHA2-256s", "SHA2-512"): (24, 331),
    ("SLH-DSA-SHAKE-128s", "SHA2-512/224"): (26, 351),
    ("SLH-DSA-SHAKE-128s", "SHA2-512/256"): (26, 364),
    ("SLH-DSA-SHAKE-192s", "SHA3-256"): (28, 386),
    ("SLH-DSA-SHAKE-192s", "SHA3-384"): (28, 388),
    ("SLH-DSA-SHAKE-256s", "SHA3-256"): (30, 412),
    ("SLH-DSA-SHAKE-256s", "SHA2-512/256"): (30, 417),
}


class CheckError(Exception):
    """A deterministic provenance failure."""


def require(condition: bool, message: str) -> None:
    if not condition:
        raise CheckError(message)


def strict_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise CheckError(f"duplicate JSON key: {key!r}")
        result[key] = value
    return result


def load_json(path: Path) -> Any:
    try:
        with path.open("r", encoding="utf-8") as stream:
            return json.load(stream, object_pairs_hook=strict_object)
    except (OSError, UnicodeError, json.JSONDecodeError) as error:
        raise CheckError(f"{path}: cannot read strict JSON: {error}") from error


def digest(path: Path) -> tuple[int, str]:
    try:
        data = path.read_bytes()
    except OSError as error:
        raise CheckError(f"{path}: cannot read: {error}") from error
    return len(data), hashlib.sha256(data).hexdigest()


def manifest_records(entries: list[tuple[str, int, str]]) -> list[dict[str, Any]]:
    return [{"path": path, "size": size, "sha256": sha256}
            for path, size, sha256 in entries]


def check_manifest_files(root: Path, entries: list[tuple[str, int, str]], label: str) -> None:
    require(root.is_dir(), f"{label} root is not a directory: {root}")
    for relative, expected_size, expected_hash in entries:
        actual = digest(root / relative)
        require(actual == (expected_size, expected_hash),
                f"{label} artifact mismatch: {relative}: expected "
                f"{expected_size}/{expected_hash}, got {actual[0]}/{actual[1]}")


def check_lossless_corpus() -> None:
    manifest = load_json(FIXTURE_ROOT / "corpus-manifest.json")
    require(set(manifest) == {
        "schemaVersion", "format", "source", "generationCommand", "encoding",
        "measurements", "output"}, "lossless corpus manifest keys are not exact")
    require(manifest["schemaVersion"] == 1, "lossless corpus manifest version")
    require(manifest["format"] == "VCVio SLH-DSA ACVP lossless binary corpus v1",
            "lossless corpus format identity")
    source = manifest["source"]
    require(source == {
        "repository": "https://github.com/usnistgov/ACVP-Server",
        "commit": SERVER_COMMIT,
        "release": SERVER_RELEASE,
        "files": [
            {"path": path, "size": size, "sha256": sha256}
            for path, size, sha256 in SERVER_ARTIFACTS
            if path.endswith(("prompt.json", "expectedResults.json"))
        ],
    }, "lossless corpus source pin or source-file hashes differ")
    require(manifest["generationCommand"] ==
            "python3 scripts/slhdsa/generate-acvp-corpus.py "
            "--source-root /path/to/pinned/ACVP-Server --write",
            "lossless corpus generation command differs")
    encoding = manifest["encoding"]
    require(encoding.get("byteOrder") == "big-endian"
            and encoding.get("lengthPrefix") == "unsigned 32-bit bytes"
            and encoding.get("optionEncoding") ==
                "one-byte presence tag followed by value when present",
            "lossless corpus encoding metadata differs")
    require(set(encoding.get("preserves", [])) == {
        "skSeed", "skPrf", "pkSeed", "pk", "sk", "message", "context",
        "hashAlg", "additionalRandomness", "signature", "testPassed", "vsId",
        "tgId", "tcId", "testType", "parameterSet", "signatureInterface",
        "preHash", "deterministic",
    }, "lossless corpus preservation inventory differs")
    require(manifest["measurements"] == {
        "keyGen": {"groups": 12, "tests": 120, "payloadBytes": 25920},
        "sigGen": {"groups": 72, "tests": 624, "payloadBytes": 18978789},
        "sigVer": {"groups": 36, "tests": 504, "payloadBytes": 15217612,
                   "positive": 72, "negative": 432},
    }, "lossless corpus measurements differ")
    output = manifest["output"]
    require(output == {
        "path": "HashSigTest/SLHDSA/ACVP/fixtures/corpus.bin",
        "size": 34252414,
        "sha256": "efd851009f802502f722b49579b00345e401e3b955e7ac8b775324d6375bbb98",
    }, "lossless corpus output record differs")
    require(digest(REPO_ROOT / output["path"]) == (output["size"], output["sha256"]),
            "committed lossless corpus bytes differ from the manifest")


def git_head(root: Path, label: str) -> str:
    try:
        result = subprocess.run(
            ["git", "-C", str(root), "rev-parse", "HEAD"],
            check=True, capture_output=True, text=True, timeout=15)
    except (OSError, subprocess.SubprocessError) as error:
        raise CheckError(f"{label}: cannot determine checkout commit: {error}") from error
    return result.stdout.strip()


def check_discriminants(document: dict[str, Any], mode: str) -> None:
    require(document.get("algorithm") == "SLH-DSA", f"{mode}: wrong algorithm")
    require(document.get("mode") == mode, f"{mode}: wrong mode")
    require(document.get("revision") == "FIPS205", f"{mode}: wrong revision")


def flatten_tests(document: dict[str, Any]) -> tuple[list[int], list[int]]:
    group_ids: list[int] = []
    case_ids: list[int] = []
    for group in document.get("testGroups", []):
        group_ids.append(group.get("tgId"))
        case_ids.extend(test.get("tcId") for test in group.get("tests", []))
    return group_ids, case_ids


def check_keygen() -> None:
    registration = load_json(FIXTURE_ROOT / "keygen-registration.json")
    prompt = load_json(FIXTURE_ROOT / "keygen-prompt.json")
    expected = load_json(FIXTURE_ROOT / "keygen-expected.json")
    for document in (registration, prompt, expected):
        check_discriminants(document, "keyGen")
    require(registration.get("parameterSets") == PARAMETER_SETS,
            "keyGen registration does not contain the exact 12 parameter sets")
    require(len(prompt["testGroups"]) == 12 and len(expected["testGroups"]) == 12,
            "keyGen must contain 12 prompt and result groups")
    prompt_groups, prompt_cases = flatten_tests(prompt)
    result_groups, result_cases = flatten_tests(expected)
    require(prompt_groups == list(range(1, 13)) == result_groups,
            "keyGen tgId sequence is not exactly 1..12")
    require(prompt_cases == list(range(1, 121)) == result_cases,
            "keyGen tcId sequence is not exactly 1..120")
    require([group["parameterSet"] for group in prompt["testGroups"]] == PARAMETER_SETS,
            "keyGen prompt parameter-set order differs from registration")


def check_registrations() -> None:
    for mode in ("sigGen", "sigVer"):
        registration = load_json(FIXTURE_ROOT / f"{mode.lower()}-registration.json")
        check_discriminants(registration, mode)
        capabilities = registration.get("capabilities")
        require(isinstance(capabilities, list) and len(capabilities) == 2,
                f"{mode} registration must contain two capability records")
        parameter_sets = [item for capability in capabilities
                          for item in capability.get("parameterSets", [])]
        require(len(parameter_sets) == 12 and set(parameter_sets) == set(PARAMETER_SETS),
                f"{mode} registration parameter-set coverage is not exact")
        for capability in capabilities:
            require(capability.get("hashAlgs") == HASH_ALGORITHMS,
                    f"{mode} registration hash-algorithm list is not exact")


def selected_map(cases: list[dict[str, Any]]) -> dict[int, list[int]]:
    result: dict[int, list[int]] = {}
    for case in cases:
        result.setdefault(case["tgId"], []).append(case["tcId"])
    return result


def project(document: dict[str, Any], cases: list[dict[str, Any]]) -> dict[str, Any]:
    selection = selected_map(cases)
    projected = {key: value for key, value in document.items() if key != "testGroups"}
    projected_groups = []
    for group in document["testGroups"]:
        ids = selection.get(group["tgId"])
        if ids is None:
            continue
        projected_group = {key: value for key, value in group.items() if key != "tests"}
        projected_group["tests"] = [
            test for test in group["tests"] if test["tcId"] in set(ids)
        ]
        require([test["tcId"] for test in projected_group["tests"]] == ids,
                f"projection selection is not present in upstream tgId {group['tgId']}")
        projected_groups.append(projected_group)
    projected["testGroups"] = projected_groups
    return projected


def case_lookup(document: dict[str, Any]) -> dict[tuple[int, int], tuple[dict[str, Any], dict[str, Any]]]:
    result = {}
    for group in document["testGroups"]:
        for test in group["tests"]:
            key = (group["tgId"], test["tcId"])
            require(key not in result, f"duplicate projected id: {key}")
            result[key] = (group, test)
    return result


def check_slice(filename: str, mode: str, cases: list[dict[str, Any]]) -> dict[str, Any]:
    wrapper = load_json(FIXTURE_ROOT / filename)
    require(set(wrapper) == {"provenance", "prompt", "expectedResults"},
            f"{filename}: wrong wrapper keys")
    provenance = wrapper["provenance"]
    require(provenance.get("sourceRepository") == "https://github.com/usnistgov/ACVP-Server",
            f"{filename}: wrong source repository")
    require(provenance.get("commit") == SERVER_COMMIT
            and provenance.get("release") == SERVER_RELEASE,
            f"{filename}: wrong source pin")
    require(provenance.get("selected") == cases, f"{filename}: wrong selection recipe")
    prompt = wrapper["prompt"]
    expected = wrapper["expectedResults"]
    check_discriminants(prompt, mode)
    check_discriminants(expected, mode)
    prompt_lookup = case_lookup(prompt)
    expected_lookup = case_lookup(expected)
    selected = {(case["tgId"], case["tcId"]) for case in cases}
    require(set(prompt_lookup) == selected == set(expected_lookup),
            f"{filename}: prompt/result selection is not bijective")
    return wrapper


def check_slice_shapes() -> None:
    siggen = check_slice("siggen-schema-slice.json", "sigGen", SIGGEN_CASES)
    prompt = case_lookup(siggen["prompt"])
    results = case_lookup(siggen["expectedResults"])
    for case in SIGGEN_CASES:
        key = (case["tgId"], case["tcId"])
        group, test = prompt[key]
        _result_group, result = results[key]
        randomized = case["shape"].endswith("randomized")
        require(group["deterministic"] is (not randomized),
                f"sigGen {key}: deterministic flag disagrees with fixture label")
        require(("additionalRandomness" in test) is randomized,
                f"sigGen {key}: conditional additionalRandomness mismatch")
        require(("hashAlg" in test) is ("preHash" in case["shape"]),
                f"sigGen {key}: conditional hashAlg mismatch")
        require(("context" in test) is (group["signatureInterface"] == "external"),
                f"sigGen {key}: conditional context mismatch")
        require(len(result["signature"]) == 2 * 7856,
                f"sigGen {key}: selected 128s signature is not 7856 bytes")

    sigver = check_slice("sigver-schema-slice.json", "sigVer", SIGVER_CASES)
    prompt = case_lookup(sigver["prompt"])
    results = case_lookup(sigver["expectedResults"])
    expected_shapes = {
        "external-pure-exact-length-invalid": (7856, False),
        "external-pure-one-byte-short-invalid": (7855, False),
        "external-pure-one-byte-long-invalid": (7857, False),
        "external-pure-valid": (7856, True),
        "external-preHash-valid": (7856, True),
        "internal-valid": (7856, True),
    }
    interfaces = set()
    for case in SIGVER_CASES:
        key = (case["tgId"], case["tcId"])
        group, test = prompt[key]
        _result_group, result = results[key]
        interfaces.add((group["signatureInterface"], group.get("preHash")))
        expected_size, expected_passed = expected_shapes[case["shape"]]
        require(len(test["signature"]) == 2 * expected_size,
                f"sigVer {key}: signature length disagrees with fixture label")
        require(result["testPassed"] is expected_passed,
                f"sigVer {key}: testPassed disagrees with fixture label")
    require(interfaces == {("external", "pure"), ("external", "preHash"), ("internal", None)},
            "sigVer slice does not cover all three interface/preHash shapes")


def check_coverage() -> None:
    coverage = load_json(FIXTURE_ROOT / "positive-prehash-coverage.json")
    require(coverage.get("parameterSets") == PARAMETER_SETS,
            "coverage parameter-set axis is not exact")
    require(coverage.get("hashAlgorithms") == HASH_ALGORITHMS,
            "coverage hash-algorithm axis is not exact")
    require(coverage.get("counts") == {
        "parameterSets": 12, "hashAlgorithms": 12, "cells": 144,
        "covered": 24, "uncovered": 120},
        "coverage summary is not exactly 12/12/144/24/120")
    cells = coverage.get("cells")
    require(isinstance(cells, list) and len(cells) == 144,
            "coverage matrix must contain 144 cells")
    expected_keys = [(parameter_set, hash_algorithm)
                     for parameter_set in PARAMETER_SETS
                     for hash_algorithm in HASH_ALGORITHMS]
    actual_keys = [(cell.get("parameterSet"), cell.get("hashAlg")) for cell in cells]
    require(actual_keys == expected_keys and len(set(actual_keys)) == 144,
            "coverage cells are not a unique ordered 12x12 cross product")
    covered = {}
    for cell in cells:
        key = (cell["parameterSet"], cell["hashAlg"])
        evidence = cell.get("evidence")
        require(cell.get("covered") is (evidence is not None),
                f"coverage flag/evidence mismatch at {key}")
        require(set(cell) == ({"parameterSet", "hashAlg", "covered", "evidence"}
                              if evidence is not None
                              else {"parameterSet", "hashAlg", "covered"}),
                f"coverage cell has unexpected keys at {key}")
        if evidence is not None:
            covered[key] = (evidence.get("tgId"), evidence.get("tcId"))
    require(covered == POSITIVE_PAIRS,
            "coverage matrix does not contain the exact 24 positive pairs")


def check_authority_document_data(reference: dict[str, Any], profile: dict[str, Any]) -> None:
    entries = reference.get("entries")
    require(isinstance(entries, list), "reference manifest entries must be an array")
    by_id = {entry.get("id"): entry for entry in entries if isinstance(entry, dict)}
    require(len(by_id) == len(entries), "reference manifest entry IDs must be unique")
    require(by_id.get("fips205") == {
        "id": "fips205",
        "kind": "file",
        "root": "sibling",
        "locator": "NIST.FIPS.205.pdf",
        "sha256": "8ef34228276f3386d23cb0da8c14592b8cfb0db3358016bba64df7a004f8d13d",
        "size_bytes": 1055752,
        "publication_status": "final",
        "publication_date": "2024-08-13",
        "authority": "primary-normative",
    }, "reference manifest final FIPS 205 authority record mismatch")
    require(by_id.get("acvp-server") == {
        "id": "acvp-server",
        "kind": "remote-git",
        "root": "remote",
        "locator": "https://github.com/usnistgov/ACVP-Server.git",
        "revision": SERVER_COMMIT,
        "release": SERVER_RELEASE,
        "authority": "primary-evidence-sample-generator",
    }, "reference manifest current ACVP-Server pin mismatch")
    require(by_id.get("acvp-server-v1.1.0.38") == {
        "id": "acvp-server-v1.1.0.38",
        "kind": "url",
        "root": "remote",
        "locator": "https://github.com/usnistgov/ACVP-Server/releases/tag/v1.1.0.38",
        "revision": SERVER_COMPATIBILITY_COMMIT,
        "release": SERVER_COMPATIBILITY_RELEASE,
        "authority": "primary-evidence-server-format-compatibility-boundary",
    }, "reference manifest v1.1.0.38 compatibility pin mismatch")
    require(by_id.get("acvp-protocol") == {
        "id": "acvp-protocol",
        "kind": "remote-git",
        "root": "remote",
        "locator": "https://github.com/usnistgov/ACVP.git",
        "revision": PROTOCOL_COMMIT,
        "document": PROTOCOL_DOCUMENT,
        "document_date": PROTOCOL_DOCUMENT_DATE,
        "root_source_sha256": PROTOCOL_ROOT_ARTIFACT[2],
        "source_composite_sha256": PROTOCOL_COMPOSITE_SHA256,
        "authority": "primary-evidence-protocol",
    }, "reference manifest ACVP protocol identity/date mismatch")
    require(by_id.get("sp800-230-ipd") == {
        "id": "sp800-230-ipd",
        "kind": "url",
        "root": "remote",
        "locator": "https://nvlpubs.nist.gov/nistpubs/SpecialPublications/NIST.SP.800-230.ipd.pdf",
        "revision": "NIST.SP.800-230.ipd",
        "sha256": "62d092f787a1f79260454bf332b642ff3b5b73dbcce2678a133a1406065e452e",
        "size_bytes": 282069,
        "publication_status": "initial-public-draft",
        "publication_date": "2026-04-13",
        "signature_cap_per_key": 16777216,
        "profile_id": SP800_PROFILE_ID,
        "authority": "primary-nonnormative-draft-profile",
    }, "reference manifest SP 800-230 IPD authority metadata mismatch")
    require(profile == {
        "schema_version": 1,
        "profile_id": SP800_PROFILE_ID,
        "excluded_legacy_current_code_profile_id": LEGACY_CURRENT_CODE_PROFILE_ID,
        "authority": "NIST SP 800-230 Initial Public Draft, Table 1",
        "publication_status": "initial-public-draft",
        "publication_date": "2026-04-13",
        "source_sha256":
            "62d092f787a1f79260454bf332b642ff3b5b73dbcce2678a133a1406065e452e",
        "source_size_bytes": 282069,
        "signature_cap_per_key": 16777216,
        "normative_fips205_profile": False,
        "parameter_sets": SP800_IPD_PARAMETER_SETS,
    }, "SP 800-230 IPD profile is not the exact six-row non-normative authority record")


def check_bibliographic_identity() -> None:
    path = REPO_ROOT / "docs" / "slhdsa" / "report" / "references.bib"
    try:
        bibliography = path.read_text(encoding="utf-8")
    except OSError as error:
        raise CheckError(f"cannot read {path}: {error}") from error
    start = bibliography.find("@misc{acvpSlhdsa,")
    require(start >= 0, "ACVP protocol bibliography entry is missing")
    end = bibliography.find("\n}", start)
    require(end >= 0, "ACVP protocol bibliography entry is malformed")
    entry = bibliography[start:end + 2]
    require("year         = {2024}" in entry
            and "draft-livelsberger-acvp-slh-dsa-01" in entry
            and "25 June 2024" in entry,
            "ACVP protocol bibliography identity/date mismatch")


def validate_provenance_controlling_sources(sources: dict[str, Any]) -> None:
    server = sources.get("acvpServer", {})
    require(server.get("compatibilityBoundary") == {
        "release": SERVER_COMPATIBILITY_RELEASE,
        "commit": SERVER_COMPATIBILITY_COMMIT,
        "scope": "External-interface server-format compatibility boundary only.",
    }, "provenance v1.1.0.38 compatibility boundary mismatch")
    protocol = sources.get("acvpProtocol", {})
    require(protocol.get("document") == PROTOCOL_DOCUMENT
            and protocol.get("documentDate") == PROTOCOL_DOCUMENT_DATE,
            "provenance ACVP protocol identity/date mismatch")
    ipd = sources.get("sp800230InitialPublicDraft", {})
    require(ipd.get("profileId") == SP800_PROFILE_ID
            and ipd.get("publicationStatus") == "initial-public-draft"
            and ipd.get("publicationDate") == "2026-04-13",
            "provenance SP 800-230 IPD identity/status mismatch")


def expect_authority_mutation_rejected(label: str, action: Any) -> None:
    try:
        action()
    except CheckError:
        return
    raise CheckError(f"authority mutation self-test was accepted: {label}")


def check_authority_documents_and_mutations() -> None:
    reference = load_json(REPO_ROOT / "docs" / "slhdsa" / "reference-manifest.json")
    profile = load_json(REPO_ROOT / "docs" / "slhdsa" / "matrices" /
                        "sp800-230-ipd-profile.json")
    check_authority_document_data(reference, profile)
    check_bibliographic_identity()
    provenance = load_json(FIXTURE_ROOT / "provenance.json")
    validate_provenance_controlling_sources(provenance.get("sources", {}))

    bad_fips_date = copy.deepcopy(reference)
    for entry in bad_fips_date["entries"]:
        if entry.get("id") == "fips205":
            entry["publication_date"] = "2099-01-01"
    expect_authority_mutation_rejected(
        "FIPS 205 publication date",
        lambda: check_authority_document_data(bad_fips_date, profile))

    bad_fips_authority = copy.deepcopy(reference)
    for entry in bad_fips_authority["entries"]:
        if entry.get("id") == "fips205":
            entry["authority"] = "secondary-untrusted"
    expect_authority_mutation_rejected(
        "FIPS 205 authority classification",
        lambda: check_authority_document_data(bad_fips_authority, profile))

    bad_server_release = copy.deepcopy(reference)
    for entry in bad_server_release["entries"]:
        if entry.get("id") == "acvp-server":
            entry["release"] = "v1.1.0.42"
    expect_authority_mutation_rejected(
        "current ACVP-Server release",
        lambda: check_authority_document_data(bad_server_release, profile))

    bad_protocol_authority = copy.deepcopy(reference)
    for entry in bad_protocol_authority["entries"]:
        if entry.get("id") == "acvp-protocol":
            entry["authority"] = "secondary"
    expect_authority_mutation_rejected(
        "ACVP protocol authority classification",
        lambda: check_authority_document_data(bad_protocol_authority, profile))

    bad_compatibility = copy.deepcopy(reference)
    for entry in bad_compatibility["entries"]:
        if entry.get("id") == "acvp-server-v1.1.0.38":
            entry["revision"] = "0" * 40
    expect_authority_mutation_rejected(
        "v1.1.0.38 compatibility commit",
        lambda: check_authority_document_data(bad_compatibility, profile))

    bad_status = copy.deepcopy(profile)
    bad_status["publication_status"] = "final"
    expect_authority_mutation_rejected(
        "SP 800-230 publication status",
        lambda: check_authority_document_data(reference, bad_status))

    bad_provenance_compatibility = copy.deepcopy(provenance["sources"])
    bad_provenance_compatibility["acvpServer"]["compatibilityBoundary"]["commit"] = "0" * 40
    expect_authority_mutation_rejected(
        "provenance v1.1.0.38 compatibility commit",
        lambda: validate_provenance_controlling_sources(bad_provenance_compatibility))
    bad_provenance_status = copy.deepcopy(provenance["sources"])
    bad_provenance_status["sp800230InitialPublicDraft"]["publicationStatus"] = "final"
    expect_authority_mutation_rejected(
        "provenance SP 800-230 publication status",
        lambda: validate_provenance_controlling_sources(bad_provenance_status))


def check_provenance() -> dict[str, Any]:
    provenance = load_json(FIXTURE_ROOT / "provenance.json")
    require(set(provenance) == {
        "schemaVersion", "recordedOn", "normalVerification",
        "optionalCheckoutEnvironment", "sources", "sampleSuiteMeasurements",
        "committedArtifacts"},
        "provenance top-level keys are not exact")
    require(provenance.get("schemaVersion") == 1
            and provenance.get("recordedOn") == "2026-08-24",
            "provenance schema/date mismatch")
    require(provenance.get("normalVerification") == {
        "networkRequired": False,
        "description": "The checker validates only committed bytes and metadata unless an optional checkout root is set.",
    }, "normal provenance verification must be exactly network-free")
    require(provenance.get("optionalCheckoutEnvironment") == {
        "SLHDSA_ACVP_SERVER_ROOT":
            "Full usnistgov/ACVP-Server checkout at the pinned commit.",
        "SLHDSA_ACVP_PROTOCOL_ROOT":
            "Full usnistgov/ACVP protocol checkout at the pinned commit.",
    }, "optional checkout environment metadata mismatch")
    sources = provenance.get("sources")
    require(isinstance(sources, dict)
            and set(sources) == {
                "acvpServer", "acvpProtocol", "sp800230InitialPublicDraft"},
            "source provenance keys are not exact")
    validate_provenance_controlling_sources(sources)
    require(sources["acvpServer"] == {
        "repository": "https://github.com/usnistgov/ACVP-Server",
        "commit": SERVER_COMMIT,
        "release": SERVER_RELEASE,
        "compatibilityBoundary": {
            "release": SERVER_COMPATIBILITY_RELEASE,
            "commit": SERVER_COMPATIBILITY_COMMIT,
            "scope": "External-interface server-format compatibility boundary only.",
        },
        "artifacts": manifest_records(SERVER_ARTIFACTS),
    }, "ACVP-Server provenance is not the exact 15-artifact pin")
    require(sources["acvpProtocol"] == {
        "repository": "https://github.com/usnistgov/ACVP",
        "commit": PROTOCOL_COMMIT,
        "document": PROTOCOL_DOCUMENT,
        "documentDate": PROTOCOL_DOCUMENT_DATE,
        "rootArtifact": {
            "path": PROTOCOL_ROOT_ARTIFACT[0],
            "size": PROTOCOL_ROOT_ARTIFACT[1],
            "sha256": PROTOCOL_ROOT_ARTIFACT[2],
        },
        "artifacts": manifest_records(PROTOCOL_ARTIFACTS),
        "composite": {
            "algorithm": "sha256-of-sha256sum-manifest-v1",
            "pathOrder": [
                "src/draft-livelsberger-acvp-slh-dsa.adoc",
                "src/slh-dsa/sections/*.adoc in LC_ALL=C order",
            ],
            "manifestLine":
                "<lowercase-file-sha256><two ASCII spaces><checkout-relative-path><LF>",
            "sha256": PROTOCOL_COMPOSITE_SHA256,
        },
    }, "ACVP protocol provenance is not the exact 15-artifact pin")
    require(sources["sp800230InitialPublicDraft"] == {
        "url": "https://nvlpubs.nist.gov/nistpubs/SpecialPublications/NIST.SP.800-230.ipd.pdf",
        "profileId": SP800_PROFILE_ID,
        "publicationStatus": "initial-public-draft",
        "publicationDate": "2026-04-13",
        "size": 282069,
        "sha256": "62d092f787a1f79260454bf332b642ff3b5b73dbcce2678a133a1406065e452e",
    }, "SP 800-230 IPD provenance mismatch")
    require(provenance.get("sampleSuiteMeasurements") == SAMPLE_SUITE_MEASUREMENTS,
            "full sample-suite measurements are not exact")

    records = provenance.get("committedArtifacts")
    require(isinstance(records, list), "committedArtifacts must be an array")
    by_path = {}
    for record in records:
        path = record.get("path")
        require(path not in by_path, f"duplicate committed-artifact record: {path}")
        by_path[path] = record
    require(set(by_path) == set(COMMITTED_ARTIFACTS),
            "committed-artifact manifest paths are not exact")
    for path, expected in COMMITTED_ARTIFACTS.items():
        record = by_path[path]
        require((record.get("size"), record.get("sha256")) == expected,
                f"committed-artifact metadata mismatch: {path}")
        require(digest(REPO_ROOT / path) == expected,
                f"committed artifact bytes mismatch: {path}")
        kind, source_path = COMMITTED_DERIVATIONS[path]
        require(record.get("kind") == kind and record.get("sourcePath") == source_path,
                f"committed-artifact derivation metadata mismatch: {path}")
    upstream_manifest = {
        path: (size, sha256) for path, size, sha256 in SERVER_ARTIFACTS
    }
    for path, source_path in EXACT_COPY_MAP.items():
        record = by_path[path]
        upstream_size, upstream_hash = upstream_manifest[source_path]
        require(record.get("modification") == {
            "date": "2026-08-24",
            "nature": "Added one final LF; JSON values and all other bytes are unchanged.",
            "upstreamSize": upstream_size,
            "upstreamSha256": upstream_hash,
        }, f"normalized-copy modification metadata mismatch: {path}")
        require(set(record) == {
            "path", "kind", "sourcePath", "size", "sha256", "modification"},
            f"normalized-copy record keys are not exact: {path}")
    for path in set(COMMITTED_ARTIFACTS) - set(EXACT_COPY_MAP):
        require(set(by_path[path]) == {
            "path", "kind", "sourcePath", "size", "sha256"},
            f"derived-artifact record keys are not exact: {path}")
    return provenance


def regenerate_coverage(server_root: Path) -> dict[str, Any]:
    prompt_path = server_root / "gen-val/json-files/SLH-DSA-sigVer-FIPS205/prompt.json"
    expected_path = server_root / "gen-val/json-files/SLH-DSA-sigVer-FIPS205/expectedResults.json"
    registration_path = server_root / "gen-val/json-files/SLH-DSA-keyGen-FIPS205/registration.json"
    sigver_registration_path = server_root / "gen-val/json-files/SLH-DSA-sigVer-FIPS205/registration.json"
    prompt = load_json(prompt_path)
    expected = load_json(expected_path)
    parameter_sets = load_json(registration_path)["parameterSets"]
    hash_algorithms = load_json(sigver_registration_path)["capabilities"][0]["hashAlgs"]
    passed = {(group["tgId"], test["tcId"]): test["testPassed"]
              for group in expected["testGroups"] for test in group["tests"]}
    positives = {}
    for group in prompt["testGroups"]:
        if group.get("signatureInterface") != "external" or group.get("preHash") != "preHash":
            continue
        for test in group["tests"]:
            if passed[(group["tgId"], test["tcId"])]:
                key = (group["parameterSet"], test["hashAlg"])
                require(key not in positives, f"upstream duplicate positive pair: {key}")
                positives[key] = {"tgId": group["tgId"], "tcId": test["tcId"]}
    cells = []
    for parameter_set in parameter_sets:
        for hash_algorithm in hash_algorithms:
            evidence = positives.get((parameter_set, hash_algorithm))
            cell = {"parameterSet": parameter_set, "hashAlg": hash_algorithm,
                    "covered": evidence is not None}
            if evidence is not None:
                cell["evidence"] = evidence
            cells.append(cell)
    return {
        "provenance": {
            "sourceRepository": "https://github.com/usnistgov/ACVP-Server",
            "commit": SERVER_COMMIT,
            "release": SERVER_RELEASE,
            "promptPath": "gen-val/json-files/SLH-DSA-sigVer-FIPS205/prompt.json",
            "promptSha256": dict((path, sha) for path, _size, sha in SERVER_ARTIFACTS)[
                "gen-val/json-files/SLH-DSA-sigVer-FIPS205/prompt.json"],
            "expectedResultsPath": "gen-val/json-files/SLH-DSA-sigVer-FIPS205/expectedResults.json",
            "expectedResultsSha256": dict((path, sha) for path, _size, sha in SERVER_ARTIFACTS)[
                "gen-val/json-files/SLH-DSA-sigVer-FIPS205/expectedResults.json"],
            "derivation": "Join prompt tests to expectedResults by (tgId, tcId); retain testPassed=true cases from external/preHash groups; cross with registration parameterSets and hashAlgs in their upstream order.",
        },
        "parameterSets": parameter_sets,
        "hashAlgorithms": hash_algorithms,
        "counts": {"parameterSets": 12, "hashAlgorithms": 12, "cells": 144,
                   "covered": 24, "uncovered": 120},
        "cells": cells,
    }


def expected_slice(server_root: Path, mode: str, cases: list[dict[str, Any]]) -> dict[str, Any]:
    directory = server_root / f"gen-val/json-files/SLH-DSA-{mode}-FIPS205"
    prompt_path = directory / "prompt.json"
    expected_path = directory / "expectedResults.json"
    prompt = load_json(prompt_path)
    expected = load_json(expected_path)
    hashes = dict((path, sha) for path, _size, sha in SERVER_ARTIFACTS)
    return {
        "provenance": {
            "sourceRepository": "https://github.com/usnistgov/ACVP-Server",
            "commit": SERVER_COMMIT,
            "release": SERVER_RELEASE,
            "promptPath": f"gen-val/json-files/SLH-DSA-{mode}-FIPS205/prompt.json",
            "promptSha256": hashes[f"gen-val/json-files/SLH-DSA-{mode}-FIPS205/prompt.json"],
            "expectedResultsPath":
                f"gen-val/json-files/SLH-DSA-{mode}-FIPS205/expectedResults.json",
            "expectedResultsSha256":
                hashes[f"gen-val/json-files/SLH-DSA-{mode}-FIPS205/expectedResults.json"],
            "extractionRecipe": "Preserve top-level fields; preserve selected test-group fields; retain only the listed tcId records, in upstream order.",
            "selected": cases,
        },
        "prompt": project(prompt, cases),
        "expectedResults": project(expected, cases),
    }


def check_server_checkout(root_text: str) -> None:
    root = Path(root_text).expanduser().resolve()
    require(git_head(root, "ACVP-Server") == SERVER_COMMIT,
            "ACVP-Server checkout is not at the pinned commit")
    check_manifest_files(root, SERVER_ARTIFACTS, "ACVP-Server")
    for fixture_path, source_path in EXACT_COPY_MAP.items():
        fixture = (REPO_ROOT / fixture_path).read_bytes()
        upstream = (root / source_path).read_bytes()
        require(fixture == upstream + b"\n",
                f"{fixture_path}: expected exact upstream JSON plus one final LF")
    require(load_json(FIXTURE_ROOT / "siggen-schema-slice.json")
            == expected_slice(root, "sigGen", SIGGEN_CASES),
            "sigGen projection does not regenerate from the pinned checkout")
    require(load_json(FIXTURE_ROOT / "sigver-schema-slice.json")
            == expected_slice(root, "sigVer", SIGVER_CASES),
            "sigVer projection does not regenerate from the pinned checkout")
    require(load_json(FIXTURE_ROOT / "positive-prehash-coverage.json")
            == regenerate_coverage(root),
            "positive pre-hash matrix does not regenerate from the pinned checkout")
    measured: dict[str, Any] = {
        "source": SAMPLE_SUITE_MEASUREMENTS["source"],
    }
    for mode in ("keyGen", "sigGen", "sigVer"):
        directory = root / f"gen-val/json-files/SLH-DSA-{mode}-FIPS205"
        prompt = load_json(directory / "prompt.json")
        expected = load_json(directory / "expectedResults.json")
        prompt_groups, prompt_cases = flatten_tests(prompt)
        result_groups, result_cases = flatten_tests(expected)
        require(prompt_groups == result_groups and prompt_cases == result_cases,
                f"{mode}: full prompt/result identifiers are not bijective")
        mode_counts: dict[str, int] = {
            "groups": len(prompt_groups),
            "tests": len(prompt_cases),
        }
        if mode == "sigVer":
            outcomes = [
                test["testPassed"]
                for group in expected["testGroups"]
                for test in group["tests"]
            ]
            require(all(type(outcome) is bool for outcome in outcomes),
                    "sigVer: non-Boolean full-suite outcome")
            mode_counts["positive"] = sum(outcomes)
            mode_counts["negative"] = len(outcomes) - sum(outcomes)
        measured[mode] = mode_counts
    require(measured == SAMPLE_SUITE_MEASUREMENTS,
            "full checkout sample-suite measurements changed")
    try:
        subprocess.run([
            sys.executable, str(REPO_ROOT / "scripts/slhdsa/generate-acvp-corpus.py"),
            "--source-root", str(root), "--check"], cwd=REPO_ROOT, check=True,
            timeout=60)
    except (OSError, subprocess.SubprocessError) as error:
        raise CheckError(f"lossless corpus does not regenerate exactly: {error}") from error


def check_protocol_checkout(root_text: str) -> None:
    root = Path(root_text).expanduser().resolve()
    require(git_head(root, "ACVP protocol") == PROTOCOL_COMMIT,
            "ACVP protocol checkout is not at the pinned commit")
    check_manifest_files(root, [PROTOCOL_ROOT_ARTIFACT], "ACVP protocol root")
    check_manifest_files(root, PROTOCOL_ARTIFACTS, "ACVP protocol")
    composite_entries = [PROTOCOL_ROOT_ARTIFACT, *PROTOCOL_ARTIFACTS]
    manifest = bytearray()
    for relative, _expected_size, _expected_hash in composite_entries:
        actual_hash = digest(root / relative)[1]
        manifest.extend(f"{actual_hash}  {relative}\n".encode("ascii"))
    require(hashlib.sha256(manifest).hexdigest() == PROTOCOL_COMPOSITE_SHA256,
            "ACVP protocol root-plus-sections composite mismatch")


def main() -> int:
    try:
        check_authority_documents_and_mutations()
        check_provenance()
        check_keygen()
        check_registrations()
        check_slice_shapes()
        check_coverage()
        check_lossless_corpus()

        server_root = os.environ.get("SLHDSA_ACVP_SERVER_ROOT")
        protocol_root = os.environ.get("SLHDSA_ACVP_PROTOCOL_ROOT")
        if server_root:
            check_server_checkout(server_root)
        if protocol_root:
            check_protocol_checkout(protocol_root)

        print(
            "SLH-DSA ACVP provenance: PASS "
            f"(9 schema/provenance artifacts + 1 lossless corpus; 15 server artifacts; "
            f"full suites 12/120, 72/624, 36/504 (+72/-432); "
            f"144 coverage cells/24 positive; "
            f"authority mutation tests: 8 rejected; "
            f"server checkout: {'verified' if server_root else 'skipped'}; "
            f"protocol checkout: {'verified' if protocol_root else 'skipped'})"
        )
        return 0
    except CheckError as error:
        print(f"SLH-DSA ACVP provenance: FAIL: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
