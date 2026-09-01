#!/usr/bin/env python3
"""Deterministic, non-mutating checks for the SLH-DSA assurance harness."""

from __future__ import annotations

import ast
import csv
import copy
import hashlib
import json
import os
import re
import shutil
import stat
import subprocess
import sys
import tempfile
import tomllib
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Callable
from unittest import mock


sys.dont_write_bytecode = True

ROOT = Path(__file__).resolve().parents[2]
DOCS = ROOT / "docs" / "slhdsa"

REQUIRED_FILES = (
    "README.md",
    "scope.md",
    "source-ledger.md",
    "reference-manifest.json",
    "specification.md",
    "lean-blueprint.md",
    "proof-obligations.md",
    "security-architecture.md",
    "validation.md",
    "matrices/coverage.csv",
    "matrices/proof-obligations.csv",
    "matrices/assumptions.csv",
    "matrices/tcb.csv",
    "matrices/fips205-profile.json",
    "matrices/sp800-230-ipd-profile.json",
)

S01_REQUIRED_FILES = (
    "lakefile.lean",
    "HashSigTest/SLHDSA/ACVP/StrictJson.lean",
    "HashSigTest/SLHDSA/ACVP/Schema.lean",
    "HashSigTest/SLHDSA/ACVP/ParserTests.lean",
    "HashSigTest/SLHDSA/ACVP/fixtures/NOTICE-NIST.txt",
    "HashSigTest/SLHDSA/ACVP/fixtures/keygen-registration.json",
    "HashSigTest/SLHDSA/ACVP/fixtures/siggen-registration.json",
    "HashSigTest/SLHDSA/ACVP/fixtures/sigver-registration.json",
    "HashSigTest/SLHDSA/ACVP/fixtures/keygen-prompt.json",
    "HashSigTest/SLHDSA/ACVP/fixtures/keygen-expected.json",
    "HashSigTest/SLHDSA/ACVP/fixtures/siggen-schema-slice.json",
    "HashSigTest/SLHDSA/ACVP/fixtures/sigver-schema-slice.json",
    "HashSigTest/SLHDSA/ACVP/fixtures/positive-prehash-coverage.json",
    "HashSigTest/SLHDSA/ACVP/fixtures/provenance.json",
    "scripts/slhdsa/check-acvp-provenance.py",
)

CSV_SCHEMAS = {
    "coverage.csv": (
        ["id", "profile", "layer", "claim", "primary_source", "source_locator",
         "current_artifact", "current_status", "target_status", "evidence", "notes"],
        {
            "profile": {"FIPS205-12", "SPX-TW-ABS", "SP800-230-IPD-6SET",
                        "LEGACY-SHA2-128-24", "C13-ETH", "DEPLOY-TBD"},
            "current_status": {"covered", "partial", "missing", "not-applicable", "disputed"},
            "target_status": {"required", "deferred", "out-of-scope", "blocked"},
        },
    ),
    "proof-obligations.csv": (
        ["id", "profile", "category", "obligation", "source", "lean_target", "status",
         "severity", "evidence", "notes"],
        {
            "profile": {"FIPS205-12", "SPX-TW-ABS", "SP800-230-IPD-6SET",
                        "LEGACY-SHA2-128-24", "C13-ETH", "DEPLOY-TBD"},
            "status": {"open", "blocked", "provisional", "discharged", "not-applicable"},
            "severity": {"critical", "high", "medium", "low"},
        },
    ),
    "assumptions.csv": (
        ["id", "profile", "assumption", "kind", "scope", "status", "discharge", "evidence",
         "notes"],
        {
            "profile": {"FIPS205-12", "SPX-TW-ABS", "SP800-230-IPD-6SET",
                        "LEGACY-SHA2-128-24", "C13-ETH", "DEPLOY-TBD"},
            "kind": {"cryptographic", "modeling", "implementation", "toolchain", "external"},
            "status": {"proposed", "accepted", "rejected", "blocked", "discharged"},
        },
    ),
    "tcb.csv": (
        ["id", "component", "boundary", "trust_reason", "status", "mitigation", "evidence",
         "notes"],
        {
            "status": {"inherited", "provisional", "accepted", "remove", "blocked"},
        },
    ),
}

# The former S00 security placeholder was removed by the upstream architecture merge. Any
# admission under HashSig is now an error; keeping this as an exact empty set preserves monotonicity.
SORRY_ALLOWLIST: set[tuple[str, int, str]] = set()

S02_REPAIR_BASE_REVISION = "7b77e700b3d24a6ab94ed741a650954bbd90859a"
S02_SOURCE_GLOBS = (
    "HashSig/SLHDSA/*.lean",
    "HashSig/SLHDSA/C13/*.lean",
    "HashSig/SLHDSA/Concrete/*.lean",
    "HashSig/SLHDSA/HypertreeGeneral/*.lean",
    "HashSig/SLHDSA/Security/*.lean",
)
S02_SOURCE_COMMAND = (
    "sha256sum HashSig/SLHDSA/*.lean HashSig/SLHDSA/C13/*.lean "
    "HashSig/SLHDSA/Concrete/*.lean HashSig/SLHDSA/HypertreeGeneral/*.lean "
    "HashSig/SLHDSA/Security/*.lean | sha256sum"
)
S02_SOURCE_DETERMINISTIC_COMMAND = f"LC_ALL=C {S02_SOURCE_COMMAND}"
# This is the one authoritative current partition. The six historical SHA-256 CLI cases are a
# subset of path-cli=20, and nominal success is deliberately excluded from mutation accounting.
PARSER_FOCUSED_CASE_COUNTS = {
    "legacy": 8,
    "source-object-link": 21,
    "imports": 4,
    "sha-output-binding": 9,
    "path-cli": 20,
    "output-types": 2,
    "artifacts": 130,
    "wrong-srcdir": 2,
    "stale": 2,
    "fresh-root": 5,
    "query-output": 5,
    "replacement-cache": 3,
    "descriptor-lifecycle": 6,
    "descriptor-ownership": 17,
}
PARSER_FOCUSED_TOTAL = sum(PARSER_FOCUSED_CASE_COUNTS.values())
PARSER_FOCUSED_PARTITION = (
    "focused-parser-partition: legacy=8; source-object-link=21; imports=4; "
    "sha-output-binding=9; path-cli=20; output-types=2; artifacts=130; wrong-srcdir=2; "
    "stale=2; fresh-root=5; query-output=5; replacement-cache=3; "
    "descriptor-lifecycle=6; descriptor-ownership=17; total=234; "
    "sha-cli-is-subset-of-path-cli=6; "
    "nominal-success-excluded=true"
)

EXPECTED_S01_AUTHORITY_RECORDS = {
    "fips205": {
        "id": "fips205",
        "kind": "file",
        "root": "sibling",
        "locator": "NIST.FIPS.205.pdf",
        "sha256": "8ef34228276f3386d23cb0da8c14592b8cfb0db3358016bba64df7a004f8d13d",
        "size_bytes": 1055752,
        "title": "Stateless Hash-Based Digital Signature Standard",
        "authors": ["National Institute of Standards and Technology"],
        "doi": "10.6028/NIST.FIPS.205",
        "publication_status": "final",
        "publication_date": "2024-08-13",
        "authority": "primary-normative",
    },
    "sp800-230-ipd": {
        "id": "sp800-230-ipd",
        "kind": "url",
        "root": "remote",
        "locator":
            "https://nvlpubs.nist.gov/nistpubs/SpecialPublications/NIST.SP.800-230.ipd.pdf",
        "revision": "NIST.SP.800-230.ipd",
        "sha256": "62d092f787a1f79260454bf332b642ff3b5b73dbcce2678a133a1406065e452e",
        "size_bytes": 282069,
        "publication_status": "initial-public-draft",
        "publication_date": "2026-04-13",
        "signature_cap_per_key": 16777216,
        "title": "Additional SLH-DSA Parameter Sets for Limited-Signature Use Cases",
        "authors": ["Quynh Dang", "Dustin Moody"],
        "doi": "10.6028/NIST.SP.800-230.ipd",
        "profile_id": "SP800-230-IPD-6SET",
        "authority": "primary-nonnormative-draft-profile",
    },
    "acvp-server": {
        "id": "acvp-server",
        "kind": "remote-git",
        "root": "remote",
        "locator": "https://github.com/usnistgov/ACVP-Server.git",
        "revision": "975de31eb83d87039ec88934fdc47d8c312b892d",
        "release": "v1.1.0.43",
        "authority": "primary-evidence-sample-generator",
    },
    "acvp-protocol": {
        "id": "acvp-protocol",
        "kind": "remote-git",
        "root": "remote",
        "locator": "https://github.com/usnistgov/ACVP.git",
        "revision": "892fd14710f3a7edbea230d0aecc5511e0257f8e",
        "document": "draft-livelsberger-acvp-slh-dsa-01",
        "document_title": "ACVP SLH-DSA JSON Specification",
        "document_author": "B. Livelsberger",
        "document_date": "2024-06-25",
        "root_source_sha256":
            "d9c7088a6bb0531b2a5ab65104f467a7abe0e5ffc4d22f8ec1b7b90978d7d061",
        "source_composite_sha256":
            "bc38ec528afcaa7f6a8155fd75a7612166203c789a540c0ac42e860a04c40a54",
        "authority": "primary-evidence-protocol",
    },
    "acvp-server-v1.1.0.38": {
        "id": "acvp-server-v1.1.0.38",
        "kind": "url",
        "root": "remote",
        "locator": "https://github.com/usnistgov/ACVP-Server/releases/tag/v1.1.0.38",
        "revision": "85f8742965b2691862079172982683757d8d91db",
        "release": "v1.1.0.38",
        "authority": "primary-evidence-server-format-compatibility-boundary",
    },
}

SP800_PROFILE_ID = "SP800-230-IPD-6SET"
LEGACY_PROFILE_ID = "LEGACY-SHA2-128-24"
DEPRECATED_PROFILE_ID = "SP800-230-" + chr(0x31) + "28-24"

FIPS205_PROFILE_SHA256 = "c833c36b33951e3b76fcf344e282cb26a37317f115b425eb776dfcdc1a23eeb5"
FIPS205_PROFILE_SIZE = 5059
FIPS205_AUTHORITY = "FIPS 205 final, Table 2, Sections 10 and 11"
FIPS205_OTHER_PREHASHES = (
    "Permitted only when approved and providing at least 8n bits of classical collision and "
    "second-preimage strength; collision strength requires a digest of at least 2n bytes. The "
    "signature identifier must identify the pure/pre-hash mode and the pre-hash/XOF (including "
    "XOF output length)."
)
FIPS205_RANDOMNESS = (
    "Hedged signing supplies an n-byte addrnd; deterministic signing omits addrnd and "
    "slh_sign_internal substitutes PK.seed as opt_rand."
)

# Updating a canonical matrix requires updating its exact pin together with the structured record.
S01_MATRIX_PINS = {
    "docs/slhdsa/matrices/assumptions.csv":
        (2489, "71347114ec62e7757907bead905527ff7a8bd1d254abaf4812171d3368211350"),
    "docs/slhdsa/matrices/coverage.csv":
        (6414, "09dc0bc3a928e0c9779f7a84e1b258a797436c98a0779dd7df4f3d5a63dfff26"),
    "docs/slhdsa/matrices/fips205-profile.json":
        (5059, "c833c36b33951e3b76fcf344e282cb26a37317f115b425eb776dfcdc1a23eeb5"),
    "docs/slhdsa/matrices/proof-obligations.csv":
        (5856, "29e924b1c1f5be3ef61ba07e561ce448252fb00fd177bec8a3096924d52c15e2"),
    "docs/slhdsa/matrices/sp800-230-ipd-profile.json":
        (1504, "77ee7c4f0e872f2f2f31c830a14f4d90d63c55d260a0f3aaa3ac0e4aec92d26e"),
    "docs/slhdsa/matrices/tcb.csv":
        (3145, "6121f899689d202e73ac1ed44beeca35b7428c214e0f94a03412123941ae3acc"),
}

# The four load-bearing ACVP roots retain the exact typed dependency/visibility boundary formerly
# represented by inventory rows. These static records are authoritative and mutation-tested.
ACVP_DEPENDENCY_RECORDS = {
    "DECL-011": {
        "name": "SLHDSA.Test.ACVP.parameterSets",
        "visibility": "public",
        "direct_dependencies": [
            "lean-public|SLHDSA.Test.ACVP.ParamInfo",
        ],
        "reverse_dependencies": [
            "source-private-direct|HashSigTest/SLHDSA/ACVP/Schema.lean|parameterByName|187",
        ],
    },
    "DECL-012": {
        "name": "SLHDSA.Test.ACVP.parseAndValidate",
        "visibility": "public",
        "direct_dependencies": [
            "lean-public|SLHDSA.Test.ACVP.parsePrompt",
            "lean-public|SLHDSA.Test.ACVP.parseResults",
            "source-private-direct|HashSigTest/SLHDSA/ACVP/Schema.lean|validatePair|377",
        ],
        "reverse_dependencies": [
            "source-private-direct|HashSigTest/SLHDSA/ACVP/ParserTests.lean|runPositive|97",
            "source-private-direct|HashSigTest/SLHDSA/ACVP/ParserTests.lean|runNegative|113",
            "root-entry-transitive|HashSigTest/SLHDSA/ACVP/ParserTests.lean|main|205",
        ],
    },
    "DECL-013": {
        "name": "main",
        "visibility": "public-root",
        "direct_dependencies": [
            "source-private-direct|HashSigTest/SLHDSA/ACVP/ParserTests.lean|runAll|197",
        ],
        "reverse_dependencies": [
            "lake-exe-direct|slhdsa_acvp_parser",
        ],
    },
    "DECL-014": {
        "name": "SLHDSA.Test.ACVP.parseWrappedPair",
        "visibility": "public",
        "direct_dependencies": [
            "lean-public|SLHDSA.Test.ACVP.StrictJson.parse",
            "source-private-direct|HashSigTest/SLHDSA/ACVP/Schema.lean|asObject|136",
            "source-private-direct|HashSigTest/SLHDSA/ACVP/Schema.lean|requireKeys|123",
            "source-private-direct|HashSigTest/SLHDSA/ACVP/Schema.lean|field|131",
            "source-private-direct|HashSigTest/SLHDSA/ACVP/Schema.lean|parsePromptJson|312",
            "source-private-direct|HashSigTest/SLHDSA/ACVP/Schema.lean|parseResultsJson|356",
            "source-private-direct|HashSigTest/SLHDSA/ACVP/Schema.lean|validatePair|377",
        ],
        "reverse_dependencies": [
            "source-private-direct|HashSigTest/SLHDSA/ACVP/ParserTests.lean|nestedPair|37",
            "source-private-direct|HashSigTest/SLHDSA/ACVP/ParserTests.lean|runNegative|113",
            "root-entry-transitive|HashSigTest/SLHDSA/ACVP/ParserTests.lean|main|205",
        ],
    },
}

# These test sources are frozen in r7. Pins are defense in depth; the semantic source and external
# elaboration checks below remain mandatory and are independently mutation-tested.
S01_ACVP_LEAN_PINS = {
    "HashSigTest/SLHDSA/ACVP/StrictJson.lean":
        (2849, "20f9aff3f5339e54d7fc5e148fadb0e37d8f4b4bd816938f0a81b4cf7b087089"),
    "HashSigTest/SLHDSA/ACVP/Schema.lean":
        (18619, "3ccab70a3ff8e2e6f39cc09e4b2296fad035267b4def0e6c8bb002062f5733a0"),
    "HashSigTest/SLHDSA/ACVP/ParserTests.lean":
        (12290, "1a56fd4fef9880a464583749d27e14840b2f48afc81fe007db473bb167585cd5"),
}


class CheckFailure(Exception):
    pass


def require(condition: bool, message: str) -> None:
    if not condition:
        raise CheckFailure(message)


def read_json(path: Path) -> Any:
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        raise CheckFailure(f"{path.relative_to(ROOT)}: invalid JSON: {error}") from error


def check_required_files() -> None:
    missing = [rel for rel in REQUIRED_FILES if not (DOCS / rel).is_file()]
    require(not missing, f"missing required files: {', '.join(missing)}")
    missing_s01 = [rel for rel in S01_REQUIRED_FILES if not (ROOT / rel).is_file()]
    require(not missing_s01, f"missing S01 files: {', '.join(missing_s01)}")
    require((ROOT / "scripts/slhdsa/PolicyAudit.lean").is_file(),
            "missing elaborated-environment audit scripts/slhdsa/PolicyAudit.lean")
    require((ROOT / "scripts/slhdsa/AxiomAudit.lean").is_file(),
            "missing permanent exact-root audit scripts/slhdsa/AxiomAudit.lean")
    require((ROOT / "scripts/slhdsa/fixtures/SLHDSAPolicyIRMacro.lean").is_file(),
            "missing compiled-IR fixture macro")
    require((ROOT / "scripts/slhdsa/fixtures/HashSig/PolicyIRFixture.lean").is_file(),
            "missing compiled-IR fixture victim")
    audit = (ROOT / "scripts/slhdsa/PolicyAudit.lean").read_text(encoding="utf-8")
    for marker in ("standardAxiomAllowlist", "collectHashSigModuleEntryFindings",
                   "mapModuleEntryFindings", "ModuleEntryArrays", "fixtureExpected",
                   "ownsExternalDependencyTheorem", "collectRawCurrentEntryFixture",
                   "importStaticTargetEnvironment", "isMeta := true", "loadExts := false",
                   "validateStaticInitializerFixture", "SLHDSA_POLICY_RUN_IR_FIXTURE",
                   "compiled fixture initializer executed during static import",
                   "regular-init/ordinary", "builtin-init/ordinary", "extern/ordinary",
                   "implemented-by/ordinary", "regular-init/ir", "builtin-init/ir",
                   "extern/ir", "implemented-by/ir", "surface : String"):
        require(marker in audit, f"PolicyAudit.lean: missing static semantic gate {marker}")
    require("import HashSig" not in audit,
            "PolicyAudit.lean must not source-import HashSig")
    axiom_audit = (ROOT / "scripts/slhdsa/AxiomAudit.lean").read_text(encoding="utf-8")
    for marker in ("expectedRoots.size == 177", "seen.contains root",
                   "Lean.collectAxioms root", "sameNames observed expected",
                   "footprints 6/26/11/134"):
        require(marker in axiom_audit,
                f"AxiomAudit.lean: missing exact-root gate {marker}")
    wrapper = (ROOT / "scripts/slhdsa/validate.sh").read_text(encoding="utf-8")
    require("lake env lean scripts/slhdsa/PolicyAudit.lean" in wrapper,
            "validate.sh does not run the authoritative elaborated audit")
    require("lake env lean scripts/slhdsa/AxiomAudit.lean" in wrapper,
            "validate.sh does not run the permanent exact-root audit")
    require("InventoryProbe.lean" not in wrapper,
            "validate.sh still depends on a phase-specific inventory probe")
    require("lake exe slhdsa_primitive_tests" in wrapper,
            "validate.sh does not run the S04 primitive tests")
    require("lake exe slhdsa_wots_tests" in wrapper,
            "validate.sh does not run the S05 WOTS construction tests")
    require("lake exe slhdsa_xmss_tests" in wrapper,
            "validate.sh does not run the S06 XMSS construction tests")
    require("lake exe slhdsa_fors_tests" in wrapper,
            "validate.sh does not run the S07 FORS construction tests")
    require("lake exe slhdsa_hypertree_tests" in wrapper,
            "validate.sh does not run the hypertree conformance tests")
    require("lake exe slhdsa_external_codec_tests" in wrapper,
            "validate.sh does not run the structured external-codec tests")
    for marker in ("python3 -B scripts/slhdsa/check-acvp-provenance.py",
                   "lake build HashSigTest", "--resolve-acvp-parser-executable"):
        require(marker in wrapper, f"validate.sh: missing S01 gate {marker}")
    for marker in ("--elaborated-acvp-dependencies", "--audit-acvp-lake-config",
                   "expected_parser_stdout_file", "require_exact_parser_stdout_file",
                   "cmp -s", "-ne 154", "PASS (16 cases)", "PASS (52 cases)",
                   "PASS (68 cases)",
                   "parser stdout file mutation self-tests: PASS (6 rejected)",
                   "successful wrong-executable stdout self-test: PASS (smoke_test rejected)",
                   "parser nonzero-exit self-test: PASS", "resolved_parser_path_file",
                   "expected_parser_path_file", "expected_parser_hash_file",
                   "before_parser_hash_file", "after_parser_hash_file",
                   "require_bound_parser_hash_files", "--sha256-ordinary-file",
                   "fresh_parser_build_root", "test ! -e",
                   "resolved_parser_executable"):
        require(marker in wrapper, f"validate.sh: missing fail-closed parser-output gate {marker}")
    for marker in ("restore_default_lake_configuration", "local original_status=$?",
                   "trap - EXIT", "set +e", "parser_build_override_active=1",
                   "cleanup_restore_mode=\"production\"", "explicit-7", "errexit",
                   "sigterm-143", "failure-preserves-7", "success-restore-failure",
                   "normal-success", "resolve-failure-23",
                   "parser override cleanup self-tests: PASS (7 cases; SIGKILL cannot run EXIT traps)"):
        require(marker in wrapper,
                f"validate.sh: missing unconditional parser-override cleanup marker {marker}")
    override_marker = "parser_build_override_active=1\nPYTHONDONTWRITEBYTECODE=1 python3 -B " \
                      "scripts/slhdsa/check-harness.py \\\n  --resolve-acvp-parser-executable"
    require(override_marker in wrapper,
            "validate.sh must arm cleanup immediately before the possibly mutating resolve query")
    require(wrapper.index(override_marker) < wrapper.rindex("restore_default_lake_configuration")
            < wrapper.index("lake env lean scripts/slhdsa/PolicyAudit.lean"),
            "validate.sh must explicitly restore the parser override before later Lake commands")
    require(wrapper.count("--audit-acvp-lake-config") == 2,
            "validate.sh must audit both the pre-query configuration and the restored default configuration")
    require("lake exe slhdsa_acvp_parser" not in wrapper,
            "validate.sh must execute the exact attested parser binary, not repeat Lake lookup")
    checker_source = (ROOT / "scripts/slhdsa/check-harness.py").read_text(encoding="utf-8")
    for marker in ('["lake", "-R", "-H", "--no-cache", f"-KbuildDir={build_root}",',
                   "parse_strict_json_bytes", "validate_parser_build_trace_data",
                   "validate_fresh_build_root_before", "sha256_ordinary_file",
                   "validate_sha256_binding", "os.O_NOFOLLOW", "os.fstat",
                   "canonical_cli_absolute_path", "proper_relative_parts",
                   "open_absolute_directory_fd", "dir_fd=parent_descriptor",
                   "_OwnedDescriptor", "_close_owned_descriptors",
                   "BaseException.add_note",
                   "validate_raw_close_inventory",
                   "Sole production raw close site",
                   "descriptor-ownership=17",
                   "30 rejected; production 10 acquisitions/1 close",
                   "owner-alias invariant failed",
                   "PARSER_MODULE_ARTIFACT_KEYS", "parser_module_artifact_manifest",
                   "validate_current_parser_artifact_paths",
                   "validate_current_parser_artifact_metadata",
                   "exact r11 18-current-artifact symlink substitution",
                   "130 current-artifact path/type/metadata",
                   "HashSigTest.SLHDSA.ACVP.Schema",
                   "HashSigTest.SLHDSA.ACVP.StrictJson", PARSER_SOURCE_SHA256):
        require(marker in checker_source,
                f"check-harness.py: missing parser build-input attestation marker {marker}")
    require('parser_stdout="$(' not in wrapper and 'swapped_parser_stdout="$(' not in wrapper,
            "validate.sh must not normalize parser stdout through command substitution")
    for marker in ("mktemp -d", "PolicyIRFixture.ir", "SLHDSA_POLICY_SENTINEL",
                   "SLHDSA_POLICY_RUN_IR_FIXTURE=1", "test ! -e"):
        require(marker in wrapper, f"validate.sh: missing compiled-IR gate {marker}")
    validation = (DOCS / "validation.md").read_text(encoding="utf-8")
    for marker in ("177 unique load-bearing roots", "exactly 17 generated unsafe recursion helpers",
                   PARSER_FOCUSED_PARTITION):
        require(marker in validation,
                f"validation.md: missing permanent audit evidence {marker!r}")


_BeforeOpenHook = Callable[[Path, str], None]


def _require_descriptor_walker_support() -> None:
    require(os.name == "posix" and sys.platform.startswith("linux"),
            "S01: identity-stable active-tree traversal requires Linux")
    require(hasattr(os, "O_DIRECTORY") and hasattr(os, "O_NOFOLLOW"),
            "S01: platform lacks O_DIRECTORY/O_NOFOLLOW")
    require(os.open in os.supports_dir_fd and os.stat in os.supports_dir_fd
            and os.scandir in os.supports_fd,
            "S01: Python runtime lacks descriptor-relative open/stat/scandir support")


def _object_identity(status: os.stat_result) -> tuple[int, int, int]:
    return (status.st_dev, status.st_ino, stat.S_IFMT(status.st_mode))


def _directory_flags() -> int:
    return os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW | getattr(os, "O_CLOEXEC", 0)


def _file_flags() -> int:
    return (os.O_RDONLY | os.O_NOFOLLOW | getattr(os, "O_CLOEXEC", 0)
            | getattr(os, "O_NONBLOCK", 0))


@dataclass
class _OwnedDescriptor:
    """One local fd owner; `take` makes it unowned before any fallible transfer/close."""

    descriptor: int
    label: str

    def take(self) -> int:
        require(self.descriptor >= 0,
                f"S01: descriptor owner was already released: {self.label}")
        descriptor = self.descriptor
        self.descriptor = -1
        return descriptor


def _close_owned_descriptors(
        owners: list[_OwnedDescriptor],
        cleanup_label: str,
        active_exception: BaseException | None = None) -> None:
    """Preflight owners, close each unique fd once, and preserve any active exception."""

    # Preflight the complete owner list before any close. Every live owner becomes unowned here,
    # and distinct owners aliasing one integer are recorded without ever retrying that integer.
    unique_descriptors: list[int] = []
    seen_descriptors: set[int] = set()
    aliased_owners = 0
    for owner in owners:
        if owner.descriptor < 0:
            continue
        descriptor = owner.take()
        if descriptor in seen_descriptors:
            aliased_owners += 1
            continue
        seen_descriptors.add(descriptor)
        unique_descriptors.append(descriptor)

    failures: list[BaseException] = []
    for descriptor in unique_descriptors:
        try:
            # Sole production raw close site. The owner is already unowned, so this integer is
            # never retried even if Linux consumed/reused it before reporting a close error.
            os.close(descriptor)
        except BaseException as error:
            failures.append(error)
    if not failures and aliased_owners == 0:
        return

    # Evidence is deliberately constant/count-only. It never reads, formats, or otherwise derives
    # data from a cleanup exception object, class, name, metaclass, attribute, or representation.
    failure_count = len(failures)
    unique_count = len(unique_descriptors)
    note = (
        "S01 descriptor cleanup anomaly: "
        f"aliased_owners={aliased_owners}; unique_descriptors={unique_count}; "
        f"close_failures={failure_count}")
    if active_exception is not None:
        try:
            # Call the base implementation explicitly: a hostile exception subclass may override
            # add_note, but cleanup evidence must never replace the exact active exception.
            BaseException.add_note(active_exception, note)
        except BaseException:
            # Recording is defense in depth and must never replace the exact active exception.
            pass
        return
    if aliased_owners:
        message = (
            "S01: descriptor cleanup owner-alias invariant failed after all unique descriptors "
            f"were attempted: aliased_owners={aliased_owners}; "
            f"unique_descriptors={unique_count}; close_failures={failure_count}")
    else:
        message = (
            "S01: descriptor cleanup failed after all unique descriptors were attempted: "
            f"unique_descriptors={unique_count}; close_failures={failure_count}")
    failure = CheckFailure(message)
    if failures:
        raise failure from failures[0]
    raise failure


def validate_raw_close_inventory(source: str | None = None) -> None:
    """Enforce the exact scoped AST policy for this frozen descriptor-management source."""

    if source is None:
        source = Path(__file__).read_text(encoding="utf-8")
    try:
        tree = ast.parse(source)
    except SyntaxError as error:
        raise CheckFailure(f"S01: cannot parse descriptor policy inventory: {error}") from error

    parents: dict[ast.AST, ast.AST] = {}
    for parent in ast.walk(tree):
        for child in ast.iter_child_nodes(parent):
            parents[child] = parent

    scopes: dict[ast.AST, str] = {}

    class ScopeVisitor(ast.NodeVisitor):
        def __init__(self) -> None:
            self.stack: list[str] = []

        def generic_visit(self, node: ast.AST) -> None:
            scopes[node] = ".".join(self.stack) if self.stack else "<module>"
            super().generic_visit(node)

        def visit_FunctionDef(self, node: ast.FunctionDef) -> None:
            scopes[node] = ".".join(self.stack) if self.stack else "<module>"
            for decorator in node.decorator_list:
                self.visit(decorator)
            self.visit(node.args)
            if node.returns is not None:
                self.visit(node.returns)
            for parameter in getattr(node, "type_params", []):
                self.visit(parameter)
            self.stack.append(node.name)
            for statement in node.body:
                self.visit(statement)
            self.stack.pop()

        def visit_AsyncFunctionDef(self, node: ast.AsyncFunctionDef) -> None:
            self.visit_FunctionDef(node)

        def visit_ClassDef(self, node: ast.ClassDef) -> None:
            scopes[node] = ".".join(self.stack) if self.stack else "<module>"
            for expression in [*node.decorator_list, *node.bases, *node.keywords,
                               *getattr(node, "type_params", [])]:
                self.visit(expression)
            self.stack.append(node.name)
            for statement in node.body:
                self.visit(statement)
            self.stack.pop()

    ScopeVisitor().visit(tree)

    protected = {"os", "_OwnedDescriptor", "_close_owned_descriptors"}
    os_imports = [node for node in ast.walk(tree) if isinstance(node, ast.Import)
                  for alias in node.names if alias.name == "os"]
    require(len(os_imports) == 1
            and len(os_imports[0].names) == 1
            and os_imports[0].names[0].name == "os"
            and os_imports[0].names[0].asname is None,
            "S01: os must have one exact unaliased import")
    require(not any(isinstance(node, ast.ImportFrom) and node.module == "os"
                    for node in ast.walk(tree)),
            "S01: from-os descriptor aliases are forbidden")
    require(not any(isinstance(node, ast.Import)
                    and any(alias.name == "importlib" or alias.name.startswith("importlib.")
                            or alias.asname == "os"
                            for alias in node.names)
                    for node in ast.walk(tree)),
            "S01: module alias/dynamic-import support is forbidden in the descriptor gate")
    require(not any(isinstance(node, ast.ImportFrom)
                    and node.module is not None and node.module.startswith("importlib")
                    for node in ast.walk(tree)),
            "S01: importlib aliases are forbidden in the descriptor gate")

    for node in ast.walk(tree):
        if isinstance(node, ast.Name) and isinstance(node.ctx, (ast.Store, ast.Del)) \
                and node.id in protected:
            raise CheckFailure(f"S01: protected descriptor symbol is rebound: {node.id}")
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            if node.name == "os":
                raise CheckFailure("S01: os is rebound by a declaration")
            if node.name == "_OwnedDescriptor" and not isinstance(node, ast.ClassDef):
                raise CheckFailure("S01: owner constructor is rebound by the wrong declaration kind")
            if node.name == "_close_owned_descriptors" \
                    and not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                raise CheckFailure("S01: cleanup helper is rebound by the wrong declaration kind")
        if isinstance(node, ast.arg) and node.arg in protected:
            raise CheckFailure(f"S01: protected descriptor symbol is shadowed by an argument: "
                               f"{node.arg}")
        if isinstance(node, (ast.Global, ast.Nonlocal)) \
                and any(name in protected for name in node.names):
            raise CheckFailure("S01: protected descriptor symbol has global/nonlocal rebinding")
        if isinstance(node, (ast.Assign, ast.AnnAssign, ast.NamedExpr)):
            value = node.value
            if isinstance(value, ast.Name) and value.id in protected:
                raise CheckFailure(
                    f"S01: protected descriptor symbol is assigned as an alias: {value.id}")
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Name) \
                and node.func.id == "getattr" and node.args \
                and isinstance(node.args[0], ast.Name) and node.args[0].id == "os":
            require(len(node.args) == 3
                    and isinstance(node.args[1], ast.Constant)
                    and node.args[1].value in {"O_CLOEXEC", "O_NONBLOCK"}
                    and isinstance(node.args[2], ast.Constant) and node.args[2].value == 0,
                    "S01: dynamic getattr(os, ...) descriptor access is forbidden")
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Name) \
                and node.func.id == "vars" and node.args \
                and isinstance(node.args[0], ast.Name) and node.args[0].id == "os":
            raise CheckFailure("S01: dynamic vars(os) descriptor access is forbidden")
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Name) \
                and node.func.id in {"__import__", "import_module", "eval", "exec"}:
            raise CheckFailure("S01: dynamic import/evaluation is forbidden in the descriptor gate")
        if isinstance(node, ast.Attribute) and isinstance(node.value, ast.Name) \
                and node.value.id == "os" and node.attr in {"__dict__", "__getattribute__"}:
            raise CheckFailure("S01: dynamic os attribute-map access is forbidden")

    os_load_count = 0
    for node in ast.walk(tree):
        if not (isinstance(node, ast.Name) and node.id == "os"
                and isinstance(node.ctx, ast.Load)):
            continue
        os_load_count += 1
        parent = parents.get(node)
        direct_attribute = isinstance(parent, ast.Attribute) and parent.value is node
        allowed_flag_lookup = (
            isinstance(parent, ast.Call) and isinstance(parent.func, ast.Name)
            and parent.func.id == "getattr" and len(parent.args) == 3
            and parent.args[0] is node and isinstance(parent.args[1], ast.Constant)
            and parent.args[1].value in {"O_CLOEXEC", "O_NONBLOCK"}
            and isinstance(parent.args[2], ast.Constant) and parent.args[2].value == 0)
        allowed_support_probe = (
            isinstance(parent, ast.Call) and isinstance(parent.func, ast.Name)
            and parent.func.id == "hasattr" and len(parent.args) == 2
            and parent.args[0] is node and isinstance(parent.args[1], ast.Constant)
            and parent.args[1].value in {"O_CLOEXEC", "O_DIRECTORY", "O_NOFOLLOW"})
        allowed_test_patch = (
            isinstance(parent, ast.Call) and len(parent.args) == 3 and parent.args[0] is node
            and isinstance(parent.func, ast.Attribute) and parent.func.attr == "object"
            and isinstance(parent.func.value, ast.Attribute)
            and parent.func.value.attr == "patch"
            and isinstance(parent.func.value.value, ast.Name)
            and parent.func.value.value.id == "mock"
            and isinstance(parent.args[1], ast.Constant)
            and parent.args[1].value in {"close", "dup", "fstat", "read", "write"}
            and scopes[parent].startswith("check_parser_build_input_self_tests"))
        require(direct_attribute or allowed_flag_lookup or allowed_support_probe
                or allowed_test_patch,
                "S01: every os load must be one registered direct attribute/probe/test-patch use")
    require(os_load_count == 221,
            f"S01: exact os-load inventory changed: expected 221, observed {os_load_count}")

    require(sum(isinstance(node, ast.ClassDef) and node.name == "_OwnedDescriptor"
                for node in ast.walk(tree)) == 1
            and sum(isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef))
                    and node.name == "_close_owned_descriptors" for node in ast.walk(tree)) == 1,
            "S01: owner/helper declaration is missing, duplicated, or rebound")

    def increment(records: dict[tuple[str, ...], int], key: tuple[str, ...]) -> None:
        records[key] = records.get(key, 0) + 1

    def retention_shape(owner_call: ast.Call) -> str:
        parent = parents.get(owner_call)
        if isinstance(parent, (ast.Assign, ast.AnnAssign)) and parent.value is owner_call:
            targets = parent.targets if isinstance(parent, ast.Assign) else [parent.target]
            require(len(targets) == 1 and isinstance(targets[0], ast.Name),
                    "S01: descriptor owner assignment must retain one exact local name")
            return "assigned"
        if isinstance(parent, ast.List):
            container_parent = parents.get(parent)
            if isinstance(container_parent, (ast.Assign, ast.AnnAssign)) \
                    and container_parent.value is parent:
                targets = (container_parent.targets if isinstance(container_parent, ast.Assign)
                           else [container_parent.target])
                require(len(targets) == 1 and isinstance(targets[0], ast.Name),
                        "S01: descriptor owner collection must retain one exact local name")
                return "collection-assigned"
            if isinstance(container_parent, ast.Call) \
                    and isinstance(container_parent.func, ast.Name) \
                    and container_parent.func.id == "_close_owned_descriptors":
                return "one-shot-close-list"
        if isinstance(parent, ast.ListComp) and parent.elt is owner_call:
            container_parent = parents.get(parent)
            if isinstance(container_parent, (ast.Assign, ast.AnnAssign)) \
                    and container_parent.value is parent:
                return "comprehension-assigned"
        raise CheckFailure(
            f"S01: descriptor owner is discarded, taken-and-discarded, or not retained in "
            f"scope {scopes.get(owner_call, '<unknown>')}")

    def owner_argument_shape(argument: ast.AST) -> str:
        if isinstance(argument, ast.Call) and isinstance(argument.func, ast.Attribute) \
                and isinstance(argument.func.value, ast.Name) \
                and argument.func.value.id == "os" \
                and argument.func.attr in {"open", "dup"}:
            return f"direct:os.{argument.func.attr}"
        if isinstance(argument, ast.Call) and isinstance(argument.func, ast.Name):
            return f"call:{argument.func.id}"
        if isinstance(argument, ast.Name):
            return f"name:{argument.id}"
        if isinstance(argument, ast.Attribute) and isinstance(argument.value, ast.Name):
            return f"attribute:{argument.value.id}.{argument.attr}"
        if isinstance(argument, ast.UnaryOp) and isinstance(argument.op, ast.USub) \
                and isinstance(argument.operand, ast.Constant) and argument.operand.value == 1:
            return "sentinel:-1"
        raise CheckFailure(
            f"S01: descriptor owner has an unregistered first-argument shape in "
            f"scope {scopes.get(argument, '<unknown>')}")

    descriptor_references: dict[tuple[str, ...], int] = {}
    for node in ast.walk(tree):
        if not (isinstance(node, ast.Attribute) and isinstance(node.value, ast.Name)
                and node.value.id == "os" and node.attr in {"open", "dup", "close"}):
            continue
        scope = scopes[node]
        parent = parents.get(node)
        if isinstance(parent, ast.Call) and parent.func is node:
            if node.attr == "close":
                require(scope == "_close_owned_descriptors"
                        and len(parent.args) == 1
                        and isinstance(parent.args[0], ast.Name)
                        and parent.args[0].id == "descriptor"
                        and not parent.keywords,
                        "S01: direct close escaped the exact centralized helper shape")
                increment(descriptor_references, (scope, "close", "production-direct-close"))
            else:
                owner_call = parents.get(parent)
                require(isinstance(owner_call, ast.Call)
                        and isinstance(owner_call.func, ast.Name)
                        and owner_call.func.id == "_OwnedDescriptor"
                        and owner_call.args and owner_call.args[0] is parent,
                        "S01: descriptor acquisition is not the direct first argument of an owner")
                increment(descriptor_references,
                          (scope, node.attr, f"acquire:{retention_shape(owner_call)}"))
        elif isinstance(parent, (ast.Assign, ast.AnnAssign)) and parent.value is node:
            targets = parent.targets if isinstance(parent, ast.Assign) else [parent.target]
            require(len(targets) == 1 and isinstance(targets[0], ast.Name),
                    "S01: descriptor function capture has a non-local/multiple target")
            increment(descriptor_references,
                      (scope, node.attr, f"test-capture:{targets[0].id}"))
        elif isinstance(parent, ast.Compare) and scope == "_require_descriptor_walker_support" \
                and node.attr == "open":
            increment(descriptor_references, (scope, "open", "production-support-check"))
        else:
            raise CheckFailure(
                f"S01: unregistered os.{node.attr} attribute reference in scope {scope}")

    expected_references: dict[tuple[str, ...], int] = {
        ("_require_descriptor_walker_support", "open", "production-support-check"): 1,
        ("_close_owned_descriptors", "close", "production-direct-close"): 1,
        ("_open_root_descriptor", "open", "acquire:assigned"): 1,
        ("_open_directory_at", "open", "acquire:assigned"): 1,
        ("_scan_directory_descriptor", "open", "acquire:assigned"): 2,
        ("_open_directory_chain", "dup", "acquire:assigned"): 1,
        ("_open_validated_directory_child", "open", "acquire:assigned"): 1,
        ("open_absolute_directory_fd", "open", "acquire:assigned"): 1,
        ("open_ordinary_file_under", "open", "acquire:assigned"): 1,
        ("validate_fresh_build_root_after", "open", "acquire:assigned"): 1,
        ("write_new_gate_record", "open", "acquire:assigned"): 1,
        ("check_parser_build_input_self_tests.repeated_descriptor_failure", "open",
         "acquire:assigned"): 1,
        ("check_parser_build_input_self_tests.repeated_ownership_case", "open",
         "acquire:collection-assigned"): 2,
        ("check_parser_build_input_self_tests.close_after_real.replacement", "open",
         "acquire:assigned"): 1,
        ("check_parser_build_input_self_tests.nominal_hostile_evidence_action", "open",
         "acquire:collection-assigned"): 2,
        ("check_parser_build_input_self_tests.nominal_hostile_evidence_action", "open",
         "acquire:comprehension-assigned"): 1,
        ("check_parser_build_input_self_tests.nominal_hostile_evidence_action", "open",
         "acquire:assigned"): 2,
        ("check_parser_build_input_self_tests.nominal_hostile_evidence_action", "dup",
         "acquire:assigned"): 1,
        ("check_parser_build_input_self_tests.active_distinct_owner_alias_action", "open",
         "acquire:assigned"): 1,
        ("check_parser_build_input_self_tests.nominal_distinct_owner_alias_action", "open",
         "acquire:assigned"): 2,
        ("check_parser_build_input_self_tests.nominal_distinct_owner_alias_action.alias_close",
         "open", "acquire:assigned"): 1,
        ("check_parser_build_input_self_tests.chain_reuse_action", "dup",
         "test-capture:real_dup"): 1,
    }
    for capture_scope in (
            "chain_reuse_action", "active_root_action", "hostile_active_action",
            "active_directory_at_action", "recursive_file_action",
            "recursive_directory_action", "nominal_scan_root_action", "load_active_action",
            "active_read_action", "active_sha_action", "active_output_action",
            "nominal_pair_action", "nominal_hostile_evidence_action",
            "active_distinct_owner_alias_action", "nominal_distinct_owner_alias_action",
            "fresh_before_action", "fresh_after_action"):
        expected_references[
            (f"check_parser_build_input_self_tests.{capture_scope}", "close",
             "test-capture:real_close")] = 1
    require(descriptor_references == expected_references,
            "S01: exact scoped descriptor reference inventory changed: "
            f"expected={expected_references}, actual={descriptor_references}")

    owner_shapes: dict[tuple[str, ...], int] = {}
    for node in ast.walk(tree):
        if not (isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
                and node.func.id == "_OwnedDescriptor"):
            continue
        require(len(node.args) == 2 and not node.keywords,
                "S01: owner construction must have two exact positional arguments")
        increment(owner_shapes,
                  (scopes[node], retention_shape(node), owner_argument_shape(node.args[0])))

    expected_owner_shapes: dict[tuple[str, ...], int] = {}
    for scope, retention, argument, count in (
            ("_open_root_descriptor", "assigned", "direct:os.open", 1),
            ("_open_directory_at", "assigned", "direct:os.open", 1),
            ("_scan_directory_descriptor", "assigned", "direct:os.open", 2),
            ("scan_regular_tree_no_follow", "assigned", "call:_open_root_descriptor", 1),
            ("_open_directory_chain", "assigned", "direct:os.dup", 1),
            ("_open_directory_chain", "assigned", "call:_open_directory_at", 1),
            ("load_active_s01_files", "assigned", "call:_open_root_descriptor", 1),
            ("load_active_s01_files", "assigned", "call:_open_directory_chain", 1),
            ("_expect_hooked_scan_rejected", "assigned", "call:_open_root_descriptor", 1),
            ("check_scanner_self_tests", "one-shot-close-list", "name:root_descriptor", 1),
            ("_open_validated_directory_child", "assigned", "direct:os.open", 1),
            ("open_absolute_directory_fd", "assigned", "direct:os.open", 1),
            ("open_absolute_directory_fd", "assigned", "name:child", 1),
            ("open_ordinary_file_under", "assigned", "call:open_absolute_directory_fd", 1),
            ("open_ordinary_file_under", "assigned", "sentinel:-1", 1),
            ("open_ordinary_file_under", "assigned", "name:child", 1),
            ("open_ordinary_file_under", "assigned", "direct:os.open", 1),
            ("require_ordinary_file_under", "one-shot-close-list", "name:descriptor", 1),
            ("require_ordinary_file_under", "one-shot-close-list", "name:parent_descriptor", 1),
            ("read_ordinary_file_under", "assigned", "name:descriptor", 1),
            ("read_ordinary_file_under", "assigned", "name:parent_descriptor", 1),
            ("validate_fresh_build_root_before", "assigned",
             "call:open_absolute_directory_fd", 1),
            ("validate_fresh_build_root_after", "assigned",
             "call:open_absolute_directory_fd", 1),
            ("validate_fresh_build_root_after", "assigned", "sentinel:-1", 1),
            ("validate_fresh_build_root_after", "assigned", "direct:os.open", 1),
            ("sha256_ordinary_file", "assigned", "name:descriptor", 1),
            ("sha256_ordinary_file", "assigned", "name:parent_descriptor", 1),
            ("write_new_gate_record", "assigned", "call:open_absolute_directory_fd", 1),
            ("write_new_gate_record", "assigned", "sentinel:-1", 1),
            ("write_new_gate_record", "assigned", "direct:os.open", 1),
            ("check_parser_build_input_self_tests.repeated_descriptor_failure", "assigned",
             "direct:os.open", 1),
            ("check_parser_build_input_self_tests.root_action", "one-shot-close-list",
             "name:descriptor", 1),
            ("check_parser_build_input_self_tests.relative_action", "one-shot-close-list",
             "name:descriptor", 1),
            ("check_parser_build_input_self_tests.relative_action", "one-shot-close-list",
             "name:parent_descriptor", 1),
            ("check_parser_build_input_self_tests.repeated_ownership_case",
             "collection-assigned", "direct:os.open", 2),
            ("check_parser_build_input_self_tests.close_after_real.replacement", "assigned",
             "direct:os.open", 1),
            ("check_parser_build_input_self_tests.chain_reuse_action", "assigned",
             "call:_open_root_descriptor", 1),
            ("check_parser_build_input_self_tests", "assigned", "call:_open_root_descriptor", 1),
            ("check_parser_build_input_self_tests.nominal_hostile_evidence_action",
             "collection-assigned", "direct:os.open", 2),
            ("check_parser_build_input_self_tests.nominal_hostile_evidence_action",
             "comprehension-assigned", "direct:os.open", 1),
            ("check_parser_build_input_self_tests.nominal_hostile_evidence_action", "assigned",
             "direct:os.open", 2),
            ("check_parser_build_input_self_tests.nominal_hostile_evidence_action", "assigned",
             "direct:os.dup", 1),
            ("check_parser_build_input_self_tests.active_distinct_owner_alias_action", "assigned",
             "direct:os.open", 1),
            ("check_parser_build_input_self_tests.active_distinct_owner_alias_action", "assigned",
             "attribute:primary_owner.descriptor", 1),
            ("check_parser_build_input_self_tests.nominal_distinct_owner_alias_action", "assigned",
             "direct:os.open", 2),
            ("check_parser_build_input_self_tests.nominal_distinct_owner_alias_action", "assigned",
             "attribute:primary_owner.descriptor", 1),
            ("check_parser_build_input_self_tests.nominal_distinct_owner_alias_action.alias_close",
             "assigned", "direct:os.open", 1)):
        expected_owner_shapes[(scope, retention, argument)] = count
    require(owner_shapes == expected_owner_shapes,
            "S01: exact retained/transferred/one-shot owner inventory changed: "
            f"expected={expected_owner_shapes}, actual={owner_shapes}")

    owner_constructor_loads = 0
    owner_annotation_loads: dict[str, int] = {}
    for node in ast.walk(tree):
        if not (isinstance(node, ast.Name) and node.id == "_OwnedDescriptor"
                and isinstance(node.ctx, ast.Load)):
            continue
        parent = parents.get(node)
        if isinstance(parent, ast.Call) and parent.func is node:
            owner_constructor_loads += 1
            continue
        require(isinstance(parent, ast.Subscript)
                and isinstance(parent.value, ast.Name) and parent.value.id == "list"
                and parent.slice is node,
                "S01: owner constructor must only be loaded for a registered call/annotation")
        owner_annotation_loads[scopes[node]] = owner_annotation_loads.get(scopes[node], 0) + 1
    expected_owner_annotation_loads = {
        "<module>": 1,
        "check_parser_build_input_self_tests": 1,
        "check_parser_build_input_self_tests.chain_reuse_action": 1,
        "check_parser_build_input_self_tests.active_distinct_owner_alias_action": 1,
        "check_parser_build_input_self_tests.nominal_distinct_owner_alias_action": 1,
    }
    require(owner_constructor_loads == sum(owner_shapes.values()) == 52
            and owner_annotation_loads == expected_owner_annotation_loads,
            "S01: exact owner-constructor load inventory changed")

    take_records: dict[tuple[str, str, str], int] = {}
    for node in ast.walk(tree):
        if not (isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute)
                and node.func.attr == "take"):
            continue
        require(not node.args and not node.keywords and isinstance(node.func.value, ast.Name),
                "S01: every take must be a zero-argument call on one exact owner local")
        parent = parents.get(node)
        if isinstance(parent, ast.Assign) and parent.value is node \
                and len(parent.targets) == 1 and isinstance(parent.targets[0], ast.Name):
            role = f"assign:{parent.targets[0].id}"
        elif isinstance(parent, ast.Return) and parent.value is node:
            role = "return"
        elif isinstance(parent, ast.Tuple) and node in parent.elts \
                and isinstance(parents.get(parent), ast.Return) \
                and parents[parent].value is parent:
            role = "return-tuple"
        else:
            raise CheckFailure(
                f"S01: unregistered take lifecycle role in scope {scopes[node]}")
        increment(take_records, (scopes[node], node.func.value.id, role))
    expected_take_records = {
        ("_close_owned_descriptors", "owner", "assign:descriptor"): 1,
        ("_open_root_descriptor", "owner", "return"): 1,
        ("_open_directory_at", "owner", "return"): 1,
        ("_open_directory_chain", "current", "return"): 1,
        ("_open_validated_directory_child", "owner", "return"): 1,
        ("open_absolute_directory_fd", "owner", "return"): 1,
        ("open_ordinary_file_under", "file_owner", "return-tuple"): 1,
        ("open_ordinary_file_under", "parent_owner", "return-tuple"): 1,
    }
    require(take_records == expected_take_records,
            "S01: exact descriptor take/transfer inventory changed: "
            f"expected={expected_take_records}, actual={take_records}")

    def cleanup_owner_item_shape(item: ast.AST) -> str:
        if isinstance(item, ast.Name):
            return item.id
        if isinstance(item, ast.Call) and isinstance(item.func, ast.Name) \
                and item.func.id == "_OwnedDescriptor" and item.args:
            return f"_OwnedDescriptor({owner_argument_shape(item.args[0])})"
        raise CheckFailure(
            f"S01: cleanup consumer has an unregistered owner expression in scope "
            f"{scopes.get(item, '<unknown>')}")

    def cleanup_owner_shape(argument: ast.AST) -> str:
        if isinstance(argument, ast.Name):
            return argument.id
        if isinstance(argument, ast.List):
            return "[" + ",".join(cleanup_owner_item_shape(item)
                                    for item in argument.elts) + "]"
        raise CheckFailure(
            f"S01: cleanup consumer has an unregistered owner-list shape in scope "
            f"{scopes.get(argument, '<unknown>')}")

    cleanup_records: dict[tuple[str, str, str], int] = {}
    cleanup_helper_loads = 0
    for node in ast.walk(tree):
        if not (isinstance(node, ast.Name) and node.id == "_close_owned_descriptors"
                and isinstance(node.ctx, ast.Load)):
            continue
        cleanup_helper_loads += 1
        call = parents.get(node)
        require(isinstance(call, ast.Call) and call.func is node
                and len(call.args) in {2, 3} and not call.keywords,
                "S01: cleanup helper must only be loaded for an exact direct call")
        if len(call.args) == 2:
            disposition = "nominal"
        else:
            require(isinstance(call.args[2], ast.Name),
                    "S01: active cleanup must receive one exact exception local")
            disposition = f"active:{call.args[2].id}"
        increment(cleanup_records,
                  (scopes[call], cleanup_owner_shape(call.args[0]), disposition))
    expected_cleanup_records = {
        ("_expect_hooked_scan_rejected", "[owner]", "active:original"): 1,
        ("_expect_hooked_scan_rejected", "[owner]", "nominal"): 2,
        ("_open_directory_at", "[owner]", "active:original"): 1,
        ("_open_directory_chain", "[child]", "active:original"): 1,
        ("_open_directory_chain", "[current]", "active:original"): 1,
        ("_open_directory_chain", "[current]", "nominal"): 1,
        ("_open_root_descriptor", "[owner]", "active:original"): 1,
        ("_open_validated_directory_child", "[owner]", "active:original"): 1,
        ("_scan_directory_descriptor", "[child_owner]", "active:original"): 2,
        ("_scan_directory_descriptor", "[child_owner]", "nominal"): 2,
        ("check_parser_build_input_self_tests", "[active_parent_owner]", "nominal"): 1,
        ("check_parser_build_input_self_tests.active_distinct_owner_alias_action",
         "reused_owners", "nominal"): 1,
        ("check_parser_build_input_self_tests.active_distinct_owner_alias_action."
         "propagate_original", "[primary_owner,alias_owner]", "active:observed"): 1,
        ("check_parser_build_input_self_tests.chain_reuse_action", "[repository_owner]",
         "nominal"): 1,
        ("check_parser_build_input_self_tests.chain_reuse_action", "reused_owners",
         "nominal"): 1,
        ("check_parser_build_input_self_tests.nominal_distinct_owner_alias_action",
         "[primary_owner,alias_owner,other_owner]", "nominal"): 1,
        ("check_parser_build_input_self_tests.nominal_distinct_owner_alias_action",
         "reused_owners", "nominal"): 1,
        ("check_parser_build_input_self_tests.nominal_hostile_evidence_action",
         "[base_owner,dup_owner]", "nominal"): 1,
        ("check_parser_build_input_self_tests.nominal_hostile_evidence_action",
         "[same_owner,same_owner]", "nominal"): 1,
        ("check_parser_build_input_self_tests.nominal_hostile_evidence_action", "owners",
         "nominal"): 1,
        ("check_parser_build_input_self_tests.nominal_hostile_evidence_action",
         "position_owners", "nominal"): 1,
        ("check_parser_build_input_self_tests.relative_action",
         "[_OwnedDescriptor(name:descriptor),_OwnedDescriptor(name:parent_descriptor)]",
         "nominal"): 1,
        ("check_parser_build_input_self_tests.repeated_descriptor_failure",
         "[sentinel_owner]", "nominal"): 1,
        ("check_parser_build_input_self_tests.repeated_ownership_case", "sentinel_owners",
         "nominal"): 1,
        ("check_parser_build_input_self_tests.root_action",
         "[_OwnedDescriptor(name:descriptor)]", "nominal"): 1,
        ("check_scanner_self_tests", "[_OwnedDescriptor(name:root_descriptor)]",
         "nominal"): 1,
        ("load_active_s01_files", "[repository_owner]", "active:original"): 1,
        ("load_active_s01_files", "[repository_owner]", "nominal"): 1,
        ("load_active_s01_files", "[root_owner]", "active:original"): 1,
        ("load_active_s01_files", "[root_owner]", "nominal"): 1,
        ("open_absolute_directory_fd", "[child_owner]", "active:original"): 1,
        ("open_absolute_directory_fd", "[owner]", "active:error"): 1,
        ("open_absolute_directory_fd", "[owner]", "nominal"): 1,
        ("open_ordinary_file_under", "[child_owner]", "active:original"): 1,
        ("open_ordinary_file_under", "[file_owner,parent_owner]", "active:error"): 1,
        ("open_ordinary_file_under", "[parent_owner]", "nominal"): 1,
        ("read_ordinary_file_under", "[file_owner,parent_owner]", "active:error"): 1,
        ("read_ordinary_file_under", "[file_owner,parent_owner]", "nominal"): 1,
        ("require_ordinary_file_under",
         "[_OwnedDescriptor(name:descriptor),_OwnedDescriptor(name:parent_descriptor)]",
         "nominal"): 1,
        ("scan_regular_tree_no_follow", "[owner]", "active:original"): 1,
        ("scan_regular_tree_no_follow", "[owner]", "nominal"): 1,
        ("sha256_ordinary_file", "[file_owner,parent_owner]", "active:error"): 1,
        ("sha256_ordinary_file", "[file_owner,parent_owner]", "nominal"): 1,
        ("validate_fresh_build_root_after", "[build_owner,parent_owner]", "active:error"): 1,
        ("validate_fresh_build_root_after", "[build_owner,parent_owner]", "nominal"): 1,
        ("validate_fresh_build_root_before", "[parent_owner]", "active:error"): 1,
        ("validate_fresh_build_root_before", "[parent_owner]", "nominal"): 1,
        ("write_new_gate_record", "[file_owner,parent_owner]", "active:error"): 1,
        ("write_new_gate_record", "[file_owner,parent_owner]", "nominal"): 1,
    }
    require(cleanup_records == expected_cleanup_records and cleanup_helper_loads == 52,
            "S01: exact cleanup-consumer inventory changed: "
            f"expected={expected_cleanup_records}, actual={cleanup_records}, "
            f"loads={cleanup_helper_loads}")

    captured_descriptor_call_records: dict[tuple[str, str, str], int] = {}
    for node in ast.walk(tree):
        if not (isinstance(node, ast.Name) and node.id in {"real_close", "real_dup"}
                and isinstance(node.ctx, ast.Load)):
            continue
        call = parents.get(node)
        require(isinstance(call, ast.Call),
                "S01: captured real_close/real_dup must be consumed by one registered call")
        if call.func is node:
            require(len(call.args) == 1 and not call.keywords
                    and isinstance(call.args[0], ast.Name),
                    "S01: captured real_close/real_dup direct call has the wrong shape")
            role = f"direct:{call.args[0].id}"
        else:
            require(isinstance(call.func, ast.Name) and call.func.id == "close_after_real"
                    and len(call.args) == 2 and call.args[0] is node
                    and isinstance(call.args[1], ast.Name) and call.args[1].id == "selected"
                    and all(keyword.arg in {"cleanup_error", "reuse"}
                            and isinstance(keyword.value, ast.Name) for keyword in call.keywords),
                    "S01: captured real_close may only feed the exact fault-injection wrapper")
            role = "wrapper:" + ",".join(
                f"{keyword.arg}={keyword.value.id}" for keyword in call.keywords)
        increment(captured_descriptor_call_records, (scopes[call], node.id, role))
    expected_captured_descriptor_calls = {
        ("check_parser_build_input_self_tests.close_after_real.replacement",
         "real_close", "direct:descriptor"): 2,
        ("check_parser_build_input_self_tests.chain_reuse_action.selected_dup",
         "real_dup", "direct:descriptor"): 1,
        ("check_parser_build_input_self_tests.nominal_distinct_owner_alias_action."
         "alias_close", "real_close", "direct:descriptor"): 1,
        ("check_parser_build_input_self_tests.nominal_hostile_evidence_action."
         "positional_close", "real_close", "direct:descriptor"): 1,
    }
    for wrapper_scope in (
            "active_directory_at_action", "active_output_action", "active_read_action",
            "active_root_action", "active_sha_action", "fresh_after_action",
            "fresh_before_action", "load_active_action", "recursive_directory_action",
            "recursive_file_action"):
        expected_captured_descriptor_calls[
             (f"check_parser_build_input_self_tests.{wrapper_scope}",
             "real_close", "wrapper:")] = 1
    for wrapper_scope in ("nominal_pair_action.failing_close",
                          "nominal_scan_root_action.failing_close"):
        expected_captured_descriptor_calls[
             (f"check_parser_build_input_self_tests.{wrapper_scope}",
             "real_close", "wrapper:")] = 1
    expected_captured_descriptor_calls.update({
        ("check_parser_build_input_self_tests.hostile_active_action", "real_close",
         "wrapper:cleanup_error=cleanup_error"): 1,
        ("check_parser_build_input_self_tests.hostile_active_action", "real_close",
         "wrapper:cleanup_error=metaclass_cleanup"): 1,
        ("check_parser_build_input_self_tests.nominal_hostile_evidence_action", "real_close",
         "wrapper:cleanup_error=cleanup_error"): 1,
        ("check_parser_build_input_self_tests.chain_reuse_action", "real_close",
         "wrapper:reuse=reused_owners"): 1,
        ("check_parser_build_input_self_tests.active_distinct_owner_alias_action", "real_close",
         "wrapper:reuse=reused_owners,cleanup_error=cleanup_error"): 1,
    })
    require(captured_descriptor_call_records == expected_captured_descriptor_calls,
            "S01: exact test-only real_close/real_dup call inventory changed: "
            f"expected={expected_captured_descriptor_calls}, "
            f"actual={captured_descriptor_call_records}")

    production_acquisitions = sum(
        count for (scope, _operation, role), count in descriptor_references.items()
        if role.startswith("acquire:")
        and not scope.startswith("check_parser_build_input_self_tests"))
    test_acquisitions = sum(
        count for (scope, _operation, role), count in descriptor_references.items()
        if role.startswith("acquire:")
        and scope.startswith("check_parser_build_input_self_tests"))
    test_captures = sum(count for (_scope, _operation, role), count
                        in descriptor_references.items() if role.startswith("test-capture:"))
    require(production_acquisitions == 10 and test_acquisitions == 14
            and test_captures == 18,
            "S01: descriptor policy production/test accounting mismatch")


def _open_root_descriptor(root: Path, before_open: Callable[[], None] | None = None) -> int:
    _require_descriptor_walker_support()
    try:
        expected = os.stat(root, follow_symlinks=False)
    except OSError as error:
        raise CheckFailure(f"S01: cannot lstat active root {root}: {error}") from error
    require(stat.S_ISDIR(expected.st_mode) and not stat.S_ISLNK(expected.st_mode),
            f"S01: active root must be a real directory, not a link/special entry: {root}")
    if before_open is not None:
        before_open()
    try:
        owner = _OwnedDescriptor(os.open(root, _directory_flags()), f"active root {root}")
    except OSError as error:
        raise CheckFailure(f"S01: cannot safely open active root {root}: {error}") from error
    try:
        opened = os.fstat(owner.descriptor)
        require(stat.S_ISDIR(opened.st_mode)
                and _object_identity(opened) == _object_identity(expected),
                f"S01: active root identity changed between metadata and open: {root}")
        return owner.take()
    except BaseException as original:
        _close_owned_descriptors([owner], f"active root {root}", original)
        raise


def _open_directory_at(parent_descriptor: int, name: str, display: Path) -> int:
    try:
        expected = os.stat(name, dir_fd=parent_descriptor, follow_symlinks=False)
    except OSError as error:
        raise CheckFailure(f"S01: cannot lstat active directory {display}: {error}") from error
    require(stat.S_ISDIR(expected.st_mode) and not stat.S_ISLNK(expected.st_mode),
            f"S01: active directory must be real, not a link/special entry: {display}")
    try:
        owner = _OwnedDescriptor(
            os.open(name, _directory_flags(), dir_fd=parent_descriptor),
            f"active directory {display}")
    except OSError as error:
        raise CheckFailure(f"S01: cannot safely open active directory {display}: {error}") from error
    try:
        opened = os.fstat(owner.descriptor)
        require(stat.S_ISDIR(opened.st_mode)
                and _object_identity(opened) == _object_identity(expected),
                f"S01: active directory identity changed between metadata and open: {display}")
        return owner.take()
    except BaseException as original:
        _close_owned_descriptors([owner], f"active directory {display}", original)
        raise


def _read_regular_descriptor(descriptor: int, display: Path) -> bytes:
    chunks: list[bytes] = []
    try:
        while True:
            chunk = os.read(descriptor, 1024 * 1024)
            if not chunk:
                return b"".join(chunks)
            chunks.append(chunk)
    except OSError as error:
        raise CheckFailure(f"S01: cannot read active file {display}: {error}") from error


def _scan_directory_descriptor(
        descriptor: int,
        display_root: Path,
        relative_parts: tuple[str, ...] = (),
        before_open: _BeforeOpenHook | None = None) -> dict[str, bytes]:
    files: dict[str, bytes] = {}
    try:
        with os.scandir(descriptor) as iterator:
            names = sorted(entry.name for entry in iterator)
    except OSError as error:
        raise CheckFailure(f"S01: cannot enumerate active directory {display_root}: {error}") from error

    for name in names:
        child_parts = relative_parts + (name,)
        relative = Path(*child_parts)
        display = display_root / relative
        try:
            expected = os.stat(name, dir_fd=descriptor, follow_symlinks=False)
        except OSError as error:
            raise CheckFailure(f"S01: cannot lstat active entry {display}: {error}") from error
        mode = expected.st_mode
        if stat.S_ISLNK(mode):
            raise CheckFailure(f"S01: symlink is prohibited in active scope: {display}")
        if stat.S_ISDIR(mode):
            require(name != "__pycache__",
                    f"S01: generated Python debris directory in active scope: {display}")
            if before_open is not None:
                before_open(relative, "directory")
            try:
                child_owner = _OwnedDescriptor(
                    os.open(name, _directory_flags(), dir_fd=descriptor),
                    f"active recursive directory {display}")
            except OSError as error:
                raise CheckFailure(f"S01: cannot safely open active directory {display}: {error}") from error
            try:
                opened = os.fstat(child_owner.descriptor)
                require(stat.S_ISDIR(opened.st_mode)
                        and _object_identity(opened) == _object_identity(expected),
                        f"S01: active directory identity changed before recursion: {display}")
                nested = _scan_directory_descriptor(
                    child_owner.descriptor, display_root, child_parts, before_open)
                require(not set(files).intersection(nested),
                        f"S01: duplicate active path while scanning {display}")
                files.update(nested)
            except BaseException as original:
                _close_owned_descriptors(
                    [child_owner], f"active recursive directory {display}", original)
                raise
            _close_owned_descriptors(
                [child_owner], f"active recursive directory {display}")
            continue
        if not stat.S_ISREG(mode):
            raise CheckFailure(f"S01: unsupported filesystem entry in active scope: {display}")
        if before_open is not None:
            before_open(relative, "file")
        try:
            child_owner = _OwnedDescriptor(
                os.open(name, _file_flags(), dir_fd=descriptor),
                f"active file {display}")
        except OSError as error:
            raise CheckFailure(f"S01: cannot safely open active file {display}: {error}") from error
        try:
            opened = os.fstat(child_owner.descriptor)
            require(stat.S_ISREG(opened.st_mode)
                    and _object_identity(opened) == _object_identity(expected),
                    f"S01: active file identity changed before read: {display}")
            files[relative.as_posix()] = _read_regular_descriptor(child_owner.descriptor, display)
        except BaseException as original:
            _close_owned_descriptors([child_owner], f"active file {display}", original)
            raise
        _close_owned_descriptors([child_owner], f"active file {display}")
    return files


def scan_regular_tree_no_follow(root: Path) -> dict[str, bytes]:
    """Read a Linux tree through identity-checked, descriptor-relative operations only."""

    owner = _OwnedDescriptor(_open_root_descriptor(root), f"active tree root {root}")
    try:
        result = _scan_directory_descriptor(owner.descriptor, root)
    except BaseException as original:
        _close_owned_descriptors([owner], f"active tree root {root}", original)
        raise
    _close_owned_descriptors([owner], f"active tree root {root}")
    return result


def _open_directory_chain(repository_descriptor: int, parts: tuple[str, ...]) -> int:
    current = _OwnedDescriptor(os.dup(repository_descriptor), "active directory chain root")
    display = ROOT
    try:
        for part in parts:
            display = display / part
            child = _OwnedDescriptor(
                _open_directory_at(current.descriptor, part, display),
                f"active directory chain child {display}")
            try:
                _close_owned_descriptors([current], f"active directory chain transfer {display}")
            except BaseException as original:
                _close_owned_descriptors(
                    [child], f"active directory chain child {display}", original)
                raise
            current = child
        return current.take()
    except BaseException as original:
        _close_owned_descriptors([current], "active directory chain", original)
        raise


def load_active_s01_files() -> dict[str, bytes]:
    files: dict[str, bytes] = {}
    repository_owner = _OwnedDescriptor(
        _open_root_descriptor(ROOT), "active-file repository root")
    roots = (
        (("docs", "slhdsa"), "docs/slhdsa"),
        (("scripts", "slhdsa"), "scripts/slhdsa"),
        (("HashSigTest", "SLHDSA"), "HashSigTest/SLHDSA"),
    )
    try:
        for parts, prefix in roots:
            root_owner = _OwnedDescriptor(
                _open_directory_chain(repository_owner.descriptor, parts),
                f"active-file scoped root {prefix}")
            try:
                scanned = _scan_directory_descriptor(
                    root_owner.descriptor, ROOT / Path(*parts))
            except BaseException as original:
                _close_owned_descriptors(
                    [root_owner], f"active-file scoped root {prefix}", original)
                raise
            _close_owned_descriptors([root_owner], f"active-file scoped root {prefix}")
            for suffix, data in scanned.items():
                relative = f"{prefix}/{suffix}"
                require(relative not in files, f"S01 active-file roots overlap at {relative}")
                files[relative] = data
    except BaseException as original:
        _close_owned_descriptors(
            [repository_owner], "active-file repository root", original)
        raise
    _close_owned_descriptors([repository_owner], "active-file repository root")
    return files


def validate_active_s01_hygiene(files: dict[str, bytes]) -> None:
    whitespace = []
    for relative, data in files.items():
        try:
            source = data.decode("utf-8")
        except UnicodeError as error:
            whitespace.append(f"{relative}: unreadable UTF-8: {error}")
            continue
        if not data.endswith(b"\n"):
            whitespace.append(f"{relative}: missing final LF")
        elif data.endswith(b"\n\n"):
            whitespace.append(f"{relative}: terminal blank line")
        for line_no, line in enumerate(source.splitlines(), 1):
            if "\t" in line:
                whitespace.append(f"{relative}:{line_no}: internal tab")
            if line.endswith((" ", "\t")):
                whitespace.append(f"{relative}:{line_no}: trailing whitespace")
    require(not whitespace, "S01 comprehensive whitespace check: " + "; ".join(whitespace))


def _expect_scanner_rejected(label: str, root: Path) -> None:
    try:
        scan_regular_tree_no_follow(root)
    except CheckFailure:
        return
    raise CheckFailure(f"S01 filesystem scanner self-test accepted {label}")


def _expect_hooked_scan_rejected(label: str, root: Path, hook: _BeforeOpenHook) -> None:
    owner = _OwnedDescriptor(_open_root_descriptor(root), f"scanner self-test root {root}")
    try:
        _scan_directory_descriptor(owner.descriptor, root, before_open=hook)
    except CheckFailure:
        _close_owned_descriptors([owner], f"scanner self-test root {root}")
        return
    except BaseException as original:
        _close_owned_descriptors([owner], f"scanner self-test root {root}", original)
        raise
    _close_owned_descriptors([owner], f"scanner self-test root {root}")
    raise CheckFailure(f"S01 filesystem replacement self-test accepted {label}")


def check_scanner_self_tests() -> None:
    with tempfile.TemporaryDirectory(prefix="slhdsa-safe-scan-", dir="/tmp") as temporary:
        base = Path(temporary)

        file_link_case = base / "file-link"
        file_link_case.mkdir()
        target = file_link_case / "target.txt"
        target.write_text("ordinary\n", encoding="utf-8")
        os.symlink(target.name, file_link_case / "linked.txt")
        _expect_scanner_rejected("file symlink", file_link_case)

        directory_link_case = base / "directory-link"
        directory_link_case.mkdir()
        hidden = directory_link_case / "hidden"
        hidden.mkdir()
        (hidden / "deprecated.txt").write_text(f"{DEPRECATED_PROFILE_ID}\n", encoding="utf-8")
        os.symlink(hidden.name, directory_link_case / "linked-directory")
        _expect_scanner_rejected("directory symlink containing deprecated content",
                                 directory_link_case)

        broken_link_case = base / "broken-link"
        broken_link_case.mkdir()
        os.symlink("absent-target", broken_link_case / "broken")
        _expect_scanner_rejected("broken symlink", broken_link_case)

        root_link_target = base / "root-link-target"
        root_link_target.mkdir()
        root_link = base / "root-link"
        os.symlink(root_link_target.name, root_link)
        _expect_scanner_rejected("symlink active root", root_link)

        fifo_case = base / "fifo"
        fifo_case.mkdir()
        os.mkfifo(fifo_case / "unsupported.fifo")
        _expect_scanner_rejected("FIFO without opening it", fifo_case)

        directory_replacement_case = base / "directory-replacement"
        directory_replacement_case.mkdir()
        victim_directory = directory_replacement_case / "zz-victim"
        victim_directory.mkdir()
        (victim_directory / "inside.txt").write_text("inside\n", encoding="utf-8")
        external_directory = base / "external-directory"
        external_directory.mkdir()
        (external_directory / "outside.txt").write_text("must-not-be-read\n", encoding="utf-8")
        directory_hook_called = False

        def replace_directory(relative: Path, kind: str) -> None:
            nonlocal directory_hook_called
            if relative == Path("zz-victim") and kind == "directory":
                directory_hook_called = True
                victim_directory.rename(directory_replacement_case / "saved-victim")
                os.symlink(external_directory, victim_directory, target_is_directory=True)

        _expect_hooked_scan_rejected(
            "checked directory replaced by r4 external symlink",
            directory_replacement_case, replace_directory)
        require(directory_hook_called, "S01: directory replacement hook was not exercised")

        file_replacement_case = base / "file-replacement"
        file_replacement_case.mkdir()
        victim_file = file_replacement_case / "victim.txt"
        victim_file.write_text("original\n", encoding="utf-8")
        file_hook_called = False

        def replace_file(relative: Path, kind: str) -> None:
            nonlocal file_hook_called
            if relative == Path("victim.txt") and kind == "file":
                file_hook_called = True
                victim_file.rename(file_replacement_case / "saved-victim.txt")
                victim_file.write_text("replacement-must-not-be-read\n", encoding="utf-8")

        _expect_hooked_scan_rejected(
            "checked file replaced by a different regular inode",
            file_replacement_case, replace_file)
        require(file_hook_called, "S01: file replacement hook was not exercised")

        root_replacement = base / "root-replacement"
        root_replacement.mkdir()
        replacement_root = base / "replacement-root"
        replacement_root.mkdir()
        root_hook_called = False

        def replace_root() -> None:
            nonlocal root_hook_called
            root_hook_called = True
            root_replacement.rename(base / "saved-root")
            os.symlink(replacement_root, root_replacement, target_is_directory=True)

        try:
            root_descriptor = _open_root_descriptor(root_replacement, replace_root)
        except CheckFailure:
            pass
        else:
            _close_owned_descriptors(
                [_OwnedDescriptor(root_descriptor, "root replacement self-test")],
                "root replacement self-test")
            raise CheckFailure("S01 filesystem replacement self-test accepted changed root")
        require(root_hook_called, "S01: root replacement hook was not exercised")


def check_hygiene() -> None:
    validate_raw_close_inventory()
    checker_source = Path(__file__).read_text(encoding="utf-8")
    descriptor_policy_mutations = {
        "literal raw close":
            "\ndef s01_forbidden_raw_close(fd):\n    os.close(fd)\n",
        "literal unowned open":
            "\ndef s01_forbidden_unowned_open(path):\n    return os.open(path, os.O_RDONLY)\n",
        "literal unowned dup":
            "\ndef s01_forbidden_unowned_dup(fd):\n    return os.dup(fd)\n",
        "assigned close alias":
            "\ndef s01_forbidden_close_alias(fd):\n    closer = os.close\n    closer(fd)\n",
        "getattr close alias":
            "\ndef s01_forbidden_getattr_close(fd):\n    getattr(os, 'close')(fd)\n",
        "from-os close alias":
            "\nfrom os import close as s01_forbidden_close\n",
        "assigned open alias":
            "\ndef s01_forbidden_open_alias(path):\n    opener = os.open\n"
            "    return opener(path, os.O_RDONLY)\n",
        "getattr open alias":
            "\ndef s01_forbidden_getattr_open(path):\n"
            "    return getattr(os, 'open')(path, os.O_RDONLY)\n",
        "from-os open alias":
            "\nfrom os import open as s01_forbidden_open\n",
        "assigned dup alias":
            "\ndef s01_forbidden_dup_alias(fd):\n    duplicator = os.dup\n"
            "    return duplicator(fd)\n",
        "getattr dup alias":
            "\ndef s01_forbidden_getattr_dup(fd):\n    return getattr(os, 'dup')(fd)\n",
        "from-os dup alias":
            "\nfrom os import dup as s01_forbidden_dup\n",
        "discarded owner":
            "\ndef s01_forbidden_discarded_owner(path):\n"
            "    _OwnedDescriptor(os.open(path, os.O_RDONLY), 'discarded')\n",
        "take-and-discard owner":
            "\ndef s01_forbidden_discarded_take(path):\n"
            "    _OwnedDescriptor(os.open(path, os.O_RDONLY), 'discarded').take()\n",
        "owner constructor rebinding":
            "\ns01_saved_owner_constructor = _OwnedDescriptor\n",
        "cleanup helper rebinding":
            "\ns01_saved_cleanup_helper = _close_owned_descriptors\n",
        "os module alias":
            "\ns01_os_alias = os\ndef s01_forbidden_module_alias(fd):\n"
            "    s01_os_alias.close(fd)\n",
        "dynamic os import":
            "\ndef s01_forbidden_dynamic_import(fd):\n"
            "    __import__('os').close(fd)\n",
        "dynamic os attribute map":
            "\ndef s01_forbidden_attribute_map(fd):\n    vars(os)['close'](fd)\n",
        "distinct alias owners":
            "\ndef s01_forbidden_alias_owners(fd):\n"
            "    first = _OwnedDescriptor(fd, 'first')\n"
            "    second = _OwnedDescriptor(first.descriptor, 'second')\n"
            "    _close_owned_descriptors([first, second], 'alias')\n",
    }
    descriptor_policy_sources = {
        label: checker_source + suffix for label, suffix in descriptor_policy_mutations.items()
    }

    def replace_once(label: str, old: str, new: str) -> None:
        require(checker_source.count(old) == 1,
                f"S01 descriptor AST self-test anchor is not unique: {label}")
        descriptor_policy_sources[label] = checker_source.replace(old, new, 1)

    replace_once(
        "extra take in an allowed scope",
        "        opened = os.fstat(owner.descriptor)\n"
        "        require(stat.S_ISDIR(opened.st_mode)\n"
        "                and _object_identity(opened) == _object_identity(expected),\n"
        "                f\"S01: active root identity changed between metadata and open: {root}\")\n",
        "        opened = os.fstat(owner.descriptor)\n        owner.take()\n"
        "        require(stat.S_ISDIR(opened.st_mode)\n"
        "                and _object_identity(opened) == _object_identity(expected),\n"
        "                f\"S01: active root identity changed between metadata and open: {root}\")\n")
    replace_once(
        "removed cleanup consumer in an allowed scope",
        "        _close_owned_descriptors([owner], f\"active root {root}\", original)\n"
        "        raise\n",
        "        pass\n        raise\n")
    replace_once(
        "extra cleanup consumer in an allowed scope",
        "        _close_owned_descriptors([owner], f\"active root {root}\", original)\n"
        "        raise\n",
        "        _close_owned_descriptors([owner], f\"active root {root}\", original)\n"
        "        _close_owned_descriptors([owner], f\"active root {root}\", original)\n"
        "        raise\n")
    replace_once(
        "extra test-only real-close call in an allowed scope",
        "            real_close(descriptor)\n            if reuse is not None:\n",
        "            real_close(descriptor)\n            real_close(descriptor)\n"
        "            if reuse is not None:\n")
    descriptor_policy_sources.update({
        "function rebinding owner constructor":
            checker_source + "\ndef _OwnedDescriptor():\n    pass\n",
        "class rebinding cleanup helper":
            checker_source + "\nclass _close_owned_descriptors:\n    pass\n",
        "tuple-contained os alias":
            checker_source + "\ns01_tuple_os_alias = (os,)[0]\n",
        "aliased os import":
            checker_source + "\nimport os as s01_imported_os_alias\n",
        "importlib module dynamic os lookup":
            checker_source + "\nimport importlib\n"
            "s01_imported_os = importlib.import_module('os')\n",
        "from-importlib dynamic os lookup":
            checker_source + "\nfrom importlib import import_module\n"
            "s01_imported_os = import_module('os')\n",
    })
    require(len(descriptor_policy_sources) == 30,
            "S01 descriptor semantic AST mutation accounting changed")
    for label, mutated_source in descriptor_policy_sources.items():
        try:
            validate_raw_close_inventory(mutated_source)
        except CheckFailure:
            pass
        else:
            raise CheckFailure(
                f"S01 descriptor semantic AST self-test accepted {label}")
    print("INFO: S01 descriptor semantic AST mutation self-tests: PASS "
          "(30 rejected; production 10 acquisitions/1 close; "
          "test-only 14 acquisitions/18 captures)")
    active_files = load_active_s01_files()
    debris = [relative for relative in active_files
              if Path(relative).name == "__pycache__"
              or Path(relative).suffix in {".pyc", ".pyo"}]
    require(not debris, f"generated Python debris: {debris}")
    validate_active_s01_hygiene(active_files)
    check_scanner_self_tests()


def check_csvs() -> None:
    for filename, (header, vocabs) in CSV_SCHEMAS.items():
        path = DOCS / "matrices" / filename
        with path.open(newline="", encoding="utf-8") as handle:
            reader = csv.DictReader(handle)
            require(reader.fieldnames == header, f"{filename}: header mismatch: {reader.fieldnames!r}")
            rows = list(reader)
        require(rows, f"{filename}: must have seed rows")
        seen: set[str] = set()
        for line_no, row in enumerate(rows, 2):
            require(None not in row, f"{filename}:{line_no}: extra CSV fields")
            require(all(value is not None and value.strip() for value in row.values()),
                    f"{filename}:{line_no}: empty field")
            row_id = row["id"]
            require(row_id not in seen, f"{filename}:{line_no}: duplicate id {row_id}")
            seen.add(row_id)
            for column, allowed in vocabs.items():
                require(row[column] in allowed,
                        f"{filename}:{line_no}: invalid {column}={row[column]!r}")


@dataclass(frozen=True)
class Token:
    text: str
    line: int


def lex_lean(source: str, *, line_offset: int = 0) -> tuple[list[Token], list[str]]:
    """Small conservative Lean lexer for defense-in-depth source policy tokens.

    This is not a Lean parser and is not the authoritative admission/runtime gate. It deliberately
    rejects malformed comments/strings and known dangerous source spellings; PolicyAudit.lean checks
    the elaborated environment. The fixture corpus locks the syntax classes used by this layer.
    """

    tokens: list[Token] = []
    errors: list[str] = []
    i = 0
    line = 1 + line_offset
    size = len(source)

    def skip_quoted(start: int, quote: str) -> int:
        nonlocal line
        j = start + 1
        while j < size:
            if source[j] == "\n":
                line += 1
            if source[j] == "\\":
                j += 2
                continue
            if source[j] == quote:
                return j + 1
            j += 1
        errors.append(f"line {line}: unterminated quoted literal")
        return size

    while i < size:
        char = source[i]
        if char == "\n":
            line += 1
            i += 1
            continue
        if char.isspace():
            i += 1
            continue
        if source.startswith("--", i):
            end = source.find("\n", i + 2)
            i = size if end < 0 else end
            continue
        if source.startswith("/-", i):
            depth = 1
            i += 2
            while i < size and depth:
                if source.startswith("/-", i):
                    depth += 1
                    i += 2
                elif source.startswith("-/", i):
                    depth -= 1
                    i += 2
                else:
                    line += source[i] == "\n"
                    i += 1
            if depth:
                errors.append(f"line {line}: unterminated block comment")
            continue
        raw = re.match(r"r(#+)?\"", source[i:])
        if raw:
            tokens.append(Token("__string_literal__", line))
            hashes = raw.group(1) or ""
            terminator = '"' + hashes
            body_start = i + len(raw.group(0))
            end = source.find(terminator, body_start)
            if end < 0:
                errors.append(f"line {line}: unterminated raw string")
                line += source[body_start:].count("\n")
                i = size
            else:
                line += source[body_start:end + len(terminator)].count("\n")
                i = end + len(terminator)
            continue
        interpolator = re.match(r"[A-Za-z_][A-Za-z0-9_]*!\"", source[i:])
        if interpolator:
            # Interpolators can embed arbitrary terms, and imported/custom prefixes are extensible.
            # HashSig currently needs none, so reject the whole escape surface conservatively rather
            # than claim a partial parser for every interpolation grammar.
            tokens.append(Token("__interpolated_string__", line))
            quote_index = i + len(interpolator.group(0)) - 1
            i = skip_quoted(quote_index, '"')
            continue
        if char == '"':
            string_line = line
            end = skip_quoted(i, '"')
            body = source[i + 1:max(i + 1, end - 1)]
            token = "__interpolated_string__" if "{" in body else "__string_literal__"
            tokens.append(Token(token, string_line))
            i = end
            continue
        if char == "'" and i + 1 < size:
            i = skip_quoted(i, "'")
            continue
        if char == "«":
            end = source.find("»", i + 1)
            if end < 0:
                errors.append(f"line {line}: unterminated quoted identifier")
                i = size
            else:
                tokens.append(Token(source[i + 1:end], line))
                line += source[i:end + 1].count("\n")
                i = end + 1
            continue
        match = re.match(r"[A-Za-z_][A-Za-z0-9_'.]*", source[i:])
        if match:
            text = match.group(0)
            tokens.append(Token(text, line))
            i += len(text)
            continue
        tokens.append(Token(char, line))
        i += 1
    return tokens, errors


def policy_findings(source: str) -> list[tuple[str, int]]:
    tokens, errors = lex_lean(source)
    findings: list[tuple[str, int]] = [("lexical-error", 0) for _ in errors]
    for token in tokens:
        leaf = token.text.rsplit(".", 1)[-1]
        if leaf in {"sorry", "admit", "sorryAx", "axiom", "unsafe", "extern"}:
            findings.append((leaf, token.line))
        elif leaf == "mkSorry":
            findings.append(("mkSorry", token.line))
        elif token.text == "__interpolated_string__":
            findings.append(("interpolated-string", token.line))
        elif leaf in {"partial", "partial_fixpoint"}:
            findings.append(("partial", token.line))
        elif leaf in {"implemented_by", "implemented_by_rfl"}:
            findings.append(("runtime-override", token.line))
        elif leaf in {"meta", "elab", "elab_rules", "macro", "macro_rules", "run_tac",
                       "syntax", "syntax_rules"}:
            findings.append(("metaprogramming", token.line))
        elif leaf == "native_decide":
            findings.append(("generated-axiom", token.line))
        elif leaf in {"addAndCompile", "addDecl", "axiomDecl", "builtin_initialize",
                       "initialize", "run_cmd", "register_option", "register_builtin_option",
                       "register_label_attr"} or (token.text == leaf and leaf.startswith("run_")):
            findings.append(("environment-mutation", token.line))
    for index, token in enumerate(tokens[:-1]):
        if token.text == "@" and tokens[index + 1].text == "[":
            cursor = index + 2
        elif token.text == "attribute" and tokens[index + 1].text == "[":
            cursor = index + 2
        else:
            continue
        depth = 1
        while cursor < len(tokens) and depth:
            current = tokens[cursor]
            if current.text == "[":
                depth += 1
            elif current.text == "]":
                depth -= 1
            elif depth == 1:
                leaf = current.text.rsplit(".", 1)[-1]
                if leaf in {"builtin_init", "computed_field", "init"}:
                    findings.append(("runtime-attribute", current.line))
            cursor += 1
    for index, token in enumerate(tokens):
        if token.text != "!" or index == 0 or index + 1 >= len(tokens):
            continue
        previous = tokens[index - 1].text
        following = tokens[index + 1].text
        if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_'.]*", previous) and following == "__string_literal__":
            findings.append(("interpolated-string", token.line))
    for index, token in enumerate(tokens):
        if token.text != "set_option":
            continue
        window = tokens[index + 1:index + 12]
        linter_at = next((j for j, item in enumerate(window)
                          if item.text.startswith("linter.") or item.text.startswith("weak.linter.")), None)
        if linter_at is not None and any(item.text == "false" for item in window[linter_at + 1:]):
            findings.append(("linter-false", token.line))
    return findings


def check_policy_fixtures() -> None:
    data = read_json(ROOT / "scripts/slhdsa/policy-fixtures.json")
    require(data.get("schema_version") == 1 and isinstance(data.get("cases"), list),
            "policy fixtures: invalid schema")
    ids: set[str] = set()
    for case in data["cases"]:
        require(set(case) == {"id", "source", "expected"}, "policy fixtures: invalid case fields")
        require(case["id"] not in ids, f"policy fixtures: duplicate id {case['id']}")
        ids.add(case["id"])
        actual = sorted({label for label, _line in policy_findings(case["source"])})
        require(actual == sorted(case["expected"]),
                f"policy fixture {case['id']}: expected {case['expected']}, got {actual}")
    victim = ROOT / "scripts/slhdsa/fixtures/HashSig/PolicyIRFixture.lean"
    victim_findings = policy_findings(victim.read_text(encoding="utf-8"))
    require(not victim_findings,
            f"compiled-IR victim source must evade the defense-in-depth policy: {victim_findings}")
    macro = (ROOT / "scripts/slhdsa/fixtures/SLHDSAPolicyIRMacro.lean").read_text(
        encoding="utf-8")
    require("syntax \"slhdsa_policy_hidden_entry \" ident : command" in macro and
            "`(initialize $name : Nat ← do" in macro and
            "SLHDSA_POLICY_SENTINEL" in macro,
            "compiled-IR macro fixture no longer generates the sentinel initializer")


def check_lean_policy() -> None:
    found_admissions: set[tuple[str, int, str]] = set()
    violations: list[str] = []
    for path in sorted((ROOT / "HashSig").rglob("*.lean")):
        rel = path.relative_to(ROOT).as_posix()
        source = path.read_text(encoding="utf-8")
        for label, line in policy_findings(source):
            if label in {"sorry", "admit", "sorryAx", "mkSorry"}:
                found_admissions.add((rel, line, label))
            elif label == "lexical-error":
                violations.append(f"{rel}: lexical error")
            else:
                violations.append(f"{rel}:{line}: prohibited {label}")
    unexpected = found_admissions - SORRY_ALLOWLIST
    require(not unexpected, f"unexpected admissions: {sorted(unexpected)!r}")
    require(not violations, "prohibited HashSig declarations/options: " + "; ".join(violations))
    removed = SORRY_ALLOWLIST - found_admissions
    if removed:
        print(f"INFO: sorry allowlist shrank monotonically: removed {sorted(removed)!r}")
    else:
        print(f"INFO: exact sorry allowlist matched: {sorted(found_admissions)!r}")


@dataclass(frozen=True)
class LeanSourceDeclaration:
    fqname: str
    short_name: str
    line: int
    namespace: str
    visibility: str
    keyword: str


def parse_s01_source_declarations(relative: str, source: str) -> dict[str, LeanSourceDeclaration]:
    """Extract declarations from the intentionally narrow, frozen S01 source grammar.

    This is not a general Lean parser. Before making source-logical claims it rejects command
    quotations and every metaprogramming command family that could manufacture declarations.
    """

    tokens, errors = lex_lean(source)
    require(not errors, f"S01: malformed Lean lexical state in {relative}: {errors}")
    unsupported_commands = {
        "macro", "macro_rules", "syntax", "syntax_rules", "elab", "elab_rules",
        "command_elab", "term_elab", "run_cmd", "run_tac",
    }
    for index, token in enumerate(tokens):
        leaf = token.text.rsplit(".", 1)[-1]
        require(leaf not in unsupported_commands,
                "S01: unsupported metaprogramming command in frozen source grammar at "
                f"{relative}:{token.line}: {leaf}")
        require(not (token.text == "`" and index + 1 < len(tokens)
                     and tokens[index + 1].text == "("),
                "S01: unsupported Lean syntax quotation in frozen source grammar at "
                f"{relative}:{token.line}")
    by_line: dict[int, list[str]] = {}
    for token in tokens:
        by_line.setdefault(token.line, []).append(token.text)

    scopes: list[tuple[str, str]] = []
    declarations: dict[str, LeanSourceDeclaration] = {}

    def current_namespace() -> str:
        return ".".join(name for kind, name in scopes if kind == "namespace")

    for line in sorted(by_line):
        words = by_line[line]
        if words[0] == "namespace":
            require(len(words) == 2 and re.fullmatch(
                r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*", words[1]),
                f"S01: unsupported namespace command in {relative}:{line}")
            scopes.append(("namespace", words[1]))
            continue
        if words[0] == "mutual":
            require(len(words) == 1,
                    f"S01: unsupported mutual command in {relative}:{line}")
            scopes.append(("mutual", ""))
            continue
        if words[0] == "end":
            require(len(words) in {1, 2} and scopes,
                    f"S01: scope underflow or malformed end in {relative}:{line}")
            kind, opened = scopes[-1]
            if len(words) == 1:
                require(kind == "mutual",
                        f"S01: unnamed end does not close the exact mutual scope in {relative}:{line}")
            else:
                require(kind == "namespace"
                        and words[1] in {opened, current_namespace()},
                        f"S01: named end disagrees with active namespace in {relative}:{line}")
            scopes.pop()
            continue

        visibility = "public"
        cursor = 0
        if words[0] == "private":
            visibility = "private"
            cursor = 1
        if cursor < len(words) and words[cursor] == "partial":
            cursor += 1
        if cursor + 1 >= len(words) or words[cursor] not in {"def", "structure"}:
            continue
        keyword = words[cursor]
        short_name = words[cursor + 1]
        require(re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*", short_name) is not None,
                f"S01: unsupported declaration name in {relative}:{line}")
        namespace = current_namespace()
        fqname = f"{namespace}.{short_name}" if namespace else short_name
        require(fqname not in declarations,
                f"S01: duplicate active declaration name in {relative}: {fqname}")
        declarations[fqname] = LeanSourceDeclaration(
            fqname, short_name, line, namespace, visibility, keyword)

    require(not scopes, f"S01: unclosed namespace/mutual state in {relative}: {scopes}")
    return declarations


def load_s01_lean_sources() -> dict[str, str]:
    return {relative: (ROOT / relative).read_text(encoding="utf-8")
            for relative in S01_ACVP_LEAN_PINS}


def validate_s01_acvp_lean_pins() -> None:
    for relative, (expected_size, expected_hash) in S01_ACVP_LEAN_PINS.items():
        data = (ROOT / relative).read_bytes()
        require(len(data) == expected_size and hashlib.sha256(data).hexdigest() == expected_hash,
                f"S01: frozen ACVP Lean source pin mismatch: {relative}")


def source_declarations(
        sources: dict[str, str]) -> dict[str, list[tuple[str, LeanSourceDeclaration]]]:
    result: dict[str, list[tuple[str, LeanSourceDeclaration]]] = {}
    for relative, source in sources.items():
        for fqname, declaration in parse_s01_source_declarations(relative, source).items():
            result.setdefault(fqname, []).append((relative, declaration))
    return result


def parse_lake_executable_roots(source: str) -> dict[str, str]:
    """Parse simple literal Lake stanzas as a non-authoritative defense-in-depth check."""

    tokens, errors = lex_lean(source)
    require(not errors, f"S01: malformed lakefile lexical state: {errors}")
    by_line: dict[int, list[str]] = {}
    for token in tokens:
        by_line.setdefault(token.line, []).append(token.text)

    roots: dict[str, str] = {}
    current: str | None = None
    for line in sorted(by_line):
        words = by_line[line]
        if words[0] == "lean_exe":
            require(len(words) == 3 and words[2] == "where"
                    and re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*", words[1]) is not None,
                    f"S01: unsupported active lean_exe stanza at lakefile.lean:{line}")
            require(words[1] not in roots and
                    (current is None or current in roots),
                    f"S01: duplicate or incomplete active lean_exe mapping: {words[1]}")
            current = words[1]
            continue
        if words[0] == "root":
            require(current is not None and len(words) == 5
                    and words[1:4] == [":", "=", "`"]
                    and re.fullmatch(
                        r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*", words[4])
                    is not None,
                    f"S01: ambiguous or malformed active executable root at lakefile.lean:{line}")
            roots[current] = words[4]
            continue
    require(current is None or current in roots, "S01: active lean_exe has no root mapping")
    return roots


def validate_lake_parser_mapping(source: str) -> None:
    roots = parse_lake_executable_roots(source)
    require(roots.get("slhdsa_acvp_parser") == "HashSigTest.SLHDSA.ACVP.ParserTests",
            "S01: active parser executable has the wrong or missing root module")


def validate_lake_source_selector_surface(source: str) -> None:
    """Reject selectors that can redirect the package or the S01 parser target.

    Unrelated targets may select their own source directories; their elaborated records do not
    affect the parser target and are outside this S01 gate.
    """

    tokens, errors = lex_lean(source)
    require(not errors, f"S01: malformed lakefile selector lexical state: {errors}")
    unsupported = {"macro", "macro_rules", "syntax", "syntax_rules", "elab", "elab_rules",
                   "command_elab", "term_elab", "run_cmd", "run_tac"}
    for index, token in enumerate(tokens):
        leaf = token.text.rsplit(".", 1)[-1]
        require(leaf not in unsupported,
                f"S01: unsupported metaprogramming in pinned Lake selector surface: {leaf}")
        require(not (token.text == "`" and index + 1 < len(tokens)
                     and tokens[index + 1].text == "("),
                "S01: unsupported command quotation in pinned Lake selector surface")

    by_line: dict[int, list[str]] = {}
    for token in tokens:
        by_line.setdefault(token.line, []).append(token.text)
    package_open = False
    parser_open = False
    for line in sorted(by_line):
        words = by_line[line]
        if words[0] == "package":
            package_open = words[-1] == "where"
            parser_open = False
            continue
        if words[0] in {"require", "lean_lib", "lean_exe"}:
            package_open = False
        if words[0] == "lean_exe":
            parser_open = len(words) >= 2 and words[1] == "slhdsa_acvp_parser"
            continue
        if package_open or parser_open:
            require(not any(word in {"srcDir", "moreLeanArgs", "weakLeanArgs"}
                            for word in words),
                    "S01: active Lake source/path argument selector is forbidden for the package "
                    "or parser target; the exact defaults are required")


def validate_translated_lake_data(data: Any) -> None:
    """Validate the parser target in Lake's elaborated TOML representation."""

    require(isinstance(data, dict), "S01: translated Lake configuration is not a TOML table")
    # Lake 5 inherits package srcDir and Lean arguments into executable compilation. Nonempty
    # moreLeanArgs/weakLeanArgs could pass an additional -R and alter source selection. The live
    # package must therefore use all three absent-field defaults. The exact parser-entry key set
    # below rejects target srcDir, both argument arrays, and every other target override.
    package_source_selectors = {"srcDir", "moreLeanArgs", "weakLeanArgs"} & set(data)
    require(not package_source_selectors,
            "S01: translated Lake package has a source/path selector: " +
            ", ".join(sorted(package_source_selectors)))
    executables = data.get("lean_exe")
    require(isinstance(executables, list),
            "S01: translated Lake configuration has no lean_exe array")
    names: list[str] = []
    parser_entries: list[dict[str, Any]] = []
    for index, entry in enumerate(executables):
        require(isinstance(entry, dict),
                f"S01: translated Lake lean_exe[{index}] is not a table")
        name = entry.get("name")
        root = entry.get("root")
        require(isinstance(name, str) and name
                and isinstance(root, str) and root,
                f"S01: translated Lake lean_exe[{index}] has a missing or non-string name/root")
        names.append(name)
        if name == "slhdsa_acvp_parser":
            parser_entries.append(entry)
    require(len(names) == len(set(names)),
            "S01: translated Lake configuration has duplicate executable names")
    require(len(parser_entries) == 1,
            "S01: translated Lake configuration must have exactly one slhdsa_acvp_parser")
    require(set(parser_entries[0]) == {"name", "root"},
            "S01: translated parser executable has an unsupported/effective source selector")
    require(parser_entries[0]["root"] == "HashSigTest.SLHDSA.ACVP.ParserTests",
            "S01: elaborated parser executable has the wrong root module")


def translate_lake_configuration(project_root: Path = ROOT) -> dict[str, Any]:
    """Re-elaborate Lake configuration into a disposable TOML file and parse it fail closed."""

    try:
        with tempfile.TemporaryDirectory(prefix="slhdsa-lake-config-", dir="/tmp") as temporary:
            output = Path(temporary) / "translated.toml"
            require(not output.exists(), "S01: disposable Lake translation target already exists")
            completed = subprocess.run(
                ["lake", "-R", "translate-config", "toml", str(output)],
                cwd=project_root, text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                timeout=120, check=False,
                env={**os.environ, "PYTHONDONTWRITEBYTECODE": "1"})
            require(completed.returncode == 0,
                    "S01: Lake configuration translation failed:\n" +
                    (completed.stdout + completed.stderr)[-4000:])
            status = output.lstat()
            require(stat.S_ISREG(status.st_mode) and not stat.S_ISLNK(status.st_mode),
                    "S01: Lake translation did not produce an ordinary TOML file")
            with output.open("rb") as handle:
                data = tomllib.load(handle)
    except (OSError, subprocess.TimeoutExpired, tomllib.TOMLDecodeError) as error:
        raise CheckFailure(f"S01: cannot translate/parse Lake configuration: {error}") from error
    require(isinstance(data, dict), "S01: translated Lake configuration is not a table")
    return data


def validate_translated_lake_parser_mapping(project_root: Path = ROOT) -> None:
    validate_translated_lake_data(translate_lake_configuration(project_root))


PARSER_MODULE = "HashSigTest.SLHDSA.ACVP.ParserTests"
PARSER_SOURCE_RELATIVE = Path("HashSigTest/SLHDSA/ACVP/ParserTests.lean")
PARSER_SOURCE_SHA256 = "1a56fd4fef9880a464583749d27e14840b2f48afc81fe007db473bb167585cd5"
ACVP_TRACE_MODULES = {
    "HashSigTest.SLHDSA.ACVP.ParserTests": (
        Path("HashSigTest/SLHDSA/ACVP/ParserTests.lean"),
        "1a56fd4fef9880a464583749d27e14840b2f48afc81fe007db473bb167585cd5"),
    "HashSigTest.SLHDSA.ACVP.Schema": (
        Path("HashSigTest/SLHDSA/ACVP/Schema.lean"),
        "3ccab70a3ff8e2e6f39cc09e4b2296fad035267b4def0e6c8bb002062f5733a0"),
    "HashSigTest.SLHDSA.ACVP.StrictJson": (
        Path("HashSigTest/SLHDSA/ACVP/StrictJson.lean"),
        "20f9aff3f5339e54d7fc5e148fadb0e37d8f4b4bd816938f0a81b4cf7b087089"),
}
LAKEFILE_BOUNDARY_SHA256 = "834dddbe1d2acbb2f0cd57cdb17838b6f5099ded45e18973c9d7517509c964d8"
FRESH_BUILD_CHILD = "fresh-root-build"
PARSER_EXPECTED_STDOUT = (
    b"SLH-DSA ACVP parser positive suite: PASS (16 cases)\n"
    b"SLH-DSA ACVP parser negative suite: PASS (52 cases)\n"
    b"SLH-DSA ACVP parser runtime gate: PASS (68 cases)\n"
)
PARSER_MODULE_ARTIFACT_KEYS = (
    "module", "module_hash", "module_trace",
    "generated_c", "generated_c_hash",
    "export_object", "export_object_hash", "export_object_trace",
)
PARSER_TRACE_LINK_LAYOUTS = {
    "Lean 4.32.2, commit f3b06c705e6c85f5314019d5d3baab0fec5b580c":
        ("linkObjs",),
    "Lean 4.33.1, commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6":
        (f"{PARSER_MODULE}:linkInfo", "Module.moreLinkObjs"),
}
PARSER_PERMITTED_LINK_LIBRARIES = (
    "libleanhashing.a",
    "libleanmlkem.a",
    "libleanmldsa.a",
    "libleanfalcon.a",
)


def write_srcdir_regression_project(
        project_root: Path,
        *,
        package_level: bool,
        selector: str = "WrongSrc") -> None:
    """Create the exact disposable r8 source-directory-selection counterexample."""

    package_fields = [
        "  buildDir := (get_config? buildDir).map System.FilePath.mk |>.getD Lake.defaultBuildDir"
    ]
    if package_level:
        package_fields.append(f'  srcDir := "{selector}"')
    package_clause = " where\n" + "\n".join(package_fields)
    target_clause = "" if package_level else f"\n  srcDir := \"{selector}\""
    lakefile = (
        "import Lake\n"
        "open Lake DSL\n\n"
        f"package SrcDirProbe{package_clause}\n\n"
        "lean_exe slhdsa_acvp_parser where\n"
        f"  root := `{PARSER_MODULE}{target_clause}\n"
    )
    canonical = project_root / PARSER_SOURCE_RELATIVE
    selected = project_root / selector / PARSER_SOURCE_RELATIVE
    canonical.parent.mkdir(parents=True)
    selected.parent.mkdir(parents=True)
    canonical.write_text(
        'def main : IO Unit := IO.println "CANONICAL REPOSITORY SOURCE EXECUTED"\n',
        encoding="utf-8")
    selected.write_text(
        "def main : IO Unit := do\n"
        "  IO.println \"SLH-DSA ACVP parser positive suite: PASS (16 cases)\"\n"
        "  IO.println \"SLH-DSA ACVP parser negative suite: PASS (52 cases)\"\n"
        "  IO.println \"SLH-DSA ACVP parser runtime gate: PASS (68 cases)\"\n",
        encoding="utf-8")
    (project_root / "lakefile.lean").write_text(lakefile, encoding="utf-8")
    (project_root / "lean-toolchain").write_bytes((ROOT / "lean-toolchain").read_bytes())


def write_unredirected_regression_lakefile(project_root: Path) -> None:
    (project_root / "lakefile.lean").write_text(
        "import Lake\nopen Lake DSL\n\npackage SrcDirProbe where\n"
        "  buildDir := (get_config? buildDir).map System.FilePath.mk "
        "|>.getD Lake.defaultBuildDir\n\n"
        "lean_lib HashSigTest\n\n"
        "lean_exe slhdsa_acvp_parser where\n"
        f"  root := `{PARSER_MODULE}\n",
        encoding="utf-8")


def write_three_module_regression_project(project_root: Path) -> None:
    """Copy the exact frozen three-module parser chain into a disposable Lake package."""

    for _module, (relative, _source_hash) in ACVP_TRACE_MODULES.items():
        destination = project_root / relative
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(ROOT / relative, destination)
    shutil.copytree(
        ROOT / "HashSigTest/SLHDSA/ACVP/fixtures",
        project_root / "HashSigTest/SLHDSA/ACVP/fixtures")
    (project_root / "lakefile.lean").write_text(
        "import Lake\nopen Lake DSL\n\npackage ThreeModuleProbe where\n"
        "  buildDir := (get_config? buildDir).map System.FilePath.mk "
        "|>.getD Lake.defaultBuildDir\n\n"
        "lean_lib HashSigTest\n\n"
        "lean_exe slhdsa_acvp_parser where\n"
        f"  root := `{PARSER_MODULE}\n",
        encoding="utf-8")
    (project_root / "lean-toolchain").write_bytes((ROOT / "lean-toolchain").read_bytes())


def parse_strict_json_bytes(data: bytes, label: str) -> Any:
    def reject_duplicates(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
        keys = [key for key, _value in pairs]
        require(len(keys) == len(set(keys)), f"S01: duplicate JSON key in {label}")
        return dict(pairs)

    try:
        return json.loads(data.decode("utf-8"), object_pairs_hook=reject_duplicates)
    except (UnicodeError, json.JSONDecodeError) as error:
        raise CheckFailure(f"S01: malformed JSON in {label}: {error}") from error


def validate_fresh_build_lake_source(source: str) -> None:
    """Pin the exact root-package buildDir override and absence of the retired UInt64 helper."""

    require(hashlib.sha256(source.encode("utf-8")).hexdigest() == LAKEFILE_BOUNDARY_SHA256,
            "S01: lakefile bytes changed; update the fresh-build/config pin deliberately")
    marker = (
        "buildDir := (get_config? buildDir).map System.FilePath.mk "
        "|>.getD Lake.defaultBuildDir"
    )
    require(source.count(marker) == 1,
            "S01: root package must have one exact CLI-controlled buildDir field")
    require("slhdsa_lake_file_hash" not in source
            and "Lake.computeBinFileHash" not in source
            and "Lake.fetchFileHash" not in source,
            "S01: retired Lake UInt64 hash helper remains in lakefile")


def parse_sha256_helper_result(
        completed: subprocess.CompletedProcess[bytes],
        label: str,
        *,
        echo_stderr: bool = False) -> str:
    if echo_stderr and completed.stderr:
        sys.stderr.buffer.write(completed.stderr)
        sys.stderr.buffer.flush()
    require(completed.returncode == 0,
            f"S01: SHA-256 helper failed for {label}:\n" +
            completed.stderr.decode("utf-8", errors="replace")[-4000:])
    require(re.fullmatch(rb"[0-9a-f]{64}\n", completed.stdout) is not None,
            f"S01: SHA-256 helper output for {label} is not exactly one canonical record")
    return completed.stdout[:-1].decode("ascii")


def validate_sha256_binding(expected_hash: str, before_hash: str, after_hash: str) -> None:
    for label, token in (("expected", expected_hash), ("before", before_hash),
                         ("after", after_hash)):
        require(re.fullmatch(r"[0-9a-f]{64}", token) is not None,
                f"S01: parser executable {label} SHA-256 is not canonical")
    require(expected_hash == before_hash == after_hash,
            "S01: parser executable SHA-256 changed before/after exact-path execution")


def validate_incremental_lake_metadata(trace_hash: Any, sidecar_hash: str) -> None:
    """Check fresh Lake records for internal consistency, not cryptographic byte identity."""

    require(isinstance(trace_hash, str)
            and re.fullmatch(r"[0-9a-f]{16}", trace_hash) is not None
            and re.fullmatch(r"[0-9a-f]{16}", sidecar_hash) is not None,
            "S01: fresh parser Lake incremental token is not canonical")
    require(trace_hash == sidecar_hash,
            "S01: fresh parser trace and sidecar incremental tokens disagree")


def canonical_cli_absolute_path(raw: str, label: str) -> Path:
    """Reject every non-canonical raw absolute spelling before constructing a Path."""

    require(raw.startswith("/") and raw != "/" and not raw.endswith("/")
            and "//" not in raw,
            f"S01: {label} must use one exact non-root absolute path spelling")
    components = raw.split("/")[1:]
    require(components and all(component not in ("", ".", "..") for component in components),
            f"S01: {label} contains an empty/dot/parent path component")
    path = Path(raw)
    require(path.is_absolute() and str(path) == raw,
            f"S01: {label} path spelling is not canonical")
    return path


def proper_relative_parts(path: Path, root: Path, label: str) -> tuple[str, ...]:
    """Return one nonempty alias-free relative component tuple, or fail before filesystem access."""

    require(path.is_absolute() and root.is_absolute() and root != Path("/") and path != root,
            f"S01: {label} path/root must be distinct non-root absolute paths")
    require(all(component not in ("", ".", "..") for component in path.parts[1:])
            and all(component not in ("", ".", "..") for component in root.parts[1:]),
            f"S01: {label} path/root contains a dot/parent component")
    try:
        relative = path.relative_to(root)
    except ValueError as error:
        raise CheckFailure(f"S01: {label} escapes its supplied root: {path}") from error
    parts = relative.parts
    require(parts and all(component not in ("", ".", "..") for component in parts)
            and path == root.joinpath(*parts),
            f"S01: {label} is not a proper canonical root-relative path")
    return parts


def _open_validated_directory_child(
        parent_descriptor: int,
        component: str,
        before: os.stat_result,
        flags: int,
        label: str,
        pre_fstat_hook: Callable[[str, int], None] | None = None) -> int:
    """Open and validate a child while owning it immediately on every exceptional path."""

    owner = _OwnedDescriptor(
        os.open(component, flags, dir_fd=parent_descriptor),
        f"{label} child {component}")
    try:
        if pre_fstat_hook is not None:
            pre_fstat_hook(component, owner.descriptor)
        after = os.fstat(owner.descriptor)
        require(stat.S_ISDIR(after.st_mode)
                and (before.st_dev, before.st_ino) == (after.st_dev, after.st_ino),
                f"S01: {label} directory identity changed while opening: {component}")
        return owner.take()
    except BaseException as original:
        _close_owned_descriptors([owner], f"{label} child {component}", original)
        raise


def open_absolute_directory_fd(
        path: Path,
        label: str,
        *,
        _pre_child_fstat: Callable[[str, int], None] | None = None) -> int:
    """Open an absolute directory from `/` using identity-stable no-follow components."""

    require(path.is_absolute() and path != Path("/")
            and all(component not in ("", ".", "..") for component in path.parts[1:]),
            f"S01: {label} directory path is not canonical absolute")
    require(hasattr(os, "O_DIRECTORY") and hasattr(os, "O_NOFOLLOW")
            and hasattr(os, "O_CLOEXEC"),
            "S01: Linux no-follow directory/file open flags are unavailable")
    flags = os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW | os.O_CLOEXEC
    try:
        owner = _OwnedDescriptor(os.open("/", flags), f"{label} root anchor")
    except OSError as error:
        raise CheckFailure(f"S01: cannot anchor {label} traversal at /: {error}") from error
    try:
        for component in path.parts[1:]:
            before = os.stat(component, dir_fd=owner.descriptor, follow_symlinks=False)
            require(stat.S_ISDIR(before.st_mode) and not stat.S_ISLNK(before.st_mode),
                    f"S01: {label} component is not an ordinary directory: {component}")
            child = _open_validated_directory_child(
                owner.descriptor, component, before, flags, label, _pre_child_fstat)
            child_owner = _OwnedDescriptor(child, f"{label} child {component}")
            try:
                _close_owned_descriptors([owner], f"{label} directory transfer {component}")
            except BaseException as original:
                _close_owned_descriptors(
                    [child_owner], f"{label} child {component}", original)
                raise
            owner = child_owner
        return owner.take()
    except BaseException as error:
        _close_owned_descriptors([owner], f"{label} traversal", error)
        if isinstance(error, CheckFailure):
            raise
        if isinstance(error, OSError):
            raise CheckFailure(f"S01: cannot traverse {label} no-follow: {error}") from error
        raise


def open_ordinary_file_under(
        path: Path,
        root: Path,
        label: str,
        *,
        _pre_relative_child_fstat: Callable[[str, int], None] | None = None,
        ) -> tuple[int, int, str, os.stat_result]:
    """Open one proper root-relative ordinary file while retaining its parent descriptor."""

    parts = proper_relative_parts(path, root, label)
    parent_owner = _OwnedDescriptor(
        open_absolute_directory_fd(root, f"{label} root"), f"{label} retained parent")
    directory_flags = os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW | os.O_CLOEXEC
    file_owner = _OwnedDescriptor(-1, f"{label} file")
    try:
        for component in parts[:-1]:
            before = os.stat(component, dir_fd=parent_owner.descriptor, follow_symlinks=False)
            require(stat.S_ISDIR(before.st_mode) and not stat.S_ISLNK(before.st_mode),
                    f"S01: {label} parent component is not an ordinary directory: {component}")
            child = _open_validated_directory_child(
                parent_owner.descriptor, component, before, directory_flags,
                f"{label} parent", _pre_relative_child_fstat)
            child_owner = _OwnedDescriptor(child, f"{label} parent child {component}")
            try:
                _close_owned_descriptors(
                    [parent_owner], f"{label} parent transfer {component}")
            except BaseException as original:
                _close_owned_descriptors(
                    [child_owner], f"{label} parent child {component}", original)
                raise
            parent_owner = child_owner
        final_name = parts[-1]
        before = os.stat(final_name, dir_fd=parent_owner.descriptor, follow_symlinks=False)
        require(stat.S_ISREG(before.st_mode) and not stat.S_ISLNK(before.st_mode),
                f"S01: {label} is not an ordinary non-symlink file: {path}")
        file_owner = _OwnedDescriptor(os.open(
            final_name, os.O_RDONLY | os.O_NOFOLLOW | os.O_CLOEXEC,
            dir_fd=parent_owner.descriptor), f"{label} file")
        opened = os.fstat(file_owner.descriptor)
        require(stat.S_ISREG(opened.st_mode)
                and (before.st_dev, before.st_ino) == (opened.st_dev, opened.st_ino),
                f"S01: {label} identity/type changed between metadata and open")
        return file_owner.take(), parent_owner.take(), final_name, opened
    except BaseException as error:
        _close_owned_descriptors(
            [file_owner, parent_owner], f"{label} open", error)
        if isinstance(error, CheckFailure):
            raise
        if isinstance(error, OSError):
            raise CheckFailure(f"S01: cannot open {label} descriptor-relative: {error}") from error
        raise


def require_ordinary_file_under(path: Path, root: Path, label: str) -> None:
    """Require an identity-stable ordinary file using descriptor-relative no-follow traversal."""

    descriptor, parent_descriptor, _name, _status = \
        open_ordinary_file_under(path, root, label)
    _close_owned_descriptors(
        [_OwnedDescriptor(descriptor, f"{label} file"),
         _OwnedDescriptor(parent_descriptor, f"{label} retained parent")],
        f"{label} requirement")


def read_ordinary_file_under(path: Path, root: Path, label: str) -> bytes:
    """Read an ordinary file and reject an identity/size/mtime transition during the read."""

    descriptor, parent_descriptor, final_name, before = \
        open_ordinary_file_under(path, root, label)
    file_owner = _OwnedDescriptor(descriptor, f"{label} file")
    parent_owner = _OwnedDescriptor(parent_descriptor, f"{label} retained parent")
    try:
        chunks: list[bytes] = []
        total = 0
        while True:
            block = os.read(file_owner.descriptor, 1024 * 1024)
            if not block:
                break
            chunks.append(block)
            total += len(block)
        after = os.fstat(file_owner.descriptor)
        path_after = os.stat(
            final_name, dir_fd=parent_owner.descriptor, follow_symlinks=False)
        stable_before = (before.st_dev, before.st_ino, before.st_size, before.st_mtime_ns)
        stable_after = (after.st_dev, after.st_ino, after.st_size, after.st_mtime_ns)
        stable_path = (
            path_after.st_dev, path_after.st_ino, path_after.st_size, path_after.st_mtime_ns)
        require(stable_before == stable_after == stable_path and total == after.st_size,
                f"S01: {label} changed identity/size/mtime while being read")
        result = b"".join(chunks)
    except BaseException as error:
        _close_owned_descriptors([file_owner, parent_owner], f"{label} read", error)
        if isinstance(error, OSError):
            raise CheckFailure(f"S01: cannot read {label}: {error}") from error
        raise
    _close_owned_descriptors([file_owner, parent_owner], f"{label} read")
    return result


def validate_fresh_build_root_before(build_root: Path, private_parent: Path) -> None:
    """Require one initially absent child below an owned mode-700 ordinary directory."""

    require(build_root.is_absolute() and private_parent.is_absolute()
            and all(component not in ("", ".", "..") for component in build_root.parts[1:])
            and all(component not in ("", ".", "..") for component in private_parent.parts[1:])
            and build_root == private_parent / FRESH_BUILD_CHILD,
            "S01: fresh build root must be the exact designated child of its private parent")
    try:
        parent_owner = _OwnedDescriptor(
            open_absolute_directory_fd(private_parent, "fresh-build private parent"),
            "fresh-build before parent")
        try:
            parent_status = os.fstat(parent_owner.descriptor)
            require(stat.S_IMODE(parent_status.st_mode) == 0o700
                    and parent_status.st_uid == os.geteuid(),
                    "S01: fresh-build parent must be an owned mode-700 ordinary directory")
            try:
                os.stat(FRESH_BUILD_CHILD, dir_fd=parent_owner.descriptor, follow_symlinks=False)
            except FileNotFoundError:
                pass
            else:
                raise CheckFailure("S01: fresh build root must be initially absent")
        except BaseException as error:
            _close_owned_descriptors([parent_owner], "fresh-build before parent", error)
            raise
        _close_owned_descriptors([parent_owner], "fresh-build before parent")
    except BaseException as error:
        if isinstance(error, CheckFailure):
            raise
        if isinstance(error, OSError):
            raise CheckFailure(f"S01: cannot inspect proposed fresh build root: {error}") from error
        raise


def validate_fresh_build_root_after(build_root: Path, private_parent: Path) -> None:
    require(build_root == private_parent / FRESH_BUILD_CHILD,
            "S01: generated build root escaped its designated private parent")
    try:
        parent_owner = _OwnedDescriptor(
            open_absolute_directory_fd(private_parent, "fresh-build private parent"),
            "fresh-build after parent")
        build_owner = _OwnedDescriptor(-1, "fresh-build generated child")
        try:
            before = os.stat(
                FRESH_BUILD_CHILD, dir_fd=parent_owner.descriptor, follow_symlinks=False)
            require(stat.S_ISDIR(before.st_mode) and not stat.S_ISLNK(before.st_mode),
                    "S01: generated fresh build root is not an ordinary directory")
            build_owner = _OwnedDescriptor(os.open(
                FRESH_BUILD_CHILD,
                os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW | os.O_CLOEXEC,
                dir_fd=parent_owner.descriptor), "fresh-build generated child")
            after = os.fstat(build_owner.descriptor)
            require((before.st_dev, before.st_ino) == (after.st_dev, after.st_ino),
                    "S01: generated fresh build root identity changed while opening")
        except BaseException as error:
            _close_owned_descriptors(
                [build_owner, parent_owner], "fresh-build after validation", error)
            raise
        _close_owned_descriptors(
            [build_owner, parent_owner], "fresh-build after validation")
    except BaseException as error:
        if isinstance(error, CheckFailure):
            raise
        if isinstance(error, OSError):
            raise CheckFailure(f"S01: Lake did not create the fresh build root: {error}") from error
        raise


def sha256_ordinary_file(path: Path, ordinary_root: Path) -> str:
    """Hash one stable ordinary file through a no-follow fd using SHA-256."""

    descriptor, parent_descriptor, final_name, fd_before = \
        open_ordinary_file_under(path, ordinary_root, "SHA-256 input")
    file_owner = _OwnedDescriptor(descriptor, "SHA-256 input file")
    parent_owner = _OwnedDescriptor(parent_descriptor, "SHA-256 retained parent")
    try:
        digest = hashlib.sha256()
        total = 0
        while True:
            block = os.read(file_owner.descriptor, 1024 * 1024)
            if not block:
                break
            digest.update(block)
            total += len(block)
        fd_after = os.fstat(file_owner.descriptor)
        path_after = os.stat(
            final_name, dir_fd=parent_owner.descriptor, follow_symlinks=False)
        stable_before = (
            fd_before.st_dev, fd_before.st_ino, fd_before.st_size, fd_before.st_mtime_ns)
        stable_after = (
            fd_after.st_dev, fd_after.st_ino, fd_after.st_size, fd_after.st_mtime_ns)
        stable_path = (
            path_after.st_dev, path_after.st_ino, path_after.st_size, path_after.st_mtime_ns)
        require(stable_before == stable_after == stable_path and total == fd_after.st_size,
                "S01: SHA-256 input changed identity/size/mtime while being read")
        result = digest.hexdigest()
    except BaseException as error:
        _close_owned_descriptors([file_owner, parent_owner], "SHA-256 input", error)
        if isinstance(error, OSError):
            raise CheckFailure(f"S01: cannot read SHA-256 input: {error}") from error
        raise
    _close_owned_descriptors([file_owner, parent_owner], "SHA-256 input")
    return result


def parser_module_artifact_manifest(build_root: Path, module: str) -> dict[str, str]:
    """Return the exact current consumed/claimed fresh artifact paths for one parser module."""

    stem = module.replace(".", "/")
    manifest = {
        "module": str(build_root / f"lib/lean/{stem}.olean"),
        "module_hash": str(build_root / f"lib/lean/{stem}.olean.hash"),
        "module_trace": str(build_root / f"lib/lean/{stem}.trace"),
        "generated_c": str(build_root / f"ir/{stem}.c"),
        "generated_c_hash": str(build_root / f"ir/{stem}.c.hash"),
        "export_object": str(build_root / f"ir/{stem}.c.o.export"),
        "export_object_hash": str(build_root / f"ir/{stem}.c.o.export.hash"),
        "export_object_trace": str(build_root / f"ir/{stem}.c.o.export.trace"),
    }
    require(tuple(manifest) == PARSER_MODULE_ARTIFACT_KEYS
            and len(set(manifest.values())) == len(PARSER_MODULE_ARTIFACT_KEYS),
            f"S01: internal artifact manifest is malformed for {module}")
    return manifest


def validate_current_parser_artifact_paths(
        build_root: Path,
        module_specs: dict[str, tuple[Path, str]] = ACVP_TRACE_MODULES,
        supplied: dict[str, dict[str, str]] | None = None,
        ) -> dict[str, dict[str, str]]:
    """Require the exact per-module manifest and every current path as an ordinary fresh file."""

    expected = {
        module: parser_module_artifact_manifest(build_root, module)
        for module in module_specs
    }
    manifests = expected if supplied is None else supplied
    require(set(manifests) == set(expected),
            "S01: current parser artifact module manifest set is incomplete or excessive")
    for module, expected_manifest in expected.items():
        short_name = module.rsplit(".", 1)[-1]
        manifest = manifests[module]
        require(tuple(manifest) == PARSER_MODULE_ARTIFACT_KEYS
                and manifest == expected_manifest,
                f"S01: {short_name} current artifact manifest path/key set is not exact")
        for kind, raw_path in manifest.items():
            require_ordinary_file_under(
                Path(raw_path), build_root, f"{short_name} {kind.replace('_', ' ')}")
    return expected


def incremental_token(output: Any, suffix: str, label: str) -> str:
    require(isinstance(output, str)
            and re.fullmatch(rf"[0-9a-f]{{16}}{re.escape(suffix)}", output) is not None,
            f"S01: {label} trace output token is malformed")
    return output[:-len(suffix)]


def read_incremental_sidecar(path: Path, build_root: Path, label: str) -> str:
    data = read_ordinary_file_under(path, build_root, label)
    require(re.fullmatch(rb"[0-9a-f]{16}", data) is not None,
            f"S01: {label} is not exactly one canonical 16-hex token")
    return data.decode("ascii")


def validate_current_parser_artifact_metadata(
        build_root: Path,
        module_traces: dict[str, Any],
        object_traces: dict[str, Any],
        module_specs: dict[str, tuple[Path, str]] = ACVP_TRACE_MODULES,
        manifests: dict[str, dict[str, str]] | None = None) -> None:
    """Bind each current module/C/export-object sidecar to its fresh structured trace token."""

    exact = validate_current_parser_artifact_paths(build_root, module_specs, manifests)
    require(set(module_traces) == set(module_specs)
            and set(object_traces) == set(module_specs),
            "S01: artifact metadata trace set is incomplete or excessive")
    for module in module_specs:
        short_name = module.rsplit(".", 1)[-1]
        manifest = exact[module]
        outputs = module_traces[module].get("outputs")
        require(isinstance(outputs, dict)
                and isinstance(outputs.get("o"), list) and len(outputs["o"]) >= 1,
                f"S01: {short_name} module output set is malformed")
        module_token = incremental_token(
            outputs["o"][0], ".olean", f"{short_name} module")
        generated_c_token = incremental_token(
            outputs.get("c"), ".c", f"{short_name} generated C")
        object_token = incremental_token(
            object_traces[module].get("outputs"), ".o", f"{short_name} export object")
        require(read_incremental_sidecar(
                    Path(manifest["module_hash"]), build_root,
                    f"{short_name} module hash sidecar") == module_token,
                f"S01: {short_name} module sidecar disagrees with trace o[0]")
        require(read_incremental_sidecar(
                    Path(manifest["generated_c_hash"]), build_root,
                    f"{short_name} generated-C hash sidecar") == generated_c_token,
                f"S01: {short_name} generated-C sidecar disagrees with trace c")
        require(read_incremental_sidecar(
                    Path(manifest["export_object_hash"]), build_root,
                    f"{short_name} export-object hash sidecar") == object_token,
                f"S01: {short_name} export-object sidecar disagrees with object trace/link token")


def require_trace_shape(trace: Any, label: str) -> list[list[Any]]:
    require(isinstance(trace, dict) and set(trace) == {
        "synthetic", "schemaVersion", "outputs", "log", "inputs", "depHash"
    }, f"S01: {label} has an unexpected trace schema")
    require(trace["synthetic"] is False,
            f"S01: {label} must be a current non-synthetic trace")
    require(trace["schemaVersion"] == "2025-09-10"
            and isinstance(trace["log"], list)
            and isinstance(trace["depHash"], str),
            f"S01: {label} metadata is malformed")
    inputs = trace["inputs"]
    require(isinstance(inputs, list)
            and all(isinstance(pair, list) and len(pair) == 2
                    and isinstance(pair[0], str) for pair in inputs),
            f"S01: {label} structured inputs are malformed")
    return inputs


def supported_trace_lean_identity(trace_inputs: list[list[Any]], label: str) -> str:
    """Return the one exact supported Lean build identity in a structured trace."""
    identities = [
        pair for pair in trace_inputs
        if pair[0] in PARSER_TRACE_LINK_LAYOUTS
    ]
    require(len(identities) == 1
            and isinstance(identities[0][1], str)
            and re.fullmatch(r"[0-9a-f]{16}", identities[0][1]) is not None,
            f"S01: {label} trace has no unique supported Lean identity")
    return identities[0][0]


def parser_link_objects_for_trace_inputs(binary_inputs: list[list[Any]]) -> list[list[Any]]:
    """Select the exact link-object array for one explicitly pinned Lean trace layout."""

    identity = supported_trace_lean_identity(binary_inputs, "parser executable")
    layout = PARSER_TRACE_LINK_LAYOUTS[identity]

    outer_keys = {candidate[0] for candidate in PARSER_TRACE_LINK_LAYOUTS.values()}
    outer_groups = [pair for pair in binary_inputs if pair[0] in outer_keys]
    require(len(outer_groups) == 1
            and outer_groups[0][0] == layout[0]
            and isinstance(outer_groups[0][1], list),
            "S01: parser executable trace has no unique link-object layout group")

    if len(layout) == 1:
        return outer_groups[0][1]

    link_info = outer_groups[0][1]
    more_link_objects = [
        pair for pair in link_info
        if isinstance(pair, list) and len(pair) == 2 and pair[0] == layout[1]
    ]
    require(len(more_link_objects) == 1
            and isinstance(more_link_objects[0][1], list),
            "S01: parser executable trace has no unique nested Module.moreLinkObjs group")
    return more_link_objects[0][1]


def module_direct_import_entries(
        module_inputs: list[list[Any]], importer: str) -> list[list[Any]]:
    """Return direct-import records from the exact supported per-version dependency layout."""

    identity = supported_trace_lean_identity(module_inputs, f"{importer} module")
    if identity.startswith("Lean 4.33.1,"):
        dependency_groups = [pair[1] for pair in module_inputs if pair[0] == "deps"]
        require(len(dependency_groups) == 1 and isinstance(dependency_groups[0], list),
                f"S01: {importer} trace has no unique 4.33 dependency group")
        dependency_entries = dependency_groups[0]
    else:
        dependency_groups = [
            pair[1] for pair in module_inputs if pair[0] == f"{importer}:deps"
        ]
        require(len(dependency_groups) == 1 and isinstance(dependency_groups[0], list),
                f"S01: {importer} trace has no unique legacy dependency group")
        nested_dependencies = [
            pair[1] for pair in dependency_groups[0]
            if isinstance(pair, list) and len(pair) == 2 and pair[0] == "deps"
        ]
        require(len(nested_dependencies) == 1
                and isinstance(nested_dependencies[0], list),
                f"S01: {importer} trace has malformed legacy structured dependencies")
        dependency_entries = nested_dependencies[0]

    imports = [
        pair[1] for pair in dependency_entries
        if isinstance(pair, list) and len(pair) == 2 and pair[0] == "imports"
    ]
    require(len(imports) == 1 and isinstance(imports[0], list),
            f"S01: {importer} trace has no unique structured import-artifact group")
    return imports[0]


def validate_parser_build_trace_data(
        binary_path: Path,
        binary_trace: Any,
        module_traces: dict[str, Any],
        object_traces: dict[str, Any],
        *,
        expected_root: Path = ROOT,
        build_root: Path | None = None,
        module_specs: dict[str, tuple[Path, str]] = ACVP_TRACE_MODULES) -> None:
    """Validate records generated under a fresh root against exact canonical source inputs."""

    build_root = expected_root / ".lake/build" if build_root is None else build_root
    expected_binary = build_root / "bin/slhdsa_acvp_parser"
    require(binary_path == expected_binary,
            "S01: queried parser executable path is not the exact worktree output")
    require(set(module_traces) == set(module_specs)
            and set(object_traces) == set(module_specs),
            "S01: selected ACVP module/object trace set is incomplete or excessive")

    binary_inputs = require_trace_shape(binary_trace, "parser executable")
    require(isinstance(binary_trace["outputs"], str),
            "S01: parser executable trace output hash is malformed")

    link_objects = parser_link_objects_for_trace_inputs(binary_inputs)
    require(all(isinstance(pair, list) and len(pair) == 2
                and isinstance(pair[0], str) and isinstance(pair[1], str)
                and re.fullmatch(r"[0-9a-f]{16}", pair[1]) is not None
                for pair in link_objects),
            "S01: parser executable link-object entries are malformed")
    expected_link_paths = {
        str(build_root / f"ir/{module.replace('.', '/')}.c.o.export")
        for module in module_specs
    }
    if expected_root == ROOT and set(module_specs) == set(ACVP_TRACE_MODULES):
        expected_link_paths |= {
            str(build_root / f"lib/{library}")
            for library in PARSER_PERMITTED_LINK_LIBRARIES
        }
    observed_link_paths = [pair[0] for pair in link_objects]
    require(len(observed_link_paths) == len(expected_link_paths)
            and len(set(observed_link_paths)) == len(observed_link_paths)
            and set(observed_link_paths) == expected_link_paths,
            "S01: parser executable link-object ownership is incomplete, duplicated, or excessive")

    module_inputs_by_name: dict[str, list[list[Any]]] = {}
    for module, (source_relative, source_sha256) in module_specs.items():
        short_name = module.rsplit(".", 1)[-1]
        stem = module.replace(".", "/")
        expected_source = expected_root / source_relative
        expected_object = build_root / f"ir/{stem}.c.o.export"
        expected_c = build_root / f"ir/{stem}.c"
        module_trace = module_traces[module]
        object_trace = object_traces[module]
        module_inputs = require_trace_shape(module_trace, f"{short_name} module")
        object_inputs = require_trace_shape(object_trace, f"{short_name} export object")
        module_inputs_by_name[module] = module_inputs

        module_outputs = module_trace["outputs"]
        require(isinstance(module_outputs, dict),
                f"S01: {short_name} module trace outputs are malformed")
        module_identity = supported_trace_lean_identity(
            module_inputs, f"{short_name} module")
        expected_output_keys = (
            ({"o", "m", "i", "c"}
             | ({"rs", "r"} if module_outputs.get("m") is True else set()))
            if module_identity.startswith("Lean 4.33.1,")
            else set(module_outputs) & {"r"} | {"o", "m", "i", "c"}
        )
        require(set(module_outputs) == expected_output_keys
                and isinstance(module_outputs["o"], list)
                and len(module_outputs["o"]) >= 1
                and (not module_identity.startswith("Lean 4.33.1,")
                     or len(module_outputs["o"]) == (3 if module_outputs["m"] is True else 1))
                and re.fullmatch(r"[0-9a-f]{16}\.olean", module_outputs["o"][0]) is not None
                and all(re.fullmatch(r"[0-9a-f]{16}\.olean\.(?:server|private)", value)
                        is not None for value in module_outputs["o"][1:])
                and isinstance(module_outputs["m"], bool)
                and isinstance(module_outputs["i"], str)
                and isinstance(module_outputs["c"], str)
                and ("r" not in module_outputs
                     or re.fullmatch(r"[0-9a-f]{16}\.ir", module_outputs["r"]) is not None)
                and ("rs" not in module_outputs
                     or re.fullmatch(r"[0-9a-f]{16}\.ir\.sig", module_outputs["rs"]) is not None),
                f"S01: {short_name} module trace outputs are malformed")
        require(isinstance(object_trace["outputs"], str),
                f"S01: {short_name} object trace output hash is malformed")

        source_entries = [pair for pair in module_inputs if pair[0].endswith(".lean")]
        require(len(source_entries) == 1
                and source_entries[0][0] == str(expected_source)
                and isinstance(source_entries[0][1], str),
                f"S01: {short_name} trace must name its canonical source exactly once")
        identity_entries = [pair for pair in module_inputs
                            if pair[0].startswith("Module.name:")]
        require(len(identity_entries) == 1
                and identity_entries[0][0] == f"Module.name: {module}"
                and isinstance(identity_entries[0][1], str),
                f"S01: {short_name} trace module identity is missing or duplicated")
        require(hashlib.sha256(expected_source.read_bytes()).hexdigest() == source_sha256,
                f"S01: {short_name} source bytes disagree with the frozen SHA-256")

        object_links = [pair for pair in link_objects if pair[0] == str(expected_object)]
        require(len(object_links) == 1 and isinstance(object_links[0][1], str),
                f"S01: executable does not link the exact {short_name} export object once")
        require(object_trace["outputs"] == object_links[0][1] + ".o",
                f"S01: {short_name} object output does not match executable link metadata")

        c_groups = [pair[1] for pair in object_inputs if pair[0] == f"{module}:c"]
        require(len(c_groups) == 1 and isinstance(c_groups[0], list),
                f"S01: {short_name} object trace has no unique structured C input group")
        c_inputs = [pair for pair in c_groups[0]
                    if isinstance(pair, list) and len(pair) == 2
                    and pair[0] == str(expected_c)]
        require(len(c_inputs) == 1 and isinstance(c_inputs[0][1], str)
                and module_outputs["c"] == c_inputs[0][1] + ".c",
                f"S01: {short_name} generated C is not linked to its export-object input")

    for importer, imported in (
            (PARSER_MODULE, "HashSigTest.SLHDSA.ACVP.Schema"),
            ("HashSigTest.SLHDSA.ACVP.Schema", "HashSigTest.SLHDSA.ACVP.StrictJson")):
        if importer not in module_specs or imported not in module_specs:
            continue
        importer_inputs = module_inputs_by_name[importer]
        imports = module_direct_import_entries(importer_inputs, importer)
        expected_labels = {
            f"{imported} transitive imports (public)",
            f"{imported}:importArts",
        }
        require({pair[0] for pair in imports
                 if isinstance(pair, list) and len(pair) == 2
                 and isinstance(pair[0], str) and isinstance(pair[1], str)} == expected_labels
                and len(imports) == 2,
                f"S01: {importer} does not record the exact direct import relationship to {imported}")


def parse_fresh_query_result(
        completed: subprocess.CompletedProcess[bytes],
        expected_binary: Path,
        *,
        echo_stderr: bool = False) -> Path:
    if echo_stderr and completed.stderr:
        sys.stderr.buffer.write(completed.stderr)
        sys.stderr.buffer.flush()
    require(completed.returncode == 0,
            "S01: fresh no-cache parser query failed:\n" +
            completed.stderr.decode("utf-8", errors="replace")[-4000:])
    expected_stdout = (json.dumps(str(expected_binary)) + "\n").encode("utf-8")
    require(completed.stdout == expected_stdout,
            "S01: fresh parser query stdout is not exactly one canonical JSON path record")
    query_result = parse_strict_json_bytes(completed.stdout, "parser executable query")
    require(query_result == str(expected_binary),
            "S01: parser executable query returned a path outside the fresh build root")
    binary_path = Path(query_result)
    require(binary_path == expected_binary,
            "S01: parser executable query returned an unexpected path alias")
    return binary_path


def query_default_parser_executable_path(project_root: Path) -> Path:
    """Reproduce the reusable r10 default-build behavior; never used by the accepted gate."""

    try:
        completed = subprocess.run(
            ["lake", "-R", "-H", "-J", "query", "slhdsa_acvp_parser:exe"],
            cwd=project_root, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            timeout=300, check=False,
            env={**os.environ, "PYTHONDONTWRITEBYTECODE": "1"})
    except (OSError, subprocess.TimeoutExpired) as error:
        raise CheckFailure(f"S01: reusable parser regression query failed: {error}") from error
    expected = project_root / ".lake/build/bin/slhdsa_acvp_parser"
    return parse_fresh_query_result(completed, expected)


def query_and_validate_fresh_parser_build(
        project_root: Path = ROOT,
        *,
        build_root: Path,
        private_parent: Path,
        module_specs: dict[str, tuple[Path, str]] = ACVP_TRACE_MODULES,
        echo_stderr: bool = False,
        run_self_tests: bool = False) -> tuple[Path, str]:
    """Build into one absent private root and return its exact path plus executable SHA-256."""

    validate_fresh_build_root_before(build_root, private_parent)
    expected_binary = build_root / "bin/slhdsa_acvp_parser"
    try:
        completed = subprocess.run(
            ["lake", "-R", "-H", "--no-cache", f"-KbuildDir={build_root}",
             "-J", "query", "slhdsa_acvp_parser:exe"],
            cwd=project_root, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            timeout=600, check=False,
            env={**os.environ, "PYTHONDONTWRITEBYTECODE": "1"})
    except (OSError, subprocess.TimeoutExpired) as error:
        raise CheckFailure(f"S01: fresh parser executable query failed: {error}") from error
    binary_path = parse_fresh_query_result(
        completed, expected_binary, echo_stderr=echo_stderr)
    validate_fresh_build_root_after(build_root, private_parent)

    binary_trace_path = Path(str(binary_path) + ".trace")
    binary_hash_path = Path(str(binary_path) + ".hash")
    required_paths: list[tuple[Path, str]] = [
            (binary_path, "queried parser executable"),
            (binary_trace_path, "parser executable trace"),
            (binary_hash_path, "parser executable hash metadata"),
    ]
    for path, label in required_paths:
        require_ordinary_file_under(path, build_root, label)
    artifact_manifests = validate_current_parser_artifact_paths(build_root, module_specs)

    binary_trace, module_traces, object_traces = load_parser_trace_data(
        build_root, binary_path, module_specs)
    validate_parser_build_trace_data(
        binary_path, binary_trace, module_traces, object_traces,
        expected_root=project_root, build_root=build_root, module_specs=module_specs)
    validate_current_parser_artifact_metadata(
        build_root, module_traces, object_traces, module_specs, artifact_manifests)
    sidecar_hash = read_incremental_sidecar(
        binary_hash_path, build_root, "parser executable hash metadata")
    trace_hash = binary_trace["outputs"]
    validate_incremental_lake_metadata(trace_hash, sidecar_hash)
    executable_sha256 = sha256_ordinary_file(binary_path, build_root)
    if run_self_tests:
        check_parser_build_input_self_tests(binary_path, build_root)
    return binary_path, executable_sha256


def load_parser_trace_data(
        build_root: Path,
        binary_path: Path,
        module_specs: dict[str, tuple[Path, str]] = ACVP_TRACE_MODULES,
        ) -> tuple[Any, dict[str, Any], dict[str, Any]]:
    binary_trace_path = Path(str(binary_path) + ".trace")
    binary_trace = parse_strict_json_bytes(
        read_ordinary_file_under(
            binary_trace_path, build_root, "parser executable trace"),
        "parser executable trace")
    module_traces: dict[str, Any] = {}
    object_traces: dict[str, Any] = {}
    for module in module_specs:
        short_name = module.rsplit(".", 1)[-1]
        stem = module.replace(".", "/")
        module_trace_path = build_root / f"lib/lean/{stem}.trace"
        object_trace_path = build_root / f"ir/{stem}.c.o.export.trace"
        module_traces[module] = parse_strict_json_bytes(
            read_ordinary_file_under(
                module_trace_path, build_root, f"{short_name} module trace"),
            f"{short_name} module trace")
        object_traces[module] = parse_strict_json_bytes(
            read_ordinary_file_under(
                object_trace_path, build_root, f"{short_name} object trace"),
            f"{short_name} object trace")
    return binary_trace, module_traces, object_traces


def check_parser_build_input_self_tests(binary_path: Path, build_root: Path) -> None:
    binary_trace, module_traces, object_traces = load_parser_trace_data(build_root, binary_path)
    artifact_manifests = validate_current_parser_artifact_paths(build_root)
    observed_cases = {category: 0 for category in PARSER_FOCUSED_CASE_COUNTS}

    def rejected(category: str, label: str, action: Any) -> None:
        require(category in observed_cases,
                f"S01: unregistered focused case category: {category}")
        expect_s01_mutation_rejected(label, action)
        observed_cases[category] += 1

    def record_completed(category: str, count: int = 1) -> None:
        require(category in observed_cases and count > 0,
                f"S01: invalid completed focused case category/count: {category}/{count}")
        observed_cases[category] += count

    def validate(
            selected_binary: Any = None,
            selected_modules: Any = None,
            selected_objects: Any = None) -> None:
        validate_parser_build_trace_data(
            binary_path if selected_binary is None else selected_binary,
            binary_trace,
            module_traces if selected_modules is None else selected_modules,
            object_traces if selected_objects is None else selected_objects,
            build_root=build_root)

    def validate_current_artifacts(
            supplied: dict[str, dict[str, str]] | None = None) -> None:
        current_manifests = validate_current_parser_artifact_paths(
            build_root, supplied=supplied)
        current_binary, current_modules, current_objects = load_parser_trace_data(
            build_root, binary_path)
        validate_parser_build_trace_data(
            binary_path, current_binary, current_modules, current_objects,
            build_root=build_root)
        validate_current_parser_artifact_metadata(
            build_root, current_modules, current_objects, manifests=current_manifests)

    def remove_mutation(path: Path) -> None:
        try:
            status = path.lstat()
        except FileNotFoundError:
            return
        require(not stat.S_ISDIR(status.st_mode),
                f"S01: artifact mutation unexpectedly created a directory: {path}")
        path.unlink()

    def mutate_one_artifact(path: Path, kind: str, label: str) -> None:
        backup = path.with_name(path.name + ".s01-r12-backup")
        require(not os.path.lexists(backup), f"S01: artifact backup already exists: {backup}")
        path.rename(backup)
        try:
            if kind == "missing":
                pass
            elif kind == "symlink-inside":
                os.symlink(backup.name, path)
            elif kind == "symlink-outside":
                os.symlink("/etc/hosts", path)
            elif kind == "fifo":
                os.mkfifo(path)
            else:
                raise CheckFailure(f"S01: unknown artifact mutation kind: {kind}")
            rejected("artifacts", label, validate_current_artifacts)
        finally:
            remove_mutation(path)
            backup.rename(path)

    # Reproduce r11's exact 18 simultaneous symlink substitutions on a genuine fresh build.
    reproduced_keys = (
        "module", "module_hash", "generated_c", "generated_c_hash",
        "export_object", "export_object_hash",
    )
    backups: list[tuple[Path, Path]] = []
    try:
        for module in ACVP_TRACE_MODULES:
            for key in reproduced_keys:
                path = Path(artifact_manifests[module][key])
                backup = path.with_name(path.name + ".s01-r11-001-backup")
                require(not os.path.lexists(backup),
                        f"S01: r11 reproduction backup already exists: {backup}")
                path.rename(backup)
                os.symlink("/etc/hosts", path)
                backups.append((path, backup))
        require(len(backups) == 18,
                "S01: exact r11 current-artifact reproduction did not mutate 18 paths")
        rejected("artifacts", "exact r11 18-current-artifact symlink substitution",
                 validate_current_artifacts)
    finally:
        for path, backup in reversed(backups):
            remove_mutation(path)
            backup.rename(path)

    # Every exact claimed path for all three modules rejects missing, inside/outside symlink,
    # and FIFO state. Every exact manifest path also rejects a parent-component spelling alias.
    for module, manifest in artifact_manifests.items():
        short_name = module.rsplit(".", 1)[-1]
        for key, raw_path in manifest.items():
            path = Path(raw_path)
            for kind in ("missing", "symlink-inside", "symlink-outside", "fifo"):
                mutate_one_artifact(
                    path, kind, f"{short_name} {key} current-file {kind}")
            aliased = copy.deepcopy(artifact_manifests)
            aliased[module][key] = str(path.parent / ".." / path.parent.name / path.name)
            rejected(
                "artifacts", f"{short_name} {key} manifest path alias",
                lambda aliased=aliased: validate_current_parser_artifact_paths(
                    build_root, supplied=aliased))

    # All nine module/C/export-object metadata sidecars reject a trace-token mismatch.
    for module, manifest in artifact_manifests.items():
        short_name = module.rsplit(".", 1)[-1]
        for key in ("module_hash", "generated_c_hash", "export_object_hash"):
            path = Path(manifest[key])
            backup = path.with_name(path.name + ".s01-r12-token-backup")
            path.rename(backup)
            try:
                path.write_text("0" * 16, encoding="ascii")
                rejected(
                    "artifacts", f"{short_name} {key} mismatched metadata token",
                    validate_current_artifacts)
            finally:
                remove_mutation(path)
                backup.rename(path)
    validate_current_artifacts()

    # Repeated production-walker failures must neither accumulate a newly opened child nor close
    # an unrelated descriptor. The private hook only identifies the exact post-open/pre-fstat fd;
    # unittest.mock supplies the controlled fstat result while every path remains under /tmp.
    def descriptor_snapshot() -> dict[int, tuple[int, int, int]]:
        snapshot: dict[int, tuple[int, int, int]] = {}
        for raw in os.listdir("/proc/self/fd"):
            if not raw.isdigit():
                continue
            descriptor = int(raw)
            try:
                status = os.fstat(descriptor)
            except OSError:
                continue
            snapshot[descriptor] = (status.st_dev, status.st_ino, status.st_mode)
        return snapshot

    def repeated_descriptor_failure(
            label: str,
            action: Callable[[], None],
            expected_exception: type[BaseException] = CheckFailure) -> None:
        sentinel_owner = _OwnedDescriptor(
            os.open("/dev/null", os.O_RDONLY | os.O_CLOEXEC), f"{label} sentinel")
        try:
            before = descriptor_snapshot()
            require(sentinel_owner.descriptor in before,
                    f"S01: {label} sentinel descriptor is not live")
            for _iteration in range(16):
                try:
                    action()
                except expected_exception as error:
                    if expected_exception is RuntimeError:
                        require(str(error) == "controlled pre-fstat hook RuntimeError",
                                f"S01: {label} did not preserve the original RuntimeError")
                except BaseException as error:
                    raise CheckFailure(
                        f"S01: {label} raised {type(error).__name__}, expected "
                        f"{expected_exception.__name__}") from error
                else:
                    raise CheckFailure(f"S01: descriptor lifecycle self-test accepted {label}")
            after = descriptor_snapshot()
            require(after == before and sentinel_owner.descriptor in after,
                    f"S01: {label} leaked or unintentionally closed a descriptor: "
                    f"before={before}, after={after}")
        finally:
            _close_owned_descriptors(
                [sentinel_owner],
                f"{label} sentinel")
        record_completed("descriptor-lifecycle")

    def altered_fstat(
            original: Callable[[int], os.stat_result],
            selected: dict[str, int],
            mode: str) -> Callable[[int], os.stat_result]:
        def replacement(descriptor: int) -> os.stat_result:
            if descriptor == selected.get("descriptor"):
                if mode == "failure":
                    raise OSError(5, "controlled post-open fstat failure")
                status = original(descriptor)
                values = list(status)
                values[1] = status.st_ino + 1
                return os.stat_result(values)
            return original(descriptor)
        return replacement

    with tempfile.TemporaryDirectory(prefix="slhdsa-descriptor-lifecycle-", dir="/tmp") as temp:
        lifecycle_root = Path(temp)
        root_target = lifecycle_root / "root-chain-target"
        root_target.mkdir()
        relative_root = lifecycle_root / "relative-root"
        relative_parent = relative_root / "relative-intermediate"
        relative_parent.mkdir(parents=True)
        relative_file = relative_parent / "ordinary"
        relative_file.write_bytes(b"ordinary\n")

        for mode, description in (
                ("identity", "identity mismatch"),
                ("failure", "fstat failure"),
                ("runtime", "hook RuntimeError")):
            selected: dict[str, int] = {}

            def root_hook(component: str, descriptor: int) -> None:
                if component == root_target.name:
                    selected["descriptor"] = descriptor
                    if mode == "runtime":
                        raise RuntimeError("controlled pre-fstat hook RuntimeError")

            def root_action() -> None:
                selected.clear()
                original = os.fstat
                with mock.patch.object(os, "fstat", altered_fstat(original, selected, mode)):
                    descriptor = open_absolute_directory_fd(
                        root_target, "controlled root-chain lifecycle",
                        _pre_child_fstat=root_hook)
                    _close_owned_descriptors(
                        [_OwnedDescriptor(descriptor, "root lifecycle success descriptor")],
                        "root lifecycle success descriptor")

            repeated_descriptor_failure(
                f"root-chain {description}", root_action,
                RuntimeError if mode == "runtime" else CheckFailure)

            selected = {}

            def relative_hook(component: str, descriptor: int) -> None:
                if component == relative_parent.name:
                    selected["descriptor"] = descriptor
                    if mode == "runtime":
                        raise RuntimeError("controlled pre-fstat hook RuntimeError")

            def relative_action() -> None:
                selected.clear()
                original = os.fstat
                with mock.patch.object(os, "fstat", altered_fstat(original, selected, mode)):
                    descriptor, parent_descriptor, _name, _status = open_ordinary_file_under(
                        relative_file, relative_root, "controlled relative lifecycle",
                        _pre_relative_child_fstat=relative_hook)
                    _close_owned_descriptors(
                        [_OwnedDescriptor(descriptor, "relative lifecycle file"),
                         _OwnedDescriptor(parent_descriptor,
                                          "relative lifecycle retained parent")],
                        "relative lifecycle success descriptors")

            repeated_descriptor_failure(
                f"relative-intermediate {description}", relative_action,
                RuntimeError if mode == "runtime" else CheckFailure)

    # Close-after-real-then-raise exercises the Linux non-retry rule across every bounded
    # production descriptor family. Each conceptual case repeats sixteen times, retains two
    # unrelated sentinels, and requires the complete process descriptor identity map to match.
    def repeated_ownership_case(
            label: str, action: Callable[[], None], *, repetitions: int = 16) -> None:
        sentinel_owners = [
            _OwnedDescriptor(os.open("/dev/null", os.O_RDONLY | os.O_CLOEXEC),
                             f"{label} sentinel one"),
            _OwnedDescriptor(os.open("/dev/null", os.O_RDONLY | os.O_CLOEXEC),
                             f"{label} sentinel two"),
        ]
        try:
            before = descriptor_snapshot()
            require(all(owner.descriptor in before for owner in sentinel_owners),
                    f"S01: {label} sentinels are not both live")
            for _iteration in range(repetitions):
                action()
            after = descriptor_snapshot()
            require(after == before
                    and all(owner.descriptor in after for owner in sentinel_owners),
                    f"S01: {label} leaked/retried/closed an unrelated descriptor: "
                    f"before={before}, after={after}")
        finally:
            _close_owned_descriptors(sentinel_owners, f"{label} sentinels")
        record_completed("descriptor-ownership")

    def require_exact_original(original: RuntimeError, action: Callable[[], None]) -> None:
        try:
            action()
        except RuntimeError as observed:
            observed_traceback = observed.__traceback__
            require(observed is original and type(observed) is type(original)
                    and observed.args == original.args
                    and observed_traceback is not None
                    and original.__traceback__ is observed_traceback,
                    "S01: descriptor cleanup did not preserve the exact original RuntimeError")
        except BaseException as error:
            raise CheckFailure(
                f"S01: descriptor cleanup replaced RuntimeError with {type(error).__name__}") \
                from error
        else:
            raise CheckFailure("S01: descriptor close-after-release probe unexpectedly returned")

    def close_after_real(
            real_close: Callable[[int], None],
            selected: dict[str, int],
            *,
            reuse: list[_OwnedDescriptor] | None = None,
            cleanup_error: BaseException | None = None) -> Callable[[int], None]:
        def replacement(descriptor: int) -> None:
            if descriptor != selected.get("descriptor"):
                real_close(descriptor)
                return
            real_close(descriptor)
            if reuse is not None:
                reused_owner = _OwnedDescriptor(
                    os.open("/dev/null", os.O_RDONLY | os.O_CLOEXEC),
                    "forced reused /dev/null")
                reuse.append(reused_owner)
                require(reused_owner.descriptor == descriptor,
                        "S01: forced descriptor-reuse probe did not reuse the selected integer")
            if cleanup_error is not None:
                raise cleanup_error
            raise OSError(5, "controlled close-after-release")
        return replacement

    class HostileActiveRuntime(RuntimeError):
        """Active exception whose dynamic add_note must never be invoked by cleanup."""

        def __init__(self, message: str):
            super().__init__(message)
            self.dynamic_add_note_calls = 0

        def add_note(self, note: str) -> None:
            self.dynamic_add_note_calls += 1
            raise RuntimeError(f"hostile dynamic add_note invoked: {note}")

    class HostileCleanupError(OSError):
        """Cleanup exception whose display methods must never be used as evidence."""

        def __str__(self) -> str:
            raise RuntimeError("hostile cleanup __str__ invoked")

        def __repr__(self) -> str:
            raise RuntimeError("hostile cleanup __repr__ invoked")

    class HostileTypeName(str):
        """Nonempty class name whose every dynamic display path raises."""

        def __bool__(self) -> bool:
            return True

        def __format__(self, _spec: str) -> str:
            raise RuntimeError("hostile type-name __format__ invoked")

        def __str__(self) -> str:
            raise RuntimeError("hostile type-name __str__ invoked")

        def __repr__(self) -> str:
            raise RuntimeError("hostile type-name __repr__ invoked")

    HostileCleanupError.__name__ = HostileTypeName("HostileCleanupError")

    class RaisingNameMeta(type):
        def __getattribute__(cls, name: str) -> Any:
            if name == "__name__":
                raise RuntimeError("hostile metaclass __name__ invoked")
            return super().__getattribute__(name)

    class MetaclassCleanupError(OSError, metaclass=RaisingNameMeta):
        pass

    class RejectBaseNote(RuntimeError):
        @property
        def __notes__(self) -> Any:
            raise RuntimeError("base note read rejected")

        @__notes__.setter
        def __notes__(self, _value: Any) -> None:
            raise RuntimeError("base note write rejected")

    with tempfile.TemporaryDirectory(prefix="slhdsa-descriptor-ownership-", dir="/tmp") as temp:
        ownership_root = Path(temp)

        chain_child = ownership_root / "chain-child"
        chain_child.mkdir()

        def chain_reuse_action() -> None:
            repository_owner = _OwnedDescriptor(
                _open_root_descriptor(ownership_root), "chain reuse repository")
            reused_owners: list[_OwnedDescriptor] = []
            selected: dict[str, int] = {}
            real_dup = os.dup
            real_close = os.close

            def selected_dup(descriptor: int) -> int:
                duplicated = real_dup(descriptor)
                selected["descriptor"] = duplicated
                return duplicated

            try:
                with mock.patch.object(os, "dup", selected_dup), \
                        mock.patch.object(
                            os, "close", close_after_real(
                                real_close, selected, reuse=reused_owners)):
                    try:
                        _open_directory_chain(repository_owner.descriptor, (chain_child.name,))
                    except CheckFailure as error:
                        require(isinstance(error.__cause__, OSError)
                                and error.args == (
                                    "S01: descriptor cleanup failed after all unique descriptors "
                                    "were attempted: unique_descriptors=1; close_failures=1",),
                                "S01: chain reuse did not expose deterministic cleanup evidence")
                    else:
                        raise CheckFailure("S01: chain reuse close failure was accepted")
                require(len(reused_owners) == 1
                        and reused_owners[0].descriptor == selected["descriptor"],
                        "S01: chain reuse sentinel was retried or lost")
            finally:
                _close_owned_descriptors(reused_owners, "chain forced reuse sentinel")
                _close_owned_descriptors([repository_owner], "chain reuse repository")

        repeated_ownership_case("old directory chain forced fd reuse", chain_reuse_action)

        active_root = ownership_root / "active-root"
        active_root.mkdir()

        def active_root_action() -> None:
            original = RuntimeError("original-active-root-runtime")
            selected: dict[str, int] = {}
            real_fstat = os.fstat
            real_close = os.close

            def failing_fstat(descriptor: int) -> os.stat_result:
                selected["descriptor"] = descriptor
                raise original

            with mock.patch.object(os, "fstat", failing_fstat), \
                    mock.patch.object(os, "close", close_after_real(real_close, selected)):
                require_exact_original(
                    original, lambda: _open_root_descriptor(active_root))

        repeated_ownership_case("active root validation cleanup", active_root_action)

        def hostile_active_action() -> None:
            original = HostileActiveRuntime("original-hostile-active-runtime")
            cleanup_error = HostileCleanupError(5, "hostile-cleanup-payload")
            selected: dict[str, int] = {}
            real_close = os.close

            def failing_fstat(descriptor: int) -> os.stat_result:
                selected["descriptor"] = descriptor
                raise original

            with mock.patch.object(os, "fstat", failing_fstat), \
                    mock.patch.object(
                        os, "close", close_after_real(
                            real_close, selected, cleanup_error=cleanup_error)):
                require_exact_original(
                    original, lambda: _open_root_descriptor(active_root))
            notes = getattr(original, "__notes__", [])
            expected_note = (
                "S01 descriptor cleanup anomaly: aliased_owners=0; "
                "unique_descriptors=1; close_failures=1")
            require(original.dynamic_add_note_calls == 0
                    and len(notes) == 1
                    and notes[0] == expected_note,
                    "S01: hostile active exception did not retain exact base cleanup evidence")

            rejecting_original = RejectBaseNote("original-base-note-rejection")
            metaclass_cleanup = MetaclassCleanupError(5, "metaclass-cleanup-payload")
            selected = {}

            def rejecting_fstat(descriptor: int) -> os.stat_result:
                selected["descriptor"] = descriptor
                raise rejecting_original

            with mock.patch.object(os, "fstat", rejecting_fstat), \
                    mock.patch.object(
                        os, "close", close_after_real(
                            real_close, selected, cleanup_error=metaclass_cleanup)):
                require_exact_original(
                    rejecting_original, lambda: _open_root_descriptor(active_root))

        repeated_ownership_case(
            "hostile active exception cleanup evidence", hostile_active_action,
            repetitions=32)

        active_parent_owner = _OwnedDescriptor(
            _open_root_descriptor(ownership_root), "active directory-at parent")

        def active_directory_at_action() -> None:
            original = RuntimeError("original-active-directory-runtime")
            selected: dict[str, int] = {}
            real_close = os.close

            def failing_fstat(descriptor: int) -> os.stat_result:
                selected["descriptor"] = descriptor
                raise original

            with mock.patch.object(os, "fstat", failing_fstat), \
                    mock.patch.object(os, "close", close_after_real(real_close, selected)):
                require_exact_original(
                    original,
                    lambda: _open_directory_at(
                        active_parent_owner.descriptor, active_root.name, active_root))

        try:
            repeated_ownership_case("active directory-at validation cleanup",
                                    active_directory_at_action)
        finally:
            _close_owned_descriptors([active_parent_owner], "active directory-at parent")

        recursive_file_root = ownership_root / "recursive-file"
        recursive_file_root.mkdir()
        (recursive_file_root / "ordinary").write_bytes(b"ordinary\n")

        def recursive_file_action() -> None:
            original = RuntimeError("original-recursive-file-runtime")
            selected: dict[str, int] = {}
            real_close = os.close

            def failing_read(descriptor: int, _size: int) -> bytes:
                selected["descriptor"] = descriptor
                raise original

            with mock.patch.object(os, "read", failing_read), \
                    mock.patch.object(os, "close", close_after_real(real_close, selected)):
                require_exact_original(
                    original, lambda: scan_regular_tree_no_follow(recursive_file_root))

        repeated_ownership_case("active recursive file cleanup", recursive_file_action)

        recursive_directory_root = ownership_root / "recursive-directory"
        recursive_child = recursive_directory_root / "child"
        recursive_child.mkdir(parents=True)

        def recursive_directory_action() -> None:
            original = RuntimeError("original-recursive-directory-runtime")
            selected: dict[str, int] = {}
            real_fstat = os.fstat
            real_close = os.close
            child_identity = recursive_child.stat()

            def failing_fstat(descriptor: int) -> os.stat_result:
                status = real_fstat(descriptor)
                if (status.st_dev, status.st_ino) == \
                        (child_identity.st_dev, child_identity.st_ino):
                    selected["descriptor"] = descriptor
                    raise original
                return status

            with mock.patch.object(os, "fstat", failing_fstat), \
                    mock.patch.object(os, "close", close_after_real(real_close, selected)):
                require_exact_original(
                    original, lambda: scan_regular_tree_no_follow(recursive_directory_root))

        repeated_ownership_case(
            "active recursive directory cleanup", recursive_directory_action)

        nominal_scan_root = ownership_root / "nominal-scan-root"
        nominal_scan_root.mkdir()

        def nominal_scan_root_action() -> None:
            selected: dict[str, int] = {}
            real_fstat = os.fstat
            real_close = os.close
            root_identity = nominal_scan_root.stat()

            def failing_close(descriptor: int) -> None:
                status = real_fstat(descriptor)
                if (status.st_dev, status.st_ino) == \
                        (root_identity.st_dev, root_identity.st_ino):
                    selected["descriptor"] = descriptor
                close_after_real(real_close, selected)(descriptor)

            with mock.patch.object(os, "close", failing_close):
                try:
                    scan_regular_tree_no_follow(nominal_scan_root)
                except CheckFailure as error:
                    require(isinstance(error.__cause__, OSError)
                            and error.args == (
                                "S01: descriptor cleanup failed after all unique descriptors "
                                "were attempted: unique_descriptors=1; close_failures=1",),
                            "S01: nominal active-tree close did not report stable evidence")
                else:
                    raise CheckFailure("S01: nominal active-tree close failure was accepted")

        repeated_ownership_case("active top-level nominal cleanup", nominal_scan_root_action)

        def load_active_action() -> None:
            original = RuntimeError("original-load-active-runtime")
            selected: dict[str, int] = {}
            real_close = os.close
            globals_map = load_active_s01_files.__globals__

            def failing_scan(descriptor: int, *_args: Any, **_kwargs: Any) -> dict[str, bytes]:
                selected["descriptor"] = descriptor
                raise original

            with mock.patch.dict(globals_map, {"_scan_directory_descriptor": failing_scan}), \
                    mock.patch.object(os, "close", close_after_real(real_close, selected)):
                require_exact_original(original, load_active_s01_files)

        repeated_ownership_case("load-active scoped/root cleanup", load_active_action)

        consumer_root = ownership_root / "consumers"
        consumer_root.mkdir()
        consumer_file = consumer_root / "ordinary"
        consumer_file.write_bytes(b"consumer\n")

        def active_read_action() -> None:
            original = RuntimeError("original-read-runtime")
            selected: dict[str, int] = {}
            real_close = os.close

            def failing_read(descriptor: int, _size: int) -> bytes:
                selected["descriptor"] = descriptor
                raise original

            with mock.patch.object(os, "read", failing_read), \
                    mock.patch.object(os, "close", close_after_real(real_close, selected)):
                require_exact_original(
                    original,
                    lambda: read_ordinary_file_under(
                        consumer_file, consumer_root, "controlled read consumer"))

        repeated_ownership_case("read consumer active cleanup", active_read_action)

        def active_sha_action() -> None:
            original = RuntimeError("original-sha-runtime")
            selected: dict[str, int] = {}
            real_close = os.close

            def failing_read(descriptor: int, _size: int) -> bytes:
                selected["descriptor"] = descriptor
                raise original

            with mock.patch.object(os, "read", failing_read), \
                    mock.patch.object(os, "close", close_after_real(real_close, selected)):
                require_exact_original(
                    original, lambda: sha256_ordinary_file(consumer_file, consumer_root))

        repeated_ownership_case("SHA consumer active cleanup", active_sha_action)

        output_counter = 0

        def active_output_action() -> None:
            nonlocal output_counter
            output_counter += 1
            output = consumer_root / f"output-{output_counter}"
            original = RuntimeError("original-output-runtime")
            selected: dict[str, int] = {}
            real_close = os.close

            def failing_write(descriptor: int, _data: bytes) -> int:
                selected["descriptor"] = descriptor
                raise original

            try:
                with mock.patch.object(os, "write", failing_write), \
                        mock.patch.object(os, "close", close_after_real(real_close, selected)):
                    require_exact_original(
                        original,
                        lambda: write_new_gate_record(
                            output, "controlled", "controlled exclusive output"))
            finally:
                output.unlink(missing_ok=True)

        repeated_ownership_case("exclusive output active cleanup", active_output_action)

        def nominal_pair_action() -> None:
            selected: dict[str, int] = {}
            real_fstat = os.fstat
            real_close = os.close

            def failing_close(descriptor: int) -> None:
                status = real_fstat(descriptor)
                if stat.S_ISREG(status.st_mode) and "descriptor" not in selected:
                    selected["descriptor"] = descriptor
                close_after_real(real_close, selected)(descriptor)

            with mock.patch.object(os, "close", failing_close):
                try:
                    require_ordinary_file_under(
                        consumer_file, consumer_root, "controlled nominal pair")
                except CheckFailure as error:
                    require(isinstance(error.__cause__, OSError)
                            and error.args == (
                                "S01: descriptor cleanup failed after all unique descriptors "
                                "were attempted: unique_descriptors=2; close_failures=1",),
                            "S01: nominal pair cleanup did not report deterministic evidence")
                else:
                    raise CheckFailure("S01: nominal pair close failure was accepted")

        repeated_ownership_case("nominal two-owner cleanup", nominal_pair_action)

        def nominal_hostile_evidence_action() -> None:
            owners = [
                _OwnedDescriptor(
                    os.open("/dev/null", os.O_RDONLY | os.O_CLOEXEC),
                    "hostile nominal first"),
                _OwnedDescriptor(
                    os.open("/dev/null", os.O_RDONLY | os.O_CLOEXEC),
                    "hostile nominal second"),
            ]
            selected = {"descriptor": owners[0].descriptor}
            real_close = os.close
            cleanup_error = HostileCleanupError(5, "hostile-cleanup-payload")
            try:
                with mock.patch.object(
                        os, "close", close_after_real(
                            real_close, selected, cleanup_error=cleanup_error)):
                    _close_owned_descriptors(owners, "hostile nominal")
            except CheckFailure as error:
                require(
                    error.__cause__ is cleanup_error
                    and error.args == (
                        "S01: descriptor cleanup failed after all unique descriptors were "
                        "attempted: unique_descriptors=2; close_failures=1",)
                    and all(owner.descriptor == -1 for owner in owners),
                    "S01: hostile nominal cleanup evidence/cause/owner state is not exact")
            except BaseException as error:
                raise CheckFailure("S01: hostile nominal cleanup replaced CheckFailure") from error
            else:
                raise CheckFailure("S01: hostile nominal cleanup failure was accepted")

            for failing_positions in ({0}, {1}, {2}, {0, 1, 2}):
                position_owners = [
                    _OwnedDescriptor(
                        os.open("/dev/null", os.O_RDONLY | os.O_CLOEXEC),
                        "position owner")
                    for _index in range(3)
                ]
                descriptors = [owner.descriptor for owner in position_owners]
                errors = [OSError(5, "controlled positional close failure") for _index in range(3)]

                def positional_close(descriptor: int) -> None:
                    position = descriptors.index(descriptor)
                    real_close(descriptor)
                    if position in failing_positions:
                        raise errors[position]

                try:
                    with mock.patch.object(os, "close", positional_close):
                        _close_owned_descriptors(position_owners, "positional failures")
                except CheckFailure as error:
                    expected_failure_count = len(failing_positions)
                    require(
                        error.__cause__ is errors[min(failing_positions)]
                        and error.args == (
                            "S01: descriptor cleanup failed after all unique descriptors were "
                            f"attempted: unique_descriptors=3; "
                            f"close_failures={expected_failure_count}",)
                        and all(owner.descriptor == -1 for owner in position_owners),
                        "S01: first/middle/last/all cleanup result is not exact")
                else:
                    raise CheckFailure("S01: positional cleanup failure was accepted")

            same_owner = _OwnedDescriptor(
                os.open("/dev/null", os.O_RDONLY | os.O_CLOEXEC), "same owner twice")
            _close_owned_descriptors([same_owner, same_owner], "same owner twice")
            require(same_owner.descriptor == -1,
                    "S01: repeated reference to one owner was not one-shot safe")

            base_owner = _OwnedDescriptor(
                os.open("/dev/null", os.O_RDONLY | os.O_CLOEXEC), "dup base")
            dup_owner = _OwnedDescriptor(
                os.dup(base_owner.descriptor), "dup distinct descriptor")
            _close_owned_descriptors([base_owner, dup_owner], "legitimate dup descriptors")
            require(base_owner.descriptor == -1 and dup_owner.descriptor == -1,
                    "S01: distinct dup descriptor numbers were not independently closed")

        repeated_ownership_case(
            "hostile nominal cleanup evidence", nominal_hostile_evidence_action,
            repetitions=32)

        def active_distinct_owner_alias_action() -> None:
            primary_owner = _OwnedDescriptor(
                os.open("/dev/null", os.O_RDONLY | os.O_CLOEXEC), "active alias primary")
            alias_owner = _OwnedDescriptor(
                primary_owner.descriptor, "active alias distinct owner")
            reused_owners: list[_OwnedDescriptor] = []
            selected = {"descriptor": primary_owner.descriptor}
            original = RuntimeError("original-active-owner-alias")
            cleanup_error = OSError(5, "controlled active alias close failure")
            real_close = os.close

            def propagate_original() -> None:
                try:
                    raise original
                except RuntimeError as observed:
                    _close_owned_descriptors(
                        [primary_owner, alias_owner], "active distinct-owner alias", observed)
                    raise

            try:
                with mock.patch.object(
                        os, "close", close_after_real(
                            real_close, selected, reuse=reused_owners,
                            cleanup_error=cleanup_error)):
                    require_exact_original(original, propagate_original)
                notes = getattr(original, "__notes__", [])
                require(
                    primary_owner.descriptor == -1 and alias_owner.descriptor == -1
                    and len(reused_owners) == 1
                    and reused_owners[0].descriptor == selected["descriptor"]
                    and os.fstat(reused_owners[0].descriptor).st_ino >= 0
                    and notes == [
                        "S01 descriptor cleanup anomaly: aliased_owners=1; "
                        "unique_descriptors=1; close_failures=1"],
                    "S01: active distinct-owner alias retried or lost the reused descriptor")
            finally:
                _close_owned_descriptors(reused_owners, "active alias reused descriptor")

        repeated_ownership_case(
            "active distinct-owner alias forced reuse", active_distinct_owner_alias_action,
            repetitions=32)

        def nominal_distinct_owner_alias_action() -> None:
            primary_owner = _OwnedDescriptor(
                os.open("/dev/null", os.O_RDONLY | os.O_CLOEXEC), "nominal alias primary")
            alias_owner = _OwnedDescriptor(
                primary_owner.descriptor, "nominal alias distinct owner")
            other_owner = _OwnedDescriptor(
                os.open("/dev/null", os.O_RDONLY | os.O_CLOEXEC), "nominal alias other")
            reused_owners: list[_OwnedDescriptor] = []
            primary_descriptor = primary_owner.descriptor
            other_descriptor = other_owner.descriptor
            first_error = OSError(5, "controlled first alias close failure")
            later_error = OSError(5, "controlled later unique close failure")
            real_close = os.close

            def alias_close(descriptor: int) -> None:
                real_close(descriptor)
                if descriptor == primary_descriptor:
                    reused_owner = _OwnedDescriptor(
                        os.open("/dev/null", os.O_RDONLY | os.O_CLOEXEC),
                        "nominal alias forced reused /dev/null")
                    reused_owners.append(reused_owner)
                    require(reused_owner.descriptor == primary_descriptor,
                            "S01: nominal alias probe did not force same-number reuse")
                    raise first_error
                if descriptor == other_descriptor:
                    raise later_error

            try:
                with mock.patch.object(os, "close", alias_close):
                    try:
                        _close_owned_descriptors(
                            [primary_owner, alias_owner, other_owner],
                            "nominal distinct-owner alias")
                    except CheckFailure as error:
                        require(
                            error.__cause__ is first_error
                            and error.args == (
                                "S01: descriptor cleanup owner-alias invariant failed after all "
                                "unique descriptors were attempted: aliased_owners=1; "
                                "unique_descriptors=2; close_failures=2",)
                            and primary_owner.descriptor == -1
                            and alias_owner.descriptor == -1
                            and other_owner.descriptor == -1,
                            "S01: nominal distinct-owner alias result/cause is not exact")
                    else:
                        raise CheckFailure("S01: nominal distinct-owner alias was accepted")
                require(
                    len(reused_owners) == 1
                    and reused_owners[0].descriptor == primary_descriptor
                    and os.fstat(reused_owners[0].descriptor).st_ino >= 0,
                    "S01: nominal distinct-owner alias closed the reused descriptor")
            finally:
                _close_owned_descriptors(reused_owners, "nominal alias reused descriptor")

        repeated_ownership_case(
            "nominal distinct-owner alias forced reuse", nominal_distinct_owner_alias_action,
            repetitions=32)

        fresh_parent = ownership_root / "fresh-parent"
        fresh_parent.mkdir(mode=0o700)
        fresh_root = fresh_parent / FRESH_BUILD_CHILD

        def fresh_before_action() -> None:
            original = RuntimeError("original-fresh-before-runtime")
            selected: dict[str, int] = {}
            matches = 0
            real_fstat = os.fstat
            real_close = os.close
            parent_identity = fresh_parent.stat()

            def failing_fstat(descriptor: int) -> os.stat_result:
                nonlocal matches
                status = real_fstat(descriptor)
                if (status.st_dev, status.st_ino) == \
                        (parent_identity.st_dev, parent_identity.st_ino):
                    matches += 1
                    if matches == 2:
                        selected["descriptor"] = descriptor
                        raise original
                return status

            with mock.patch.object(os, "fstat", failing_fstat), \
                    mock.patch.object(os, "close", close_after_real(real_close, selected)):
                require_exact_original(
                    original,
                    lambda: validate_fresh_build_root_before(fresh_root, fresh_parent))

        repeated_ownership_case("fresh-root before active cleanup", fresh_before_action)

        fresh_root.mkdir()

        def fresh_after_action() -> None:
            original = RuntimeError("original-fresh-after-runtime")
            selected: dict[str, int] = {}
            real_fstat = os.fstat
            real_close = os.close
            build_identity = fresh_root.stat()

            def failing_fstat(descriptor: int) -> os.stat_result:
                status = real_fstat(descriptor)
                if (status.st_dev, status.st_ino) == \
                        (build_identity.st_dev, build_identity.st_ino):
                    selected["descriptor"] = descriptor
                    raise original
                return status

            with mock.patch.object(os, "fstat", failing_fstat), \
                    mock.patch.object(os, "close", close_after_real(real_close, selected)):
                require_exact_original(
                    original,
                    lambda: validate_fresh_build_root_after(fresh_root, fresh_parent))

        repeated_ownership_case("fresh-root after active cleanup", fresh_after_action)

    # Preserve the eight r9 semantic/JSON cases.
    for mode in ("wrong", "missing", "duplicate"):
        mutated_modules = copy.deepcopy(module_traces)
        trace = mutated_modules[PARSER_MODULE]
        source_entry = next(pair for pair in trace["inputs"] if pair[0].endswith(".lean"))
        if mode == "wrong":
            source_entry[0] = "/tmp/WrongSrc/HashSigTest/SLHDSA/ACVP/ParserTests.lean"
        elif mode == "missing":
            trace["inputs"] = [pair for pair in trace["inputs"] if not pair[0].endswith(".lean")]
        else:
            trace["inputs"].append(copy.deepcopy(source_entry))
        rejected(
            "legacy", f"{mode} structured ParserTests source input",
            lambda mutated_modules=mutated_modules: validate(selected_modules=mutated_modules))
    synthetic_modules = copy.deepcopy(module_traces)
    synthetic_modules[PARSER_MODULE]["synthetic"] = True
    rejected("legacy", "synthetic ParserTests module trace",
             lambda: validate(selected_modules=synthetic_modules))
    malformed_modules = copy.deepcopy(module_traces)
    malformed_modules[PARSER_MODULE]["inputs"] = {"not": "a trace input array"}
    rejected("legacy", "malformed ParserTests structured trace",
             lambda: validate(selected_modules=malformed_modules))
    rejected("legacy", "wrong resolved parser executable",
             lambda: validate(selected_binary=build_root / "bin/smoke_test"))
    rejected(
        "legacy", "duplicate key in structured trace JSON",
        lambda: parse_strict_json_bytes(b'{"synthetic":false,"synthetic":true}',
                                        "mutated trace"))
    rejected("legacy", "malformed structured trace JSON",
             lambda: parse_strict_json_bytes(b'{"synthetic":', "mutated trace"))

    # Every frozen module gets independent source, generated-C/object, and executable-link cases.
    for module in ACVP_TRACE_MODULES:
        short_name = module.rsplit(".", 1)[-1]
        stem = module.replace(".", "/")
        expected_object = str(build_root / f"ir/{stem}.c.o.export")
        expected_c = str(build_root / f"ir/{stem}.c")
        for mode in ("wrong", "missing", "duplicate"):
            mutated_modules = copy.deepcopy(module_traces)
            trace = mutated_modules[module]
            source_entry = next(pair for pair in trace["inputs"] if pair[0].endswith(".lean"))
            if mode == "wrong":
                source_entry[0] = "/tmp/WrongSource/" + source_entry[0].rsplit("/", 1)[-1]
            elif mode == "missing":
                trace["inputs"] = [pair for pair in trace["inputs"]
                                   if not pair[0].endswith(".lean")]
            else:
                trace["inputs"].append(copy.deepcopy(source_entry))
            rejected(
                "source-object-link", f"{mode} {short_name} canonical source",
                lambda mutated_modules=mutated_modules: validate(
                    selected_modules=mutated_modules))

        mutated_objects = copy.deepcopy(object_traces)
        c_group = next(pair[1] for pair in mutated_objects[module]["inputs"]
                       if pair[0] == f"{module}:c")
        next(pair for pair in c_group if pair[0] == expected_c)[0] += ".wrong"
        rejected(
            "source-object-link", f"wrong {short_name} generated-C object input",
            lambda mutated_objects=mutated_objects: validate(selected_objects=mutated_objects))

        for mode in ("wrong", "missing", "duplicate"):
            mutated_binary = copy.deepcopy(binary_trace)
            link_objects = parser_link_objects_for_trace_inputs(mutated_binary["inputs"])
            object_entry = next(pair for pair in link_objects if pair[0] == expected_object)
            if mode == "wrong":
                if module.endswith("StrictJson"):
                    link_objects.append([
                        str(build_root / "ir/Unrelated/ParserDependency.c.o.export"),
                        "0000000000000000",
                    ])
                else:
                    object_entry[1] = "0000000000000000"
            elif mode == "missing":
                link_objects.remove(object_entry)
            elif module == PARSER_MODULE:
                link_info = next(
                    pair[1] for pair in mutated_binary["inputs"]
                    if pair[0] == f"{PARSER_MODULE}:linkInfo")
                more_link_objects = next(
                    pair for pair in link_info if pair[0] == "Module.moreLinkObjs")
                link_info.append(copy.deepcopy(more_link_objects))
            elif module.endswith("Schema"):
                link_info = next(
                    pair for pair in mutated_binary["inputs"]
                    if pair[0] == f"{PARSER_MODULE}:linkInfo")
                mutated_binary["inputs"].append(copy.deepcopy(link_info))
            else:
                link_objects.append(copy.deepcopy(object_entry))
            rejected(
                "source-object-link", f"{mode} {short_name} executable object link",
                lambda mutated_binary=mutated_binary: validate_parser_build_trace_data(
                    binary_path, mutated_binary, module_traces, object_traces,
                    build_root=build_root))

    for importer, imported in (
            (PARSER_MODULE, "HashSigTest.SLHDSA.ACVP.Schema"),
            ("HashSigTest.SLHDSA.ACVP.Schema", "HashSigTest.SLHDSA.ACVP.StrictJson")):
        for mode in ("wrong", "missing"):
            mutated_modules = copy.deepcopy(module_traces)
            trace = mutated_modules[importer]
            imports = module_direct_import_entries(trace["inputs"], importer)
            if mode == "wrong":
                imports[0][0] = imports[0][0].replace(imported, "Wrong.Import")
            else:
                imports.pop()
            rejected(
                "imports", f"{mode} structured import relationship {importer} -> {imported}",
                lambda mutated_modules=mutated_modules: validate(
                    selected_modules=mutated_modules))

    # SHA-256 output and before/after binding are tested independently of subprocess expectations.
    canonical_sha = hashlib.sha256(b"ordinary\n").hexdigest()
    for label, completed in (
            ("missing hash-helper record", subprocess.CompletedProcess([], 0, b"", b"")),
            ("short hash-helper record", subprocess.CompletedProcess([], 0, b"abcd\n", b"")),
            ("uppercase hash-helper record",
             subprocess.CompletedProcess([], 0, canonical_sha.upper().encode() + b"\n", b"")),
            ("hash-helper record without LF",
             subprocess.CompletedProcess([], 0, canonical_sha.encode(), b"")),
            ("extra hash-helper record",
             subprocess.CompletedProcess([], 0, canonical_sha.encode() + b"\nextra\n", b"")),
            ("nonzero hash helper",
             subprocess.CompletedProcess([], 7, canonical_sha.encode() + b"\n", b"failed\n"))):
        rejected(
            "sha-output-binding", label,
            lambda completed=completed: parse_sha256_helper_result(completed, "mutated helper"))
    for label, expected_hash, before_hash, after_hash in (
            ("wrong expected SHA-256", "0" * 64, canonical_sha, canonical_sha),
            ("wrong before SHA-256", canonical_sha, "0" * 64, canonical_sha),
            ("wrong after SHA-256", canonical_sha, canonical_sha, "0" * 64)):
        rejected(
            "sha-output-binding", label,
            lambda expected_hash=expected_hash, before_hash=before_hash,
            after_hash=after_hash: validate_sha256_binding(
                expected_hash, before_hash, after_hash))

    with tempfile.TemporaryDirectory(prefix="slhdsa-parser-output-types-", dir="/tmp") as temporary:
        type_root = Path(temporary)
        ordinary = type_root / "ordinary"
        ordinary.write_text("ordinary\n", encoding="utf-8")
        linked = type_root / "linked"
        os.symlink(ordinary.name, linked)
        rejected(
            "output-types", "symlink queried executable output",
            lambda: require_ordinary_file_under(linked, type_root, "mutated output"))
        fifo = type_root / "special.fifo"
        os.mkfifo(fifo)
        rejected(
            "output-types", "special queried executable output",
            lambda: require_ordinary_file_under(fifo, type_root, "mutated output"))

    # The checker SHA-256 mode must reject wrong arity, path scope, and non-ordinary inputs.
    with tempfile.TemporaryDirectory(prefix="slhdsa-sha256-helper-", dir="/tmp") as temporary:
        helper_parent = Path(temporary)
        helper_root = helper_parent / "root"
        helper_root.mkdir()
        ordinary = helper_root / "ordinary"
        ordinary.write_bytes(b"ordinary\n")
        outside = helper_parent / "outside"
        outside.write_bytes(b"outside\n")
        nested = helper_root / "nested"
        nested.mkdir()
        inside = helper_root / "inside"
        inside.mkdir()
        (inside / "ordinary").write_bytes(b"inside\n")
        intermediate_link = helper_root / "intermediate-link"
        os.symlink(inside.name, intermediate_link)
        linked = helper_root / "linked"
        os.symlink(ordinary.name, linked)
        fifo = helper_root / "special.fifo"
        os.mkfifo(fifo)
        checker = ROOT / "scripts/slhdsa/check-harness.py"
        completed = subprocess.run(
            ["python3", "-B", str(checker), "--sha256-ordinary-file",
             str(ordinary), str(helper_root)],
            cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            timeout=120, check=False)
        require(completed.returncode == 0
                and completed.stdout == canonical_sha.encode() + b"\n"
                and completed.stderr == b"",
                "S01: live SHA-256 helper did not emit its exact success record")
        rejected(
            "path-cli", "shared sibling parent escape",
            lambda: sha256_ordinary_file(helper_root / ".." / outside.name, helper_root))
        rejected(
            "path-cli", "shared nested parent escape",
            lambda: sha256_ordinary_file(nested / ".." / ".." / outside.name, helper_root))
        for label, args in (
                ("missing arguments", []),
                ("extra argument",
                 [str(ordinary), str(helper_root), str(ordinary), str(ordinary)]),
                ("directory input", [str(helper_root), str(helper_root)]),
                ("symlink input", [str(linked), str(helper_root)]),
                ("intermediate symlink input",
                 [str(intermediate_link / "ordinary"), str(helper_root)]),
                ("special input", [str(fifo), str(helper_root)]),
                ("path outside root", ["/etc/hosts", str(helper_root)]),
                ("sibling parent escape",
                 [str(helper_root / ".." / outside.name), str(helper_root)]),
                ("nested parent escape",
                 [str(nested / ".." / ".." / outside.name), str(helper_root)]),
                ("redundant dot input",
                 [str(helper_root) + "/./ordinary", str(helper_root)]),
                ("duplicate separator input",
                 [str(helper_root) + "//ordinary", str(helper_root)]),
                ("trailing separator input",
                 [str(ordinary) + "/", str(helper_root)]),
                ("trailing separator root",
                 [str(ordinary), str(helper_root) + "/"]),
                ("parent-component root",
                 [str(ordinary), str(helper_root / ".." / helper_root.name)]),
                ("relative input", ["ordinary", str(helper_root)]),
                ("relative root", [str(ordinary), "root"]),
                ("root-equal input", [str(helper_root), str(helper_root)]),
                ("aliased output record",
                 [str(ordinary), str(helper_root), str(helper_parent) + "/./digest"])):
            completed = subprocess.run(
                ["python3", "-B", str(checker), "--sha256-ordinary-file", *args],
                cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                timeout=120, check=False)
            require(completed.returncode != 0 and completed.stdout == b""
                    and completed.stderr != b"",
                    f"S01: SHA-256 helper accepted {label}")
            record_completed("path-cli")

    for package_level, label in (
            (False, "executable-level WrongSrc"),
            (True, "package-level inherited WrongSrc")):
        with tempfile.TemporaryDirectory(prefix="slhdsa-parser-srcdir-build-",
                                         dir="/tmp") as temporary:
            project_root = Path(temporary)
            write_srcdir_regression_project(project_root, package_level=package_level)
            canonical_source = project_root / PARSER_SOURCE_RELATIVE
            canonical_hash = hashlib.sha256(canonical_source.read_bytes()).hexdigest()
            translated = translate_lake_configuration(project_root)
            expect_s01_mutation_rejected(
                label + " translated configuration",
                lambda translated=translated: validate_translated_lake_data(translated))
            redirected_binary = query_default_parser_executable_path(project_root)
            redirected_run = subprocess.run(
                [str(redirected_binary)], cwd=project_root, stdout=subprocess.PIPE,
                stderr=subprocess.PIPE, timeout=30, check=False)
            require(redirected_run.returncode == 0
                    and redirected_run.stdout == PARSER_EXPECTED_STDOUT,
                    f"S01: {label} fixture did not reproduce exact 154-byte spoof output")
            first_parent = project_root / "first-private-parent"
            first_parent.mkdir(mode=0o700)
            expect_s01_mutation_rejected(
                label + " structured build-input trace",
                lambda: query_and_validate_fresh_parser_build(
                    project_root, build_root=first_parent / FRESH_BUILD_CHILD,
                    private_parent=first_parent,
                    module_specs={PARSER_MODULE: (PARSER_SOURCE_RELATIVE, canonical_hash)}))
            record_completed("wrong-srcdir")

            # A second absent root must observe the configuration change rather than stale traces.
            write_unredirected_regression_lakefile(project_root)
            second_parent = project_root / "second-private-parent"
            second_parent.mkdir(mode=0o700)
            repaired_binary, _repaired_hash = query_and_validate_fresh_parser_build(
                project_root, build_root=second_parent / FRESH_BUILD_CHILD,
                private_parent=second_parent,
                module_specs={PARSER_MODULE: (PARSER_SOURCE_RELATIVE, canonical_hash)})
            repaired_run = subprocess.run(
                [str(repaired_binary)], cwd=project_root, stdout=subprocess.PIPE,
                stderr=subprocess.PIPE, timeout=30, check=False)
            require(repaired_run.returncode == 0
                    and repaired_run.stdout == b"CANONICAL REPOSITORY SOURCE EXECUTED\n",
                    f"S01: {label} configuration-change query trusted a stale selected source")
            record_completed("stale")

    # Every kind of pre-existing proposed build root must fail before Lake is invoked.
    with tempfile.TemporaryDirectory(prefix="slhdsa-fresh-root-types-", dir="/tmp") as temporary:
        mutation_root = Path(temporary)
        for kind in ("empty-directory", "nonempty-directory", "ordinary-file", "symlink", "fifo"):
            parent = mutation_root / kind
            parent.mkdir(mode=0o700)
            proposed = parent / FRESH_BUILD_CHILD
            if kind == "empty-directory":
                proposed.mkdir()
            elif kind == "nonempty-directory":
                proposed.mkdir()
                (proposed / "contamination").write_text("cached\n", encoding="utf-8")
            elif kind == "ordinary-file":
                proposed.write_text("not a directory\n", encoding="utf-8")
            elif kind == "symlink":
                os.symlink(mutation_root, proposed)
            else:
                os.mkfifo(proposed)
            rejected(
                "fresh-root", f"pre-existing fresh build root: {kind}",
                lambda proposed=proposed, parent=parent:
                    validate_fresh_build_root_before(proposed, parent))

    query_parent = Path("/tmp/slhdsa-query-mutation-parent")
    expected_query_binary = query_parent / FRESH_BUILD_CHILD / "bin/slhdsa_acvp_parser"
    canonical_query = (json.dumps(str(expected_query_binary)) + "\n").encode()
    for label, completed in (
            ("nonzero fresh query", subprocess.CompletedProcess([], 7, b"", b"failed\n")),
            ("noisy fresh query",
             subprocess.CompletedProcess([], 0, canonical_query + b"noise\n", b"")),
            ("malformed fresh query", subprocess.CompletedProcess([], 0, b"{\n", b"")),
            ("fresh query outside root",
             subprocess.CompletedProcess([], 0, b'"/tmp/wrong/parser"\n', b"")),
            ("wrong-type fresh query", subprocess.CompletedProcess([], 0, b"null\n", b""))):
        rejected(
            "query-output", label,
            lambda completed=completed: parse_fresh_query_result(
                completed, expected_query_binary))

    # Exact r10 coherent-cache regression plus the earlier one-sided replacement cases.
    with tempfile.TemporaryDirectory(prefix="slhdsa-coherent-cache-regression-",
                                     dir="/tmp") as temporary:
        project_root = Path(temporary)
        write_three_module_regression_project(project_root)
        default_binary = query_default_parser_executable_path(project_root)
        default_build = project_root / ".lake/build"
        original_sha = sha256_ordinary_file(default_binary, default_build)
        trace_path = Path(str(default_binary) + ".trace")
        sidecar_path = Path(str(default_binary) + ".hash")

        wrong_output = project_root / "wrong-output-replacement"
        wrong_output.write_bytes(b"#!/bin/sh\nprintf '%s\\n' 'WRONG OUTPUT'\n")
        wrong_output.chmod(0o755)
        wrong_sha = sha256_ordinary_file(wrong_output, project_root)
        rejected(
            "replacement-cache", "r9 different-output executable SHA-256",
            lambda: validate_sha256_binding(original_sha, wrong_sha, wrong_sha))

        same_output = project_root / "same-output-replacement"
        same_output.write_bytes(
            b"#!/bin/sh\n"
            b"if [ -n \"${S01_REPLACEMENT_SENTINEL:-}\" ]; then "
            b": > \"$S01_REPLACEMENT_SENTINEL\"; fi\n"
            b"printf '%s\\n' 'SLH-DSA ACVP parser positive suite: PASS (16 cases)' "
            b"'SLH-DSA ACVP parser negative suite: PASS (52 cases)' "
            b"'SLH-DSA ACVP parser runtime gate: PASS (68 cases)'\n")
        same_output.chmod(0o755)
        shutil.copyfile(same_output, default_binary)
        default_binary.chmod(0o755)
        replacement_sha = sha256_ordinary_file(default_binary, default_build)
        require(replacement_sha != original_sha,
                "S01: coherent-cache replacement did not change executable SHA-256")
        rejected(
            "replacement-cache", "r9 same-output executable SHA-256",
            lambda: validate_sha256_binding(original_sha, replacement_sha, replacement_sha))

        # Lake's reusable query refreshes the sidecar token. Make the retained trace coherent too.
        require(query_default_parser_executable_path(project_root) == default_binary,
                "S01: coherent-cache query did not retain the replacement path")
        sidecar_token = sidecar_path.read_text(encoding="ascii")
        retained_trace = parse_strict_json_bytes(trace_path.read_bytes(), "retained trace")
        retained_trace["outputs"] = sidecar_token
        trace_path.write_text(json.dumps(retained_trace, separators=(",", ":")), encoding="utf-8")
        require(query_default_parser_executable_path(project_root) == default_binary
                and sha256_ordinary_file(default_binary, default_build) == replacement_sha,
                "S01: exact r10 coherent reusable query did not retain replacement bytes")
        old_binary_trace, old_module_traces, old_object_traces = load_parser_trace_data(
            default_build, default_binary)
        validate_parser_build_trace_data(
            default_binary, old_binary_trace, old_module_traces, old_object_traces,
            expected_root=project_root, build_root=default_build)
        validate_incremental_lake_metadata(
            old_binary_trace["outputs"], sidecar_path.read_text(encoding="ascii"))

        # The accepted gate ignores that coherent default state and builds into an absent child.
        private_parent = project_root / "accepted-private-parent"
        private_parent.mkdir(mode=0o700)
        fresh_build = private_parent / FRESH_BUILD_CHILD
        fresh_binary, fresh_sha = query_and_validate_fresh_parser_build(
            project_root, build_root=fresh_build, private_parent=private_parent)
        sentinel = project_root / "replacement-executed"
        run = subprocess.run(
            [str(fresh_binary)], cwd=project_root, stdout=subprocess.PIPE,
            stderr=subprocess.PIPE, timeout=30, check=False,
            env={**os.environ, "S01_REPLACEMENT_SENTINEL": str(sentinel)})
        require(run.returncode == 0 and run.stdout == PARSER_EXPECTED_STDOUT
                and not sentinel.exists()
                and fresh_binary != default_binary
                and fresh_binary.is_relative_to(fresh_build),
                "S01: fresh accepted gate ran or reused the coherent cached replacement "
                f"(status={run.returncode}, stdout={run.stdout!r}, stderr={run.stderr!r}, "
                f"sentinel={sentinel.exists()}, path={fresh_binary})")
        validate_sha256_binding(
            fresh_sha,
            sha256_ordinary_file(fresh_binary, fresh_build),
            sha256_ordinary_file(fresh_binary, fresh_build))
        record_completed("replacement-cache")

    require(observed_cases == PARSER_FOCUSED_CASE_COUNTS,
            "S01: focused parser category execution disagrees with its authoritative partition: "
            f"expected={PARSER_FOCUSED_CASE_COUNTS}, observed={observed_cases}")
    require(PARSER_FOCUSED_TOTAL == 234,
            "S01: focused parser authoritative partition arithmetic changed unexpectedly")
    print(f"S01 parser fresh-build mutation self-tests: PASS ({PARSER_FOCUSED_PARTITION})",
          file=sys.stderr)


def validate_s01_dependency_token(
        field: str,
        token: str,
        *,
        sources: dict[str, str] | None = None,
        lake_source: str | None = None) -> None:
    """Validate one typed token from active, comment-aware declaration/configuration state."""

    sources = load_s01_lean_sources() if sources is None else sources
    private_names = {"asObject", "field", "nestedPair", "parameterByName", "parsePromptJson",
                     "parseResultsJson", "requireKeys", "runAll", "runNegative", "runPositive",
                     "validatePair"}
    parts = token.split("|")
    kind = parts[0]
    if kind == "lean-public":
        require(field == "direct_dependencies" and len(parts) == 2
                and re.fullmatch(r"[A-Za-z_][A-Za-z0-9_'.]*(?:\.[A-Za-z_][A-Za-z0-9_']*)+",
                                 parts[1]) is not None,
                f"S01: invalid public direct-dependency token {token!r}")
        matches = source_declarations(sources).get(parts[1], [])
        require(len(matches) == 1 and matches[0][1].visibility == "public",
                f"S01: public token does not resolve to one active public source declaration: {token!r}")
        return
    if kind == "source-private-direct":
        require(len(parts) == 4,
                f"S01: invalid private source token {token!r}")
        relative, name, line_text = parts[1:]
        require(relative in {
            "HashSigTest/SLHDSA/ACVP/Schema.lean",
            "HashSigTest/SLHDSA/ACVP/ParserTests.lean",
        } and name in private_names and line_text.isdigit() and relative in sources,
                f"S01: private source token is outside the exact S01 anchor set: {token!r}")
        declarations = parse_s01_source_declarations(relative, sources[relative])
        matches = [declaration for declaration in declarations.values()
                   if declaration.short_name == name and declaration.line == int(line_text)]
        require(len(matches) == 1 and matches[0].visibility == "private"
                and matches[0].keyword == "def",
                f"S01: private source token does not anchor one active private def: {token!r}")
        return
    if kind == "root-entry-transitive":
        require(field == "reverse_dependencies" and len(parts) == 4,
                f"S01: root entry token has invalid direction or shape: {token!r}")
        relative, name, line_text = parts[1:]
        require(relative == "HashSigTest/SLHDSA/ACVP/ParserTests.lean"
                and name == "main" and line_text.isdigit() and relative in sources,
                f"S01: root entry token does not name the parser executable root: {token!r}")
        declaration = parse_s01_source_declarations(relative, sources[relative]).get("main")
        require(declaration is not None and declaration.line == int(line_text)
                and declaration.namespace == "" and declaration.visibility == "public"
                and declaration.keyword == "def",
                f"S01: root token is not one active root-level public def main: {token!r}")
        return
    if kind == "lake-exe-direct":
        require(field == "reverse_dependencies" and len(parts) == 2
                and parts[1] == "slhdsa_acvp_parser",
                f"S01: Lake executable token has invalid direction or target: {token!r}")
        if lake_source is None:
            lake_source = (ROOT / "lakefile.lean").read_text(encoding="utf-8")
        validate_lake_parser_mapping(lake_source)
        return
    raise CheckFailure(f"S01: unknown typed dependency token class: {token!r}")


def validate_s01_dependency_accounting() -> None:
    """Validate exact typed dependencies against active source/configuration semantics."""

    validate_s01_acvp_lean_pins()
    sources = load_s01_lean_sources()
    lake_source = (ROOT / "lakefile.lean").read_text(encoding="utf-8")
    validate_fresh_build_lake_source(lake_source)
    # Literal parsing is defense in depth; Lake's elaborated translation is authoritative.
    validate_lake_source_selector_surface(lake_source)
    validate_lake_parser_mapping(lake_source)
    validate_translated_lake_parser_mapping()
    print("INFO: elaborated Lake configuration audit: PASS "
          "(slhdsa_acvp_parser -> HashSigTest.SLHDSA.ACVP.ParserTests)")
    prior_main = "HashSigTest.SLHDSA.ACVP.ParserTests.main"

    for declaration_id, record in ACVP_DEPENDENCY_RECORDS.items():
        require(record["visibility"] in {"public", "public-root"}
                and isinstance(record["name"], str),
                f"S01: static ACVP root record is invalid: {declaration_id}")
        for field in ("direct_dependencies", "reverse_dependencies"):
            tokens = record[field]
            require(prior_main not in tokens,
                    f"S01: {declaration_id} retains the nonexistent qualified main spelling")
            for token in tokens:
                validate_s01_dependency_token(
                    field, token, sources=sources, lake_source=lake_source)
def run_external_lean_probe(names: list[str]) -> subprocess.CompletedProcess[str]:
    require(names and len(names) == len(set(names)),
            "S01: external Lean probe names must be nonempty and unique")
    source = "import HashSigTest.SLHDSA.ACVP.ParserTests\n\n" + \
        "\n".join(f"#check {name}" for name in names) + "\n"
    with tempfile.TemporaryDirectory(prefix="slhdsa-dependency-probe-", dir="/tmp") as temporary:
        probe = Path(temporary) / "DependencyProbe.lean"
        probe.write_text(source, encoding="utf-8")
        return subprocess.run(
            ["lake", "env", "lean", str(probe)], cwd=ROOT, text=True,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=120, check=False,
            env={**os.environ, "PYTHONDONTWRITEBYTECODE": "1"})


def validate_elaborated_resolvable_names(names: list[str]) -> None:
    completed = run_external_lean_probe(names)
    require(completed.returncode == 0,
            "S01: external Lean public/root probe failed:\n" +
            (completed.stdout + completed.stderr)[-4000:])


def validate_elaborated_unresolvable_names(names: list[str]) -> None:
    completed = run_external_lean_probe(names)
    output = completed.stdout + completed.stderr
    require(completed.returncode != 0,
            "S01: external Lean private/false-name probe unexpectedly succeeded")
    for name in names:
        require(f"Unknown identifier `{name}`" in output,
                f"S01: external Lean probe did not reject exact private/false name {name}")


def elaborated_dependency_probe_names() -> tuple[list[str], list[str]]:
    validate_s01_dependency_accounting()
    public_names: set[str] = set()
    private_names: set[str] = set()
    sources = load_s01_lean_sources()
    parsed = {relative: parse_s01_source_declarations(relative, source)
              for relative, source in sources.items()}
    for declaration_id, record in ACVP_DEPENDENCY_RECORDS.items():
        require(record["visibility"] in {"public", "public-root"},
                f"S01: elaborated probe root is not public: {declaration_id}")
        public_names.add(record["name"])
        for field in ("direct_dependencies", "reverse_dependencies"):
            for token in record[field]:
                parts = token.split("|")
                if parts[0] == "lean-public":
                    public_names.add(parts[1])
                elif parts[0] == "root-entry-transitive":
                    public_names.add(parts[2])
                elif parts[0] == "source-private-direct":
                    relative, short_name, line_text = parts[1:]
                    matches = [declaration for declaration in parsed[relative].values()
                               if declaration.short_name == short_name
                               and declaration.line == int(line_text)]
                    require(len(matches) == 1 and matches[0].visibility == "private",
                            f"S01: cannot derive private external spelling from {token}")
                    private_names.add(matches[0].fqname)
    private_names.update({
        "HashSigTest.SLHDSA.ACVP.ParserTests.main",
        "SLHDSA.Test.ACVP.ParserTests.main",
    })
    return sorted(public_names), sorted(private_names)


def check_elaborated_s01_dependencies() -> None:
    public_names, private_names = elaborated_dependency_probe_names()
    validate_elaborated_resolvable_names(public_names)
    mutated_names = [name for name in public_names if name != "SLHDSA.Test.ACVP.ParamInfo"]
    mutated_names.append("Does.Not.Exist")
    mutated_names.sort()
    expect_s01_mutation_rejected(
        "nonexistent public declaration in external Lean environment",
        lambda: validate_elaborated_resolvable_names(mutated_names))
    validate_elaborated_unresolvable_names(private_names)
    print("ACVP elaborated dependency probe: PASS "
          f"({len(public_names)} public/root resolved; {len(private_names)} private/false rejected; "
          "Does.Not.Exist mutation rejected)")


def check_acvp_dependency_sources() -> None:
    validate_s01_dependency_accounting()

    expect_s01_mutation_rejected(
        "prior qualified parser-main dependency spelling",
        lambda: validate_s01_dependency_token(
            "reverse_dependencies", "HashSigTest.SLHDSA.ACVP.ParserTests.main"))
    expect_s01_mutation_rejected(
        "unqualified private helper dependency",
        lambda: validate_s01_dependency_token(
            "direct_dependencies", "SLHDSA.Test.ACVP.validatePair"))
    expect_s01_mutation_rejected(
        "nonexistent private helper source anchor",
        lambda: validate_s01_dependency_token(
            "direct_dependencies",
            "source-private-direct|HashSigTest/SLHDSA/ACVP/Schema.lean|missingPromptJson|312"))
    expect_s01_mutation_rejected(
        "transitive root token in direct-dependency direction",
        lambda: validate_s01_dependency_token(
            "direct_dependencies",
            "root-entry-transitive|HashSigTest/SLHDSA/ACVP/ParserTests.lean|main|205"))
    expect_s01_mutation_rejected(
        "false private helper source line",
        lambda: validate_s01_dependency_token(
            "direct_dependencies",
            "source-private-direct|HashSigTest/SLHDSA/ACVP/Schema.lean|validatePair|376"))
    expect_s01_mutation_rejected(
        "false private helper source path",
        lambda: validate_s01_dependency_token(
            "direct_dependencies",
            "source-private-direct|HashSigTest/SLHDSA/ACVP/../Schema.lean|validatePair|377"))
    expect_s01_mutation_rejected(
        "nonexistent public source declaration",
        lambda: validate_s01_dependency_token(
            "direct_dependencies", "lean-public|Does.Not.Exist"))

    sources = load_s01_lean_sources()
    schema_path = "HashSigTest/SLHDSA/ACVP/Schema.lean"
    schema_lines = sources[schema_path].splitlines()
    require(schema_lines[376].startswith("private def validatePair"),
            "S01: private-comment mutation target moved")
    commented_sources = dict(sources)
    commented_lines = list(schema_lines)
    commented_lines[376] = f"/- {commented_lines[376]} -/"
    commented_sources[schema_path] = "\n".join(commented_lines) + "\n"
    expect_s01_mutation_rejected(
        "private declaration anchor wholly inside a block comment",
        lambda: validate_s01_dependency_token(
            "direct_dependencies",
            "source-private-direct|HashSigTest/SLHDSA/ACVP/Schema.lean|validatePair|377",
            sources=commented_sources))

    parser_path = "HashSigTest/SLHDSA/ACVP/ParserTests.lean"
    parser_lines = sources[parser_path].splitlines()
    require(parser_lines[202] == "" and parser_lines[204].startswith("def main"),
            "S01: Fake.main mutation targets moved")
    fake_sources = dict(sources)
    fake_lines = list(parser_lines)
    fake_lines[202] = "namespace Fake"
    fake_lines.append("end Fake")
    fake_sources[parser_path] = "\n".join(fake_lines) + "\n"
    expect_s01_mutation_rejected(
        "namespace-shifted Fake.main root anchor",
        lambda: validate_s01_dependency_token(
            "reverse_dependencies",
            "root-entry-transitive|HashSigTest/SLHDSA/ACVP/ParserTests.lean|main|205",
            sources=fake_sources))
    expect_s01_mutation_rejected(
        "namespace-state underflow",
        lambda: parse_s01_source_declarations("mutation.lean", "end Ghost\n"))
    expect_s01_mutation_rejected(
        "unclosed namespace state",
        lambda: parse_s01_source_declarations("mutation.lean", "namespace Ghost\n"))
    expect_s01_mutation_rejected(
        "unterminated block-comment state",
        lambda: parse_s01_source_declarations("mutation.lean", "/- never closed\n"))

    quoted_sources = dict(sources)
    quoted_lines = list(schema_lines)
    quoted_lines[374:377] = [
        'macro "unusedPairAnchor" : command => `(',
        "",
        "private def validatePair (prompt : Prompt) (results : Results) : "
        "Except String Unit := pure ())",
        "private opaque validatePair (prompt : Prompt) (results : Results) : "
        "Except String Unit := do",
    ]
    require(quoted_lines[376].startswith("private def validatePair")
            and quoted_lines[377].startswith("private opaque validatePair"),
            "S01: quoted/private-opaque mutation did not preserve its exact line anchors")
    quoted_sources[schema_path] = "\n".join(quoted_lines) + "\n"
    expect_s01_mutation_rejected(
        "r7 quoted line-377 private def plus active line-378 private opaque helper",
        lambda: validate_s01_dependency_token(
            "direct_dependencies",
            "source-private-direct|HashSigTest/SLHDSA/ACVP/Schema.lean|validatePair|377",
            sources=quoted_sources))
    expect_s01_mutation_rejected(
        "nested Lean syntax quotation",
        lambda: parse_s01_source_declarations(
            "mutation.lean", "`(`(private def hidden : Nat := 1))\n"))
    expect_s01_mutation_rejected(
        "malformed unclosed Lean syntax quotation",
        lambda: parse_s01_source_declarations(
            "mutation.lean", "`(private def hidden : Nat := 1\n"))
    for command in ("macro", "syntax", "elab", "run_cmd"):
        expect_s01_mutation_rejected(
            f"active unsupported {command} command family",
            lambda command=command: parse_s01_source_declarations(
                "mutation.lean", f"{command} unsupported_surface\n"))

    lake_source = (ROOT / "lakefile.lean").read_text(encoding="utf-8")
    parser_stanza = (
        "lean_exe slhdsa_acvp_parser where\n"
        "  root := `HashSigTest.SLHDSA.ACVP.ParserTests"
    )
    require(lake_source.count(parser_stanza) == 1,
            "S01: parser Lake stanza mutation target is not unique")
    expect_s01_mutation_rejected(
        "commented-out parser Lake mapping",
        lambda: validate_lake_parser_mapping(
            lake_source.replace(parser_stanza, f"/- {parser_stanza} -/", 1)))
    expect_s01_mutation_rejected(
        "wrong active parser Lake root",
        lambda: validate_lake_parser_mapping(lake_source.replace(
            parser_stanza,
            "lean_exe slhdsa_acvp_parser where\n"
            "  root := `HashSigTest.SLHDSA.C13KAT", 1)))
    expect_s01_mutation_rejected(
        "duplicate active parser Lake mapping",
        lambda: validate_lake_parser_mapping(
            lake_source + "lean_exe slhdsa_acvp_parser where\n"
            "  root := `HashSigTest.SLHDSA.ACVP.ParserTests\n"))
    shadow_permutation = lake_source.replace(
        parser_stanza,
        f"/- {parser_stanza} -/\n"
        "lean_exe slhdsa_acvp_parser where\n"
        "  root := `HashSigTest.SLHDSA.C13KAT", 1)
    shadow_permutation = shadow_permutation.replace(
        "root := `HashSigTest.SLHDSA.C13KAT",
        "root := `HashSigTest.SLHDSA.Sha2KAT", 1)
    shadow_permutation = shadow_permutation.replace(
        "root := `HashSigTest.SLHDSA.Sha2KAT",
        "root := `VCVioTest.Smoke", 1)
    shadow_permutation = shadow_permutation.replace(
        "root := `VCVioTest.Smoke",
        "root := `HashSigTest.SLHDSA.ACVP.ParserTests", 1)
    expect_s01_mutation_rejected(
        "r6 comment-shadowed four-root permutation",
        lambda: validate_lake_parser_mapping(shadow_permutation))

    translated = translate_lake_configuration()
    validate_translated_lake_data(translated)
    missing_parser = copy.deepcopy(translated)
    missing_parser["lean_exe"] = [entry for entry in missing_parser["lean_exe"]
                                  if entry.get("name") != "slhdsa_acvp_parser"]
    expect_s01_mutation_rejected(
        "translated Lake configuration missing parser target",
        lambda: validate_translated_lake_data(missing_parser))
    wrong_type = copy.deepcopy(translated)
    next(entry for entry in wrong_type["lean_exe"]
         if entry.get("name") == "slhdsa_acvp_parser")["root"] = 7
    expect_s01_mutation_rejected(
        "translated Lake parser root has wrong TOML type",
        lambda: validate_translated_lake_data(wrong_type))
    wrong_root = copy.deepcopy(translated)
    next(entry for entry in wrong_root["lean_exe"]
         if entry.get("name") == "slhdsa_acvp_parser")["root"] = "Wrong.Root"
    expect_s01_mutation_rejected(
        "translated Lake parser has wrong elaborated root",
        lambda: validate_translated_lake_data(wrong_root))
    duplicate_parser = copy.deepcopy(translated)
    parser_entry = next(entry for entry in duplicate_parser["lean_exe"]
                        if entry.get("name") == "slhdsa_acvp_parser")
    duplicate_parser["lean_exe"].append(copy.deepcopy(parser_entry))
    expect_s01_mutation_rejected(
        "translated Lake configuration has duplicate parser target",
        lambda: validate_translated_lake_data(duplicate_parser))

    macro_lakefile = """import Lake
open Lake DSL
package QuoteProbe
macro "wrongTarget" n:identOrStr field:ident r:term : command => `(lean_exe $n where $field := $r)
wrongTarget slhdsa_acvp_parser root `Wrong.Root
macro "unusedExpected" : command => `(
lean_exe slhdsa_acvp_parser where
  root := `HashSigTest.SLHDSA.ACVP.ParserTests
)
"""
    # This locks the exact r7 disagreement: the old literal layer sees the quoted expected root,
    # while Lake elaboration registers Wrong.Root and the authoritative layer rejects it.
    validate_lake_parser_mapping(macro_lakefile)
    expect_s01_mutation_rejected(
        "r7 Lake macro/quotation source-selector surface",
        lambda: validate_lake_source_selector_surface(macro_lakefile))
    with tempfile.TemporaryDirectory(prefix="slhdsa-r7-lake-quote-", dir="/tmp") as temporary:
        macro_root = Path(temporary)
        (macro_root / "lakefile.lean").write_text(macro_lakefile, encoding="utf-8")
        (macro_root / "lean-toolchain").write_bytes((ROOT / "lean-toolchain").read_bytes())
        translated_macro = translate_lake_configuration(macro_root)
        require(any(entry.get("name") == "slhdsa_acvp_parser"
                    and entry.get("root") == "Wrong.Root"
                    for entry in translated_macro.get("lean_exe", [])),
                "S01: reconstructed r7 Lake macro project did not elaborate Wrong.Root")
        expect_s01_mutation_rejected(
            "r7 quoted expected Lake stanza plus active macro Wrong.Root",
            lambda: validate_translated_lake_data(translated_macro))

    for package_level, label in (
            (False, "r8 executable-level srcDir WrongSrc"),
            (True, "r8 package-level inherited srcDir WrongSrc")):
        with tempfile.TemporaryDirectory(prefix="slhdsa-r8-lake-srcdir-",
                                         dir="/tmp") as temporary:
            source_root = Path(temporary)
            write_srcdir_regression_project(source_root, package_level=package_level)
            redirected_source = (source_root / "lakefile.lean").read_text(encoding="utf-8")
            expect_s01_mutation_rejected(
                f"{label} literal selector surface",
                lambda redirected_source=redirected_source:
                validate_lake_source_selector_surface(redirected_source))
            redirected = translate_lake_configuration(source_root)
            parser_record = next(entry for entry in redirected["lean_exe"]
                                 if entry.get("name") == "slhdsa_acvp_parser")
            if package_level:
                require(redirected.get("srcDir") == "WrongSrc"
                        and "srcDir" not in parser_record,
                        "S01: Lake did not expose inherited package srcDir semantics")
            else:
                require("srcDir" not in redirected
                        and parser_record.get("srcDir") == "WrongSrc",
                        "S01: Lake did not expose executable srcDir semantics")
            expect_s01_mutation_rejected(
                label, lambda redirected=redirected:
                validate_translated_lake_data(redirected))

    for selector, label in (
            (".", "dot source-directory alias"),
            ("./", "dot-slash source-directory alias"),
            ("../outside", "parent-traversal source directory"),
            ("/tmp/slhdsa-r9-absolute-source", "absolute source directory")):
        with tempfile.TemporaryDirectory(prefix="slhdsa-r9-lake-srcdir-alias-",
                                         dir="/tmp") as temporary:
            alias_root = Path(temporary)
            (alias_root / "lakefile.lean").write_text(
                "import Lake\nopen Lake DSL\npackage AliasProbe\n"
                "lean_exe slhdsa_acvp_parser where\n"
                f"  root := `{PARSER_MODULE}\n"
                f"  srcDir := \"{selector}\"\n",
                encoding="utf-8")
            (alias_root / "lean-toolchain").write_bytes((ROOT / "lean-toolchain").read_bytes())
            alias_source = (alias_root / "lakefile.lean").read_text(encoding="utf-8")
            expect_s01_mutation_rejected(
                label, lambda alias_source=alias_source:
                validate_lake_source_selector_surface(alias_source))
            alias_data = translate_lake_configuration(alias_root)
            alias_record = next(entry for entry in alias_data["lean_exe"]
                                if entry.get("name") == "slhdsa_acvp_parser")
            if selector == ".":
                require("srcDir" not in alias_record,
                        f"S01: Lake 5 did not normalize {label} as documented")
                validate_translated_lake_data(alias_data)
            else:
                require(alias_record.get("srcDir") == selector,
                        f"S01: Lake did not preserve {label} in translated data")
                expect_s01_mutation_rejected(
                    label, lambda alias_data=alias_data:
                    validate_translated_lake_data(alias_data))

    for field in ("moreLeanArgs", "weakLeanArgs"):
        with tempfile.TemporaryDirectory(prefix="slhdsa-r9-lake-args-",
                                         dir="/tmp") as temporary:
            argument_root = Path(temporary)
            (argument_root / "lakefile.lean").write_text(
                "import Lake\nopen Lake DSL\n"
                "package ArgumentProbe where\n"
                f"  {field} := #[\"-R\", \"WrongSrc\"]\n"
                "lean_exe slhdsa_acvp_parser where\n"
                f"  root := `{PARSER_MODULE}\n",
                encoding="utf-8")
            (argument_root / "lean-toolchain").write_bytes(
                (ROOT / "lean-toolchain").read_bytes())
            argument_source = (argument_root / "lakefile.lean").read_text(encoding="utf-8")
            expect_s01_mutation_rejected(
                f"package {field} source/path selector",
                lambda argument_source=argument_source:
                validate_lake_source_selector_surface(argument_source))
            argument_data = translate_lake_configuration(argument_root)
            require(argument_data.get(field) == ["-R", "WrongSrc"],
                    f"S01: Lake did not preserve package {field} in translated data")
            expect_s01_mutation_rejected(
                f"translated package {field} source/path selector",
                lambda argument_data=argument_data:
                validate_translated_lake_data(argument_data))

    wrong_srcdir_type = copy.deepcopy(translated)
    next(entry for entry in wrong_srcdir_type["lean_exe"]
         if entry.get("name") == "slhdsa_acvp_parser")["srcDir"] = 7
    expect_s01_mutation_rejected(
        "non-string translated executable srcDir",
        lambda: validate_translated_lake_data(wrong_srcdir_type))

    print("INFO: S01 declaration/source/Lake mutation self-tests: PASS "
          "(23 source/token/static-Lake, 9 Lake-selector-source, and 13 translated-Lake rejected)")


EXPECTED_TUPLES = {
    ("SHA2", 16, 63, 7, 9, 12, 14, 4, 30, 1, 32, 64, 7856),
    ("SHAKE", 16, 63, 7, 9, 12, 14, 4, 30, 1, 32, 64, 7856),
    ("SHA2", 16, 66, 22, 3, 6, 33, 4, 34, 1, 32, 64, 17088),
    ("SHAKE", 16, 66, 22, 3, 6, 33, 4, 34, 1, 32, 64, 17088),
    ("SHA2", 24, 63, 7, 9, 14, 17, 4, 39, 3, 48, 96, 16224),
    ("SHAKE", 24, 63, 7, 9, 14, 17, 4, 39, 3, 48, 96, 16224),
    ("SHA2", 24, 66, 22, 3, 8, 33, 4, 42, 3, 48, 96, 35664),
    ("SHAKE", 24, 66, 22, 3, 8, 33, 4, 42, 3, 48, 96, 35664),
    ("SHA2", 32, 64, 8, 8, 14, 22, 4, 47, 5, 64, 128, 29792),
    ("SHAKE", 32, 64, 8, 8, 14, 22, 4, 47, 5, 64, 128, 29792),
    ("SHA2", 32, 68, 17, 4, 9, 35, 4, 49, 5, 64, 128, 49856),
    ("SHAKE", 32, 68, 17, 4, 9, 35, 4, 49, 5, 64, 128, 49856),
}

EXPECTED_FIPS_ROWS = [
    ("SLH-DSA-SHA2-128s", "SHA2", 16, 63, 7, 9, 12, 14, 4, 30, 1, 32, 64, 7856),
    ("SLH-DSA-SHAKE-128s", "SHAKE", 16, 63, 7, 9, 12, 14, 4, 30, 1, 32, 64, 7856),
    ("SLH-DSA-SHA2-128f", "SHA2", 16, 66, 22, 3, 6, 33, 4, 34, 1, 32, 64, 17088),
    ("SLH-DSA-SHAKE-128f", "SHAKE", 16, 66, 22, 3, 6, 33, 4, 34, 1, 32, 64, 17088),
    ("SLH-DSA-SHA2-192s", "SHA2", 24, 63, 7, 9, 14, 17, 4, 39, 3, 48, 96, 16224),
    ("SLH-DSA-SHAKE-192s", "SHAKE", 24, 63, 7, 9, 14, 17, 4, 39, 3, 48, 96, 16224),
    ("SLH-DSA-SHA2-192f", "SHA2", 24, 66, 22, 3, 8, 33, 4, 42, 3, 48, 96, 35664),
    ("SLH-DSA-SHAKE-192f", "SHAKE", 24, 66, 22, 3, 8, 33, 4, 42, 3, 48, 96, 35664),
    ("SLH-DSA-SHA2-256s", "SHA2", 32, 64, 8, 8, 14, 22, 4, 47, 5, 64, 128, 29792),
    ("SLH-DSA-SHAKE-256s", "SHAKE", 32, 64, 8, 8, 14, 22, 4, 47, 5, 64, 128, 29792),
    ("SLH-DSA-SHA2-256f", "SHA2", 32, 68, 17, 4, 9, 35, 4, 49, 5, 64, 128, 49856),
    ("SLH-DSA-SHAKE-256f", "SHAKE", 32, 68, 17, 4, 9, 35, 4, 49, 5, 64, 128, 49856),
]

EXPECTED_GRAMMARS = {
    "SHAKE_all_n": {
        "Hmsg": "SHAKE256(R || PK.seed || PK.root || M, 8m)",
        "PRF": "SHAKE256(PK.seed || ADRS || SK.seed, 8n)",
        "PRFmsg": "SHAKE256(SK.prf || opt_rand || M, 8n)",
        "F": "SHAKE256(PK.seed || ADRS || M1, 8n)",
        "H": "SHAKE256(PK.seed || ADRS || M2, 8n)",
        "Tl": "SHAKE256(PK.seed || ADRS || Ml, 8n)",
    },
    "SHA2_n16": {
        "Hmsg": "MGF1-SHA-256(R || PK.seed || SHA-256(R || PK.seed || PK.root || M), m)",
        "PRF": "Trunc_n(SHA-256(PK.seed || toByte(0,64-n) || ADRS_c || SK.seed))",
        "PRFmsg": "Trunc_n(HMAC-SHA-256(SK.prf, opt_rand || M))",
        "F": "Trunc_n(SHA-256(PK.seed || toByte(0,64-n) || ADRS_c || M1))",
        "H": "Trunc_n(SHA-256(PK.seed || toByte(0,64-n) || ADRS_c || M2))",
        "Tl": "Trunc_n(SHA-256(PK.seed || toByte(0,64-n) || ADRS_c || Ml))",
    },
    "SHA2_n24_n32": {
        "Hmsg": "MGF1-SHA-512(R || PK.seed || SHA-512(R || PK.seed || PK.root || M), m)",
        "PRF": "Trunc_n(SHA-256(PK.seed || toByte(0,64-n) || ADRS_c || SK.seed))",
        "PRFmsg": "Trunc_n(HMAC-SHA-512(SK.prf, opt_rand || M))",
        "F": "Trunc_n(SHA-256(PK.seed || toByte(0,64-n) || ADRS_c || M1))",
        "H": "Trunc_n(SHA-512(PK.seed || toByte(0,128-n) || ADRS_c || M2))",
        "Tl": "Trunc_n(SHA-512(PK.seed || toByte(0,128-n) || ADRS_c || Ml))",
    },
}


def validate_fips_profile_data(data: Any) -> None:
    require(isinstance(data, dict) and set(data) == {
        "schema_version", "authority", "parameter_sets", "external_api",
        "primitive_grammars",
    }, "fips205-profile.json: exact top-level keys")
    require(data["schema_version"] == 1, "fips205-profile.json: schema version")
    require(data["authority"] == FIPS205_AUTHORITY,
            "fips205-profile.json: exact authority classification")
    rows = data.get("parameter_sets")
    require(isinstance(rows, list) and len(rows) == 12, "fips205-profile.json: 12 sets required")
    names = [row.get("name") for row in rows]
    require(len(set(names)) == 12 and all(isinstance(name, str) for name in names),
            "fips205-profile.json: unique names required")
    actual = set()
    for row in rows:
        require(set(row) == {"name", "family", "n", "h", "d", "hp", "a", "k", "lgw", "m",
                             "category", "public_key_bytes", "secret_key_bytes", "signature_bytes"},
                f"fips205-profile.json: fields for {row.get('name')}")
        require(row["h"] == row["d"] * row["hp"], f"fips205-profile.json: h=d*hp for {row['name']}")
        require(row["public_key_bytes"] == 2 * row["n"] and row["secret_key_bytes"] == 4 * row["n"],
                f"fips205-profile.json: key sizes for {row['name']}")
        expected_name = f"SLH-DSA-{row['family']}-{8 * row['n']}{'s' if row['signature_bytes'] in {7856, 16224, 29792} else 'f'}"
        require(row["name"] == expected_name, f"fips205-profile.json: inconsistent name {row['name']}")
        actual.add(tuple(row[key] for key in ("family", "n", "h", "d", "hp", "a", "k", "lgw",
                                                "m", "category", "public_key_bytes",
                                                "secret_key_bytes", "signature_bytes")))
    ordered = [tuple(row[key] for key in (
        "name", "family", "n", "h", "d", "hp", "a", "k", "lgw", "m", "category",
        "public_key_bytes", "secret_key_bytes", "signature_bytes")) for row in rows]
    require(ordered == EXPECTED_FIPS_ROWS,
            "fips205-profile.json: ordered Table-2 row mismatch")
    require(actual == EXPECTED_TUPLES, "fips205-profile.json: Table-2 tuple mismatch")
    api = data.get("external_api")
    require(isinstance(api, dict) and set(api) == {
        "max_context_bytes", "pure_m_prime", "prehash_m_prime", "prehashes_shown_by_fips",
        "other_prehashes", "randomness",
    }, "fips205-profile.json: exact external API keys")
    require(api["max_context_bytes"] == 255,
            "fips205-profile.json: context limit")
    require(api.get("pure_m_prime") == "toByte(0,1) || toByte(|ctx|,1) || ctx || M",
            "fips205-profile.json: pure M' grammar")
    require(api.get("prehash_m_prime") ==
            "toByte(1,1) || toByte(|ctx|,1) || ctx || DER(OID(PH)) || PH(M)",
            "fips205-profile.json: pre-hash M' grammar")
    prehashes = api.get("prehashes_shown_by_fips")
    require(isinstance(prehashes, list) and len(prehashes) == 4,
            "fips205-profile.json: four enumerated pre-hashes required")
    expected_oids = [
        ("SHA-256", "2.16.840.1.101.3.4.2.1", "0609608648016503040201", 256, 32, (1,)),
        ("SHA-512", "2.16.840.1.101.3.4.2.3", "0609608648016503040203", 512, 64, (1, 3, 5)),
        ("SHAKE128", "2.16.840.1.101.3.4.2.11", "060960864801650304020B", 256, 32, (1,)),
        ("SHAKE256", "2.16.840.1.101.3.4.2.12", "060960864801650304020C", 512, 64, (1, 3, 5)),
    ]
    for row in prehashes:
        require(set(row) == {"name", "oid", "der_oid_hex", "output_bits", "output_bytes",
                             "eligible_categories"},
                f"fips205-profile.json: pre-hash fields for {row.get('name')}")
    actual_oids = [(row["name"], row["oid"], row["der_oid_hex"], row["output_bits"],
                    row["output_bytes"], tuple(row["eligible_categories"])) for row in prehashes]
    require(actual_oids == expected_oids, "fips205-profile.json: OID/digest/eligibility mismatch")
    require(api["other_prehashes"] == FIPS205_OTHER_PREHASHES,
            "fips205-profile.json: exact other-prehash policy")
    require(api["randomness"] == FIPS205_RANDOMNESS,
            "fips205-profile.json: exact deterministic/hedged randomness rule")
    grammars = data.get("primitive_grammars")
    require(grammars == EXPECTED_GRAMMARS,
            "fips205-profile.json: exact primitive grammar mismatch")


def check_fips_profile() -> None:
    path = DOCS / "matrices/fips205-profile.json"
    raw = path.read_bytes()
    require(len(raw) == FIPS205_PROFILE_SIZE
            and hashlib.sha256(raw).hexdigest() == FIPS205_PROFILE_SHA256,
            "fips205-profile.json: exact canonical byte pin mismatch")
    try:
        data = json.loads(raw)
    except (UnicodeError, json.JSONDecodeError) as error:
        raise CheckFailure(f"fips205-profile.json: invalid JSON: {error}") from error
    validate_fips_profile_data(data)


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def git_revision(path: Path) -> str:
    result = subprocess.run(["git", "-C", str(path), "rev-parse", "HEAD"], check=False,
                            capture_output=True, text=True)
    require(result.returncode == 0, f"cannot read git revision at {path}")
    return result.stdout.strip()


def git_revision_is_ancestor(path: Path, revision: str) -> bool:
    if not re.fullmatch(r"[0-9a-f]{40}", revision):
        return False
    result = subprocess.run(
        ["git", "-C", str(path), "merge-base", "--is-ancestor", revision, "HEAD"],
        check=False, capture_output=True, text=True)
    return result.returncode == 0


def source_tree_composite_digest(composite: dict[str, Any], root: Path) -> str:
    require(composite.get("id") == "vcvio-slh-dsa-lean-tree"
            and composite.get("algorithm") == "sha256-of-sha256sum-manifest-v1"
            and composite.get("working_directory") == "repository root"
            and composite.get("manifest_line") ==
                "<lowercase-file-sha256><two ASCII spaces><repository-relative-path><LF>",
            "reference-manifest.json: composite schema")
    require(tuple(composite.get("globs_in_order", ())) == S02_SOURCE_GLOBS,
            "reference-manifest.json: exact source-tree glob recipe mismatch")
    require(composite.get("original_command") == S02_SOURCE_COMMAND
            and composite.get("deterministic_command") == S02_SOURCE_DETERMINISTIC_COMMAND,
            "reference-manifest.json: source-tree command/glob recipe mismatch")
    manifest = bytearray()
    matched: list[str] = []
    for pattern in S02_SOURCE_GLOBS:
        paths = sorted(root.glob(pattern), key=lambda item: item.as_posix())
        require(paths, f"reference-manifest.json: empty composite glob {pattern}")
        for path in paths:
            rel = path.relative_to(root).as_posix()
            matched.append(rel)
            manifest.extend(f"{sha256_file(path)}  {rel}\n".encode("ascii"))
    require(len(matched) == len(set(matched)),
            "reference-manifest.json: duplicate composite path")
    return hashlib.sha256(manifest).hexdigest()


def check_source_tree_mutation(composite: dict[str, Any]) -> None:
    with tempfile.TemporaryDirectory(prefix="slhdsa-source-composite-") as temporary:
        fixture = Path(temporary)
        for pattern in S02_SOURCE_GLOBS:
            for source in sorted(ROOT.glob(pattern), key=lambda item: item.as_posix()):
                relative = source.relative_to(ROOT)
                target = fixture / relative
                target.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(source, target)
        mutated = fixture / "HashSig/SLHDSA/Security/Architecture.lean"
        mutated.write_bytes(mutated.read_bytes() + b"\n-- controlled provenance mutation\n")
        try:
            require(source_tree_composite_digest(composite, fixture) == composite.get("sha256"),
                    "reference-manifest.json: source-tree composite mismatch")
        except CheckFailure as error:
            require(str(error) == "reference-manifest.json: source-tree composite mismatch",
                    "reference-manifest.json: Security-source mutation failed unexpectedly")
        else:
            raise CheckFailure(
                "reference-manifest.json: Security-source mutation did not invalidate composite")
    print("INFO: source-tree Security-byte mutation regression: PASS")


def check_s04_primitive_projection() -> None:
    data = read_json(ROOT / "HashSigTest/SLHDSA/PrimitiveVectors/vectors.json")
    fips202 = data.get("sources", {}).get("fips202")
    require(fips202 == {
        "url": "https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.202.pdf",
        "size_bytes": 1459683,
        "sha256": "1592607831ff0908cc590632ce371c6c95e94025bb1a0c8ae90a4d0ec1ed025e",
        "locator": "Section 6.2 SHAKE; SHAKE256 capacity 512 and 1088-bit rate",
        "license": ("NIST-authored U.S. government work; attribution and no-endorsement "
                    "boundary retained in NOTICE.md"),
    }, "S04 primitive projection: exact FIPS 202 authority record mismatch")
    derivation = data.get("derivation_tools", {}).get("python_hashlib")
    require(derivation == {
        "tool": "Python 3.12.3 hashlib.shake_256",
        "method": ("hashlib.shake_256(bytes.fromhex('61') * input_len_bytes)."
                   "hexdigest(out_len)"),
        "corroboration": ("OpenSSL 3.0.13 dgst -shake256 -xoflen 32 over the same "
                          "generated input"),
        "classification": "independent derived regression only; no copied vector corpus",
        "license": ("tool outputs are locally derived facts; Python/OpenSSL implementations "
                    "are not vendored"),
    }, "S04 primitive projection: exact SHAKE derivation record mismatch")

    empty272 = (
        "46b9dd2b0ba88d13233b3feb743eeb243fcd52ea62b81b82b50c27646ed5762f"
        "d75dc4ddd8c0f200cb05019d67b592f6fc821c49479ab48640292eacb3b7c4be"
        "141e96616fb13957692cc7edd0b45ae3dc07223c8e92937bef84bc0eab8628533"
        "49ec75546f58fb7c2775c38462c5010d846c185c15111e595522a6bcd16cf86f"
        "3d122109e3b1fdd943b6aec468a2d621a7c06c6a957c62b54dafc3be87567d67"
        "7231395f6147293b68ceab7a9e0c58d864e8efde4e1b9a46cbe854713672f5ca"
        "aae314ed9083dab4b099f8e300f01b8650f1f4b1d8fcf3f3cb53fb8e9eb2ea2"
        "03bdc970f50ae55428a91f7f53ac266b28419c3778a15fd248d339ede785fb7f"
        "5a1aaa96d313eacc890936c173cdcd0f")
    expected = {
        "shake256-empty-out272": {
            "algorithm": "SHAKE256", "mode": "XOF", "input_len_bytes": 0,
            "out_len": 272, "output": empty272,
            "classification": "official-nist-example-prefix",
        },
        "shake256-a61-in135-out32": {
            "algorithm": "SHAKE256", "mode": "XOF", "input_len_bytes": 135,
            "out_len": 32,
            "output": "55b991ece1e567b6e7c2c714444dd201cd51f4f3832d08e1d26bebc63e07a3d7",
            "classification": "derived-regression-only",
        },
        "shake256-a61-in136-out32": {
            "algorithm": "SHAKE256", "mode": "XOF", "input_len_bytes": 136,
            "out_len": 32,
            "output": "8fcc5a08f0a1f6827c9cf64ee8d16e0443106359ca6c8efd230759256f44996a",
            "classification": "derived-regression-only",
        },
        "shake256-a61-in137-out32": {
            "algorithm": "SHAKE256", "mode": "XOF", "input_len_bytes": 137,
            "out_len": 32,
            "output": "a44e1a438dad6273d540be65ee26386c59588efb09139dc086385d2db0c25782",
            "classification": "derived-regression-only",
        },
    }
    cases = data.get("vectors", {}).get("shake256")
    require(isinstance(cases, list), "S04 primitive projection: SHAKE case list missing")
    indexed = {case.get("id"): case for case in cases
               if isinstance(case, dict) and isinstance(case.get("id"), str)}
    for case_id, fields in expected.items():
        case = indexed.get(case_id)
        require(isinstance(case, dict),
                f"S04 primitive projection: missing active case {case_id}")
        for key, value in fields.items():
            require(case.get(key) == value,
                    f"S04 primitive projection: {case_id} exact {key} mismatch")
        if case_id == "shake256-empty-out272":
            require(case.get("source") == "SHAKE256_Msg0.pdf"
                    and case.get("source_locator") ==
                        "4096-bit output for the empty message; exact leading 272 bytes"
                    and case.get("msg") == "",
                    "S04 primitive projection: official empty-output provenance mismatch")
        else:
            count = fields["input_len_bytes"]
            require(case.get("authority") == "FIPS 202 Section 6.2"
                    and case.get("derivation") == "python_hashlib"
                    and case.get("input_recipe") == {"byte": "61", "count": count},
                    f"S04 primitive projection: derived provenance mismatch for {case_id}")
    print("INFO: S04 primitive projection: PASS (4 exact SHAKE boundary cases)")


def check_reference_manifest() -> None:
    data = read_json(DOCS / "reference-manifest.json")
    require(data.get("schema_version") == 1 and isinstance(data.get("entries"), list),
            "reference-manifest.json: invalid schema")
    entries = data["entries"]
    ids = [entry.get("id") for entry in entries]
    require(all(isinstance(item, str) and item for item in ids) and len(ids) == len(set(ids)),
            "reference-manifest.json: unique entry ids required")
    reference_root = Path(os.environ.get("SLHDSA_REFERENCE_ROOT", ROOT.parent)).resolve()
    bundle_available = (reference_root / "prompt.md").is_file()
    checked = 0
    for entry in entries:
        require(entry.get("kind") in {"file", "git", "remote-git", "url"},
                f"reference-manifest.json: invalid kind for {entry.get('id')}")
        require(entry.get("root") in {"sibling", "repo", "remote"},
                f"reference-manifest.json: invalid root for {entry.get('id')}")
        require(isinstance(entry.get("locator"), str) and entry["locator"],
                f"reference-manifest.json: missing locator for {entry.get('id')}")
        if entry["root"] == "remote":
            require("revision" in entry, f"reference-manifest.json: remote revision for {entry['id']}")
            continue
        if entry["root"] == "sibling" and not bundle_available:
            continue
        base = reference_root if entry["root"] == "sibling" else ROOT
        target = (base / entry["locator"]).resolve()
        if entry["kind"] == "file":
            require(target.is_file(), f"reference-manifest.json: missing {entry['id']} at {target}")
            require(sha256_file(target) == entry.get("sha256"),
                    f"reference-manifest.json: hash mismatch for {entry['id']}")
        elif entry["kind"] == "git":
            require(target.is_dir(), f"reference-manifest.json: missing git tree {entry['id']}")
            if entry["root"] == "repo":
                require(set(entry) == {"id", "kind", "root", "locator",
                                       "repair_base_revision", "revision_semantics", "authority"}
                        and entry.get("revision_semantics") == "exact-repair-base"
                        and entry.get("repair_base_revision") == S02_REPAIR_BASE_REVISION
                        and "revision" not in entry,
                        f"reference-manifest.json: repo revision semantics for {entry['id']}")
                require(git_revision_is_ancestor(target, S02_REPAIR_BASE_REVISION),
                        f"reference-manifest.json: exact repair base is not an ancestor for "
                        f"{entry['id']}")
                ledger = (DOCS / "source-ledger.md").read_text(encoding="utf-8")
                require("active SLH-DSA Lean source composite" in ledger,
                        "reference-manifest.json: source-ledger repair/composite boundary missing")
            else:
                require(git_revision(target) == entry.get("revision"),
                        f"reference-manifest.json: revision mismatch for {entry['id']}")
        checked += 1
    if bundle_available:
        print(f"INFO: verified {checked} local reference-manifest entries under {reference_root}")
    else:
        print(f"INFO: sibling reference bundle absent at {reference_root}; metadata checked, "
              "set SLHDSA_REFERENCE_ROOT to reproduce external hashes")
    composite = data.get("source_tree_composite")
    require(isinstance(composite, dict), "reference-manifest.json: composite schema")
    require(source_tree_composite_digest(composite, ROOT) == composite.get("sha256"),
            "reference-manifest.json: source-tree composite mismatch")
    check_source_tree_mutation(composite)
    check_s04_primitive_projection()


def validate_s01_authority_metadata(entries: dict[str, Any], profile: dict[str, Any]) -> None:
    for record_id, expected in EXPECTED_S01_AUTHORITY_RECORDS.items():
        require(entries.get(record_id) == expected,
                f"S01: exact controlling authority record mismatch for {record_id}")
    require(profile.get("schema_version") == 1
            and profile.get("profile_id") == SP800_PROFILE_ID
            and profile.get("excluded_legacy_current_code_profile_id") == LEGACY_PROFILE_ID
            and profile.get("publication_status") == "initial-public-draft"
            and profile.get("publication_date") == "2026-04-13"
            and profile.get("authority") == "NIST SP 800-230 Initial Public Draft, Table 1"
            and profile.get("source_sha256") ==
            "62d092f787a1f79260454bf332b642ff3b5b73dbcce2678a133a1406065e452e"
            and profile.get("source_size_bytes") == 282069
            and profile.get("normative_fips205_profile") is False
            and profile.get("signature_cap_per_key") == 2 ** 24,
            "S01: SP 800-230 profile status/cap mismatch")
    require(set(profile) == {
        "schema_version", "profile_id", "excluded_legacy_current_code_profile_id",
        "authority", "publication_status", "publication_date", "source_sha256",
        "source_size_bytes", "signature_cap_per_key", "normative_fips205_profile",
        "parameter_sets",
    }, "S01: SP 800-230 profile keys are not exact")
    rows = profile.get("parameter_sets")
    expected_ipd_rows = [
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
    require(rows == expected_ipd_rows,
            "S01: SP 800-230 profile must match the exact six non-normative IPD tuples")


def parse_scope_profile_rows(scope: str) -> dict[str, dict[str, str]]:
    header = "| Profile | Authority and purpose | Required target | Current state | Security/refinement claim |"
    separator = "|---|---|---|---|---|"
    lines = scope.splitlines()
    require(lines.count(header) == 1, "S01: scope.md must contain one canonical profile table")
    start = lines.index(header)
    require(start + 1 < len(lines) and lines[start + 1] == separator,
            "S01: scope.md canonical profile-table separator mismatch")
    parsed: list[tuple[str, dict[str, str]]] = []
    for line in lines[start + 2:]:
        if not line.startswith("|"):
            break
        cells = [cell.strip() for cell in line.strip("|").split("|")]
        require(len(cells) == 5, "S01: scope.md canonical profile row must have five cells")
        require(cells[0].startswith("`") and cells[0].endswith("`") and len(cells[0]) > 2,
                "S01: scope.md profile identifier must be a nonempty code span")
        profile_id = cells[0][1:-1]
        parsed.append((profile_id, {
            "authority": cells[1],
            "target": cells[2],
            "state": cells[3],
            "claim": cells[4],
        }))
    profile_ids = [profile_id for profile_id, _ in parsed]
    require(profile_ids == [
        "FIPS205-12", "SPX-TW-ABS", SP800_PROFILE_ID, LEGACY_PROFILE_ID,
        "C13-ETH", "DEPLOY-TBD",
    ], "S01: scope.md profile rows are missing, duplicated, reordered, or contradictory")
    require(len(profile_ids) == len(set(profile_ids)),
            "S01: scope.md contains duplicate profile identifiers")
    return dict(parsed)


def validate_scope_profile_separation(scope: str) -> None:
    rows = parse_scope_profile_rows(scope)
    require(rows[SP800_PROFILE_ID] == {
        "authority": "NIST SP 800-230 Initial Public Draft",
        "target": "Six proposed limited-signature sets and strict `2^24` signatures/key cap",
        "state": "Exact draft rows and metadata are pinned",
        "claim": "Non-normative and no implementation claim",
    }, "S01: scope.md six-set non-normative authority/profile row mismatch")
    require(rows[LEGACY_PROFILE_ID] == {
        "authority": "Repository regression profile",
        "target": "One reduced depth-one profile",
        "state": "Abstract/concrete runtime regression",
        "claim": "Not FIPS the six-set draft or a security claim",
    }, "S01: scope.md one-set legacy current-code row mismatch")
    require(SP800_PROFILE_ID != LEGACY_PROFILE_ID,
            "S01: six-set and one-set profile identifiers must be distinct")


def decode_active_s01_files(files: dict[str, bytes]) -> dict[str, str]:
    decoded = {}
    for relative, data in files.items():
        try:
            decoded[relative] = data.decode("utf-8")
        except UnicodeError as error:
            raise CheckFailure(f"S01: cannot decode active file {relative}: {error}") from error
    return decoded


def validate_deprecated_profile_id(files: dict[str, bytes]) -> None:
    violations: list[str] = []
    for relative, source in decode_active_s01_files(files).items():
        for line_no, line in enumerate(source.splitlines(), 1):
            if DEPRECATED_PROFILE_ID in line:
                violations.append(f"{relative}:{line_no}")
    require(not violations,
            "S01: deprecated ambiguous profile identifier occurs on active surfaces: " +
            ", ".join(violations))


def validate_current_profile_occurrences(files: dict[str, bytes]) -> None:
    decoded = decode_active_s01_files(files)
    require(any(SP800_PROFILE_ID in source for source in decoded.values()),
            "S01: six-set draft profile identity is absent")
    require(any(LEGACY_PROFILE_ID in source for source in decoded.values()),
            "S01: legacy regression profile identity is absent")
    provenance = decoded["HashSigTest/SLHDSA/ACVP/fixtures/provenance.json"]
    require(f'"profileId": "{SP800_PROFILE_ID}"' in provenance,
            "S01: ACVP provenance does not identify the six-set draft profile")


def ascii_alphanumeric_stream(source: str) -> str:
    """Drop every non-ASCII-alphanumeric codepoint and lowercase the remainder."""

    return "".join(character.lower() for character in source
                   if character.isascii() and character.isalnum())


def count_overlapping(source: str, needle: str) -> int:
    count = 0
    offset = 0
    while True:
        offset = source.find(needle, offset)
        if offset < 0:
            return count
        count += 1
        offset += 1


def validate_profile_id_reconstruction(files: dict[str, bytes]) -> None:
    decoded = decode_active_s01_files(files)
    ids = (DEPRECATED_PROFILE_ID, SP800_PROFILE_ID, LEGACY_PROFILE_ID)
    canonical_ids = {profile_id: ascii_alphanumeric_stream(profile_id) for profile_id in ids}
    totals = {profile_id: 0 for profile_id in ids}
    literals = {profile_id: 0 for profile_id in ids}

    for relative, source in decoded.items():
        canonical_source = ascii_alphanumeric_stream(source)
        for profile_id, canonical_id in canonical_ids.items():
            canonical_count = count_overlapping(canonical_source, canonical_id)
            literal_count = source.count(profile_id)
            totals[profile_id] += canonical_count
            literals[profile_id] += literal_count
            require(canonical_count == literal_count,
                    "S01: a profile identity is syntactically reconstructed rather than an exact "
                    f"registered literal in {relative}: {profile_id}")
        if relative.startswith("HashSigTest/SLHDSA/") and relative.endswith(".lean"):
            require(all(count_overlapping(canonical_source, canonical_ids[item]) == 0
                        for item in ids),
                    f"S01: test Lean source must not carry documentation profile IDs: {relative}")

    require(totals[DEPRECATED_PROFILE_ID] == literals[DEPRECATED_PROFILE_ID] == 0,
            "S01: deprecated canonical identity must be absent")
    require(totals[SP800_PROFILE_ID] == literals[SP800_PROFILE_ID] > 0
            and totals[LEGACY_PROFILE_ID] == literals[LEGACY_PROFILE_ID] > 0,
            "S01: current profile identities must be exact literals and remain present")


def validate_profile_id_policy(files: dict[str, bytes]) -> None:
    validate_deprecated_profile_id(files)
    validate_current_profile_occurrences(files)
    validate_profile_id_reconstruction(files)


PARSER_FOCUSED_DOCUMENTS = (
    "validation.md",
)


def parse_parser_focused_partition(line: str) -> dict[str, int]:
    prefix = "focused-parser-partition: "
    require(line.startswith(prefix), "S01: focused parser partition prefix is malformed")
    fields: dict[str, str] = {}
    for item in line[len(prefix):].split("; "):
        require(item.count("=") == 1, "S01: focused parser partition item is malformed")
        key, value = item.split("=", 1)
        require(key and key not in fields, "S01: focused parser partition key is duplicated")
        fields[key] = value
    expected_keys = set(PARSER_FOCUSED_CASE_COUNTS) | {
        "total", "sha-cli-is-subset-of-path-cli", "nominal-success-excluded"
    }
    require(set(fields) == expected_keys,
            "S01: focused parser partition has a missing/extra/double-counted category")
    observed: dict[str, int] = {}
    for category in PARSER_FOCUSED_CASE_COUNTS:
        require(fields[category].isdigit(),
                f"S01: focused parser partition count is not numeric: {category}")
        observed[category] = int(fields[category])
    require(observed == PARSER_FOCUSED_CASE_COUNTS
            and fields["total"].isdigit()
            and int(fields["total"]) == sum(observed.values()) == PARSER_FOCUSED_TOTAL
            and fields["sha-cli-is-subset-of-path-cli"] == "6"
            and int(fields["sha-cli-is-subset-of-path-cli"]) <= observed["path-cli"]
            and fields["nominal-success-excluded"] == "true",
            "S01: focused parser partition arithmetic/subset/nominal policy disagrees with code")
    return observed


def validate_parser_focused_documentation(
        replacements: dict[str, str] | None = None) -> None:
    replacements = {} if replacements is None else replacements
    for relative in PARSER_FOCUSED_DOCUMENTS:
        source = replacements.get(
            relative, (DOCS / relative).read_text(encoding="utf-8"))
        lines = [line.strip() for line in source.splitlines()
                 if line.strip().startswith("focused-parser-partition: ")]
        require(lines == [PARSER_FOCUSED_PARTITION],
                f"S01: {relative} must contain the one exact current focused partition")
        parse_parser_focused_partition(lines[0])

    stale = re.compile(r"\b(?:55|67|211|215|217|218|232)\b")
    stale_prior = re.compile(
        r"(?:total=230\b|\b230-case partition\b|\ball 230 (?:mechanically|focused)\b|"
        r"\btotal 230\b)")
    for path in DOCS.rglob("*"):
        if not path.is_file():
            continue
        relative = path.relative_to(DOCS).as_posix()
        try:
            source = replacements.get(relative, path.read_text(encoding="utf-8"))
        except UnicodeDecodeError as error:
            raise CheckFailure(f"S01: active documentation is not UTF-8: {relative}") from error
        require(stale.search(source) is None and stale_prior.search(source) is None,
                f"S01: active documentation retains stale focused total in {relative}")
        for obsolete in (
                "trace/sidecar/current hash", "fresh current Lake hash",
                "Lake's current-file hash", "Lake's hash of the current",
                "`Lake.computeBinFileHash`"):
            require(obsolete not in source,
                    f"S01: active documentation retains obsolete current-Lake-hash wording in "
                    f"{relative}: {obsolete}")


def check_parser_documentation() -> None:
    validate_parser_focused_documentation()

    double_count = PARSER_FOCUSED_PARTITION.replace(
        "; total=234", "; sha-cli=6; total=240")
    expect_s01_mutation_rejected(
        "double-counted SHA CLI focused subset",
        lambda: parse_parser_focused_partition(double_count))
    stale_validation = (DOCS / "validation.md").read_text(
        encoding="utf-8") + "\nFocused suite: 211 cases.\n"
    expect_s01_mutation_rejected(
        "stale focused total in validation documentation",
        lambda: validate_parser_focused_documentation({
            "validation.md": stale_validation,
        }))


def expect_s01_mutation_rejected(label: str, action: Any) -> None:
    try:
        action()
    except CheckFailure:
        return
    raise CheckFailure(f"S01 authority mutation self-test accepted {label}")


def read_matrix_rows(filename: str) -> dict[str, dict[str, str]]:
    with (DOCS / "matrices" / filename).open(newline="", encoding="utf-8") as handle:
        rows = list(csv.DictReader(handle))
    ids = [row["id"] for row in rows]
    require(len(ids) == len(set(ids)), f"S01: duplicate matrix ID in {filename}")
    return {row["id"]: row for row in rows}


def validate_matrix_artifact_pins(files: dict[str, bytes]) -> None:
    actual_paths = {relative for relative in files
                    if relative.startswith("docs/slhdsa/matrices/")}
    require(actual_paths == set(S01_MATRIX_PINS),
            "S01: canonical matrix path set changed; update exact pins deliberately after review")
    for relative, (expected_size, expected_hash) in S01_MATRIX_PINS.items():
        data = files[relative]
        require(len(data) == expected_size and hashlib.sha256(data).hexdigest() == expected_hash,
                f"S01: canonical matrix byte pin mismatch for {relative}")


def validate_s01_matrix_records(
        coverage: dict[str, dict[str, str]],
        obligations: dict[str, dict[str, str]],
        assumptions: dict[str, dict[str, str]],
        tcb: dict[str, dict[str, str]]) -> None:
    require(coverage.get("COV-005", {}).get("current_status") == "missing"
            and coverage.get("COV-005", {}).get("target_status") == "required",
            "S01: ACVP implementation coverage gap must remain explicit")
    require(coverage.get("COV-014", {}).get("profile") == SP800_PROFILE_ID
            and coverage.get("COV-014", {}).get("current_status") == "covered"
            and coverage.get("COV-014", {}).get("target_status") == "deferred"
            and coverage.get("COV-014", {}).get("claim") ==
                "Six proposed limited-signature sets"
            and coverage.get("COV-014", {}).get("evidence") ==
                "Exact draft tuples status date and cap pinned"
            and coverage.get("COV-014", {}).get("notes") ==
                "No six-set implementation claim",
            "S01: six-set draft authority row mismatch")
    require({row_id for row_id, row in coverage.items()
             if row["profile"] == LEGACY_PROFILE_ID} == {"COV-009", "COV-010"}
            and {row_id for row_id, row in coverage.items()
                 if row["profile"] == SP800_PROFILE_ID} == {"COV-014"},
            "S01: extra or missing coverage rows conflict with the two current profile identities")

    require(obligations.get("PO-014", {}).get("profile") == LEGACY_PROFILE_ID
            and obligations.get("PO-014", {}).get("status") == "provisional",
            "S01: legacy correctness obligation mismatch")
    require("PO-001" not in obligations and obligations.get("PO-026", {}).get("status") == "open"
            and obligations.get("PO-026", {}).get("severity") == "critical",
            "S01: obsolete admitted placeholder or missing master-composition gap")
    require({row_id for row_id, row in obligations.items()
             if row["profile"] == LEGACY_PROFILE_ID} == {"PO-014"}
            and not {row_id for row_id, row in obligations.items()
                     if row["profile"] == SP800_PROFILE_ID},
            "S01: extra proof-obligation rows conflict with the two current profile identities")

    require(assumptions.get("ASM-007", {}).get("profile") == LEGACY_PROFILE_ID,
            "S01: legacy vector-provenance assumption mismatch")
    require(assumptions.get("ASM-011", {}).get("evidence") ==
            "HashSigTest/SLHDSA/ACVP/fixtures/provenance.json",
            "S01: ACVP provenance assumption mismatch")
    require(assumptions.get("ASM-012", {}).get("evidence") ==
            "scripts/slhdsa/validate.sh",
            "S01: sequential parser-attestation assumption mismatch")
    require({row_id for row_id, row in assumptions.items()
             if row["profile"] == LEGACY_PROFILE_ID} == {"ASM-007"}
            and not {row_id for row_id, row in assumptions.items()
                     if row["profile"] == SP800_PROFILE_ID},
            "S01: extra assumption rows conflict with the two current profile identities")

    require("TCB-003" not in tcb
            and tcb.get("TCB-009", {}).get("component") ==
                "Permanent curated AxiomAudit roots"
            and "177 unique exact roots" in tcb.get("TCB-009", {}).get("mitigation", ""),
            "S01: permanent exact-root trust boundary mismatch")
    require(tcb.get("TCB-010", {}).get("component") ==
            "Lean 4.33.1 generated unsafe recursion"
            and "17 named recursive parents" in tcb.get("TCB-010", {}).get("boundary", ""),
            "S01: generated-helper trust boundary mismatch")
    require(tcb.get("TCB-011", {}).get("notes") == "No admission exception",
            "S01: logical-axiom boundary must not retain an admission exception")


def validate_parser_assurance_claims(files: dict[str, bytes], coverage: dict[str, dict[str, str]]) -> None:
    active = decode_active_s01_files(files)
    combined = "\n".join(active.values())
    old_phrase = "These tests are " + \
        "conformance evidence only; they make no construction or security claim."
    qualification = (
        "These tests are parser/schema-format validation evidence only. They are not "
        "implementation-conformance evidence, construction evidence, or security evidence."
    )
    require(old_phrase not in " ".join(combined.split()),
            "S01: deprecated unqualified parser conformance-evidence phrase is present")
    parser = " ".join(active["HashSigTest/SLHDSA/ACVP/ParserTests.lean"].split())
    require(parser.count(qualification) == 1,
            "S01: ParserTests must contain one exact schema-only evidence qualification")
    schema = active["HashSigTest/SLHDSA/ACVP/Schema.lean"]
    for private_name in ("parsePromptJson", "parseResultsJson", "validatePair"):
        require(len(re.findall(rf"^private def {private_name}\b", schema, re.MULTILINE)) == 1,
                f"S01: lower-level parser helper must be private: {private_name}")
        require(re.search(rf"^def {private_name}\b", schema, re.MULTILINE) is None,
                f"S01: lower-level parser helper leaked publicly: {private_name}")
    for public_name in ("parsePrompt", "parseResults", "parseAndValidate", "parseWrappedPair"):
        require(len(re.findall(rf"^def {public_name}\b", schema, re.MULTILINE)) == 1,
                f"S01: safe parser string root must be public exactly once: {public_name}")
    require('requireKeys "wrapped pair" object ["prompt", "expectedResults"]' in schema
            and "let wrapper ← StrictJson.parse source" in schema,
            "S01: wrapped-pair root must strict-parse and require exact wrapper keys")
    public_roots = {record["name"] for record in ACVP_DEPENDENCY_RECORDS.values()}
    require("SLHDSA.Test.ACVP.parseWrappedPair" in public_roots,
            "S01: public wrapped-pair string root is absent from static accounting")
    require(not {f"SLHDSA.Test.ACVP.{name}" for name in
                 ("parsePromptJson", "parseResultsJson", "validatePair")}.intersection(
                     public_roots),
            "S01: private parser helpers must not be statically exposed")
    cov005 = coverage.get("COV-005", {})
    require(cov005.get("current_status") == "missing"
            and cov005.get("target_status") == "required",
            "S01: COV-005 implementation-conformance obligation must remain missing/required")


def check_s01_metadata() -> None:
    manifest = read_json(DOCS / "reference-manifest.json")
    entries = {entry["id"]: entry for entry in manifest["entries"]}
    profile = read_json(DOCS / "matrices/sp800-230-ipd-profile.json")
    validate_s01_authority_metadata(entries, profile)

    fips_profile = read_json(DOCS / "matrices/fips205-profile.json")
    validate_fips_profile_data(fips_profile)
    fips_mutations: list[tuple[str, Any]] = []
    bad = copy.deepcopy(fips_profile)
    bad["authority"] = "secondary summary"
    fips_mutations.append(("false canonical FIPS profile authority", bad))
    bad = copy.deepcopy(fips_profile)
    bad["external_api"]["randomness"] = bad["external_api"]["randomness"].replace(
        "deterministic signing omits addrnd", "deterministic signing requires addrnd")
    fips_mutations.append(("false deterministic randomness rule", bad))
    bad = copy.deepcopy(fips_profile)
    bad["external_api"]["randomness"] = bad["external_api"]["randomness"].replace(
        "Hedged signing supplies an n-byte addrnd", "Hedged signing omits addrnd")
    fips_mutations.append(("false hedged randomness rule", bad))
    bad = copy.deepcopy(fips_profile)
    del bad["authority"]
    fips_mutations.append(("missing FIPS profile top-level key", bad))
    bad = copy.deepcopy(fips_profile)
    bad["external_api"]["future_mode"] = "unreviewed"
    fips_mutations.append(("extra FIPS profile API key", bad))
    bad = copy.deepcopy(fips_profile)
    bad["external_api"]["other_prehashes"] = "Any approved hash is permitted."
    fips_mutations.append(("false other-prehash policy", bad))
    bad = copy.deepcopy(fips_profile)
    bad["external_api"]["pure_m_prime"] = "ctx || M"
    fips_mutations.append(("false external API grammar", bad))
    bad = copy.deepcopy(fips_profile)
    bad["parameter_sets"][0], bad["parameter_sets"][1] = \
        bad["parameter_sets"][1], bad["parameter_sets"][0]
    fips_mutations.append(("reordered FIPS Table-2 rows", bad))
    bad = copy.deepcopy(fips_profile)
    bad["external_api"]["prehashes_shown_by_fips"][0]["oid"] = "0.0"
    fips_mutations.append(("false FIPS pre-hash OID", bad))
    bad = copy.deepcopy(fips_profile)
    bad["primitive_grammars"]["SHAKE_all_n"]["F"] = "SHAKE256(M1, 8n)"
    fips_mutations.append(("false primitive grammar", bad))
    for label, mutation in fips_mutations:
        expect_s01_mutation_rejected(label, lambda mutation=mutation:
                                     validate_fips_profile_data(mutation))

    bad_fips_date = copy.deepcopy(entries)
    bad_fips_date["fips205"]["publication_date"] = "2099-01-01"
    expect_s01_mutation_rejected(
        "false FIPS 205 publication date",
        lambda: validate_s01_authority_metadata(bad_fips_date, profile))
    bad_fips_authority = copy.deepcopy(entries)
    bad_fips_authority["fips205"]["authority"] = "secondary-untrusted"
    expect_s01_mutation_rejected(
        "false FIPS 205 authority classification",
        lambda: validate_s01_authority_metadata(bad_fips_authority, profile))
    bad_compatibility = copy.deepcopy(entries)
    bad_compatibility["acvp-server-v1.1.0.38"]["revision"] = "0" * 40
    expect_s01_mutation_rejected(
        "corrupt v1.1.0.38 commit",
        lambda: validate_s01_authority_metadata(bad_compatibility, profile))
    bad_status = copy.deepcopy(profile)
    bad_status["publication_status"] = "final"
    expect_s01_mutation_rejected(
        "false SP 800-230 final status",
        lambda: validate_s01_authority_metadata(entries, bad_status))
    bad_server_release = copy.deepcopy(entries)
    bad_server_release["acvp-server"]["release"] = "v1.1.0.42"
    expect_s01_mutation_rejected(
        "false current ACVP-Server release",
        lambda: validate_s01_authority_metadata(bad_server_release, profile))
    bad_protocol_authority = copy.deepcopy(entries)
    bad_protocol_authority["acvp-protocol"]["authority"] = "secondary"
    expect_s01_mutation_rejected(
        "false ACVP protocol authority classification",
        lambda: validate_s01_authority_metadata(bad_protocol_authority, profile))

    scope = (DOCS / "scope.md").read_text(encoding="utf-8")
    validate_scope_profile_separation(scope)
    old_id_scope = scope.replace(
        f"| `{SP800_PROFILE_ID}` |", f"| `{DEPRECATED_PROFILE_ID}` |", 1)
    require(old_id_scope != scope, "S01: scope old-ID mutation did not change its target")
    expect_s01_mutation_rejected(
        "deprecated ambiguous six-set scope identifier",
        lambda: validate_scope_profile_separation(old_id_scope))
    conflated_scope = scope.replace(
        f"| `{SP800_PROFILE_ID}` |", f"| `{LEGACY_PROFILE_ID}` |", 1)
    require(conflated_scope != scope, "S01: scope conflation mutation did not change its target")
    expect_s01_mutation_rejected(
        "six-set scope changed to one-set legacy identifier",
        lambda: validate_scope_profile_separation(conflated_scope))

    active_files = load_active_s01_files()
    validate_active_s01_hygiene(active_files)
    validate_profile_id_policy(active_files)
    validate_matrix_artifact_pins(active_files)
    check_parser_documentation()

    coverage_rows = read_matrix_rows("coverage.csv")
    obligation_rows = read_matrix_rows("proof-obligations.csv")
    assumption_rows = read_matrix_rows("assumptions.csv")
    tcb_rows = read_matrix_rows("tcb.csv")
    validate_s01_matrix_records(
        coverage_rows, obligation_rows, assumption_rows, tcb_rows)
    validate_parser_assurance_claims(active_files, coverage_rows)

    outer_existing = copy.deepcopy(active_files)
    outer_path = "HashSigTest/SLHDSA/Sha2KAT.lean"
    outer_existing[outer_path] += f"-- {DEPRECATED_PROFILE_ID}\n".encode("utf-8")
    expect_s01_mutation_rejected(
        "deprecated identifier appended to outer-scope Sha2KAT",
        lambda: validate_deprecated_profile_id(outer_existing))

    outer_new = copy.deepcopy(active_files)
    outer_new["HashSigTest/SLHDSA/new-profile-note.md"] = \
        f"{DEPRECATED_PROFILE_ID}\n".encode("utf-8")
    expect_s01_mutation_rejected(
        "deprecated identifier in new outer-scope file",
        lambda: validate_deprecated_profile_id(outer_new))

    bad_new_whitespace = copy.deepcopy(active_files)
    bad_new_whitespace["HashSigTest/SLHDSA/new-whitespace-note.md"] = b"note\n\n"
    expect_s01_mutation_rejected(
        "terminal blank line in new outer-scope file",
        lambda: validate_active_s01_hygiene(bad_new_whitespace))

    bad_internal_tab = copy.deepcopy(active_files)
    validation_path = "docs/slhdsa/validation.md"
    bad_internal_tab[validation_path] = bad_internal_tab[validation_path].replace(
        b"exact axiom footprints", b"exact axiom \tfootprints", 1)
    require(bad_internal_tab[validation_path] != active_files[validation_path],
            "S01: validation internal-tab mutation did not change its target")
    expect_s01_mutation_rejected(
        "internal tab in active validation documentation",
        lambda: validate_active_s01_hygiene(bad_internal_tab))
    schema_path = "HashSigTest/SLHDSA/ACVP/Schema.lean"

    split_comment = copy.deepcopy(active_files)
    split_comment[schema_path] += (
        f"-- {SP800_PROFILE_ID[:-4]}\n-- {SP800_PROFILE_ID[-4:]} is one set; "
        f"{LEGACY_PROFILE_ID[:-2]}\n-- {LEGACY_PROFILE_ID[-2:]} is six sets.\n"
    ).encode("utf-8")
    expect_s01_mutation_rejected(
        "r3 split-comment current profile identities",
        lambda: validate_profile_id_reconstruction(split_comment))

    concatenated_strings = copy.deepcopy(active_files)
    concatenated_strings[schema_path] += (
        f"#check \"{SP800_PROFILE_ID[:-4]}\" ++ \"{SP800_PROFILE_ID[-4:]} is one set; "
        f"{LEGACY_PROFILE_ID[:-2]}\" ++ \"{LEGACY_PROFILE_ID[-2:]} is six sets\"\n"
    ).encode("utf-8")
    expect_s01_mutation_rejected(
        "r3 Lean string-concatenation current profile identities",
        lambda: validate_profile_id_reconstruction(concatenated_strings))

    short_fragments = copy.deepcopy(active_files)
    short_fragments[schema_path] += (
        f"-- {SP800_PROFILE_ID[:8]}\n-- {SP800_PROFILE_ID[8:17]}\n"
        f"-- {SP800_PROFILE_ID[17:]} and {LEGACY_PROFILE_ID[:10]}\n"
        f"-- {LEGACY_PROFILE_ID[10:-1]}\n-- {LEGACY_PROFILE_ID[-1:]}\n"
    ).encode("utf-8")
    expect_s01_mutation_rejected(
        "short-fragment current profile identity reconstruction",
        lambda: validate_profile_id_reconstruction(short_fragments))

    deprecated_split = copy.deepcopy(active_files)
    deprecated_split[schema_path] += (
        f"-- {DEPRECATED_PROFILE_ID[:-6]}\n-- {DEPRECATED_PROFILE_ID[-6:]}\n"
    ).encode("utf-8")
    expect_s01_mutation_rejected(
        "split deprecated profile identity reconstruction",
        lambda: validate_profile_id_reconstruction(deprecated_split))

    contradictory_coverage = copy.deepcopy(coverage_rows)
    contradictory_coverage["COV-014"]["claim"] = "Single current-code parameter set"
    contradictory_coverage["COV-014"]["evidence"] = "Current one-set implementation complete"
    contradictory_coverage["COV-014"]["notes"] = "This is the legacy implementation profile"
    expect_s01_mutation_rejected(
        "contradictory COV-014 claim/evidence/notes",
        lambda: validate_s01_matrix_records(
            contradictory_coverage, obligation_rows, assumption_rows, tcb_rows))

    old_parser_claim = copy.deepcopy(active_files)
    parser_path = "HashSigTest/SLHDSA/ACVP/ParserTests.lean"
    new_claim = (
        "These tests\nare parser/schema-format validation evidence only. They are not "
        "implementation-conformance\nevidence, construction evidence, or security evidence."
    )
    old_claim = "These tests\nare " + \
        "conformance evidence only; they make no construction or security claim."
    parser_text = old_parser_claim[parser_path].decode("utf-8")
    require(parser_text.count(new_claim) == 1,
            "S01: parser assurance mutation target is not unique")
    old_parser_claim[parser_path] = parser_text.replace(new_claim, old_claim).encode("utf-8")
    expect_s01_mutation_rejected(
        "old unqualified ParserTests conformance phrase",
        lambda: validate_parser_assurance_claims(old_parser_claim, coverage_rows))

    coverage_extra = copy.deepcopy(active_files)
    coverage_extra["docs/slhdsa/matrices/coverage.csv"] += (
        b"COV-015,FIPS205-12,conformance,All twelve implementations conform,FIPS 205,Table 2,"
        b"HashSig/SLHDSA,covered,required,Full implementation conformance,"
        b"Complete implementation conformance established\n"
    )
    expect_s01_mutation_rejected(
        "r3 extra contradictory COV-015 row",
        lambda: validate_matrix_artifact_pins(coverage_extra))

    extra_tcb = copy.deepcopy(active_files)
    extra_tcb["docs/slhdsa/matrices/tcb.csv"] += (
        b"TCB-999,Unreviewed component,Unknown boundary,Unknown trust,provisional,Review it,None,"
        b"Must not enter the pinned corpus silently\n"
    )
    expect_s01_mutation_rejected(
        "extra canonical TCB row", lambda: validate_matrix_artifact_pins(extra_tcb))

    missing_matrix = copy.deepcopy(active_files)
    del missing_matrix["docs/slhdsa/matrices/tcb.csv"]
    expect_s01_mutation_rejected(
        "missing canonical matrix file", lambda: validate_matrix_artifact_pins(missing_matrix))

    extra_matrix = copy.deepcopy(active_files)
    extra_matrix["docs/slhdsa/matrices/unregistered.csv"] = b"id,value\nX,unreviewed\n"
    expect_s01_mutation_rejected(
        "extra canonical matrix file", lambda: validate_matrix_artifact_pins(extra_matrix))

    field_change = copy.deepcopy(active_files)
    field_change["docs/slhdsa/matrices/assumptions.csv"] = field_change[
        "docs/slhdsa/matrices/assumptions.csv"].replace(
            b"Quantum oracle access semantics", b"Quantum-oracle access semantics", 1)
    expect_s01_mutation_rejected(
        "canonical matrix field change", lambda: validate_matrix_artifact_pins(field_change))

    print("INFO: S01 authority/profile mutation self-tests: PASS "
          f"(6 authority, {len(fips_mutations)} FIPS-profile, profile reconstruction/claim, "
          "and 5 matrix corruptions rejected; 8 filesystem/replacement cases rejected)")

    coverage = read_json(ROOT / "HashSigTest/SLHDSA/ACVP/fixtures/positive-prehash-coverage.json")
    require(coverage.get("counts") == {
        "parameterSets": 12,
        "hashAlgorithms": 12,
        "cells": 144,
        "covered": 24,
        "uncovered": 120,
    }, "S01: exact positive pre-hash coverage counts mismatch")
    cells = coverage.get("cells", [])
    require(len(cells) == 144,
            "S01: positive pre-hash matrix must contain 144 cells")
    missing_by_parameter: dict[str, int] = {}
    for cell in cells:
        parameter = cell.get("parameterSet")
        require(isinstance(parameter, str) and isinstance(cell.get("covered"), bool),
                "S01: malformed pre-hash coverage cell")
        if not cell["covered"]:
            missing_by_parameter[parameter] = missing_by_parameter.get(parameter, 0) + 1
    require(len(missing_by_parameter) == 12 and min(missing_by_parameter.values()) == 10,
            "S01: minimum missing positive cells per parameter set must be exactly ten")
    for absent in ("SHA3-224", "SHAKE-128"):
        require(not any(cell.get("hashAlg") == absent and cell.get("covered") for cell in cells),
                f"S01: {absent} must have no positive sample cell")


def write_new_gate_record(path: Path, record: str, label: str) -> None:
    proper_relative_parts(path, path.parent, label)
    parent_owner = _OwnedDescriptor(
        open_absolute_directory_fd(path.parent, f"{label} output parent"),
        f"{label} output parent")
    file_owner = _OwnedDescriptor(-1, f"{label} output file")
    try:
        file_owner = _OwnedDescriptor(os.open(
            path.name,
            os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW | os.O_CLOEXEC,
            0o600, dir_fd=parent_owner.descriptor), f"{label} output file")
        data = (record + "\n").encode("ascii")
        offset = 0
        while offset < len(data):
            offset += os.write(file_owner.descriptor, data[offset:])
        status = os.fstat(file_owner.descriptor)
        require(stat.S_ISREG(status.st_mode) and status.st_size == len(data),
                f"S01: {label} output is not an exact ordinary record file")
    except BaseException as error:
        _close_owned_descriptors(
            [file_owner, parent_owner], f"{label} output", error)
        if isinstance(error, (OSError, UnicodeError)):
            raise CheckFailure(f"S01: cannot write {label} output: {error}") from error
        raise
    _close_owned_descriptors([file_owner, parent_owner], f"{label} output")
    require_ordinary_file_under(path, path.parent, label)


def main() -> int:
    try:
        if sys.argv[1:] == ["--elaborated-acvp-dependencies"]:
            check_elaborated_s01_dependencies()
            return 0
        if sys.argv[1:] == ["--audit-acvp-lake-config"]:
            validate_translated_lake_parser_mapping()
            print("S01 elaborated Lake configuration audit: PASS "
                  "(slhdsa_acvp_parser -> HashSigTest.SLHDSA.ACVP.ParserTests)")
            return 0
        if len(sys.argv) == 5 and sys.argv[1] == "--resolve-acvp-parser-executable":
            build_root = canonical_cli_absolute_path(sys.argv[2], "fresh parser build root")
            path_output = canonical_cli_absolute_path(sys.argv[3], "resolved parser path output")
            hash_output = canonical_cli_absolute_path(sys.argv[4], "expected parser hash output")
            binary_path, expected_hash = query_and_validate_fresh_parser_build(
                build_root=build_root, private_parent=build_root.parent,
                echo_stderr=True, run_self_tests=True)
            write_new_gate_record(path_output, str(binary_path), "resolved parser path")
            write_new_gate_record(hash_output, expected_hash, "expected parser SHA-256")
            return 0
        if len(sys.argv) == 4 and sys.argv[1] == "--sha256-ordinary-file":
            path = canonical_cli_absolute_path(sys.argv[2], "SHA-256 input")
            ordinary_root = canonical_cli_absolute_path(sys.argv[3], "SHA-256 root")
            print(sha256_ordinary_file(path, ordinary_root))
            return 0
        if len(sys.argv) == 5 and sys.argv[1] == "--sha256-ordinary-file":
            path = canonical_cli_absolute_path(sys.argv[2], "SHA-256 input")
            ordinary_root = canonical_cli_absolute_path(sys.argv[3], "SHA-256 root")
            output = canonical_cli_absolute_path(sys.argv[4], "SHA-256 output")
            write_new_gate_record(
                output, sha256_ordinary_file(path, ordinary_root),
                "current parser SHA-256")
            return 0
        require(not sys.argv[1:],
                "usage: check-harness.py "
                "[--elaborated-acvp-dependencies|--audit-acvp-lake-config|"
                "--resolve-acvp-parser-executable FRESH_BUILD PATH_FILE HASH_FILE|"
                "--sha256-ordinary-file FILE ROOT [OUTPUT_FILE]]")
        check_hygiene()
        check_required_files()
        check_csvs()
        check_policy_fixtures()
        check_lean_policy()
        check_acvp_dependency_sources()
        check_fips_profile()
        check_reference_manifest()
        check_s01_metadata()
    except CheckFailure as error:
        print(f"SLH-DSA harness check: FAIL: {error}", file=sys.stderr)
        return 1
    print("SLH-DSA harness check: PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
