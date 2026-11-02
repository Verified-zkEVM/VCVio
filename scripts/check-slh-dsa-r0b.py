#!/usr/bin/env python3
"""Freshly check current SLH-DSA strength, operational and readable contracts.

Normal `lake test` calls this after its registered executables and exact table check. This
command checks their bindings; it never reruns those runtimes or recursively invokes `lake test`.
The unchanged check-slh-dsa-r0.py remains the separately callable historical construction-syntax
audit. Changed protected construction identity is a historical nonPASS, not a refreshed baseline.
"""
from __future__ import annotations

import argparse
import importlib.util
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile
import time

ROOT = Path(__file__).resolve().parents[1]
DATA = ROOT / "docs/design/slh-dsa-reuse-evidence/r0b"
MODULE = "HashSigTest.SLHDSA.Refactor.SemanticContracts"
LEAVES = ["HashSigTest.SLHDSA.Refactor.Semantics." + name
          for name in ("Legacy", "Bounds", "Game", "Construction")]
RUNTIMES = {"slhdsa_shake128s_compiler_tests", "slhdsa_shake128s_game_tests",
            "slhdsa_shake128s_wire_bridge_tests", "slhdsa_fors_secret_order_tests"}
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
# This archived digest describes a whole implementation, rather than a runtime/parser binding.
# Its historical value stays in bindings.json; current construction claims are checked below.
HISTORICAL_SCHEME_SOURCE = "HashSig/SLHDSA/SHAKE128s/Statement/Scheme.lean"
# Explicit compiler owner/client retain the original executable canary.
COMPILER_SOURCE = "HashSigTest/SLHDSA/SHAKE128s/Compiler.lean"
COMPILER_OWNER = "ToMathlib/Compiler/FinCases.lean"
COMPILER_OWNER_MODULE = "ToMathlib.Compiler.FinCases"
COMPILER_RULE = "Fin.cases_eq_casesDirect"
COMPILER_MAIN = "def main : IO Unit := SLHDSA.SHAKE128s.CompilerTest.check"
COMPILER_CANARY_SHA256 = "cd397f6186ac9a4151337b741ed4df661c6d6c61c32a1741567cc2d588e710c8"
# The archived Game source digest remains in bindings.json. Current readable Game
# meaning is checked by these literal full types, freshly elaborated below. Never derive
# these types from the current proof source: the applications freeze all 15 contracts.
HISTORICAL_GAME_SOURCE = "HashSigTest/SLHDSA/Refactor/Semantics/Game.lean"
READABLE_GAME_WITNESSES = r"""/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSigTest.SLHDSA.Refactor.Semantics.Game

/-! # Complete quantified readable Game witnesses -/

public section
open OracleComp OracleSpec
open scoped ENNReal
open SLHDSA.SHAKE128s

example : ∀ {Output : Type} (input : (Game.World Output).Domain),
  Game.hashCost input = match input with
      | .inl _ => 0
      | .inr _ => 1 := SLHDSA.Refactor.Semantics.hashSelectorEquation

example : ∀ {Output PK SK : Type}
    (scheme : Game.ExternalScheme Output PK SK) (sk : SK) (request : Message)
    (signed : Game.SigningLog),
  ((Game.Counted.legacyRun
      (SignatureAlg.SigningView.countedSigningOracleUsing Game.Counted.phasePolicy
        (scheme.sign sk) request)).run).run signed =
      scheme.sign sk request >>= fun answer =>
        pure ((answer, Multiplicative.ofAdd (Game.Counts.single .signing 1)),
          signed ++ [⟨request, answer⟩]) := SLHDSA.Refactor.Semantics.countedSigningEquation

example : ∀ {Output PK SK : Type}
    (scheme : Game.ExternalScheme Output PK SK) (adversary : Game.Adversary Output PK)
    (keys : SK × PK),
  Game.afterKeygen scheme adversary keys = (do
      let ((forgery, adversaryCounts), signed) ←
        Game.runPhase scheme keys.1 (adversary.main keys.2) []
      let (verified, verifierCounts) ← Game.countQueries
        (fun input => Game.Counts.single .verification (Game.hashCost input))
        (scheme.verify keys.2 forgery.message forgery.signature)
      return {
        forgery := forgery
        signed := signed
        verified := verified
        counts := adversaryCounts + verifierCounts }) := SLHDSA.Refactor.Semantics.countedAfterKeygenEquation

example : ∀ (signed : Game.SigningLog) (forgery : Game.Forgery),
  Game.Fresh signed forgery ↔
      ¬∃ entry ∈ signed, entry.1 = forgery.message ∧ entry.2 = some forgery.signature := SLHDSA.Refactor.Semantics.countedFreshnessEquation

example : ∀ (outcome : Game.Outcome),
  Game.Wins outcome ↔ outcome.verified = true ∧
      ¬∃ entry ∈ outcome.signed,
        entry.1 = outcome.forgery.message ∧ entry.2 = some outcome.forgery.signature := SLHDSA.Refactor.Semantics.countedWinningEquation

example : ∀ (outcome : Game.Outcome) (keygenHashes laterHashes : Nat),
  Game.sourceCounts outcome keygenHashes laterHashes = fun kind => match kind with
      | .sign => outcome.counts .signing
      | .hash => outcome.counts .hash
      | .keygen => keygenHashes
      | .signer => laterHashes - outcome.counts .hash - outcome.counts .verification
      | .verifier => outcome.counts .verification := SLHDSA.Refactor.Semantics.countedSourcesEquation

example : ∀ {Output PK SK : Type}
    (scheme : Game.ExternalScheme Output PK SK) (adversary : Game.Adversary Output PK),
  Game.experimentBySource scheme adversary = (do
      let (keys, keygenHashes) ← Game.countAllHashes scheme.keygen
      let (outcome, laterHashes) ← Game.countAllHashes (Game.afterKeygen scheme adversary keys)
      return (outcome, Game.sourceCounts outcome keygenHashes laterHashes)) := SLHDSA.Refactor.Semantics.countedExperimentEquation

example : ∀ {Output PK SK : Type} [SampleableType Output]
    (scheme : Game.ExternalScheme Output PK SK) (adversary : Game.Adversary Output PK),
  Game.runBySource scheme adversary =
      (simulateQ (RandomOracleModel.impl Bytes Output)
        (Game.experimentBySource scheme adversary)).run' ∅ := SLHDSA.Refactor.Semantics.countedRandomOracleEquation

example : ∀ {Output PK SK : Type} [SampleableType Output]
    (scheme : Game.ExternalScheme Output PK SK) (adversary : Game.Adversary Output PK),
  (Game.securityGame scheme).experiment () adversary =
      (fun result => (decide (Game.Wins result.1), result.2)) <$>
        Game.runBySource scheme adversary := SLHDSA.Refactor.Semantics.countedSecurityGameEquation

example : ∀ {Scheme Kind : Type}
    (game : SecurityGame Scheme Kind) (scheme : Scheme) (selected : Finset Kind)
    (adversary : game.Adversary) (budget : Nat),
  game.HasQueryBound scheme selected adversary budget ↔
      Pr{let result ← game.experiment scheme adversary}[
        ∑ kind ∈ selected, result.2 kind ≤ budget] = 1 := SLHDSA.Refactor.Semantics.probabilityOneBudgetEquation

example : signingLimit = 2 ^ 64 := SLHDSA.Refactor.Semantics.signingLimitEquation

example : ∀ {Output PK SK : Type} [SampleableType Output]
    (scheme : Game.ExternalScheme Output PK SK) (adversary : Game.Adversary Output PK),
  Game.WithinSigningLimit scheme adversary ↔
      Pr{let result ← (Game.securityGame scheme).experiment () adversary}[
        result.2 .sign ≤ 2 ^ 64] = 1 := SLHDSA.Refactor.Semantics.lifetimeEquation

example : ∀ {Output PK SK : Type} [SampleableType Output]
    (scheme : Game.ExternalScheme Output PK SK) (selected : Finset Unforgeability.QueryKind)
    (bits : Nat),
  Game.HasSecurityBits scheme selected bits ↔
      ∀ budget : Nat, 1 ≤ budget → ∀ adversary : Game.Adversary Output PK,
        Game.WithinSigningLimit scheme adversary →
        (Game.securityGame scheme).HasQueryBound () selected adversary budget →
        (Game.securityGame scheme).advantage () adversary ≤
          budget / ((2 ^ bits : Nat) : ℝ≥0∞) := SLHDSA.Refactor.Semantics.bitSecurityEquation

example : Game.adversaryWork = ({.sign, .hash, .verifier} : Finset Unforgeability.QueryKind) := SLHDSA.Refactor.Semantics.selectedWorkEquation

example : ∀ (counts : Game.Counts),
  counts.work = counts .hash + counts .verification := SLHDSA.Refactor.Semantics.hashWorkEquation
"""

WOTS_RUNTIME = "slhdsa_wots_integration_tests"
WOTS_TARGET = {"root": "SLHDSAWotsIntegrationTests", "srcDir": "scripts"}
WOTS_JOINT_MODULE = "HashSigTest.SLHDSA.Refactor.WotsIntegration"
WOTS_JOINT_NAMES = ["SLHDSA.Refactor.WotsIntegration." + name
                    for name in ("observePublicKey", "observeSign", "observeRecovery")]

# The archived Construction digest remains unchanged. Fresh literal full-type
# applications below check the readable equations independently of their proof bodies.
HISTORICAL_CONSTRUCTION_SOURCE = "HashSigTest/SLHDSA/Refactor/Semantics/Construction.lean"
READABLE_CONSTRUCTION_WITNESSES = r"""/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSigTest.SLHDSA.Refactor.Semantics.Construction

/-! # Complete quantified readable construction witnesses -/

public section

open OracleComp OracleSpec
open SLHDSA SLHDSA.Security SLHDSA.External SLHDSA.Concrete
open SLHDSA.SHAKE128s

example :
    (FIPS205.params.params.n, FIPS205.params.params.h, FIPS205.params.params.d,
      FIPS205.params.params.hp, FIPS205.params.params.a, FIPS205.params.params.k,
      FIPS205.params.params.m) = (16, 63, 7, 9, 12, 14, 30) :=
  SLHDSA.Refactor.Semantics.shake128sParametersEquation

example : Bridge.verifierCap = 3929 :=
  SLHDSA.Refactor.Semantics.conservativeVerifierCapEquation

example : FIPS205.Answer = SLHDSA.Bytes 30 :=
  SLHDSA.Refactor.Semantics.answerCarrierEquation

example : ∀ (pk : PublicKeyCore FIPS205.core),
    FIPS205.deterministicRand pk = pure pk.pkSeed :=
  SLHDSA.Refactor.Semantics.deterministicRandomizerEquation

example :
    FIPS205.internal = shakeRomScheme FIPS205.params (fun pk => pure pk.pkSeed)
      ($ᵗ FIPS205.core.PkSeed) :=
  SLHDSA.Refactor.Semantics.internalSchemeEquation

example :
    FIPS205.scheme.keygen = (fun keys => (keys.2, keys.1)) <$> FIPS205.internal.keygen :=
  SLHDSA.Refactor.Semantics.externalKeygenEquation

example : ∀ (sk : SecretKeyCore FIPS205.core) (request : Message),
    FIPS205.scheme.sign sk request =
      match encodePureMessage request.context request.message with
      | .error _ => pure none
      | .ok message =>
        (fun signature => some (encodeSignature FIPS205.params
          (shakeWireCodec FIPS205.params.params) signature)) <$>
            FIPS205.internal.sign ⟨sk.pkSeed, sk.pkRoot⟩ sk message :=
  SLHDSA.Refactor.Semantics.externalSigningEquation

example : ∀ (pk : PublicKeyCore FIPS205.core)
    (request : Message) (signature : SHAKE128s.Bytes),
    FIPS205.scheme.verify pk request signature =
      match encodePureMessage request.context request.message with
      | .error _ => pure false
      | .ok message =>
        match decodeSignature FIPS205.params (shakeWireCodec FIPS205.params.params) signature with
        | .error _ => pure false
        | .ok decoded => FIPS205.internal.verify pk message decoded :=
  SLHDSA.Refactor.Semantics.externalVerificationEquation

example : ∀ {p : Params} (core : CorePrimitives p)
    {m : Type → Type*} [Monad m]
    (hash : Adrs → core.Y → m core.Y) (nodeHash : Adrs → core.Y → core.Y → m core.Y)
    (secret : Adrs → m core.Y) (digest : List Byte) (address : Adrs),
    forsSignWithSecret core hash nodeHash secret digest address =
      Vector.ofFnM (fun i : Fin p.k => do
        let index := i.val * 2 ^ p.a + forsIdx p digest i.val
        let selected ← secret (forsSkAdrs address index)
        let path ← PerfectMerkleTree.intrinsicAuthPathM
          (forsLeafWithSecret core hash secret address)
          (forsNodeHashWith nodeHash address) index p.a
        return ⟨selected, path⟩) :=
  SLHDSA.Refactor.Semantics.secretFirstProgramEquation

example : ForsSecretOrderTest.expectedTrace = [
    .secret ⟨2, 7, 6, 3, 0, 1⟩,
    .secret ⟨2, 7, 6, 3, 0, 0⟩, .leafHash ⟨2, 7, 3, 3, 0, 0⟩ 100,
    .secret ⟨2, 7, 6, 3, 0, 2⟩, .leafHash ⟨2, 7, 3, 3, 0, 2⟩ 102,
    .secret ⟨2, 7, 6, 3, 0, 3⟩, .leafHash ⟨2, 7, 3, 3, 0, 3⟩ 103,
    .nodeHash ⟨2, 7, 3, 3, 1, 1⟩ 1122 1133,
    .secret ⟨2, 7, 6, 3, 0, 6⟩,
    .secret ⟨2, 7, 6, 3, 0, 7⟩, .leafHash ⟨2, 7, 3, 3, 0, 7⟩ 107,
    .secret ⟨2, 7, 6, 3, 0, 4⟩, .leafHash ⟨2, 7, 3, 3, 0, 4⟩ 104,
    .secret ⟨2, 7, 6, 3, 0, 5⟩, .leafHash ⟨2, 7, 3, 3, 0, 5⟩ 105,
    .nodeHash ⟨2, 7, 3, 3, 1, 2⟩ 1144 1155] :=
  SLHDSA.Refactor.Semantics.literalForsTraceEquation
"""

# The runtime file retains its original whole-source binding. Its named rejection
# proof may use the public signing-view equation without changing executable behavior.
WIRE_BRIDGE_SOURCE = "HashSigTest/SLHDSA/SHAKE128s/WireBridge.lean"
WIRE_BRIDGE_SIGNING_PROOF = r"""theorem executableRejectedSign_eq (sk : SecretKeyCore FIPS205.core)
    (request : Message) (long : 255 < request.context.length) :
    executableRejectedSign request long = FIPS205.scheme.sign sk request := by
  unfold executableRejectedSign
  split <;> rename_i framed
  · simp only [FIPS205.scheme, framed]
  · rw [encodePureMessage_error request long] at framed
    cases framed
"""

# The counted-game fixture retains its original whole-file digest. Only the exact
# two shared-program wrapper bodies below may be normalized to their original bodies.
SUPPORT_SOURCE = "HashSigTest/SLHDSA/SHAKE128s/Support.lean"
SUPPORT_WRAPPERS = (
    (r"""@[expose] def executableAfterKeygen (scheme : ExternalScheme Output PK SK)
    (adversary : Adversary Output PK) (keys : SK × PK) :
    OracleComp (World Output) Outcome := do
  let (sk, pk) := keys
  let ((forgery, adversaryCounts), signed) ←
    (simulateQ
      ((QueryImpl.ofLift (World Output)
          (StateT SigningLog (OracleComp (World Output)))).withAddCost
          (fun input => Counts.single .hash (hashCost input)) + signingOracle scheme sk)
      (adversary.main pk)).run.run []
  let (verified, verifierCounts) ← countQueries
    (fun input => Counts.single .verification (hashCost input))
    (scheme.verify pk forgery.message forgery.signature)
  return {
    forgery := forgery
    signed := signed
    verified := verified
    counts := Multiplicative.toAdd adversaryCounts + verifierCounts }

""", r"""@[expose] def executableAfterKeygen (scheme : ExternalScheme Output PK SK)
    (adversary : Adversary Output PK) (keys : SK × PK) :
    OracleComp (World Output) Outcome :=
  Counted.legacyOutcome <$> Counted.canonicalAfterKeygen scheme adversary keys

"""),
    (r"""@[expose] def executableExperimentBySource (scheme : ExternalScheme Output PK SK)
    (adversary : Adversary Output PK) :
    OracleComp (World Output) (Outcome × Unforgeability.QueryCounts) := do
  let (keys, keygenHashes) ← countAllHashes scheme.keygen
  let (outcome, laterHashes) ← countAllHashes (executableAfterKeygen scheme adversary keys)
  return (outcome, sourceCounts outcome keygenHashes laterHashes)

""", r"""@[expose] def executableExperimentBySource (scheme : ExternalScheme Output PK SK)
    (adversary : Adversary Output PK) :
    OracleComp (World Output) (Outcome × Unforgeability.QueryCounts) :=
  Counted.legacyObservation <$> Counted.canonicalExperiment scheme adversary

"""),
)

spec = importlib.util.spec_from_file_location("slh_dsa_r0a", ROOT / "scripts/check-slh-dsa-r0.py")
if spec is None or spec.loader is None:
    raise RuntimeError("The original R0a verifier is unavailable")
r0a = importlib.util.module_from_spec(spec)
spec.loader.exec_module(r0a)


def execute(argv: list[str], log: Path, steps: list[dict]) -> None:
    environment = {key: value for key, value in os.environ.items()
                   if key not in ("LEAN_PATH", "LEAN_SRC_PATH")}
    started = time.monotonic()
    with log.open("wb") as output:
        result = subprocess.run(argv, cwd=ROOT, stdout=output, stderr=subprocess.STDOUT,
                                env={**environment, "LEAN_NUM_THREADS": "4"})
    steps.append({"argv": argv, "exitCode": result.returncode,
                  "seconds": round(time.monotonic() - started, 3),
                  "log": str(log), "sha256": r0a.sha256(log.read_bytes())})
    if result.returncode:
        raise RuntimeError(f"Command exited {result.returncode}; see {log}")


def test_driver(source: str) -> str:
    """Select the ordinary driver's complete control-flow scaffold."""
    marker = "script test (args) do"
    if source.count(marker) != 1:
        raise ValueError("The ordinary test-driver declaration is ambiguous")
    return source.split(marker, 1)[1].split("/-- ML-KEM test executable", 1)[0]


def driver_scaffold(driver: str) -> str:
    """Allow additive standalone unprotected exe entries; retain every other source byte."""
    result = []
    pattern = re.compile(r'\s*#\["exe", "([A-Za-z0-9_]+)"\],?\s*')
    for line in driver.splitlines(keepends=True):
        match = pattern.fullmatch(line)
        if match and match[1] not in RUNTIMES:
            continue
        result.append(line)
    return "".join(result)


def target_binding(source: str, name: str) -> dict:
    """Fail closed on nonliteral or extra configuration of a protected executable."""
    prefix = r"^lean_exe " + re.escape(name) + r"\b"
    if len(re.findall(prefix, source, re.MULTILINE)) != 1:
        raise ValueError(f"Protected target declaration is ambiguous: {name}")
    match = re.search(prefix + r" where\n((?:[ \t].*\n|\n)*)", source, re.MULTILINE)
    if match is None:
        raise ValueError(f"Protected target configuration is unsupported: {name}")
    values = {"srcDir": "."}
    seen = set()
    for line in match[1].splitlines():
        line = line.split("--", 1)[0].strip()
        if not line:
            continue
        root = re.fullmatch(r"root\s*:=\s*`([A-Za-z0-9_.]+)", line)
        directory = re.fullmatch(r'srcDir\s*:=\s*("[^"\\]*")', line)
        if root:
            field, value = "root", root[1]
        elif directory:
            field, value = "srcDir", json.loads(directory[1])
        else:
            raise ValueError(f"Protected target has unsupported configuration: {name}: {line}")
        if field in seen:
            raise ValueError(f"Protected target field is duplicated: {name}.{field}")
        seen.add(field)
        values[field] = value
    if "root" not in values:
        raise ValueError(f"Protected target has no literal module root: {name}")
    return values


def check_current_compiler() -> dict:
    """Bind the explicit owner/client while retaining the original executable canary."""
    source = (ROOT / COMPILER_SOURCE).read_text()
    owner = (ROOT / COMPILER_OWNER).read_bytes()
    imports = [line.split("--", 1)[0].strip() for line in
               re.findall(r"^(?:(?:public|meta)[ \t]+)*import[ \t]+([^\n]+)$",
                          source, re.MULTILINE)]
    if imports != [COMPILER_OWNER_MODULE, "HashSig.SLHDSA.SHAKE128s.Statement.Scheme"]:
        raise ValueError("Compiler client must import the explicit owner and actual Scheme client")
    owner_imports = [line.split("--", 1)[0].strip() for line in
                     re.findall(r"^(?:(?:public|meta)[ \t]+)*import[ \t]+([^\n]+)$",
                                owner.decode(), re.MULTILINE)]
    if owner_imports != ["Mathlib.Data.Fin.Basic"]:
        raise ValueError("Compiler owner must retain its explicit finite-index dependency")
    start = "namespace SLHDSA.SHAKE128s.CompilerTest\n"
    end = "end SLHDSA.SHAKE128s.CompilerTest\n"
    if source.count(start) != 1 or source.count(end) != 1:
        raise ValueError("Compiler canary namespace is ambiguous")
    canary = source[source.index(start):source.index(end) + len(end)]
    if r0a.sha256(canary.encode()) != COMPILER_CANARY_SHA256:
        raise ValueError("The original direct/nested compiler canary changed")
    tail = source[source.index(end) + len(end):].strip()
    if tail.startswith("/--"):
        doc_end = tail.find("-/")
        if doc_end < 0:
            raise ValueError("Compiler main doc comment is unterminated")
        tail = tail[doc_end + 2:].strip()
    if tail != COMPILER_MAIN or len(re.findall(r"^def main\b", source, re.MULTILINE)) != 1:
        raise ValueError("Compiler main must make its original single CompilerTest.check call")
    return {"owner": COMPILER_OWNER, "rule": COMPILER_RULE,
            "ownerSha256": r0a.sha256(owner),
            "client": COMPILER_SOURCE, "clientSha256": r0a.sha256(source.encode()),
            "originalCanarySha256": COMPILER_CANARY_SHA256,
            "scope": "Imports/canary/main bindings; whole source hashes are observed provenance only; "
                     "preceding ordinary lake-test step executes the canary"}


def check_bindings(bindings: dict) -> list[str]:
    check_current_compiler()
    wire_source = (ROOT / WIRE_BRIDGE_SOURCE).read_bytes()
    original_proof = WIRE_BRIDGE_SIGNING_PROOF.encode()
    public_equation_proof = WIRE_BRIDGE_SIGNING_PROOF.replace(
        "  · simp only [FIPS205.scheme, framed]",
        "  · simp only [FIPS205.scheme, FIPS205.signingView_sign, framed]", 1).encode()
    if wire_source.count(public_equation_proof) == 1:
        wire_source = wire_source.replace(public_equation_proof, original_proof, 1)
    if r0a.sha256(wire_source) != bindings["runtimeSourceSha256"][WIRE_BRIDGE_SOURCE]:
        raise ValueError(f"Frozen runtimeSourceSha256 binding changed: {WIRE_BRIDGE_SOURCE}")
    support_source = (ROOT / SUPPORT_SOURCE).read_bytes()
    wrappers = [(old.encode(), new.encode()) for old, new in SUPPORT_WRAPPERS]
    if all(support_source.count(new) == 1 for _, new in wrappers):
        for old, new in wrappers:
            support_source = support_source.replace(new, old, 1)
    if r0a.sha256(support_source) != bindings["runtimeSourceSha256"][SUPPORT_SOURCE]:
        raise ValueError(f"Frozen runtimeSourceSha256 binding changed: {SUPPORT_SOURCE}")
    bindings = {**bindings, "runtimeSourceSha256": {
        path: digest for path, digest in bindings["runtimeSourceSha256"].items()
        if path != SUPPORT_SOURCE}}
    # Preserve every archived binding on disk; only whole Construction proof identity
    # is superseded by the literal quantified applications executed below.
    bindings = {**bindings, "semanticSourceSha256": {
        path: digest for path, digest in bindings["semanticSourceSha256"].items()
        if path != HISTORICAL_CONSTRUCTION_SOURCE}, "runtimeSourceSha256": {
        path: digest for path, digest in bindings["runtimeSourceSha256"].items()
        if path != WIRE_BRIDGE_SOURCE}}
    for field in ("r0aProtectedFiles", "semanticSourceSha256", "runtimeSourceSha256"):
        for relative, digest in bindings[field].items():
            if field == "runtimeSourceSha256" and relative in {HISTORICAL_SCHEME_SOURCE, COMPILER_SOURCE}:
                continue
            if field == "semanticSourceSha256" and relative == HISTORICAL_GAME_SOURCE:
                continue
            if r0a.sha256((ROOT / relative).read_bytes()) != digest:
                raise ValueError(f"Frozen {field} binding changed: {relative}")
    original = json.loads((ROOT / "docs/design/slh-dsa-reuse-evidence/r0/capture-input.json").read_text())
    groups = bindings["semanticGroups"]
    if groups.keys() != original["semanticGroups"].keys():
        raise ValueError("The readable contracts must cover exactly the original eleven groups")
    declared = []
    for module in LEAVES:
        source = ROOT / (module.replace(".", "/") + ".lean")
        declared.extend(re.findall(r"^theorem (\w+)", source.read_text(), re.MULTILINE))
    selected = [name for names in groups.values() for name in names]
    if len(set(declared)) != len(declared) or set(selected) != set(declared):
        raise ValueError("Readable contract coverage omitted or redirected a public equation")
    if set(bindings["registeredRuntimes"]) != RUNTIMES:
        raise ValueError("The four original runtime bindings changed")
    lakefile = (ROOT / "lakefile.lean").read_text()
    driver = test_driver(lakefile)
    targets = bindings["targetBindings"]
    if set(targets) != RUNTIMES | {"slhdsa_bound_table"}:
        raise ValueError("The protected executable/table target inventory changed")
    for name, expected in targets.items():
        if target_binding(lakefile, name) != expected:
            raise ValueError(f"Protected target root/srcDir changed: {name}")
    if r0a.sha256(driver_scaffold(driver).encode()) != bindings["driverScaffoldSha256"]:
        raise ValueError("The protected test-driver control-flow scaffold changed")
    for name in sorted(RUNTIMES):
        pattern = r'#\[\s*"exe"\s*,\s*"' + re.escape(name) + r'"\s*\]'
        if len(re.findall(pattern, driver)) != 1:
            raise ValueError(f"Ordinary lake test must register {name} exactly once")
    if target_binding(lakefile, WOTS_RUNTIME) != WOTS_TARGET:
        raise ValueError("The WOTS integration runtime root/srcDir changed")
    wots_registration = r'#\[\s*"exe"\s*,\s*"' + WOTS_RUNTIME + r'"\s*\]'
    if len(re.findall(wots_registration, driver)) != 1:
        raise ValueError("Ordinary lake test must register the WOTS integration runtime exactly once")
    if len(re.findall(r'"scripts/check-slh-dsa-r0b\.py"', driver)) != 1:
        raise ValueError("Ordinary lake test must register its R0b tail gate exactly once")
    csv = ROOT / "docs/design/slh-dsa-security-bounds.csv"
    if r0a.sha256(csv.read_bytes()) != bindings["csvSha256"]:
        raise ValueError("The original exact eighteen-row CSV changed")
    return ["SLHDSA.Refactor.Semantics." + name for name in sorted(declared)]


def check_axioms(names: list[str], report: Path, steps: list[dict]) -> None:
    probe = report / "Axioms.lean"
    imports = [MODULE, r0a.STRENGTH_MODULE, WOTS_JOINT_MODULE, COMPILER_OWNER_MODULE]
    probe.write_text("".join("import " + module + "\n" for module in imports) +
                     "".join("#print axioms " + name + "\n" for name in names))
    log = report / "axioms.log"
    execute(["lake", "env", "lean", "-DautoImplicit=false", str(probe)], log, steps)
    actual = {}
    pattern = r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)"
    for match in re.finditer(pattern, log.read_text(), re.MULTILINE):
        actual[match[1]] = set(filter(None, (name.strip() for name in (match[2] or "").split(","))))
    if set(actual) != set(names):
        raise ValueError("The standard-axiom audit did not cover every current source, witness and joint claim")
    for name, axioms in actual.items():
        if not axioms <= ALLOWED_AXIOMS:
            raise ValueError(f"Nonstandard axioms in {name}: {sorted(axioms - ALLOWED_AXIOMS)}")


def check_current_pins(current: dict, historical: dict) -> None:
    """Check the current lock while retaining the historical evaluator requirement."""
    manifest_bytes = (ROOT / "lake-manifest.json").read_bytes()
    packages = json.loads(manifest_bytes)["packages"]
    revisions = {}
    for package in packages:
        name, revision = package["name"], package.get("rev", "")
        if package["type"] != "git" or re.fullmatch(r"[0-9a-f]{40}", revision) is None:
            raise ValueError(f"Dependency {name} has no full Git revision in the current lock")
        if name in revisions:
            raise ValueError(f"Dependency {name} occurs more than once in the current lock")
        revisions[name] = revision
    if set(current["dependencies"]) != set(revisions):
        raise ValueError("The dependency frame does not cover exactly the current lock")
    r0a.check_pins(current, {
        "manifestSha256": r0a.sha256(manifest_bytes),
        "toolchain": historical["toolchain"],
        "dependencyRevisions": revisions,
    })


def verify(report: Path, steps: list[dict]) -> dict:
    before = r0a.frame()
    (report / "before.json").write_text(json.dumps(before, indent=2) + "\n")
    bindings = json.loads((DATA / "bindings.json").read_text())
    names = check_bindings(bindings)
    historical = ROOT / "docs/design/slh-dsa-reuse-evidence/r0"
    baseline = json.loads((historical / "baseline.json").read_text())
    contracts = json.loads((historical / "kernel-types.json").read_text())["contracts"]
    contract_spec = json.loads((historical / "capture-input.json").read_text())
    if len(contracts) != baseline["strengthContracts"]:
        raise ValueError("The current strength-contract inventory is incomplete")
    source_names = [entry["source"] for entry in contracts]
    witness_names = [entry["witness"] for entry in contracts]
    if len(set(source_names)) != len(contracts) or len(set(witness_names)) != len(contracts):
        raise ValueError("A current strength source or witness occurs more than once")
    check_current_pins(before, baseline)
    version_log = report / "lean-version.log"
    execute(["lake", "env", "lean", "--version"], version_log, steps)
    if version_log.read_text().strip() != baseline["leanVersionOutput"]:
        raise ValueError("The actual commit-bearing Lean evaluator changed")
    execute(["lake", "build", MODULE, r0a.CAPTURE_MODULE, r0a.STRENGTH_MODULE,
             WOTS_JOINT_MODULE, COMPILER_OWNER_MODULE], report / "build.log", steps)
    for index, module in enumerate(LEAVES):
        execute(["lake", "env", "lean", "-DautoImplicit=false",
                 module.replace(".", "/") + ".lean"], report / f"semantic-{index}.log", steps)
    # These are literal full-type applications, not a source/name/axiom-only check.
    game_witnesses = report / "ReadableGameWitnesses.lean"
    game_witnesses.write_text(READABLE_GAME_WITNESSES)
    execute(["lake", "env", "lean", "-DautoImplicit=false", str(game_witnesses)],
            report / "readable-game-witnesses.log", steps)
    # Literal JSON reads are not Lake dependencies: elaborate each family freshly.
    for index, module in enumerate(contract_spec["witnessModules"]):
        execute(["lake", "env", "lean", "-DautoImplicit=false",
                 module.replace(".", "/") + ".lean"], report / f"witness-{index}.log", steps)
    driver = report / "StrengthWitnesses.lean"
    driver.write_text("\n".join("import " + module for module in contract_spec["imports"]) +
                      f"\nimport {r0a.CAPTURE_MODULE}\nimport {r0a.STRENGTH_MODULE}\n\n" +
                      "slhdsa_r0_validate_witnesses " +
                      json.dumps(str(historical / "kernel-types.json")) + "\n")
    witness_log = report / "strength-witnesses.log"
    execute(["lake", "env", "lean", "-DautoImplicit=false", str(driver)], witness_log, steps)
    if f"Validated {len(contracts)} literal kernel contract witnesses" not in witness_log.read_text():
        raise ValueError("The complete current strength-witness validation did not execute")
    # These literal statements retain all ten public Construction equations.
    construction_witnesses = report / "ReadableConstructionWitnesses.lean"
    construction_witnesses.write_text(READABLE_CONSTRUCTION_WITNESSES)
    execute(["lake", "env", "lean", "-DautoImplicit=false", str(construction_witnesses)],
            report / "readable-construction-witnesses.log", steps)
    axiom_names = list(dict.fromkeys(names + source_names + witness_names + WOTS_JOINT_NAMES + [COMPILER_RULE]))
    check_axioms(axiom_names, report, steps)
    after = r0a.frame()
    (report / "after.json").write_text(json.dumps(after, indent=2) + "\n")
    if after != before:
        raise ValueError("Source or dependencies changed during the readable-contract gate")
    return {"accepted": True, "semanticGroups": 11, "publicEquations": len(names),
            "freshStrengthContracts": len(contracts), "standardAxiomClaims": len(axiom_names),
            "freshReadableGameContracts": 15,
            "wotsJointClaims": WOTS_JOINT_NAMES,
            "requiredRuntimeBindings": sorted(RUNTIMES | {WOTS_RUNTIME}),
            "runtimeScope": "Bindings only here; preceding ordinary lake-test steps execute once",
            "freshReadableConstructionContracts": 10,
            "retiredReadableConstructionSourceIdentity": {
                "path": HISTORICAL_CONSTRUCTION_SOURCE,
                "recordedSha256": bindings["semanticSourceSha256"][HISTORICAL_CONSTRUCTION_SOURCE],
                "observedSha256": r0a.sha256((ROOT / HISTORICAL_CONSTRUCTION_SOURCE).read_bytes()),
                "currentCheck": "10 fresh literal full-type readable Construction applications"},
            "historicalConstructionAudit": {
                "executed": False, "accepted": None,
                "command": "python3 scripts/check-slh-dsa-r0.py --report-dir FRESH_EXTERNAL_DIR",
                "scope": "Separate historical construction identity; mismatch is nonPASS, never refreshed"},
            "currentCompilerBinding": check_current_compiler(),
            "historicalCompilerRule": bindings["globalCompilerRule"],
            "historicalCompilerClientSha256": bindings["runtimeSourceSha256"][COMPILER_SOURCE],
            "retiredRuntimeSourceIdentity": {
                "path": HISTORICAL_SCHEME_SOURCE,
                "recordedSha256": bindings["runtimeSourceSha256"][HISTORICAL_SCHEME_SOURCE]},
            "retiredSemanticSourceIdentity": {
                "path": HISTORICAL_GAME_SOURCE,
                "recordedSha256": bindings["semanticSourceSha256"][HISTORICAL_GAME_SOURCE],
                "observedSha256": r0a.sha256((ROOT / HISTORICAL_GAME_SOURCE).read_bytes()),
                "currentCheck": "15 fresh literal full-type readable Game applications"},
            "scope": "Current quantified strength, readable and WOTS joint operational contracts; "
                     "no historical private-body identity or future-family recovery claim"}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--report-dir", type=Path)
    args = parser.parse_args()
    report = (args.report_dir or Path(tempfile.mkdtemp(prefix="vcvio-slh-dsa-r0b-"))).resolve()
    if report.is_relative_to(ROOT):
        parser.error("Use a report directory outside the checkout")
    report.mkdir(parents=True, exist_ok=True)
    if any(report.iterdir()):
        parser.error("The report directory must be empty")
    steps = []
    try:
        result = verify(report, steps)
        status = 0
    except (ValueError, RuntimeError, OSError, KeyError, IndexError) as error:
        result = {"accepted": False, "error": str(error)}
        status = 1
    result["steps"] = steps
    (report / "result.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({**result, "reportDir": str(report)}))
    return status


if __name__ == "__main__":
    raise SystemExit(main())
