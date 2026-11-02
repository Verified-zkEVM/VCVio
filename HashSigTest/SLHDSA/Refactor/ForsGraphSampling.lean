/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.Security.ForsGraphSampling
public import HashSigTest.SLHDSA.Refactor.ForsGraphRecovery

/-!
# Ordinary canonical FORS sampling clients

The concrete 128s and 192f consumers retain every event of the jointly returned graph state and
full-answer cache. Prefix marginals use the existing byte-prefix law with their actual fit
inequalities. The arithmetic-valid short-digest instance retains its padded state conversion
without a uniform-node interpretation.
-/

public section

open OracleComp OracleSpec RandomOracleTraversal SLHDSA SLHDSA.Graph SLHDSA.Security
open scoped ENNReal

namespace SLHDSA.Refactor.ForsGraphSamplingTest

local notation "vp128" => FipsParameterSet.SLHDSA_SHAKE_128s.validatedParams
local notation "vp192" => FipsParameterSet.SLHDSA_SHAKE_192f.validatedParams

/-- Every joint 128s graph-state/cache event has the independently programmed-table law. -/
theorem shake128s_event (pk : Bytes (vp128).params.n) (key : ForsKey (vp128).params)
    (md : List Byte) (initial : Node (vp128).params → Bytes (vp128).params.n)
    (event : ((Node (vp128).params → Bytes (vp128).params.n) ×
      QueryCache (shakeSpec vp128)) → Prop) :
    Pr{let result ← (simulateQ randomOracle
      (evaluate (GraphInput.input vp128 pk)
        (fun parent cells (answer : Bytes (vp128).params.m) =>
          updateCell parent cells (prefixBytes (vp128).params.n answer))
        (ForsSchedule.signing key md) initial)).run ∅}[event result] =
      Pr{let outputs ← ForsGraphSampling.uniformAnswers vp128}[
        let nodes := ForsSchedule.signing key md
        let target := GraphProgramming.tableTarget vp128 nodes initial outputs
        event (target, Programming.cacheFrom
          (fun parent => GraphInput.input vp128 pk parent target) outputs nodes ∅)] := by
  simpa only [prEvent_map] using
    (ForsGraphSampling.shake128s pk key md initial).prEvent_eq event

/-- The actual 192f schedule uses the same sampling mechanism and complete joint observation. -/
theorem shake192f_event (pk : Bytes (vp192).params.n) (key : ForsKey (vp192).params)
    (md : List Byte) (initial : Node (vp192).params → Bytes (vp192).params.n)
    (event : ((Node (vp192).params → Bytes (vp192).params.n) ×
      QueryCache (shakeSpec vp192)) → Prop) :
    Pr{let result ← (simulateQ randomOracle
      (evaluate (GraphInput.input vp192 pk)
        (fun parent cells (answer : Bytes (vp192).params.m) =>
          updateCell parent cells (prefixBytes (vp192).params.n answer))
        (ForsSchedule.signing key md) initial)).run ∅}[event result] =
      Pr{let outputs ← ForsGraphSampling.uniformAnswers vp192}[
        let nodes := ForsSchedule.signing key md
        let target := GraphProgramming.tableTarget vp192 nodes initial outputs
        event (target, Programming.cacheFrom
          (fun parent => GraphInput.input vp192 pk parent target) outputs nodes ∅)] := by
  simpa only [prEvent_map] using
    (ForsGraphSampling.shake192f pk key md initial).prEvent_eq event

/-- Actual 128s node-length prefixes of a full answer are uniform. -/
theorem shake128s_prefix (value : Bytes (vp128).params.n) :
    Pr{let answer ← $ᵗ (Bytes (vp128).params.m)}[
      prefixBytes (vp128).params.n answer = value] =
      (Nat.card (Bytes (vp128).params.n) : ℝ≥0∞)⁻¹ :=
  prEvent_uniformSample_prefixBytes_eq (by decide) value

/-- Actual 192f supplies its own prefix-fit certificate to the same byte-prefix law. -/
theorem shake192f_prefix (value : Bytes (vp192).params.n) :
    Pr{let answer ← $ᵗ (Bytes (vp192).params.m)}[
      prefixBytes (vp192).params.n answer = value] =
      (Nat.card (Bytes (vp192).params.n) : ℝ≥0∞)⁻¹ :=
  prEvent_uniformSample_prefixBytes_eq (by decide) value

/-- A cache populated in another actual 192f coordinate remains fresh for a singleton traversal. -/
theorem shake192f_local_namespace (pk : Bytes (vp192).params.n)
    (left right : StructuralNode (vp192).params) (different : left ≠ right)
    (cells : Node (vp192).params → Bytes (vp192).params.n)
    (answer : Bytes (vp192).params.m) :
    FreshFor (GraphInput.input vp192 pk) [left]
      ((∅ : QueryCache (shakeSpec vp192)).cacheQuery
        (GraphInput.input vp192 pk right cells) answer) :=
  ForsGraphSampling.freshFor_single_outside vp192 (Graph.widths_fips .SLHDSA_SHAKE_192f)
    pk [left] right
    (by simpa using Ne.symm different) cells answer

local notation "shortVp" => ForsGraphRecovery.shortVp

/-- The complete short-digest state/cache sampling law remains valid with actual padding. -/
theorem short_digest_sampling (pk : Bytes (shortVp).params.n) (key : ForsKey (shortVp).params)
    (md : List Byte) (initial : Node (shortVp).params → Bytes (shortVp).params.n) :
    let nodes := ForsSchedule.signing key md
    (simulateQ randomOracle
      (evaluate (GraphInput.input shortVp pk)
        (fun parent cells (answer : Bytes (shortVp).params.m) =>
          updateCell parent cells (prefixBytes (shortVp).params.n answer))
        nodes initial)).run ∅ =ᵈ
      ((fun outputs =>
        let target := GraphProgramming.tableTarget shortVp nodes initial outputs
        (target, Programming.cacheFrom
          (fun parent => GraphInput.input shortVp pk parent target) outputs nodes ∅)) <$>
        ForsGraphSampling.uniformAnswers shortVp) :=
  ForsGraphSampling.signing_empty shortVp (by constructor <;> decide) pk key md initial

/-- The short-digest example does not satisfy the prefix-uniformity law's fit premise. -/
theorem short_digest_not_prefix_fit : ¬ (shortVp).params.n ≤ (shortVp).params.m := by decide

end SLHDSA.Refactor.ForsGraphSamplingTest
