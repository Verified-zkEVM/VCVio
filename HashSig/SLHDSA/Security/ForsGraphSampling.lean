/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.Security.GraphProgramming
public import VCVio.OracleComp.QueryTracking.RandomOracle.Traversal

/-!
# Full-answer sampling for the canonical FORS graph

The existing canonical SHAKE input and ordered FORS schedule instantiate the generic fresh
traversal law. The result retains the complete graph state and full-answer outer cache.
Uniform answers have the full digest length; the state stores their canonical node-length
prefix conversion, including its padding behavior. A uniform node-length marginal requires
the separate prefix-fit condition. These local laws assert no freshness of an arbitrary warm
signing execution and impose no new premise on the universal effectful program equality.
-/

public section

open OracleComp OracleSpec RandomOracleTraversal
open SLHDSA.Graph

namespace SLHDSA.Security.ForsGraphSampling

/-- Sample independent full-length answers at finite structural coordinates without a
computable enumeration of the complete graph. -/
@[expose] noncomputable def uniformAnswers (vp : ValidatedParams) :
    ProbComp (StructuralNode vp.params → Bytes vp.params.m) :=
  letI : Fintype (StructuralNode vp.params) := Fintype.ofFinite _
  $ᵗ (StructuralNode vp.params → Bytes vp.params.m)

/-- A duplicate-free fresh canonical traversal retains its entire state and full-answer cache. -/
theorem evaluate_eq_uniform_program (vp : ValidatedParams) (widths : Widths vp.params)
    (pk : Bytes vp.params.n) (nodes : List (StructuralNode vp.params)) (unique : nodes.Nodup)
    (initial : Node vp.params → Bytes vp.params.n) (cache : QueryCache (shakeSpec vp))
    (fresh : FreshFor (GraphInput.input vp pk) nodes cache) :
    (simulateQ randomOracle
      (evaluate (GraphInput.input vp pk)
        (fun parent cells (answer : Bytes vp.params.m) =>
          updateCell parent cells (prefixBytes vp.params.n answer))
        nodes initial)).run cache =ᵈ
      ((fun outputs => program (GraphInput.input vp pk)
          (fun parent cells (answer : Bytes vp.params.m) =>
          updateCell parent cells (prefixBytes vp.params.n answer))
          outputs nodes initial cache) <$> uniformAnswers vp) := by
  let : Fintype (StructuralNode vp.params) := Fintype.ofFinite _
  exact RandomOracleTraversal.evalDist_evaluate_eq_uniform_program
    (GraphInput.input vp pk)
    (fun parent cells (answer : Bytes vp.params.m) =>
          updateCell parent cells (prefixBytes vp.params.n answer))
    (GraphInput.input_separated vp widths pk) nodes unique initial cache fresh

/-- A cached coordinate outside a traversal's namespace does not invalidate local freshness. -/
theorem freshFor_single_outside (vp : ValidatedParams) (widths : Widths vp.params)
    (pk : Bytes vp.params.n) (nodes : List (StructuralNode vp.params))
    (reserved : StructuralNode vp.params) (outside : reserved ∉ nodes)
    (reservedCells : Node vp.params → Bytes vp.params.n) (answer : Bytes vp.params.m) :
    FreshFor (GraphInput.input vp pk) nodes
      ((∅ : QueryCache (shakeSpec vp)).cacheQuery
        (GraphInput.input vp pk reserved reservedCells) answer) := by
  intro node member cells
  have different : node ≠ reserved := by
    intro same
    exact outside (same ▸ member)
  rw [QueryCache.cacheQuery_of_ne _ _
    (GraphInput.input_separated vp widths pk node reserved different cells reservedCells)]
  rfl

/-- Fresh canonical subtree evaluation equals an independently sampled full table, with every
boundary cell and full cached answer retained. -/
theorem subtree (vp : ValidatedParams) (widths : Widths vp.params) (pk : Bytes vp.params.n)
    (key : ForsKey vp.params) (height : Nat) (bound : height ≤ vp.params.a)
    (index : Fin (vp.params.k * 2 ^ (vp.params.a - height)))
    (initial : Node vp.params → Bytes vp.params.n) (cache : QueryCache (shakeSpec vp))
    (fresh : FreshFor (GraphInput.input vp pk)
      (ForsSchedule.subtree key height bound index) cache) :
    let nodes := ForsSchedule.subtree key height bound index
    (simulateQ randomOracle
      (evaluate (GraphInput.input vp pk)
        (fun parent cells (answer : Bytes vp.params.m) =>
          updateCell parent cells (prefixBytes vp.params.n answer))
        nodes initial)).run cache =ᵈ
      ((fun outputs =>
        let target := GraphProgramming.tableTarget vp nodes initial outputs
        (target, Programming.cacheFrom
          (fun parent => GraphInput.input vp pk parent target) outputs nodes cache)) <$>
        uniformAnswers vp) := by
  let nodes := ForsSchedule.subtree key height bound index
  have law := evaluate_eq_uniform_program vp widths pk nodes
    (ForsSchedule.subtree_nodup key height bound index) initial cache fresh
  have programmed :
      (fun outputs => program (GraphInput.input vp pk)
        (fun parent cells (answer : Bytes vp.params.m) =>
          updateCell parent cells (prefixBytes vp.params.n answer))
        outputs nodes initial cache) =
      (fun outputs =>
        let target := GraphProgramming.tableTarget vp nodes initial outputs
        (target, Programming.cacheFrom
          (fun parent => GraphInput.input vp pk parent target) outputs nodes cache)) := by
    funext outputs
    exact GraphProgramming.subtree_program vp pk key height bound index initial outputs cache
  rw [programmed] at law
  exact law

/-- Fresh canonical signing-forest evaluation retains the complete state and full-answer cache. -/
theorem signing_from (vp : ValidatedParams) (widths : Widths vp.params)
    (pk : Bytes vp.params.n) (key : ForsKey vp.params) (md : List Byte)
    (initial : Node vp.params → Bytes vp.params.n) (cache : QueryCache (shakeSpec vp))
    (fresh : FreshFor (GraphInput.input vp pk) (ForsSchedule.signing key md) cache) :
    let nodes := ForsSchedule.signing key md
    (simulateQ randomOracle
      (evaluate (GraphInput.input vp pk)
        (fun parent cells (answer : Bytes vp.params.m) =>
          updateCell parent cells (prefixBytes vp.params.n answer))
        nodes initial)).run cache =ᵈ
      ((fun outputs =>
        let target := GraphProgramming.tableTarget vp nodes initial outputs
        (target, Programming.cacheFrom
          (fun parent => GraphInput.input vp pk parent target) outputs nodes cache)) <$>
        uniformAnswers vp) := by
  let nodes := ForsSchedule.signing key md
  have law := evaluate_eq_uniform_program vp widths pk nodes
    (ForsSchedule.signing_nodup key md) initial cache fresh
  have programmed :
      (fun outputs => program (GraphInput.input vp pk)
        (fun parent cells (answer : Bytes vp.params.m) =>
          updateCell parent cells (prefixBytes vp.params.n answer))
        outputs nodes initial cache) =
      (fun outputs =>
        let target := GraphProgramming.tableTarget vp nodes initial outputs
        (target, Programming.cacheFrom
          (fun parent => GraphInput.input vp pk parent target) outputs nodes cache)) := by
    funext outputs
    exact GraphProgramming.signing_program vp pk key md initial outputs cache
  rw [programmed] at law
  exact law

/-- The empty-cache canonical signing traversal discharges freshness locally. -/
theorem signing_empty (vp : ValidatedParams) (widths : Widths vp.params)
    (pk : Bytes vp.params.n) (key : ForsKey vp.params) (md : List Byte)
    (initial : Node vp.params → Bytes vp.params.n) :
    let nodes := ForsSchedule.signing key md
    (simulateQ randomOracle
      (evaluate (GraphInput.input vp pk)
        (fun parent cells (answer : Bytes vp.params.m) =>
          updateCell parent cells (prefixBytes vp.params.n answer))
        nodes initial)).run ∅ =ᵈ
      ((fun outputs =>
        let target := GraphProgramming.tableTarget vp nodes initial outputs
        (target, Programming.cacheFrom
          (fun parent => GraphInput.input vp pk parent target) outputs nodes ∅)) <$>
        uniformAnswers vp) :=
  signing_from vp widths pk key md initial ∅ (by intro _ _ _; rfl)

local notation "vp128" => FipsParameterSet.SLHDSA_SHAKE_128s.validatedParams
local notation "vp192" => FipsParameterSet.SLHDSA_SHAKE_192f.validatedParams

/-- Actual SHAKE-128s FORS uses the generic full-table law, with coordinate widths, duplicate
freedom and empty-cache freshness discharged by its concrete schedule. -/
theorem shake128s (pk : Bytes (vp128).params.n) (key : ForsKey (vp128).params)
    (md : List Byte) (initial : Node (vp128).params → Bytes (vp128).params.n) :
    let nodes := ForsSchedule.signing key md
    (simulateQ randomOracle
      (evaluate (GraphInput.input vp128 pk)
        (fun parent cells (answer : Bytes (vp128).params.m) =>
          updateCell parent cells (prefixBytes (vp128).params.n answer))
        nodes initial)).run ∅ =ᵈ
      ((fun outputs =>
        let target := GraphProgramming.tableTarget vp128 nodes initial outputs
        (target, Programming.cacheFrom
          (fun parent => GraphInput.input vp128 pk parent target) outputs nodes ∅)) <$>
        uniformAnswers vp128) :=
  signing_empty vp128 (Graph.widths_fips .SLHDSA_SHAKE_128s) pk key md initial

/-- Actual SHAKE-192f FORS uses the same full-table law and its own concrete coordinates and
schedule. -/
theorem shake192f (pk : Bytes (vp192).params.n) (key : ForsKey (vp192).params)
    (md : List Byte) (initial : Node (vp192).params → Bytes (vp192).params.n) :
    let nodes := ForsSchedule.signing key md
    (simulateQ randomOracle
      (evaluate (GraphInput.input vp192 pk)
        (fun parent cells (answer : Bytes (vp192).params.m) =>
          updateCell parent cells (prefixBytes (vp192).params.n answer))
        nodes initial)).run ∅ =ᵈ
      ((fun outputs =>
        let target := GraphProgramming.tableTarget vp192 nodes initial outputs
        (target, Programming.cacheFrom
          (fun parent => GraphInput.input vp192 pk parent target) outputs nodes ∅)) <$>
        uniformAnswers vp192) :=
  signing_empty vp192 (Graph.widths_fips .SLHDSA_SHAKE_192f) pk key md initial

end SLHDSA.Security.ForsGraphSampling
