/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.Security.GraphProgramming
public import HashSig.SLHDSA.SHAKE128s.Proof.CanonicalGraph.Programming
public import HashSigTest.SLHDSA.Refactor.ForsGraphRecovery

/-! # Ordinary concrete programming consumers -/

public section
open OracleComp OracleSpec SLHDSA SLHDSA.Graph SLHDSA.Security

namespace HashSigTest.SLHDSA.Refactor.GraphProgramming
local notation "vp192" => FipsParameterSet.SLHDSA_SHAKE_192f.validatedParams
local notation "vpShort" => SLHDSA.Refactor.ForsGraphRecovery.shortVp

/-- The actual shake192f subtree uses the proved all-parameter programming law. -/
theorem shake192f_subtree (pk : Bytes (vp192).params.n) (key : ForsKey (vp192).params)
    (height : Nat) (bound : height ≤ (vp192).params.a)
    (index : Fin ((vp192).params.k * 2 ^ ((vp192).params.a - height)))
    (initial : Node (vp192).params → Bytes (vp192).params.n)
    (outputs : StructuralNode (vp192).params → Bytes (vp192).params.m)
    (cache : QueryCache (List Byte →ₒ Bytes (vp192).params.m)) :
    let nodes := ForsSchedule.subtree key height bound index
    let target := GraphProgramming.tableTarget (vp192) nodes initial outputs
    RandomOracleTraversal.program (GraphInput.input (vp192) pk)
      (fun parent cells answer => updateCell parent cells (prefixBytes (vp192).params.n answer))
      outputs nodes initial cache =
      (target, RandomOracleTraversal.Programming.cacheFrom
        (fun parent => GraphInput.input (vp192) pk parent target) outputs nodes cache) :=
  GraphProgramming.subtree_program (vp192) pk key height bound index initial outputs cache

/-- The actual shake192f signing schedule uses the same proved all-parameter programming law. -/
theorem shake192f_signing (pk : Bytes (vp192).params.n) (key : ForsKey (vp192).params)
    (md : List Byte) (initial : Node (vp192).params → Bytes (vp192).params.n)
    (outputs : StructuralNode (vp192).params → Bytes (vp192).params.m)
    (cache : QueryCache (List Byte →ₒ Bytes (vp192).params.m)) :
    let nodes := ForsSchedule.signing key md
    let target := GraphProgramming.tableTarget (vp192) nodes initial outputs
    RandomOracleTraversal.program (GraphInput.input (vp192) pk)
      (fun parent cells answer => updateCell parent cells (prefixBytes (vp192).params.n answer))
      outputs nodes initial cache =
      (target, RandomOracleTraversal.Programming.cacheFrom
        (fun parent => GraphInput.input (vp192) pk parent target) outputs nodes cache) :=
  GraphProgramming.signing_program (vp192) pk key md initial outputs cache

/-- The actual short subtree uses the proved all-parameter programming law. -/
theorem short_subtree (pk : Bytes (vpShort).params.n) (key : ForsKey (vpShort).params)
    (height : Nat) (bound : height ≤ (vpShort).params.a)
    (index : Fin ((vpShort).params.k * 2 ^ ((vpShort).params.a - height)))
    (initial : Node (vpShort).params → Bytes (vpShort).params.n)
    (outputs : StructuralNode (vpShort).params → Bytes (vpShort).params.m)
    (cache : QueryCache (List Byte →ₒ Bytes (vpShort).params.m)) :
    let nodes := ForsSchedule.subtree key height bound index
    let target := GraphProgramming.tableTarget (vpShort) nodes initial outputs
    RandomOracleTraversal.program (GraphInput.input (vpShort) pk)
      (fun parent cells answer => updateCell parent cells (prefixBytes (vpShort).params.n answer))
      outputs nodes initial cache =
      (target, RandomOracleTraversal.Programming.cacheFrom
        (fun parent => GraphInput.input (vpShort) pk parent target) outputs nodes cache) :=
  GraphProgramming.subtree_program (vpShort) pk key height bound index initial outputs cache

/-- The actual short signing schedule uses the same proved all-parameter programming law. -/
theorem short_signing (pk : Bytes (vpShort).params.n) (key : ForsKey (vpShort).params)
    (md : List Byte) (initial : Node (vpShort).params → Bytes (vpShort).params.n)
    (outputs : StructuralNode (vpShort).params → Bytes (vpShort).params.m)
    (cache : QueryCache (List Byte →ₒ Bytes (vpShort).params.m)) :
    let nodes := ForsSchedule.signing key md
    let target := GraphProgramming.tableTarget (vpShort) nodes initial outputs
    RandomOracleTraversal.program (GraphInput.input (vpShort) pk)
      (fun parent cells answer => updateCell parent cells (prefixBytes (vpShort).params.n answer))
      outputs nodes initial cache =
      (target, RandomOracleTraversal.Programming.cacheFrom
        (fun parent => GraphInput.input (vpShort) pk parent target) outputs nodes cache) :=
  GraphProgramming.signing_program (vpShort) pk key md initial outputs cache

/-- The explicit target retains the independent seed for every instance and schedule. -/
theorem target_seed (vp : ValidatedParams) (nodes : List (StructuralNode vp.params))
    (initial : Node vp.params → Bytes vp.params.n)
    (outputs : StructuralNode vp.params → Bytes vp.params.m) :
    GraphProgramming.tableTarget vp nodes initial outputs .secretSeed = initial .secretSeed := rfl

/-- Any unscheduled structural coordinate retains its arbitrary initial value. -/
theorem target_unscheduled (vp : ValidatedParams) (nodes : List (StructuralNode vp.params))
    (initial : Node vp.params → Bytes vp.params.n)
    (outputs : StructuralNode vp.params → Bytes vp.params.m)
    (node : StructuralNode vp.params) (absent : node ∉ nodes) :
    GraphProgramming.tableTarget vp nodes initial outputs (.structural node) =
      initial (.structural node) := by
  simp only [GraphProgramming.tableTarget, absent, ↓reduceIte]

/-- Scheduled coordinates receive exactly the canonical prefix, without a prefix-fit hypothesis. -/
theorem target_scheduled (vp : ValidatedParams) (nodes : List (StructuralNode vp.params))
    (initial : Node vp.params → Bytes vp.params.n)
    (outputs : StructuralNode vp.params → Bytes vp.params.m)
    (node : StructuralNode vp.params) (member : node ∈ nodes) :
    GraphProgramming.tableTarget vp nodes initial outputs (.structural node) =
      prefixBytes vp.params.n (outputs node) := by
  simp only [GraphProgramming.tableTarget, member, ↓reduceIte]

/-- The actual 192f forest preserves boundary cells and the scheduled full-table prefixes. -/
theorem shake192f_signing_cells (pk : Bytes (vp192).params.n) (key : ForsKey (vp192).params)
    (md : List Byte) (initial : Node (vp192).params → Bytes (vp192).params.n)
    (outputs : StructuralNode (vp192).params → Bytes (vp192).params.m)
    (cache : QueryCache (List Byte →ₒ Bytes (vp192).params.m)) :
    let result := RandomOracleTraversal.program (GraphInput.input (vp192) pk)
      (fun parent cells answer => updateCell parent cells (prefixBytes (vp192).params.n answer))
      outputs (ForsSchedule.signing key md) initial cache
    result.1 .secretSeed = initial .secretSeed ∧ ∀ parent,
      result.1 (.structural parent) = if parent ∈ ForsSchedule.signing key md then
        prefixBytes (vp192).params.n (outputs parent) else initial (.structural parent) := by
  rw [GraphProgramming.signing_program]
  constructor
  · rfl
  · intro parent
    rfl

/-- The shared boundary predicate retains the original seed and outside-cell scope. -/
theorem agreesOutside_iff_seed_and_outside
    (remaining : List SHAKE128s.CanonicalGraph.StructuralNode)
    (cells target : SHAKE128s.CanonicalGraph.Cells) :
    SHAKE128s.CanonicalGraph.Programming.AgreesOutside remaining cells target ↔
      cells .secretSeed = target .secretSeed ∧
        ∀ parent ∉ remaining, cells (.structural parent) = target (.structural parent) := by
  constructor
  · intro agrees
    constructor
    · exact agrees .secretSeed (by simp)
    · intro parent absent
      apply agrees (.structural parent)
      intro other member same
      exact absent ((SHAKE128s.CanonicalGraph.Node.structural.inj same) ▸ member)
  · rintro ⟨seed, structural⟩ key outside
    cases key with
    | secretSeed => exact seed
    | structural parent => exact structural parent (fun member => outside parent member rfl)

private def recursiveCache (publicSeed : SHAKE128s.Digest)
    (cells : SHAKE128s.CanonicalGraph.Cells)
    (outputs : SHAKE128s.CanonicalGraph.Programming.Outputs) :
    List SHAKE128s.CanonicalGraph.StructuralNode → QueryCache SHAKE128s.HashSpec →
      QueryCache SHAKE128s.HashSpec
  | [], cache => cache
  | parent :: parents, cache => recursiveCache publicSeed cells outputs parents
      (cache.cacheQuery (SHAKE128s.CanonicalGraph.canonicalInput publicSeed cells parent)
        (outputs parent))

/-- The ordered fold has the original complete cache law for every list and initial cache. -/
private theorem cacheFrom_eq_recursive (publicSeed : SHAKE128s.Digest)
    (cells : SHAKE128s.CanonicalGraph.Cells)
    (outputs : SHAKE128s.CanonicalGraph.Programming.Outputs)
    (parents : List SHAKE128s.CanonicalGraph.StructuralNode)
    (cache : QueryCache SHAKE128s.HashSpec) :
    SHAKE128s.CanonicalGraph.Programming.cacheFrom publicSeed cells outputs parents cache =
      recursiveCache publicSeed cells outputs parents cache := by
  induction parents generalizing cache with
  | nil =>
      exact SHAKE128s.CanonicalGraph.Programming.cacheFrom_nil publicSeed cells outputs cache
  | cons parent parents ih =>
      rw [SHAKE128s.CanonicalGraph.Programming.cacheFrom_cons, recursiveCache]
      exact ih _

end HashSigTest.SLHDSA.Refactor.GraphProgramming
