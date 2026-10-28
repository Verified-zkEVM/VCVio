/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.GroupModel.HashToGroup
public import Mathlib.Data.ZMod.Basic

/-! # Hash-to-group regression tests

Local fixtures over `ZMod 101` exercise certified adaptive hashing, coefficient substitution,
perfect simulation, and cancellation caused by repeated cached replies.
-/

public section

open OracleComp OracleSpec GroupModel.Interaction GroupModel.HashToGroup

namespace HashToGroupTest

private abbrev F := ZMod 101
private abbrev Gs := fun _ : Unit => F
private abbrev Spec := explainedSpec F Gs Bool (fun _ => Unit)

private def sumAdversary : Adversary F Gs Unit Bool (fun _ => Unit) Unit where
  main input := do
    let first ← Spec.query ⟨⟨false, fun _ => []⟩, fun _ => []⟩
    let second ← Spec.query ⟨⟨true, fun _ => []⟩, fun _ => []⟩
    return Explained.ofVectors (extend (extend input.groups first.groups) second.groups)
      () (fun s => [fun i => if i.val < (input.groups s).length then 0 else 1])
  algebraic input := by
    refine ⟨fun _ => .nil, fun first => ?_⟩
    refine ⟨fun _ => .nil, fun second => ?_⟩
    exact Explained.valid_ofVectors _ _ _

private def rows (l : Bool) : Fin 2 → F := if l then ![5, 7] else ![2, 3]

private def deterministic (B : Fin 2 → F) :
    ProbComp (Explained F Unit Gs × State Bool (Fin 2 → F)) :=
  execution (F := F) (G := F) B
    (fun l => pure (rows l)) sumAdversary []

example : (fun z => z.1.value.groups ()) <$> deterministic (pairBasis (G := F) 1 11) =
    pure [16] := by
  suffices h : (2 + 3 * 11 + (5 + 7 * 11) : F) = 16 by
    simpa [deterministic, execution, runProgram, interactionProgram, sumAdversary,
      programmed, game, oracle_apply, initial, reply, rows,
      Explained.ofVectors, extend, evaluate, List.mapIdx_cons, List.mapIdx_nil,
      basisMap, pairBasis, Fin.sum_univ_two] using h
  decide

example : (fun z => transportExplained (fun _ => z.2.2) z.1 ()) <$>
    deterministic (pairBasis (G := F) 1 11) =
    pure [![7, 10]] := by
  suffices h : (![(2 : F) + 5, 3 + 7] : Fin 2 → F) = ![7, 10] by
    simpa [deterministic, execution, runProgram, interactionProgram, sumAdversary,
      programmed, game, oracle_apply, initial, reply, rows,
      Explained.ofVectors, extend, transportExplained, transport, evaluate,
      List.mapIdx_cons, List.mapIdx_nil] using h
  decide

private theorem generator_bijective : Function.Bijective (· • (1 : F) : F → F) := by
  constructor
  · intro x y h
    simpa only [smul_eq_mul, mul_one] using h
  · intro y
    exact ⟨y, by simp⟩

-- This checks the public simulation interface on an actual adaptive certified program.
example :
    Prod.map id (mapState (basisMap (F := F) (G := F) (pairBasis (G := F) (1 : F) 11))) <$>
      (simulateQ (programmed (F := F) (G := F) (pairBasis (G := F) (1 : F) 11)
        (fun _ : Bool => (pairSample : ProbComp (Fin 2 → F))))
        (interactionProgram (sumAdversary.main ⟨(), fun _ => []⟩))).run (initial []) =ᵈ
      (simulateQ honest (interactionProgram (sumAdversary.main ⟨(), fun _ => []⟩))).run
        (mapState (basisMap (F := F) (G := F) (pairBasis (G := F) (1 : F) 11)) (initial [])) :=
  programmed_simulation _ _ (fun _ => pairSample_uniform _ _ generator_bijective) _ _

-- Scalar-only programming uses the same imported public interface.
example : basisMap (fun _ : Unit => (1 : F)) <$> (scalarSample : ProbComp (Unit → F)) =ᵈ
    ($ᵗ F : ProbComp F) := scalarSample_uniform _ generator_bijective

private def duplicateAdversary : Adversary F Gs Unit Bool (fun _ => Unit) Unit where
  main input := do
    let first ← Spec.query ⟨⟨false, fun _ => []⟩, fun _ => []⟩
    let second ← Spec.query ⟨⟨false, fun _ => []⟩, fun _ => []⟩
    let basis := extend (extend input.groups first.groups) second.groups
    return Explained.ofVectors basis () (fun s =>
      [fun i => if i.val = (input.groups s).length then 1 else 0,
       fun i => if i.val = (extend input.groups first.groups s).length then 1 else 0])
  algebraic input := by
    refine ⟨fun _ => .nil, fun first => ?_⟩
    refine ⟨fun _ => .nil, fun second => ?_⟩
    exact Explained.valid_ofVectors _ _ _

-- The exact loss in the relation bound can be one, even with honest uniform programming.
example (B : Fin 2 → F) (sample : Bool → ProbComp (Fin 2 → F)) :
    Pr{let z ← execution (G := F) B sample duplicateAdversary []}[
      RepresentationCollision z.1 ∧ relationVector z.2.2 z.1 = 0] = 1 := by
  simp [execution, runProgram, interactionProgram, duplicateAdversary, programmed, game,
    oracle_apply, initial, reply, Explained.ofVectors, extend, RepresentationCollision,
    relationVector, transport, evaluate, List.mapIdx_cons, List.mapIdx_nil, prEvent_norm,
    show (1 : F) ≠ 0 by decide]

-- A cached response still pushes a fresh handle into the table.
example (r : Fin 2 → F) :
    ((do
      let first ← handle (basisMap (G := F) (pairBasis (G := F) 1 11))
        (fun _ : Bool => pure r) ⟨false, fun _ => []⟩
      let second ← handle (basisMap (G := F) (pairBasis (G := F) 1 11))
        (fun _ : Bool => pure r) ⟨false, fun _ => []⟩
      pure (first.groups (), second.groups ())).run' (fun _ => [])).run' (initial []) =
        (pure ([0], [1]) : ProbComp _) := by
  simp [handle_apply, StateT.run'_eq, oracle_apply, initial]

/-- The difference of two identical receipt rows cancels under representation transport. -/
theorem transport_duplicate_rows (r : Fin 2 → ZMod 101) : transport [r, r] [1, -1] = 0 := by
  simp [transport, evaluate, List.mapIdx_cons, List.mapIdx_nil]

end HashToGroupTest
