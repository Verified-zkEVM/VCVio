/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.GroupModel.HashToGroup
public import Mathlib.Algebra.Field.ZMod

/-! # Hash-to-group regression tests

Local fixtures over `ZMod 101` exercise certified adaptive hashing, coefficient substitution,
perfect simulation, private coins, and symbolic normalization of repeated cached replies.
-/

public section

open OracleComp OracleSpec GroupModel.Interaction GroupModel.HashToGroup

namespace HashToGroupTest

private abbrev F := ZMod 101

private instance : Fact (Nat.Prime 101) := ⟨by decide⟩
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

-- Receipt-level differences can cancel, even with honest uniform programming.
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

private abbrev CoinSpec := explainedSpec F Gs (GroupModel.CoinQuery Bool)
  (GroupModel.CoinReply (fun _ => Unit))

private def collisionAdversary (nextLabel : F → Bool) :
    Adversary F Gs Unit (GroupModel.CoinQuery Bool)
      (GroupModel.CoinReply (fun _ => Unit)) Unit where
  main input := do
    let first ← CoinSpec.query ⟨⟨.inl false, fun _ => []⟩, fun _ => []⟩
    let second ← CoinSpec.query
      ⟨⟨.inl (nextLabel ((first.groups ()).getD 0 0)), fun _ => []⟩, fun _ => []⟩
    let basis := extend (extend input.groups first.groups) second.groups
    return Explained.ofVectors basis () (fun s =>
      [fun i => if i.val = (input.groups s).length then 1 else 0,
       fun i => if i.val = (extend input.groups first.groups s).length then 1 else 0])
  algebraic input := by
    refine ⟨fun _ => .nil, fun first => ?_⟩
    refine ⟨fun _ => .nil, fun second => ?_⟩
    exact Explained.valid_ofVectors _ _ _

-- Repeated cached labels remain two receipts, but no longer win the normalized game.
example (B : Origin 0 Bool → F) :
    Pr{let z ← normalizedExecution (F := F) (G := F) B (collisionAdversary fun _ => false)}[
      NormalizedCollision z.2.2 z.1] = 0 := by
  dsimp only [normalizedExecution, collisionAdversary]
  erw [runGameWithCoins_hash]
  simp only [initial, oracle_apply, QueryCache.empty_apply, map_pure, pure_bind]
  erw [runGameWithCoins_hash]
  simp [oracle_apply, reply, Explained.ofVectors, extend, NormalizedCollision,
    merge, transport, evaluate, List.mapIdx_cons, List.mapIdx_nil, prEvent_norm]


-- Equal values at different labels remain a real normalized collision.
example (g : F) :
    Pr{let z ← (normalizedExecution (n := 0) (F := F) (G := F) (fun _ => g)
      (collisionAdversary fun _ => true))}[NormalizedCollision z.2.2 z.1] = 1 := by
  have hne := merge_pair_ne (F := F) (Sum.inr false : Origin 0 Bool) (Sum.inr true)
    (by decide)
  dsimp only [normalizedExecution, collisionAdversary]
  erw [runGameWithCoins_hash]
  simp only [initial, oracle_apply, QueryCache.empty_apply, map_pure, pure_bind]
  erw [runGameWithCoins_hash]
  simpa [oracle_apply, reply, Explained.ofVectors, extend, NormalizedCollision,
    evaluate, List.mapIdx_cons, List.mapIdx_nil, prEvent_norm] using hne


-- The finite challenge-table bound accepts labels selected from previous group replies.
example :
    Pr{let w ← (normalizedTrial (F := F) (G := F) 1 (1 : F)
      (collisionAdversary fun g => decide (g ≠ 0)))}[NormalizedCollision w.2.2.2 w.2.1] ≤
      Pr{let b ← (DiffieHellman.dlogExperiment (1 : F)
        (DiscreteLogRelation.plainReduction (normalizedReduction (F := F) (G := F) (n := 1)
          (collisionAdversary fun g => decide (g ≠ 0)))))}[b = true] + 1 / 101 := by
  simpa only [ZMod.card, Nat.cast_ofNat] using
    normalizedTrial_le_dlog (F := F) (G := F) 1 (1 : F) generator_bijective
    (collisionAdversary fun g => decide (g ≠ 0))

private def coinHandle : GroupModel.HandleAdversary F (GroupModel.discreteSig Unit) Gs
    Unit Bool (fun _ => Unit) Unit := fun _ => do
  let c : Fin 2 ← (GroupModel.HandleSpec F Unit Gs Bool (fun _ => Unit)).query
    (.inr (.inr (.inl 1)))
  (GroupModel.HandleSpec F Unit Gs Bool (fun _ => Unit)).query
    (.inr (.inr (.inr ⟨decide (c = 1), fun _ => []⟩)))

-- Ordinary imports suffice to transport the actual translated randomized handle run.
example (B : Fin 2 → F) (sample : Bool → ProbComp (Fin 2 → F))
    (z : (Explained F Unit Gs × Groups Gs) × State Bool (Fin 2 → F))
    (hz : z ∈ support (((GroupModel.toExplained coinHandle (fun _ => id)).run
      (GroupModel.withCoins coins (programmed (F := F) (G := F) B sample))
      ⟨(), fun _ => []⟩).run (initial []))) :
    (transportExplained (fun _ => z.2.2) z.1.1 ()).map (basisMap (G := F) B) =
      z.1.1.value.groups () :=
  toExplained_programmed_transport B sample coinHandle (fun _ => id) (initial []) z hz

private abbrev NatCoinSpec := explainedSpec F Gs (GroupModel.CoinQuery ℕ)
  (GroupModel.CoinReply (fun _ => Unit))

private def adaptiveCoinAdversary :
    Adversary F Gs Unit (GroupModel.CoinQuery ℕ)
      (GroupModel.CoinReply (fun _ => Unit)) Unit where
  main input := do
    let coin ← NatCoinSpec.query ⟨⟨.inr 1, fun _ => []⟩, fun _ => []⟩
    let first ← NatCoinSpec.query ⟨⟨.inl coin.data.val, fun _ => []⟩, fun _ => []⟩
    let secondLabel := if (first.groups ()).getD 0 0 = 0 then coin.data.val else coin.data.val + 1
    let second ← NatCoinSpec.query ⟨⟨.inl secondLabel, fun _ => []⟩, fun _ => []⟩
    let beforeHash := extend input.groups coin.groups
    let afterFirst := extend beforeHash first.groups
    return Explained.ofVectors (extend afterFirst second.groups) () (fun s =>
      [fun i => if i.val = (beforeHash s).length then 1 else 0,
       fun i => if i.val = (afterFirst s).length then 1 else 0])
  algebraic input := by
    refine ⟨fun _ => .nil, fun coin => ?_⟩
    refine ⟨fun _ => .nil, fun first => ?_⟩
    refine ⟨fun _ => .nil, fun second => ?_⟩
    exact Explained.valid_ofVectors _ _ _

private theorem adaptiveCoinAdversary_bound (n : ℕ) :
    HashQueryBound (F := F) (G := F) n 2 adaptiveCoinAdversary := by
  intro fixed
  simp only [rawProgram, interactionProgram, adaptiveCoinAdversary,
    simulateQ_bind, simulateQ_spec_query, simulateQ_pure, rawGame]
  apply isQueryBoundP_bind (n := 0) (m := 2)
  · apply (isQueryBoundP_map_iff _ _ _).mpr
    simp
  · intro coin _
    apply isQueryBoundP_bind (n := 1) (m := 1)
    · apply (isQueryBoundP_map_iff _ _ _).mpr
      simp
    · intro first _
      apply isQueryBoundP_bind (n := 1) (m := 0)
      · apply (isQueryBoundP_map_iff _ _ _).mpr
        simp
      · intro second _
        exact isQueryBoundP_pure (p := fun t : ℕ ⊕ ℕ => t.isRight) _ _

-- Ordinary imports expose the final lazy-oracle bound on an infinite label type. The first
-- label depends on a private coin; the second depends on both that coin and a hash reply.
example :
    Pr{let z ← lazyTrial (F := F) (G := F) 1 adaptiveCoinAdversary}[
      NormalizedCollision (receiptOrigins 1 z.2) z.1] ≤
      Pr{let b ← (DiffieHellman.dlogExperiment (1 : F)
        (DiscreteLogRelation.plainReduction
          (lazyRelationReduction (F := F) (G := F) (n := 1) (q := 2)
            adaptiveCoinAdversary)))}[b = true] + 1 / 101 := by
  simpa only [ZMod.card, Nat.cast_ofNat] using
    lazyTrial_le_dlog (F := F) (G := F) 1 2 (1 : F) generator_bijective
      adaptiveCoinAdversary (adaptiveCoinAdversary_bound 1)

end HashToGroupTest
