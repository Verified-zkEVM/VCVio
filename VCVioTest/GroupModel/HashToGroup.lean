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
      () (fun s => [fun i => if i.val < (input.groups s).length then 0 else
        if i.val = (input.groups s).length then 1 else 2])
  algebraic input := by
    refine ⟨fun _ => .nil, fun first => ?_⟩
    refine ⟨fun _ => .nil, fun second => ?_⟩
    exact Explained.valid_ofVectors _ _ _

/-- Execute a certified hash adversary, starting from specified rows for its fixed inputs. -/
private def execution {Label κ : Type} [DecidableEq Label] [Fintype κ] (B : κ → F)
    (sample : Label → ProbComp (κ → F))
    (A : Adversary F Gs Unit Label (fun _ => Unit) Unit) (rows : List (κ → F)) :
    ProbComp (Explained F Unit Gs × State Label (κ → F)) :=
  runProgram B sample (A.main ⟨(), fun _ => rows.map (Fintype.linearCombination F B)⟩)
    (initial rows)

/-- Two different coefficient lists explaining the same group element as two final outputs. -/
private def RepresentationCollision (out : Explained F Unit Gs) : Prop :=
  ∃ (a b : List F) (g : F), out.coefficients () = [a, b] ∧ out.value.groups () = [g, g] ∧ a ≠ b

/-- Subtract the first two output representations after substituting their recorded rows. -/
private def relationVector {κ : Type} (rows : List (κ → F)) (out : Explained F Unit Gs) : κ → F :=
  transport rows (((out.coefficients ())[0]?).getD []) -
    transport rows (((out.coefficients ())[1]?).getD [])

private def rows (l : Bool) : Fin 2 → F := if l then ![5, 7] else ![2, 3]

private def deterministic (B : Fin 2 → F) :
    ProbComp (Explained F Unit Gs × State Bool (Fin 2 → F)) :=
  execution B (fun l => pure (rows l)) sumAdversary []

example : (fun z => z.1.value.groups ()) <$> deterministic (pairBasis (G := F) 1 11) =
    pure [98] := by
  suffices h : (2 + 3 * 11 + 2 * (5 + 7 * 11) : F) = 98 by
    simpa [deterministic, execution, runProgram, interactionProgram, sumAdversary,
      programmed, game, oracle_apply, initial, reply, rows,
      Explained.ofVectors, extend, evaluate, List.mapIdx_cons, List.mapIdx_nil,
      Fintype.linearCombination_apply, pairBasis, Fin.sum_univ_two] using h
  decide

example : (fun z => transportExplained (fun _ => z.2.2) z.1 ()) <$>
    deterministic (pairBasis (G := F) 1 11) =
    pure [![12, 17]] := by
  suffices h : (![(2 : F) + 2 * 5, 3 + 2 * 7] : Fin 2 → F) = ![12, 17] by
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
    Prod.map id (mapState (Fintype.linearCombination F (pairBasis (G := F) (1 : F) 11))) <$>
      (simulateQ (programmed (F := F) (G := F) (pairBasis (G := F) (1 : F) 11)
        (fun _ : Bool => (pairSample : ProbComp (Fin 2 → F))))
        (interactionProgram (sumAdversary.main ⟨(), fun _ => []⟩))).run (initial []) =ᵈ
      (simulateQ honest (interactionProgram (sumAdversary.main ⟨(), fun _ => []⟩))).run
        (mapState (Fintype.linearCombination F (pairBasis (G := F) (1 : F) 11)) (initial [])) :=
  programmed_simulation _ _ (fun _ => pairSample_uniform _ _ generator_bijective) _ _

-- Scalar-only programming uses the same imported public interface.
example :
    Fintype.linearCombination F (fun _ : Unit => (1 : F)) <$>
      (scalarSample : ProbComp (Unit → F)) =ᵈ
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
    Pr{let z ← execution B sample duplicateAdversary []}[
      RepresentationCollision z.1 ∧ relationVector z.2.2 z.1 = 0] = 1 := by
  simp [execution, runProgram, interactionProgram, duplicateAdversary, programmed, game,
    oracle_apply, initial, reply, Explained.ofVectors, extend, RepresentationCollision,
    relationVector, transport, evaluate, List.mapIdx_cons, List.mapIdx_nil, prEvent_norm,
    show (1 : F) ≠ 0 by decide]

-- A cached response still pushes a fresh handle into the table.
example (r : Fin 2 → F) :
    ((do
      let first ← handle (Fintype.linearCombination F (pairBasis (G := F) 1 11))
        (fun _ : Bool => pure r) ⟨false, fun _ => []⟩
      let second ← handle (Fintype.linearCombination F (pairBasis (G := F) 1 11))
        (fun _ : Bool => pure r) ⟨false, fun _ => []⟩
      pure (first.groups (), second.groups ())).run' (fun _ => [])).run' (initial []) =
        (pure ([0], [1]) : ProbComp _) := by
  simp [handle_apply, StateT.run'_eq, oracle_apply, initial]

-- Two queries on one label install two handles to one sampled element, whatever it is.
example :
    Pr{let z ← ((do
      let _ ← handle id (fun _ : Bool => ($ᵗ F : ProbComp F)) ⟨false, fun _ => []⟩
      let _ ← handle id (fun _ : Bool => ($ᵗ F : ProbComp F)) ⟨false, fun _ => []⟩
      pure ()).run (fun _ => [])).run (initial [])}[∃ g, z.1.2 () = [g, g]] = 1 := by
  refine prEvent_eq_one_of_forall_mem_support _ _ fun z hz => ?_
  obtain ⟨y, hy⟩ : ∃ y, z.1.2 = fun _ => [y, y] := by
    simpa [handle_apply, oracle_apply, initial] using
      (by simp [handle_apply, oracle_apply, initial] at hz; exact hz.imp fun _ h => by rw [← h])
  exact ⟨y, by rw [hy]⟩

/-- The difference of two identical receipt rows cancels under representation transport. -/
theorem transport_duplicate_rows (r : Fin 2 → ZMod 101) : transport [r, r] [1, -1] = 0 := by
  simp [transport, evaluate, List.mapIdx_cons, List.mapIdx_nil]

private abbrev CoinSpec (Label : Type) := explainedSpec F Gs (GroupModel.CoinQuery Label)
  (GroupModel.CoinReply (fun _ => Unit))

private def collisionAdversary {Label : Type} (firstLabel : Label) (nextLabel : F → Label) :
    Adversary F Gs Unit (GroupModel.CoinQuery Label)
      (GroupModel.CoinReply (fun _ => Unit)) Unit where
  main input := do
    let first ← (CoinSpec Label).query ⟨⟨.inl firstLabel, fun _ => []⟩, fun _ => []⟩
    let second ← (CoinSpec Label).query
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
    Pr{let z ← normalizedExecution (F := F) (G := F) B (collisionAdversary false fun _ => false)}[
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
      (collisionAdversary false fun _ => true))}[NormalizedCollision z.2.2 z.1] = 1 := by
  have hne := merge_pair_ne (F := F) (Sum.inr false : Origin 0 Bool) (Sum.inr true)
    (by decide)
  dsimp only [normalizedExecution, collisionAdversary]
  erw [runGameWithCoins_hash]
  simp only [initial, oracle_apply, QueryCache.empty_apply, map_pure, pure_bind]
  erw [runGameWithCoins_hash]
  simpa [oracle_apply, reply, Explained.ofVectors, extend, NormalizedCollision,
    evaluate, List.mapIdx_cons, List.mapIdx_nil, prEvent_norm] using hne


private abbrev adaptiveFinAdversary :=
  collisionAdversary (0 : Fin 2) fun g => if g = 0 then 0 else 1

-- The finite challenge-table bound accepts labels selected from previous group replies.
example :
    Pr{let w ← (normalizedTrial (F := F) (G := F) 1 (1 : F)
      adaptiveFinAdversary)}[NormalizedCollision w.2.2.2 w.2.1] ≤
      Pr{let b ← (DiffieHellman.dlogExperiment (1 : F)
        (DiscreteLogRelation.plainReduction (normalizedReduction (F := F) (G := F) (n := 1)
          adaptiveFinAdversary)))}[b = true] + 1 / 101 := by
  simpa only [ZMod.card, Nat.cast_ofNat] using
    normalizedTrial_le_dlog (F := F) (G := F) 1 (1 : F) one_ne_zero adaptiveFinAdversary

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
    (transportExplained (fun _ => z.2.2) z.1.1 ()).map (Fintype.linearCombination F B) =
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

-- The adversary makes two hash queries, so it does not meet a budget of one.
example (n : ℕ) : ¬ HashQueryBound (F := F) (G := F) n 1 adaptiveCoinAdversary := by
  intro h
  have h := (h 0).2 (0 : Fin 2)
  have h : ¬ true = true ∨ 0 < 0 := (h.2 (0 : F)).1
  simp at h

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

section Solver

variable {K : Type} [Field K] [DecidableEq K]

private abbrev KGroups (K : Type) := fun _ : Unit => K

/-- One element explained in two ways from a received `x` and a hash reply `y`: as `y` and as
`(y / x) • x`, or, when `x = 0`, as `x` and as `0`. -/
private def solverOutput (inputs replies : Groups (KGroups K)) : Explained K Unit (KGroups K) :=
  Explained.ofVectors (extend inputs replies) () (fun _ =>
    if (inputs ()).getD 0 0 = 0 then [fun i => if i.val = 0 then 1 else 0, fun _ => 0]
    else [fun i => if i.val = 0 then 0 else 1,
      fun i => if i.val = 0 then (replies ()).getD 0 0 / (inputs ()).getD 0 0 else 0])

private def solver : Adversary K (KGroups K) Unit (GroupModel.CoinQuery Bool)
    (GroupModel.CoinReply (fun _ => Unit)) Unit where
  main := fun ⟨_, groups⟩ => do
    let r ← (explainedSpec K (KGroups K) (GroupModel.CoinQuery Bool)
      (GroupModel.CoinReply (fun _ => Unit))).query ⟨⟨.inl false, fun _ => []⟩, fun _ => []⟩
    return solverOutput groups r.groups
  algebraic _ := ⟨fun _ => .nil, fun _ => Explained.valid_ofVectors _ _ _⟩

private theorem lazyExecution_solver [SampleableType K] (fixed : Fin 1 → K) :
    lazyExecution fixed solver =
      (fun y => (solverOutput (fun _ => List.ofFn fixed) (reply y).groups, [(false, y)])) <$>
        ($ᵗ K : ProbComp K) := by
  have h : rawProgram (solver.main ⟨(), fun _ => List.ofFn fixed⟩) =
      (liftM ((unifSpec + (Bool →ₒ K)).query (.inr false)) :
          OracleComp (unifSpec + (Bool →ₒ K)) K) >>= fun y =>
        pure (solverOutput (fun _ => List.ofFn fixed) (reply y).groups) := rfl
  rw [lazyExecution, h]
  have hh : (SlotRenaming.honest (D := Bool) (R := K) (.inr false)).run (∅, []) =
      (fun y => (y, (∅ : (Bool →ₒ K).QueryCache).cacheQuery false y, [(false, y)])) <$>
        ($ᵗ K : ProbComp K) := by
    change (fun z => (z.1, z.2, [] ++ [(false, z.1)])) <$>
      ((Bool →ₒ K).randomOracle false).run ∅ = _
    rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_none _ (by simp)]
    simp [uniformSampleImpl, Functor.map_map]
  simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure, StateT.run_bind,
    StateT.run_pure]
  rw [hh]
  simp [Functor.map_map]

-- The lazy trial can be won: this solver wins it with probability one.
example [SampleableType K] : Pr{let z ← lazyTrial (F := K) (G := K) 1 solver}[
    NormalizedCollision (receiptOrigins 1 z.2) z.1] = 1 := by
  refine prEvent_eq_one_of_forall_mem_support _ _ fun z hz => ?_
  obtain ⟨fixed, _, hz⟩ := (mem_support_bind_iff _ _ _).mp hz
  rw [lazyExecution_solver, support_map] at hz
  obtain ⟨y, _, rfl⟩ := hz
  by_cases h : fixed 0 = 0
  · refine ⟨[1, 0], [0, 0], 0, ?_, ?_, fun he => ?_⟩
    · simp [solverOutput, Explained.ofVectors, extend, reply, h]
    · simp [solverOutput, Explained.ofVectors, extend, reply, h, evaluate]
    · simpa [merge, transport, evaluate, receiptOrigins] using congrFun he (.inl 0)
  · refine ⟨[0, 1], [y / fixed 0, 0], y, ?_, ?_, fun he => ?_⟩
    · simp [solverOutput, Explained.ofVectors, extend, reply, h]
    · simp [solverOutput, Explained.ofVectors, extend, reply, h, evaluate]
    · simpa [merge, transport, evaluate, receiptOrigins] using congrFun he (.inr false)

end Solver

end HashToGroupTest
