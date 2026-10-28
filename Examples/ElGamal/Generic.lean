/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import Examples.ElGamal.Basic
public import VCVio.CryptoFoundations.GroupModel.GenericDDH
public import VCVio.CryptoFoundations.GroupModel.Virtualize
import Mathlib.Data.List.GetD

/-! # Unconditional generic one-time security of ElGamal

A generic adversary with phase budgets `q₁` and `q₂` has one-time IND-CPA advantage at most
`2 * (3 * (q₁ + q₂ + 7).choose 2 / |F|)` in the ordinary ElGamal game. Handle virtualization
realizes the existing DDH reduction with two additional group operations.
-/

public section

open OracleComp OracleSpec GroupModel
open scoped ENNReal

namespace elGamalAsymmEnc

variable {F G : Type}

/-- A two-phase adversary accessing group elements only through handles and private coins. -/
structure GenericOneTimeAdversary (F : Type) where
  /-- Private state passed between the two phases. -/
  State : Type
  /-- Choose message handles on the initial table `[gen, pk]`, retaining the final table. -/
  chooseMessages : OracleComp (genSpec F groupSig) (Handle × Handle × State)
  /-- Guess the challenge bit on the retained table extended by the ciphertext components,
  with the two fresh ciphertext handles supplied as arguments. -/
  distinguish : State → Handle → Handle → OracleComp (genSpec F groupSig) Bool

/-- Interpret a generic adversary in the ordinary one-time game, with zero for invalid handles. -/
@[expose] def GenericOneTimeAdversary.toOneTime [Field F] [Fintype F] [DecidableEq F]
    [SampleableType F] [AddCommGroup G] [Module F G] [SampleableType G] [DecidableEq G]
    (gen : G) (A : GenericOneTimeAdversary F) :
    AsymmEncAlg.IND_CPA_OneTime_Adversary (elGamalAsymmEnc F G gen) where
  State := A.State × Tbl (fun _ : Unit => G)
  chooseMessages pk := (fun r =>
    (lookup r.2 () r.1.1, lookup r.2 () r.1.2.1, r.1.2.2, r.2)) <$>
      runGen (Model.group G) (fun _ => id) A.chooseMessages (fun _ => [gen, pk])
  distinguish st c := Prod.fst <$>
    runGen (Model.group G) (fun _ => id)
      (A.distinguish st.1 (st.2 ()).length ((st.2 ()).length + 1))
      (append (append st.2 () c.1) () c.2)

/-- Realize the one-time DDH reduction on `[g, X, Y, T]`, isolating both adversarial phases
with virtual handles. Setup creates zero, and the challenge adds the selected message to `T`. -/
@[expose] def ddhOfGeneric [Zero F] (A : GenericOneTimeAdversary F) :
    OracleComp (genSpec F groupSig) Bool := do
  let z ← OracleComp.lift ((genSpec F groupSig).query (.inl (.smul () 0 0)))
  let (out, τ) ← (virtualize (fun _ => z) A.chooseMessages).run (fun _ => [0, 1])
  let bit : Bool ← FinEnum.equiv.symm <$>
    OracleComp.lift ((genSpec F groupSig).query (.inr 1))
  let m := (τ ()).getD (if bit then out.1 else out.2.1) z
  let c ← OracleComp.lift ((genSpec F groupSig).query (.inl (.add () 3 m)))
  let (guess, _) ← (virtualize (fun _ => z)
    (A.distinguish out.2.2 (τ ()).length ((τ ()).length + 1))).run
      (append (append τ () 2) () c)
  pure (bit == guess)

/-- The generic DDH solver adds exactly two group operations to the two phase budgets. -/
theorem isQueryBoundP_ddhOfGeneric [Zero F] (A : GenericOneTimeAdversary F) (q₁ q₂ : ℕ)
    (h₁ : IsQueryBoundP A.chooseMessages (fun i => isGroupOp i = true) q₁)
    (h₂ : ∀ s a b, IsQueryBoundP (A.distinguish s a b)
      (fun i => isGroupOp i = true) q₂) :
    IsQueryBoundP (ddhOfGeneric A) (fun i => isGroupOp i = true) (q₁ + q₂ + 2) := by
  rw [ddhOfGeneric]
  erw [isQueryBoundP_query_bind_iff]
  change (¬true = true ∨ 0 < q₁ + q₂ + 2) ∧ _
  simp only [not_true_eq_false, false_or]
  constructor
  · omega
  · intro z
    have hn : q₁ + q₂ + 2 - 1 = q₁ + (q₂ + 1) := by omega
    rw [hn]
    apply isQueryBoundP_bind (isQueryBoundP_virtualize (fun _ => z) h₁ _)
    rintro ⟨out, τ⟩ _
    rw [bind_map_left]
    erw [isQueryBoundP_query_bind_iff]
    refine ⟨Or.inl (by simp [isGroupOp]), fun bit => ?_⟩
    change IsQueryBoundP (OracleComp.lift ((genSpec F groupSig).query
      (.inl (.add () 3 ((τ ()).getD
        (if (FinEnum.equiv.symm bit : Bool) then out.1 else out.2.1) z)))) >>= _)
        (fun i => isGroupOp i = true) (q₂ + 1)
    erw [isQueryBoundP_query_bind_iff]
    refine ⟨Or.inr (by omega), fun c => ?_⟩
    change IsQueryBoundP (_ >>= _) (fun i => isGroupOp i = true) (q₂ + 1 - 1)
    simpa only [Nat.add_sub_cancel, bind_pure_comp, isQueryBoundP_map_iff] using
      isQueryBoundP_virtualize (fun _ => z) (h₂ out.2.2 (τ ()).length ((τ ()).length + 1))
        (append (append τ () 2) () c)

section Interpretation

variable [Field F] [AddCommGroup G] [Module F G] [DecidableEq G]

private theorem runGen_bind {α β : Type} (A : OracleComp (genSpec F groupSig) α)
    (k : α → OracleComp (genSpec F groupSig) β) (tbl : Tbl (fun _ : Unit => G)) :
    runGen (Model.group G) (fun _ => id) (A >>= k) tbl =
      (runGen (Model.group G) (fun _ => id) A tbl >>= fun r =>
        runGen (Model.group G) (fun _ => id) (k r.1) r.2) := by
  simp only [runGen, run, simulateQ_bind, StateT.run_bind]

private theorem runGen_smul (tbl : Tbl (fun _ : Unit => G)) (d : F) (a : Handle) :
    runGen (Model.group G) (fun _ => id)
      (OracleComp.lift ((genSpec F groupSig).query (.inl (.smul () d a)))) tbl =
      pure ((tbl ()).length, append tbl () (d • lookup tbl () a)) := rfl

private theorem runGen_add (tbl : Tbl (fun _ : Unit => G)) (a b : Handle) :
    runGen (Model.group G) (fun _ => id)
      (OracleComp.lift ((genSpec F groupSig).query (.inl (.add () a b)))) tbl =
      pure ((tbl ()).length, append tbl () (lookup tbl () a + lookup tbl () b)) := rfl

private theorem runGen_pure {α : Type} (tbl : Tbl (fun _ : Unit => G)) (a : α) :
    runGen (Model.group (F := F) G) (fun _ => id) (pure a) tbl = pure (a, tbl) := rfl

private theorem runGen_coin (tbl : Tbl (fun _ : Unit => G)) :
    runGen (Model.group (F := F) G) (fun _ => id)
      (OracleComp.lift ((genSpec F groupSig).query (.inr 1))) tbl =
      (fun b => (b, tbl)) <$> (OracleComp.lift (unifSpec.query 1)) := rfl

end Interpretation

private theorem readBack_extend [AddCommGroup G]
    {z : Unit → Handle} {τ : Tbl (fun _ : Unit => Handle)}
    {tbl : Tbl (fun _ : Unit => G)} (hw : WellFormed z τ tbl)
    (h : Handle) (hh : h < (tbl ()).length) (v : G) :
    readBack (append (append τ () h) () (tbl ()).length) (append tbl () v) =
      append (append (readBack τ tbl) () (lookup tbl () h)) () v := by
  funext u
  cases u
  have hp := prefix_append tbl () () v
  have hm : (τ ()).map (lookup (append tbl () v) ()) = (τ ()).map (lookup tbl ()) := by
    apply List.map_congr_left
    intro a ha
    exact lookup_eq_of_prefix () hp a ((hw ()).1 a ha)
  simp only [readBack, append, Function.update_self, List.map_append, List.map_cons,
    List.map_nil]
  change (τ ()).map (lookup (append tbl () v) ()) ++
    [lookup (append tbl () v) () h] ++ [lookup (append tbl () v) () (tbl ()).length] = _
  rw [hm, lookup_eq_of_prefix () hp h hh]
  simp [lookup, append]

private theorem wellFormed_extend [AddCommGroup G]
    {z : Unit → Handle} {τ : Tbl (fun _ : Unit => Handle)}
    {tbl : Tbl (fun _ : Unit => G)} (hw : WellFormed z τ tbl)
    (h : Handle) (hh : h < (tbl ()).length) (v : G) :
    WellFormed z (append (append τ () h) () (tbl ()).length) (append tbl () v) := by
  intro u
  cases u
  have hp := prefix_append tbl () () v
  refine ⟨?_, lt_of_lt_of_le (hw ()).2.1 hp.length_le, ?_⟩
  · intro a ha
    simp only [append, Function.update_self, List.mem_append, List.mem_singleton] at ha
    simp only [append, Function.update_self, List.length_append, List.length_singleton]
    rcases ha with (ha | rfl) | rfl
    · exact Nat.lt_succ_of_lt ((hw ()).1 a ha)
    · exact Nat.lt_succ_of_lt hh
    · exact Nat.lt_succ_self _
  · rw [lookup_eq_of_prefix () hp _ (hw ()).2.1, (hw ()).2.2]

/-- On a DDH challenge with generator `gen`, interpreting the virtualized solver is exactly
 the existing one-time reduction of the interpreted adversary, as computations. -/
theorem oneTimeDDHReduction_toOneTime_eq [Field F] [Fintype F] [DecidableEq F]
    [SampleableType F] [AddCommGroup G] [Module F G] [SampleableType G] [DecidableEq G]
    (gen X Y T : G) (A : GenericOneTimeAdversary F) :
    IND_CPA_OneTime_DDHReduction (A.toOneTime gen) gen X Y T =
      DDHAdversary.ofGeneric (ddhOfGeneric A) gen X Y T := by
  have hw : WellFormed (fun _ => 4) (fun _ => [0, 1])
      (fun _ : Unit => [gen, X, Y, T, 0]) := by
    intro u
    simp [lookup]
  have hr : readBack (fun _ => [0, 1]) (fun _ : Unit => [gen, X, Y, T, 0]) =
      (fun _ => [gen, X]) := by
    funext u
    simp [readBack, lookup]
  have hv := runGen_virtualize (Model.group (F := F) G) (fun _ => id) A.chooseMessages hw
  rw [hr] at hv
  simp only [IND_CPA_OneTime_DDHReduction, oneTimeDDHReductionBody,
    GenericOneTimeAdversary.toOneTime, DDHAdversary.ofGeneric, ddhOfGeneric]
  erw [runGen_bind, runGen_smul, pure_bind]
  have ht : append (fun _ : Unit => [gen, X, Y, T]) ()
      ((0 : F) • lookup (fun _ => [gen, X, Y, T]) () 0) =
        (fun _ => [gen, X, Y, T, 0]) := by
    funext u
    cases u
    simp [append]
  rw [ht]
  change _ = Prod.fst <$> (runGen (Model.group G) (fun _ => id)
    ((virtualize (fun _ => 4) A.chooseMessages).run (fun _ => [0, 1]) >>= _)
      (fun _ => [gen, X, Y, T, 0]))
  rw [hv]
  simp only [bind_map_left, runGen_bind, map_bind]
  apply bind_congr_of_forall_mem_support
  rintro ⟨⟨out, τ⟩, tbl⟩ hs
  have hw' := wellFormed_runGen_virtualize (Model.group G) (fun _ => id)
    A.chooseMessages hw ((out, τ), tbl) hs
  have hp := runGen_prefix (Model.group G) (fun _ => id)
    ((virtualize (fun _ => 4) A.chooseMessages).run (fun _ => [0, 1]))
    (fun _ => [gen, X, Y, T, 0]) ((out, τ), tbl) hs ()
  have hlen : 5 ≤ (tbl ()).length := hp.length_le
  have hY : lookup tbl () 2 = Y := by
    rw [lookup_eq_of_prefix (tbl := fun _ : Unit => [gen, X, Y, T, 0]) () hp 2 (by simp)]
    rfl
  have hT : lookup tbl () 3 = T := by
    rw [lookup_eq_of_prefix (tbl := fun _ : Unit => [gen, X, Y, T, 0]) () hp 3 (by simp)]
    rfl
  erw [runGen_coin]
  rw [show ($ᵗ Bool) = FinEnum.equiv.symm <$>
    (OracleComp.lift (unifSpec.query 1)) from rfl]
  simp only [bind_map_left]
  erw [bind_map_left]
  apply bind_congr_of_forall_mem_support
  intro coin _
  let bit : Bool := FinEnum.equiv.symm coin
  erw [runGen_add, pure_bind]
  simp only [runGen_pure, map_pure, bind_pure_comp]
  have hm : lookup tbl () ((τ ()).getD (if bit then out.1 else out.2.1) 4) =
      if bit then lookup (readBack τ tbl) () out.1
      else lookup (readBack τ tbl) () out.2.1 := by
    rw [← lookup_readBack hw']
    cases bit <;> rfl
  rw [hT]
  erw [hm]
  have he := readBack_extend hw' 2 (by change 2 < (tbl ()).length; omega)
    (T + if bit then lookup (readBack τ tbl) () out.1
      else lookup (readBack τ tbl) () out.2.1)
  rw [hY] at he
  have hw'' := wellFormed_extend hw' 2 (by change 2 < (tbl ()).length; omega)
    (T + if bit then lookup (readBack τ tbl) () out.1
      else lookup (readBack τ tbl) () out.2.1)
  have hv' := runGen_virtualize (Model.group G) (fun _ => id)
    (A.distinguish out.2.2 (τ ()).length ((τ ()).length + 1)) hw''
  rw [he] at hv'
  simp only [readBack, List.length_map] at *
  rw [hv']
  simp only [Functor.map_map]
  rfl

/-- A generic adversary with phase budgets `q₁` and `q₂` has unconditional advantage at most
`2 * (3 * (q₁ + q₂ + 7).choose 2 / |F|)` in the unchanged one-time ElGamal game. -/
theorem oneTimeAdvantage_toOneTime_le [Field F] [Fintype F] [DecidableEq F]
    [SampleableType F] [AddCommGroup G] [Module F G] [SampleableType G] [DecidableEq G]
    {gen : G} (hg : Function.Bijective (· • gen : F → G))
    (A : GenericOneTimeAdversary F) (q₁ q₂ : ℕ)
    (h₁ : IsQueryBoundP A.chooseMessages (fun i => isGroupOp i = true) q₁)
    (h₂ : ∀ s a b, IsQueryBoundP (A.distinguish s a b) (fun i => isGroupOp i = true) q₂) :
    AsymmEncAlg.IND_CPA_OneTime_Advantage (elGamalAsymmEnc F G gen) ProbCompRuntime.probComp
        (A.toOneTime gen) ≤
      2 * ((3 * (q₁ + q₂ + 7).choose 2 : ℕ) / (Fintype.card F : ℝ≥0∞)) := by
  have hg0 : gen ≠ 0 := by
    intro h
    exact zero_ne_one (hg.1 (by simp [h] : (0 : F) • gen = (1 : F) • gen))
  rw [elGamal_oneTime_advantage_eq_two_mul_ddhAdvantage hg]
  have he : DiffieHellman.ddhAdvantage gen (IND_CPA_OneTime_DDHReduction (A.toOneTime gen)) =
      DiffieHellman.ddhAdvantage gen (DDHAdversary.ofGeneric (ddhOfGeneric A)) := by
    simp only [DiffieHellman.ddhAdvantage, DiffieHellman.ddhRealExperiment,
      DiffieHellman.ddhRandomExperiment, oneTimeDDHReduction_toOneTime_eq]
  rw [he]
  gcongr
  simpa only [Nat.add_assoc] using ddhAdvantage_ofGeneric_le gen hg0 (ddhOfGeneric A)
    (q₁ + q₂ + 2) (isQueryBoundP_ddhOfGeneric A q₁ q₂ h₁ h₂)

end elGamalAsymmEnc
