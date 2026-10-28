/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Schemes.BLS.Reduction

/-! # The guessed forgery slot in BLS

A fresh valid forgery at the guessed insertion index transfers through deferred challenge
sampling to a non-aborted execution whose signature is the challenge's honest signature.
This is the extraction event in the Boneh–Lynn–Shacham co-CDH reduction.
-/

public section

open OracleComp OracleSpec

namespace BLS

/-- A fresh valid forgery, with its final verification hash carried in the output. -/
@[expose] def Winning {V M G : Type} (sign : G → G)
    (z : ((M × G) × G) × OracleState V M) : Prop :=
  z.1.1.1 ∉ z.2.signed ∧ z.1.1.2 = sign z.1.2

/-- A winning forgery whose message occupies the guessed insertion slot. -/
@[expose] def TargetWin {V M G : Type} (sign : G → G) (j : ℕ)
    (z : ((M × G) × G) × OracleState V M) : Prop :=
  Winning sign z ∧ ∃ v, z.2.cache z.1.1.1 = some (v, j)

/-- A non-aborted challenge-tagged output carrying the honest signature of the challenge. -/
@[expose] def ExtractEvent {V M G : Type} (sign : G → G) (j : ℕ)
    (z : ((M × G) × G) × (OracleState (Option V) M × G)) : Prop :=
  z.1.1.2 = sign z.2.2 ∧ z.2.1.cache z.1.1.1 = some (none, j) ∧ ¬z.2.1.bad = true

private theorem fillChallenge_target {V M G : Type} [SampleableType G]
    (f : V → G) (sign : G → G) (j : ℕ)
    (z : ((M × G) × G) × OracleState V M)
    (hi : IndexInv (some j) z.2) (hs : SelectionInv j z.2)
    (he : ∃ v i, z.2.cache z.1.1.1 = some (v, i) ∧ z.1.2 = f v)
    (hw : TargetWin sign j z)
    (st : OracleState (Option V) M × G) (hst : st ∈ support (fillChallenge f j z.2)) :
    ExtractEvent sign j (z.1, st) := by
  obtain ⟨⟨hf, hv⟩, v, hc⟩ := hw
  obtain ⟨w, i, hec, he⟩ := he
  have hp := Option.some.inj (hc.symm.trans hec)
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hp
  have hsel := hs.selected z.1.1.1 v hc
  simp only [fillChallenge, hsel, support_pure, Set.mem_singleton_iff] at hst
  subst st
  refine ⟨hv.trans (congrArg sign he), ?_, ?_⟩
  · simp [tagState, hc]
  · have hb := hi.not_bad_of_fresh hc hf
    simpa only [tagState, hb] using Bool.false_ne_true

/-- A winning forgery at a fixed guessed slot becomes a non-aborted challenge extraction
event after completing the selected challenge. -/
theorem prEvent_targetWin_le_programmed {V M G : Type}
    [SampleableType V] [SampleableType G] [DecidableEq M]
    (f : V → G) (hf : Function.Bijective f) (sign : G → G) (j : ℕ)
    (oa : OracleComp ((unifSpec + (M →ₒ G)) + (M →ₒ G)) (M × G)) :
    Pr{let z ← (simulateQ (indexedOracle (fun _ => $ᵗ V) f (sign ∘ f) (some j))
        (withFinalHash oa)).run OracleState.empty}[TargetWin sign j z] ≤
    Pr{let h ← ($ᵗ G : ProbComp G)
       let z ← (simulateQ (indexedOracle (tagDraw j) (fun tag => tag.elim h f)
         (fun tag => sign (tag.elim h f)) (some j)) (withFinalHash oa)).run OracleState.empty}[
      ExtractEvent sign j (z.1, z.2, h)] := by
  let run := (simulateQ (indexedOracle (fun _ => $ᵗ V) f (sign ∘ f) (some j))
    (withFinalHash oa)).run (OracleState.empty : OracleState V M)
  have hle : Pr{let z ← run}[TargetWin sign j z] ≤
      Pr{let w ← run >>= fun z => (fun st => (z.1, st)) <$> fillChallenge f j z.2}[
        ExtractEvent sign j w] := by
    apply prEvent_le_prEvent_bind_of_support
    intro z hz hw
    apply prEvent_eq_one_of_forall_mem_support
    intro w hw'
    obtain ⟨st, hst, heq⟩ := mem_support_map_peel _ _ hw'
    subst w
    have hi := simulateQ_run_preservesInv _ _
      (indexedOracle_preserves_indexInv (fun _ => $ᵗ V) f (sign ∘ f) (some j))
      (withFinalHash oa) _ (indexInv_empty (some j)) z hz
    have hs := simulateQ_run_preservesInv _ _
      (indexedOracle_preserves_selectionInv (fun _ => $ᵗ V) f (sign ∘ f) j)
      (withFinalHash oa) _ (selectionInv_empty j) z hz
    exact fillChallenge_target f sign j z hi hs
      (withFinalHash_support_entry _ _ _ _ oa _ (indexInv_empty (some j)) z hz) hw st hst
  have heq := simulateQ_fillChallenge_evalDistEq f hf sign j (withFinalHash oa)
    OracleState.empty (selectionInv_empty j)
  have hempty : fillChallenge f j (OracleState.empty : OracleState V M) =
      (fun h => (OracleState.empty, h)) <$> ($ᵗ G : ProbComp G) := by
    change (fun h => (tagState j OracleState.empty, h)) <$> ($ᵗ G : ProbComp G) = _
    rw [tagState_empty]
  have hev := heq.prEvent_eq (ExtractEvent sign j)
  simp only [hempty, bind_map_left, programmedOracle_run, map_bind, Functor.map_map] at hev
  simp only [run, map_bind, Functor.map_map] at hle
  exact hle.trans_eq hev

/-- A fresh valid forgery at the fixed guessed slot yields a co-CDH solution from the named
reduction at that slot, after averaging the independent challenge. -/
theorem prEvent_targetWin_le_reductionAt {F G₁ G₂ Gₜ M : Type}
    [Field F] [SampleableType F] [AddCommGroup G₁] [Module F G₁] [SampleableType G₁]
    [AddCommGroup G₂] [Module F G₂] [AddCommGroup Gₜ] [Module F Gₜ]
    [DecidableEq Gₜ] [DecidableEq M]
    {e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ} {g₁ : G₁} {g₂ : G₂}
    (A : SignatureAlg.UnforgeableAdversary (scheme (M := M) e g₁ g₂))
    (hg₁ : Function.Bijective (· • g₁ : F → G₁)) (x : F) (j : ℕ) :
    Pr{let z ← (simulateQ (indexedOracle (fun _ => $ᵗ F) (· • g₁)
        (fun ρ => x • (ρ • g₁)) (some j))
        (withFinalHash (A.main (x • g₁, x • g₂)))).run OracleState.empty}[
      TargetWin (x • ·) j z] ≤
    Pr{let h ← ($ᵗ G₁ : ProbComp G₁)
       let y ← reductionAt A j g₁ g₂ (x • g₁) (x • g₂) h}[y = x • h] := by
  refine (prEvent_targetWin_le_programmed (· • g₁) hg₁ (x • ·) j
    (A.main (x • g₁, x • g₂))).trans ?_
  let : MeasurableSpace G₁ := ⊤
  rw [prEvent_bind_of_discrete, prEvent_bind_of_discrete]
  apply MeasureTheory.lintegral_mono
  intro h
  have habort := prEvent_indexedOracle_and_not_bad_le
    (M := M) (fun tag : Option F => tag.elim h (· • g₁))
    (fun tag => x • tag.elim h (· • g₁))
    (fun tag => tag.elim 0 (· • (x • g₁)))
    (fun ρ => (simulated_signature_eq g₁ x ρ).symm) j
    (withFinalHash (A.main (x • g₁, x • g₂)))
    (fun z => ExtractEvent (x • ·) j (z.1, z.2, h))
  simp only [ExtractEvent, and_assoc, and_self] at habort
  refine habort.trans ?_
  unfold reductionAt
  apply prEvent_le_prEvent_bind_of_support
  intro z _ hz
  obtain ⟨hv, hc, hb⟩ := hz
  simp [hb, hc, hv]

/-- Every winning run has a forgery index in the finite guessing range. Summing its indexed
events therefore bounds the total winning probability. -/
theorem prEvent_winning_le_sum_targetWin {V M G : Type} [DecidableEq M]
    (draw : ℕ → ProbComp V) (hash sign : V → G)
    (check : G → G)
    (oa : OracleComp ((unifSpec + (M →ₒ G)) + (M →ₒ G)) (M × G))
    (qH qS : ℕ) (hH : oa.IsQueryBoundP (· matches .inl (.inr _)) qH)
    (hS : oa.IsQueryBoundP (· matches .inr _) qS) :
    Pr{let z ← (simulateQ (indexedOracle draw hash sign none) (withFinalHash oa)).run
        OracleState.empty}[Winning check z] ≤
    ∑ j : Fin (qH + qS + 1),
      Pr{let z ← (simulateQ (indexedOracle draw hash sign none) (withFinalHash oa)).run
          OracleState.empty}[TargetWin check j.val z] := by
  refine (prEvent_mono_of_support _ _
    (fun z => ∃ j : Fin (qH + qS + 1), TargetWin check j.val z) ?_).trans
      (prEvent_exists_le _ _)
  intro z hz hw
  obtain ⟨v, i, hc, _, hi⟩ := withFinalHash_support_index_lt draw hash sign none oa qH qS hH hS z hz
  exact ⟨⟨i, hi⟩, hw, v, hc⟩

/-- Passive selected-slot bookkeeping does not change the probability of a winning forgery
at that slot. -/
theorem prEvent_targetWin_eraseSelection {V M G : Type} [DecidableEq M]
    (draw : ℕ → ProbComp V) (hash sign : V → G) (check : G → G) (j : ℕ)
    (oa : OracleComp ((unifSpec + (M →ₒ G)) + (M →ₒ G)) ((M × G) × G)) :
    Pr{let z ← (simulateQ (indexedOracle draw hash sign none) oa).run
        OracleState.empty}[TargetWin check j z] =
    Pr{let z ← (simulateQ (indexedOracle draw hash sign (some j)) oa).run
        OracleState.empty}[TargetWin check j z] := by
  have h := simulateQ_indexedOracle_eraseSelection draw hash sign (some j) oa OracleState.empty
  have hp := congrArg (fun mx => Pr{let z ← mx}[TargetWin check j z]) h
  simp only [prEvent_map, TargetWin, Winning, OracleState.eraseSelection,
    OracleState.empty, Prod.map, id_eq] at hp ⊢
  exact hp.symm

/-- For each fixed secret key, the scalar-sampled real game is bounded by the sum of the
success probabilities of the named reductions at individual guessed slots. -/
theorem prEvent_winning_le_sum_reductionAt {F G₁ G₂ Gₜ M : Type}
    [Field F] [SampleableType F] [AddCommGroup G₁] [Module F G₁] [SampleableType G₁]
    [AddCommGroup G₂] [Module F G₂] [AddCommGroup Gₜ] [Module F Gₜ]
    [DecidableEq Gₜ] [DecidableEq M]
    {e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ} {g₁ : G₁} {g₂ : G₂}
    (A : SignatureAlg.UnforgeableAdversary (scheme (M := M) e g₁ g₂))
    (hg₁ : Function.Bijective (· • g₁ : F → G₁)) (x : F) (qH qS : ℕ)
    (hQ : QueryBound A qH qS) :
    Pr{let z ← (simulateQ (indexedOracle (fun _ => $ᵗ F) (· • g₁)
        (fun ρ => x • (ρ • g₁)) none)
        (withFinalHash (A.main (x • g₁, x • g₂)))).run OracleState.empty}[Winning (x • ·) z] ≤
    ∑ j : Fin (qH + qS + 1),
      Pr{let h ← ($ᵗ G₁ : ProbComp G₁)
         let y ← reductionAt A j.val g₁ g₂ (x • g₁) (x • g₂) h}[y = x • h] := by
  refine (prEvent_winning_le_sum_targetWin (fun _ => $ᵗ F) (· • g₁)
    (fun ρ => x • (ρ • g₁)) (x • ·) (A.main (x • g₁, x • g₂)) qH qS
    (hQ _).1 (hQ _).2).trans ?_
  apply Finset.sum_le_sum
  intro j _
  rw [prEvent_targetWin_eraseSelection]
  exact prEvent_targetWin_le_reductionAt A hg₁ x j.val

end BLS
