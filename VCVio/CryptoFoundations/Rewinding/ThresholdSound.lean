/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.Rewinding.ThresholdSemantics

/-!
# Soundness of recursive threshold extraction

Every returned tree has distinct sibling challenges and accepting leaves. These are operational
support properties and do not require a probability interpretation of the acceptance operation.
-/

public section

open OracleComp OracleSpec

namespace Rewinding

/-- A successful recursive threshold program returns a structured tree of accepting vectors. -/
theorem thresholdProgram_sound {ι : Type} {spec : OracleSpec ι}
    (sample : (j : ℕ) → OracleComp spec (Fin (j + 1)))
    (n : ℕ) (C : Fin n → Type) (k : Fin n → ℕ) (pools : (i : Fin n) → List (C i))
    (accept : ((i : Fin n) → C i) → OracleComp spec Bool)
    (f : ((i : Fin n) → C i) → Bool) (hpools : ∀ i, (pools i).Nodup)
    (haccept : ∀ q, true ∈ support (accept q) → f q = true)
    (t : VecTree C k) (ht : some t ∈ support (thresholdProgram sample n C k pools accept)) :
    t.IsStructured (fun _ ch => Function.Injective ch) ∧ ∀ p, f (t.leaf p) = true := by
  induction n with
  | zero =>
    rw [thresholdProgram, mem_support_bind_iff] at ht
    obtain ⟨b, hb, ht⟩ := ht
    cases b with
    | false => simp at ht
    | true =>
      simp only [ite_true, support_pure, Set.mem_singleton_iff, Option.some.injEq] at ht
      subst t
      exact ⟨fun _ r => Fin.elim0 r, fun _ => haccept _ hb⟩
  | succ n ih =>
    rw [thresholdProgram, mem_support_bind_iff] at ht
    obtain ⟨ws, hws, ht⟩ := ht
    cases ws with
    | none => simp at ht
    | some ws =>
      simp only [Option.bind_some, support_pure, Set.mem_singleton_iff] at ht
      unfold assembleChildren at ht
      split at ht
      next hlen =>
        have heq := Option.some.inj ht
        subst t
        let P := fun w : C 0 × VecTree (fun i : Fin n => C i.succ) (fun i => k i.succ) =>
          w.2.IsStructured (fun _ ch => Function.Injective ch) ∧
            ∀ p, f (Fin.cons w.1 (w.2.leaf p)) = true
        have hchild : ∀ c w,
            some w ∈ support (do
              let t ← thresholdProgram sample n (fun i => C i.succ) (fun i => k i.succ)
                (fun i => pools i.succ) (fun q => accept (Fin.cons c q))
              pure (t.map (fun t => (c, t)))) → w.1 = c ∧ P w := by
          intro c w hw
          rw [mem_support_bind_iff] at hw
          obtain ⟨u, hu, hw⟩ := hw
          cases u with
          | none => simp at hw
          | some u =>
            simp only [Option.map_some, support_pure, Set.mem_singleton_iff,
              Option.some.injEq] at hw
            subst w
            exact ⟨rfl, ih _ _ _ _ (fun q => f (Fin.cons c q))
              (fun i => hpools i.succ) (fun q => haccept (Fin.cons c q)) u hu⟩
        obtain ⟨hnd, hmem⟩ := sound_thresholdChildren sample _ Prod.fst P hchild
          (k 0) (pools 0) (hpools 0) ws hws
        have hget : ∀ j : Fin (k 0), (j : ℕ) < ws.length := by
          intro j
          simpa only [hlen] using j.isLt
        constructor
        · apply VecTree.cons_isStructured
          · intro i j hij
            apply Fin.ext
            apply (hnd.getElem_inj_iff
              (hi := by simpa using hget i) (hj := by simpa using hget j)).mp
            rw [List.getElem_map, List.getElem_map]
            exact hij
          · intro j
            exact (hmem _ (List.getElem_mem (hget j))).2.1
        · intro p
          exact (hmem _ (List.getElem_mem (hget (p 0)))).2.2 (fun i => p i.succ)
      next hlen => simp at ht

/-- The counted black-box threshold finder returns only structured accepting trees. -/
theorem thresholdFinder_sound {n : ℕ} (C : Fin n → Type) [∀ i, SampleableType (C i)]
    [∀ i, DecidableEq (C i)] (k : Fin n → ℕ)
    (f : ((i : Fin n) → C i) → Bool)
    (z : Option (VecTree C k) × ℕ) (hz : z ∈ support (runFinder (thresholdFinder C k) f))
    (t : VecTree C k) (ht : z.1 = some t) :
    t.IsStructured (fun _ ch => Function.Injective ch) ∧ ∀ p, f (t.leaf p) = true := by
  have hz' : some t ∈ support (Prod.fst <$> runFinder (thresholdFinder C k) f) := by
    rw [support_map]
    exact ⟨z, hz, ht⟩
  rw [runFinder, counted_fst, thresholdFinder, simulateQ_thresholdFinderWithPools] at hz'
  apply thresholdProgram_sound _ n C k _ _ f (fun i => nodup_challengePool (C i)) _ t hz'
  intro q hq
  change true ∈ support (pure (f q) : ProbComp Bool) at hq
  simpa only [support_pure, Set.mem_singleton_iff, eq_comm] using hq

end Rewinding
