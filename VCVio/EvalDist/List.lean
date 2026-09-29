/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module
public import VCVio.EvalDist.Defs.Support.Failure
public import VCVio.EvalDist.Monad.Seq

/-!
# Support of computations with lists and vectors

The support of `cons <$> mx <*> my` for lists and vectors, and index extraction from the support
of `Vector.mapM`. The lemmas are generic over any monad `m` with
`[MonadAttach m] [ExactMonadAttach m]`.
-/

@[expose] public section

universe u v w

variable {α β γ : Type v} {m : Type _ → Type _} [Monad m]

open List

/-! ## Support of `cons` -/

section support

variable [MonadAttach m] [ExactMonadAttach m]

lemma cons_mem_support_seq_map_cons_iff [LawfulMonad m]
    (mx : m α) (my : m (List α)) (x : α) (xs : List α) :
    x :: xs ∈ support (cons <$> mx <*> my) ↔ x ∈ support mx ∧ xs ∈ support my := by
  rw [support_seq_map_eq_image2, Set.mem_image2_iff injective2_cons]

lemma cons_mem_finSupport_seq_map_cons_iff [LawfulMonad m] [HasEvalFinset m] [DecidableEq α]
    (mx : m α) (my : m (List α)) (x : α) (xs : List α) :
    x :: xs ∈ finSupport (cons <$> mx <*> my) ↔
      x ∈ finSupport mx ∧ xs ∈ finSupport my := by
  simpa only [mem_finSupport_iff_mem_support] using cons_mem_support_seq_map_cons_iff mx my x xs

lemma support_seq_map_vector_cons {n : ℕ} (mx : m α) (my : m (List.Vector α n))
    [LawfulMonad m] :
    support ((· ::ᵥ ·) <$> mx <*> my) =
    {xs | xs.head ∈ support mx ∧ xs.tail ∈ support my} := by
  ext xs
  simp only [support_seq_map_eq_image2, Set.mem_image2, Set.mem_ofPred_eq]
  exact ⟨fun ⟨a, ha, b, hb, h⟩ => h ▸ ⟨by simpa using ha, by simpa using hb⟩,
    fun ⟨hh, ht⟩ => ⟨xs.head, hh, xs.tail, ht, xs.cons_head_tail⟩⟩

end support

section VectorMapM

/-- Index-extraction for `Vector.mapM`: any component of a vector in the support of
the sequenced computation lies in the support of the corresponding component computation. -/
lemma Vector.support_mapM_index
    {m : Type u → Type v} [Monad m] [LawfulMonad m]
    [MonadAttach m] [ExactMonadAttach m]
    {α β : Type u} {L : ℕ} (xs : _root_.Vector β L) (f : β → m α)
    {v : _root_.Vector α L} (hv : v ∈ support (xs.mapM f)) (i : Fin L) :
    v[i] ∈ support (f xs[i]) := by
  induction L with
  | zero => exact Fin.elim0 i
  | succ L ih =>
      obtain ⟨xs0, x, hxs⟩ := Vector.exists_push (xs := xs)
      obtain ⟨v0, y, hv0⟩ := Vector.exists_push (xs := v)
      subst hxs
      subst hv0
      have hpush : (xs0.push x).mapM f =
          (xs0.mapM f >>= (fun ys ↦ f x >>= fun last ↦ pure (ys.push last))) := by
        have hsingle : (#v[x]).mapM f = (fun last ↦ #v[last]) <$> f x := by
          apply Vector.map_toArray_inj.mp
          simp
        rw [← Vector.append_singleton, Vector.mapM_append, hsingle]
        simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp, pure_bind]
        rfl
      rw [hpush, mem_support_bind_iff] at hv
      obtain ⟨ys, hys, hv⟩ := hv
      rw [mem_support_bind_iff] at hv
      obtain ⟨last, hlast, hpush_eq⟩ := hv
      rw [mem_support_pure_iff] at hpush_eq
      have hparts := Vector.push_eq_push.mp hpush_eq.symm
      by_cases hi : (i : ℕ) < L
      · change (v0.push y)[(i : ℕ)] ∈ support (f ((xs0.push x)[(i : ℕ)]))
        rw [Vector.getElem_push_lt hi, Vector.getElem_push_lt hi, ← hparts.2]
        exact ih xs0 hys ⟨i, hi⟩
      · have hilast : (i : ℕ) = L := by omega
        have hi_eq : i = ⟨L, Nat.lt_succ_self L⟩ := Fin.ext hilast
        subst i
        simpa [← hparts.1] using hlast

end VectorMapM
