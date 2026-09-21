/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import ToMathlib.Data.Vector.Induction
public import ToMathlib.Data.Vector.ListVector
public import ToMathlib.Logic.Basic
public import Mathlib.Control.Monad.Basic
public import PolyFun.Control.Monad.Hom

/-!
# Lemmas about monadic operations on `Vector`

Commutation lemmas for `Vector.mapM` against pure post-processing maps, index-wise
extraction lemmas for sequencing `Option`-valued vectors, and the naturality of `Vector.ofFnM`
under a monad morphism.
-/

@[expose] public section

universe u v

namespace Vector

/-- `Vector.mapM` commutes with post-composition by a pure map:
mapping `g` after each monadic action is the same as mapping `g` over the collected vector. -/
lemma mapM_map_postcomp {m : Type → Type} {α β γ : Type} {n : ℕ}
    [Monad m] [LawfulMonad m]
    (v : Vector α n) (f : α → m β) (g : β → γ) :
    (v.mapM (fun a => g <$> f a)) = (Vector.map g) <$> (v.mapM f) := by
  have hlist : ∀ l : List α, l.mapM (fun a ↦ g <$> f a) = List.map g <$> l.mapM f := by
    intro l
    induction l with
    | nil => simp
    | cons a t ih => simp [ih]
  apply Vector.map_toArray_inj.mp
  rw [Vector.toArray_mapM]
  simp only [Functor.map_map, Vector.toArray_map]
  rw [← Functor.map_map, Vector.toArray_mapM, Array.mapM_eq_mapM_toList,
    Array.mapM_eq_mapM_toList]
  simp only [Functor.map_map]
  rw [hlist]
  simp [Functor.map_map]

/-- `Option.map` distributes through `Vector.mapM id` (sequencing of options):
mapping before sequencing equals sequencing then mapping. -/
lemma mapM_id_option_map_comm {α β : Type} {n : ℕ}
    (v : Vector (Option α) n) (g : α → β) :
    (v.map (Option.map g)).mapM (id : Option β → Option β) =
    (v.mapM (id : Option α → Option α)).map (Vector.map g) := by
  rw [Vector.mapM_map]
  exact Vector.mapM_map_postcomp v (id : Option α → Option α) g

/-- Two `Vector.mapM` calls with pointwise-related monadic bodies produce equal
results after compatible post-processing when the bodies differ by a pure map. -/
lemma mapM_bind_map_eq {m : Type → Type} {α β γ δ : Type} {n : ℕ}
    [Monad m] [LawfulMonad m]
    (v : Vector α n)
    (f₁ : α → m γ) (f₂ : α → m β) (g : β → γ)
    (hf : ∀ a, f₁ a = g <$> f₂ a)
    (post₁ : Vector γ n → m δ) (post₂ : Vector β n → m δ)
    (hpost : ∀ opts, post₁ (opts.map g) = post₂ opts) :
    (v.mapM f₁ >>= post₁) = (v.mapM f₂ >>= post₂) := by
  have hf' : f₁ = fun a ↦ g <$> f₂ a := funext hf
  rw [hf', Vector.mapM_map_postcomp]
  simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp, pure_bind]
  exact bind_congr hpost

/-- For a `Vector` of `Option` values, if `mapM id` yields `some w`, then each entry is
`some` of the corresponding entry in `w`. -/
lemma mapM_id_some_index
    {α : Type} {L : ℕ} {v : Vector (Option α) L} {w : Vector α L}
    (h : v.mapM id = some w) (i : Fin L) : v[i] = some w[i] := by
  induction L with
  | zero => exact Fin.elim0 i
  | succ L ih =>
      obtain ⟨v0, a, hv⟩ := Vector.exists_push (xs := v)
      obtain ⟨w0, b, hw⟩ := Vector.exists_push (xs := w)
      subst hv
      subst hw
      have hdecomp : v0.mapM id = some w0 ∧ a = some b := by
        have hpush : (v0.push a).mapM id =
            (v0.mapM id >>= (fun x ↦ a.map (fun last ↦ x.push last))) := by
          have hsingle : (#v[a]).mapM id = a.map (fun last ↦ #v[last]) := by
            apply Vector.map_toArray_inj.mp
            cases a <;> simp
          rw [← Vector.append_singleton, Vector.mapM_append, hsingle]
          cases a <;> simp [Vector.append_singleton]
        rw [hpush] at h
        cases hv0 : v0.mapM id with
        | none => simp [hv0] at h
        | some w0' =>
            cases ha : a with
            | none => simp [hv0, ha] at h
            | some aval =>
                simp only [hv0, ha, Option.map_some, Option.bind_eq_bind, Option.bind_some,
                  Option.some.injEq] at h
                have hp := Vector.push_eq_push.mp h
                exact ⟨congrArg some hp.2, congrArg some hp.1⟩
      by_cases hi : (i : ℕ) < L
      · change (v0.push a)[(i : ℕ)] = some ((w0.push b)[(i : ℕ)])
        rw [Vector.getElem_push_lt hi, Vector.getElem_push_lt hi]
        exact ih hdecomp.1 ⟨i, hi⟩
      · have hilast : (i : ℕ) = L := by omega
        have hi_eq : i = ⟨L, Nat.lt_succ_self L⟩ := Fin.ext hilast
        subst i
        simp [hdecomp.2]

/-- `Vector.ofFnM` is natural in the monad: a monad morphism applied to a monadic vector
construction is the construction of the componentwise images. -/
theorem ofFnM_natural {m n : Type → Type*} [Monad m] [LawfulMonad m]
    [Monad n] [LawfulMonad n] (F : m →ᵐ n) {α : Type} {k : ℕ}
    (fm : Fin k → m α) (fn : Fin k → n α) (h : ∀ i, F (fm i) = fn i) :
    F (Vector.ofFnM fm) = Vector.ofFnM fn := by
  induction k with
  | zero => simp [F.mmap_pure]
  | succ k ih =>
      rw [Vector.ofFnM_succ, Vector.ofFnM_succ, F.mmap_bind]
      rw [ih (fun i => fm i.castSucc) (fun i => fn i.castSucc) (fun i => h i.castSucc)]
      congr 1
      funext xs
      rw [F.mmap_bind, h (Fin.last k)]
      simp [F.mmap_pure]

end Vector
