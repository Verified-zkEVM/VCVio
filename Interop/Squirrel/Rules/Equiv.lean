/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Squirrel.Global

/-!
# Structural rules for indistinguishability

The rules of BC14 (Fig. 2) and LICS23 (Figs. 5, 8) about `∼` that need no cryptographic
assumption, sound over `Valid` for every model restriction and every class of machines:

* `Valid.equiv_refl`, `Valid.equiv_symm`, `Valid.equiv_trans`;
* FA, as LICS23 splits it: `Valid.equiv_fn` (an honest symbol may be added), `Valid.equiv_adv`
  (G.Equiv:FA-Adv, a term the attacker computes may be added) and `Valid.equiv_app`
  (G.Equiv:FA-App, two entries may be replaced by the application of one to the other). BC14's
  FA for an honest symbol `f` is `equiv_fn` followed by `equiv_app` (`Valid.equiv_fa`);
* `Valid.equiv_rename` (Perm): both vectors reindexed along one map of positions, of which
  `Valid.equiv_tail` (Restr) and `Valid.equiv_dup` (Dup) are instances;
* `Valid.equiv_ite` (FA for `if`);
* `Valid.equiv_caseStudy` (LICS23's G.Case-Study:ITE) and `Valid.equiv_if1` (BC14's If1): the
  case split on a condition, whose two premises each keep the condition beside one branch;
* `Valid.equiv_rewrite`: rewriting an entry under an overwhelming equality `[t = t']`;
* `Valid.equiv_eq_self` (BC14's Eq1): `EQ(t, t)` may be replaced by `true`.

Each rule reads its premises and conclusion through `Form.holds_equiv` and applies one law of
`Interop.Squirrel.Indist`, whose proof is a named reduction and an equality of advantages at every
`η`; for the case split it is two named reductions and a bound by the sum of their advantages.
The vector entries that rules act on are the first ones. Every vector has order at most one
(`Ty.IndistOrder`); a rule's conclusion carries the bound derived from its premise's, and a rule
that adds an entry (`equiv_fn`, `equiv_adv`) takes the conclusion's bound, so that the added term
has order at most one.

## References

* [BC14] Bana, Comon-Lundh, *A Computationally Complete Symbolic Attacker for Equivalence
  Properties*, CCS 2014: Fig. 2 and Prop. 2.
* [LICS23] Baelde, Koutsos, Lallemand, *A Higher-Order Indistinguishability Logic for
  Cryptographic Reasoning*, LICS 2023: Figs. 5, 7 and 8.
-/

public section

namespace Interop.Squirrel

open IPFunctor IPFunctor.ScopedSignature

variable {B : Type} {D : Decl B} {R : Model D → Prop} {C : ∀ M : Model D, AdvClass M}
  {Γ : List (Kind B)} {Θ : List (Form D Γ)} {a τ : Ty B} {τs : List (Ty B)} {u v w : Vec D Γ τs}

namespace Valid

/-- **Refl.** -/
theorem equiv_refl (u : Vec D Γ τs) {h : Ty.IndistOrder τs} : Valid R C Θ (.equiv u u h) :=
  fun _ _ _ _ _ => Form.holds_equiv.2 (AdvClass.Indist.refl _)

/-- **Sym.** -/
theorem equiv_symm {ho : Ty.IndistOrder τs} (h : Valid R C Θ (.equiv u v ho)) :
    Valid R C Θ (.equiv v u ho) :=
  fun M hl hR env hΘ => Form.holds_equiv.2 (Form.holds_equiv.1 (h M hl hR env hΘ)).symm

/-- **Trans.** -/
theorem equiv_trans {ho : Ty.IndistOrder τs} (h₁ : Valid R C Θ (.equiv u v ho))
    (h₂ : Valid R C Θ (.equiv v w ho)) : Valid R C Θ (.equiv u w ho) :=
  fun M hl hR env hΘ => Form.holds_equiv.2 <|
  (Form.holds_equiv.1 (h₁ M hl hR env hΘ)).trans (Form.holds_equiv.1 (h₂ M hl hR env hΘ))

/-- **G.Equiv:FA-App.** Two entries may be replaced by the application of the first to the
second. The order bound makes the argument a Boolean or base type, which the reduction
`Machine.app` reads. -/
theorem equiv_app {b : Ty B} {t s : FTerm D Γ (.arrow a b)} {t' s' : FTerm D Γ a}
    {ho : Ty.IndistOrder (.arrow a b :: a :: τs)}
    (h : Valid R C Θ (.equiv (Env.cons t (Env.cons t' u)) (Env.cons s (Env.cons s' v)) ho)) :
    Valid R C Θ (.equiv (Env.cons (FTerm.app t t') u) (Env.cons (FTerm.app s s') v)
      ho.app) := by
  intro M hl hR env hΘ
  have hI := Form.holds_equiv.1 (h M hl hR env hΘ)
  simp only [Form.holds_equiv, Vec.rv_cons] at hI ⊢
  exact hI.app ho.isGround_app

/-- **FA-Fn.** An honest symbol may be added. -/
theorem equiv_fn {ho : Ty.IndistOrder (τ :: τs)} (f : D.Fn τ)
    (h : Valid R C Θ (.equiv u v ho.tail)) :
    Valid R C Θ (.equiv (Env.cons (FTerm.fn f) u) (Env.cons (FTerm.fn f) v) ho) := by
  intro M hl hR env hΘ
  simp only [Form.holds_equiv, Vec.rv_cons, FTerm.denote_fn]
  exact (Form.holds_equiv.1 (h M hl hR env hΘ)).fn f

/-- **G.Equiv:FA-Adv.** A term the attacker computes may be added. -/
theorem equiv_adv {τs₀ : List (Ty B)} {β : Ty B} {t : FTerm D Γ (Ty.arrows τs₀ β)}
    {ha : Ty.AdvOrder τs₀ β} {ho : Ty.IndistOrder (Ty.arrows τs₀ β :: τs)}
    (ht : Valid R C Θ (.adv t ha)) (h : Valid R C Θ (.equiv u v ho.tail)) :
    Valid R C Θ (.equiv (Env.cons t u) (Env.cons t v) ho) := by
  intro M hl hR env hΘ
  simp only [Form.holds_equiv, Vec.rv_cons]
  exact (Form.holds_equiv.1 (h M hl hR env hΘ)).adv (Form.holds_adv.1 (ht M hl hR env hΘ))

/-- **Restr.** An entry may be dropped. -/
theorem equiv_tail {t s : FTerm D Γ τ} {ho : Ty.IndistOrder (τ :: τs)}
    (h : Valid R C Θ (.equiv (Env.cons t u) (Env.cons s v) ho)) :
    Valid R C Θ (.equiv u v ho.tail) := by
  intro M hl hR env hΘ
  have hI := Form.holds_equiv.1 (h M hl hR env hΘ)
  simp only [Vec.rv_cons] at hI
  exact Form.holds_equiv.2 hI.tail

/-- **Dup.** An entry may be duplicated. -/
theorem equiv_dup {t s : FTerm D Γ τ} {ho : Ty.IndistOrder (τ :: τs)}
    (h : Valid R C Θ (.equiv (Env.cons t u) (Env.cons s v) ho)) :
    Valid R C Θ (.equiv (Env.cons t (Env.cons t u)) (Env.cons s (Env.cons s v)) ho.dup) := by
  intro M hl hR env hΘ
  have hI := Form.holds_equiv.1 (h M hl hR env hΘ)
  simp only [Form.holds_equiv, Vec.rv_cons] at hI ⊢
  exact hI.dup

/-- **If.** A condition and two branches may be replaced by the conditional. -/
theorem equiv_ite {c c' : FTerm D Γ .bool} {t t' s s' : FTerm D Γ a}
    {ho : Ty.IndistOrder (.bool :: a :: a :: τs)}
    (h : Valid R C Θ (.equiv (Env.cons c (Env.cons t (Env.cons t' u)))
      (Env.cons c' (Env.cons s (Env.cons s' v))) ho)) :
    Valid R C Θ (.equiv (Env.cons (FTerm.ite c t t') u) (Env.cons (FTerm.ite c' s s') v)
      ho.ite) := by
  intro M hl hR env hΘ
  have hI := Form.holds_equiv.1 (h M hl hR env hΘ)
  simp only [Form.holds_equiv, Vec.rv_cons] at hI ⊢
  exact hI.ite

/-- **G.Case-Study:ITE** (LICS23 Fig. 8; the tool's `cs` with one condition on both sides). A
conditional splits into its branches, each beside the condition: from `c, t, u⃗ ∼ c', s, v⃗` and
`c, t', u⃗ ∼ c', s', v⃗`, conclude `if c then t else t', u⃗ ∼ if c' then s else s', v⃗`. The
reductions are `Machine.guard true` and `.guard false`, and the advantage is at most the sum
of the two premises' advantages at every `η` (`advantage_cons_cond_le`). -/
theorem equiv_caseStudy {c c' : FTerm D Γ .bool} {t t' s s' : FTerm D Γ a}
    {ho : Ty.IndistOrder (.bool :: a :: τs)}
    (h₁ : Valid R C Θ (.equiv (Env.cons c (Env.cons t u)) (Env.cons c' (Env.cons s v)) ho))
    (h₂ : Valid R C Θ (.equiv (Env.cons c (Env.cons t' u)) (Env.cons c' (Env.cons s' v)) ho)) :
    Valid R C Θ (.equiv (Env.cons (FTerm.ite c t t') u) (Env.cons (FTerm.ite c' s s') v)
      ho.tail) := by
  intro M hl hR env hΘ
  have hI₁ := Form.holds_equiv.1 (h₁ M hl hR env hΘ)
  have hI₂ := Form.holds_equiv.1 (h₂ M hl hR env hΘ)
  simp only [Form.holds_equiv, Vec.rv_cons, FTerm.denote_ite] at hI₁ hI₂ ⊢
  exact hI₁.caseStudy hI₂

/-- **If1** (BC14 Fig. 2, Prop. 2): from `c, x, u⃗ ∼ c', z, v⃗` and `c, y, u⃗ ∼ c', z, v⃗`, conclude
`if c then x else y, u⃗ ∼ z, v⃗`. BC14 states it with one condition and one context on both sides
(`c' = c`, `v⃗ = u⃗`), an instance. It is the case split with both right-hand branches `z`. -/
theorem equiv_if1 {c c' : FTerm D Γ .bool} {x y z : FTerm D Γ a}
    {ho : Ty.IndistOrder (.bool :: a :: τs)}
    (h₁ : Valid R C Θ (.equiv (Env.cons c (Env.cons x u)) (Env.cons c' (Env.cons z v)) ho))
    (h₂ : Valid R C Θ (.equiv (Env.cons c (Env.cons y u)) (Env.cons c' (Env.cons z v)) ho)) :
    Valid R C Θ (.equiv (Env.cons (FTerm.ite c x y) u) (Env.cons z v) ho.tail) := by
  intro M hl hR env hΘ
  have hI₁ := Form.holds_equiv.1 (h₁ M hl hR env hΘ)
  have hI₂ := Form.holds_equiv.1 (h₂ M hl hR env hΘ)
  simp only [Form.holds_equiv, Vec.rv_cons, FTerm.denote_ite] at hI₁ hI₂ ⊢
  exact hI₁.if1 hI₂

/-- **Rewriting under an overwhelming equality.** If `[t = t']`, an entry `t` may be replaced by
`t'`. LICS23's G.Rewrite, for an equivalence atom. -/
theorem equiv_rewrite {t t' : FTerm D Γ τ} {w : Vec D Γ (τ :: τs)}
    {ho : Ty.IndistOrder (τ :: τs)} (heq : Valid R C Θ (.box (FTerm.eq t t')))
    (h : Valid R C Θ (.equiv (Env.cons t' u) w ho)) :
    Valid R C Θ (.equiv (Env.cons t u) w ho) := by
  intro M hl hR env hΘ
  have hI := Form.holds_equiv.1 (h M hl hR env hΘ)
  simp only [Form.holds_equiv, Vec.rv_cons] at hI ⊢
  refine hI.of_negligible_ne (negligible_of_le (fun η => prEvent_mono _ _ _ fun ρ hne => ?_)
    (Form.holds_box.1 (heq M hl hR env hΘ)))
  simp only [FTerm.denote_eq]
  refine @decide_eq_false _ (Classical.propDecidable _) fun he => hne ?_
  change Env.cons _ _ = Env.cons _ _
  rw [he]

/-- **Perm.** Reindexing both vectors along one map of positions that preserves types; this
permutes, projects and duplicates entries. -/
theorem equiv_rename {τs' : List (Ty B)} {ho : Ty.IndistOrder τs} (r : Renaming τs' τs)
    (h : Valid R C Θ (.equiv u v ho)) :
    Valid R C Θ (.equiv (Env.rename r u) (Env.rename r v) (ho.rename r)) :=
  fun M hl hR env hΘ => Form.holds_equiv.2 ((Form.holds_equiv.1 (h M hl hR env hΘ)).rename r)

/-- **Eq1** (BC14 Fig. 2): `EQ(t, t), u⃗ ∼ true, u⃗`. The two vectors have the same values at
every tape. -/
theorem equiv_eq_self (t : FTerm D Γ τ) (u : Vec D Γ τs) {ho : Ty.IndistOrder (.bool :: τs)} :
    Valid R C Θ (.equiv (Env.cons (FTerm.eq t t) u) (Env.cons FTerm.tt u) ho) := by
  intro M _ _ env _
  refine Form.holds_equiv.2 fun A _ => negligible_of_zero fun η => ENNReal.absDiff_eq_zero.2 ?_
  have h : Vec.rv M (C M) (Env.cons (FTerm.eq t t) u) env =
      Vec.rv M (C M) (Env.cons FTerm.tt u) env := by
    simp only [Vec.rv_cons, FTerm.denote_eq, FTerm.denote_tt]
    congr 1
  rw [h]

/-- **FA** (BC14) for an honest symbol of arrow type: FA-Fn, then FA-App. The order bound `ho`
of the intermediate vector makes the symbol's argument a Boolean or base type. -/
theorem equiv_fa {b : Ty B} (ho : Ty.IndistOrder (.arrow a b :: a :: τs)) (f : D.Fn (.arrow a b))
    {t s : FTerm D Γ a} (h : Valid R C Θ (.equiv (Env.cons t u) (Env.cons s v) ho.tail)) :
    Valid R C Θ (.equiv (Env.cons (FTerm.app (FTerm.fn f) t) u)
      (Env.cons (FTerm.app (FTerm.fn f) s) v) ho.app) :=
  (equiv_fn (ho := ho) f h).equiv_app

end Valid

end Interop.Squirrel
