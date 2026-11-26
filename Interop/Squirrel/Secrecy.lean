/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Squirrel.Global
import VCVio.EvalDist.ProbabilityBounds
import VCVio.OracleComp.EvalDist.Measure

/-!
# Non-deduction and deduction

Hérouard, Jacomme, Koutsos and Lallemand (CCS26, §3.1, p. 6) define two global formulas from the
global connectives, with no new primitive:

* `u⃗ ⊬ v ≜ ∀̃ f. adv(f) ⇒̃ [¬ (f(u⃗) = v)]`: no attacker function computes `v` from `u⃗`, except
  with negligible probability;
* `u⃗ ▷ v ≜ ∃̃ f. adv(f) ∧̃ [f(u⃗) = v]`: some attacker function computes `v` from `u⃗` with
  overwhelming probability.

The logic has no product types, so a tuple `u₁, …, uₙ` on the left is a vector of the types `τs`,
and `f` is a curried function of type `Ty.arrows τs β`, applied to the vector by `FTerm.apps`. The
right side is one term. CCS26 defines `adv` only for terms of order at most two, so `u⃗` and `v`
have order at most one; `Form.nonDed` and `Form.ded` carry this bound (`Ty.SecrecyOrder`), and the
attacker function's bound follows (`Ty.SecrecyOrder.advOrder`).

Read over random variables, the two predicates are:

* `deduceAdv g u v η`, the probability that the attacker function `g`, run on the attacker tape,
  computes `v` from `u` at `η`, and `deduceErr g u v η`, the probability that it does not;
* `AdvClass.NonDed C u v`: `deduceAdv g.eval u v` is negligible for every admitted attacker
  machine `g`;
* `AdvClass.Ded C u v`: `deduceErr g.eval u v` is negligible for some admitted `g`.

`Form.holds_nonDed` and `Form.holds_ded` say that the global formulas mean these predicates. The
attacker machine reads the attacker tape that every machine of the model shares, as `adv` does in
LICS23.

## The laws of CCS26 Fig. 3 (p. 7)

Each law is a concrete inequality at every `η` with its reduction named, then its asymptotic form.

* Neg1, Neg2: `deduceAdv g u v + deduceErr g u v = 1`, at the witness `g` of `▷`; no closure.
* Ineq: `Pr[v = w] ≤ deduceAdv g u v + deduceErr g u w`, at the witness `g` of `u ▷ w`; no
  closure.
* Trans: `deduceErr (k.comp f) u w ≤ deduceErr f u v + deduceErr k [v] w`, by the reduction
  `AttackerFn.comp`, the denotation of `AdvMachine.comp` (`AdvClass.comp_mem`: substitution and
  relabelling).
* WeakL: `deduceAdv g [v] w ≤ deduceAdv (g.comp f) u w + deduceErr f u v`, by the same reduction.
* WeakR: `deduceAdv g u w ≤ deduceAdv (k.comp g) u v + deduceErr k [w] v`, by the same reduction.
* Rw-Equiv: `deduceAdv g u₁ v₁ ≤ deduceAdv g u₂ v₂ + advantage (Machine.deduce g).test …`, by
  the reduction `Machine.deduce`, which runs `g` on the left part of the vector and tests its
  result against the last entry (`AdvClass.deduce_mem`: the equality test, substitution and
  relabelling).

Rw-Equiv is stated for a right side of Boolean or base type (`Ty.IsGround`): its distinguisher
tests `f(u⃗) = v`, which no machine does at an arrow type. The rules themselves, as statements
about validity, are in `Interop.Squirrel.Rules.Secrecy`.

## References

* [CCS26] Hérouard, Jacomme, Koutsos, Lallemand, *Secrecy in Squirrel and the Post-Compromise
  Security of a Ratchet*, CCS 2026: §3.1 and Fig. 3.
* [LICS23] Baelde, Koutsos, Lallemand, *A Higher-Order Indistinguishability Logic for
  Cryptographic Reasoning*, LICS 2023: Fig. 2.
-/

public section

namespace Interop.Squirrel

open IPFunctor IPFunctor.ScopedSignature

variable {B : Type} {D : Decl B}

/-! ## Vectors with one more entry -/

namespace VecRV

variable {M : Model D} {τs : List (Ty B)} {β : Ty B}

/-- The vector of one random variable. -/
@[expose] def single (X : RV M β) : VecRV M [β] := fun η ρ => Env.cons (X η ρ) Env.empty

/-- A vector followed by one random variable: CCS26's `u⃗, v`. -/
@[expose] def snoc (u : VecRV M τs) (X : RV M β) : VecRV M (τs ++ [β]) :=
  fun η ρ => Env.append (u η ρ) (Env.cons (X η ρ) Env.empty)

end VecRV

/-! ## Success and failure of an attacker function -/

section Semantics

variable {M : Model D} {τs : List (Ty B)} {β γ : Ty B}

/-- The probability that the attacker function `g` computes `v` from the vector `u` at `η`, over
uniform tapes: CCS26's `Pr[f(u⃗) = v]`. -/
@[expose] noncomputable def deduceAdv (g : AttackerFn M (Ty.arrows τs β)) (u : VecRV M τs)
    (v : RV M β) (η : ℕ) : ENNReal :=
  Pr{let ρ ← $ᵗ (M.Tape η)}[Ty.appVals (g η ρ.1) (u η ρ) = v η ρ]

/-- The probability that the attacker function `g` does not compute `v` from `u` at `η`. -/
@[expose] noncomputable def deduceErr (g : AttackerFn M (Ty.arrows τs β)) (u : VecRV M τs)
    (v : RV M β) (η : ℕ) : ENNReal :=
  Pr{let ρ ← $ᵗ (M.Tape η)}[Ty.appVals (g η ρ.1) (u η ρ) ≠ v η ρ]

/-- Success and failure partition the tapes. -/
theorem deduceAdv_add_deduceErr (g : AttackerFn M (Ty.arrows τs β)) (u : VecRV M τs)
    (v : RV M β) (η : ℕ) : deduceAdv g u v η + deduceErr g u v η = 1 := by
  rw [deduceAdv, deduceErr, prEvent_add_prEvent_not_eq_prEvent_true,
    OracleComp.prEvent_true_eq_one]

/-- `u⃗ ⊬ v` (CCS26 §3.1): every admitted attacker machine computes `v` from `u` with negligible
probability. -/
@[expose] def AdvClass.NonDed (C : AdvClass M) (u : VecRV M τs) (v : RV M β) : Prop :=
  ∀ g : AdvMachine M τs β, C.mem g → negligible (deduceAdv g.eval u v)

/-- `u⃗ ▷ v` (CCS26 §3.1): some admitted attacker machine computes `v` from `u` with overwhelming
probability. -/
@[expose] def AdvClass.Ded (C : AdvClass M) (u : VecRV M τs) (v : RV M β) : Prop :=
  ∃ g : AdvMachine M τs β, C.mem g ∧ negligible (deduceErr g.eval u v)

/-! ## Concrete statements at every `η` -/

/-- Ineq at `η`: `v` and `w` agree only where `g` computes `v` or misses `w`. -/
theorem prEvent_eq_le_deduceAdv_add_deduceErr (g : AttackerFn M (Ty.arrows τs β))
    (u : VecRV M τs) (v w : RV M β) (η : ℕ) :
    Pr{let ρ ← $ᵗ (M.Tape η)}[v η ρ = w η ρ] ≤ deduceAdv g u v η + deduceErr g u w η :=
  prEvent_le_prEvent_add_prEvent_of_imp _ fun _ h h' => (of_not_not h').trans h.symm

/-- Trans at `η`, by the reduction `AttackerFn.comp k f`. -/
theorem deduceErr_comp_le (k : AttackerFn M (.arrow β γ)) (f : AttackerFn M (Ty.arrows τs β))
    (u : VecRV M τs) (v : RV M β) (w : RV M γ) (η : ℕ) :
    deduceErr (k.comp f) u w η ≤
      deduceErr f u v η + deduceErr (τs := [β]) k (VecRV.single v) w η := by
  rw [add_comm]
  refine prEvent_le_prEvent_add_prEvent_of_imp _ fun ρ h h' => ?_
  simp only [AttackerFn.comp, Ty.appVals_postcomp, VecRV.single, not_not] at h h' ⊢
  rwa [← h']

/-- WeakL at `η`, by the reduction `AttackerFn.comp g f`: an attacker function computing `w` from
`v` computes it from `u` through `f`, wherever `f` computes `v`. -/
theorem deduceAdv_single_le (g : AttackerFn M (.arrow β γ)) (f : AttackerFn M (Ty.arrows τs β))
    (u : VecRV M τs) (v : RV M β) (w : RV M γ) (η : ℕ) :
    deduceAdv (τs := [β]) g (VecRV.single v) w η ≤
      deduceAdv (g.comp f) u w η + deduceErr f u v η :=
  prEvent_le_prEvent_add_prEvent_of_imp _ fun ρ h h' => by
    simp only [AttackerFn.comp, Ty.appVals_postcomp, VecRV.single, not_not] at h h' ⊢
    rwa [h']

/-- WeakR at `η`, by the reduction `AttackerFn.comp k g`: wherever `k` computes `v` from `w`, an
attacker function computing `w` computes `v` through `k`. -/
theorem deduceAdv_le_comp (g : AttackerFn M (Ty.arrows τs γ)) (k : AttackerFn M (.arrow γ β))
    (u : VecRV M τs) (v : RV M β) (w : RV M γ) (η : ℕ) :
    deduceAdv g u w η ≤
      deduceAdv (k.comp g) u v η + deduceErr (τs := [γ]) k (VecRV.single w) v η :=
  prEvent_le_prEvent_add_prEvent_of_imp _ fun ρ h h' => by
    simp only [AttackerFn.comp, Ty.appVals_postcomp, VecRV.single, not_not] at h h' ⊢
    rwa [h]

/-- Rw-Equiv at `η`: the success of `g` against `u₁, v₁` is at most its success against `u₂, v₂`
plus the advantage of the reduction `Machine.deduce g` between the two vectors. -/
theorem deduceAdv_le_add_advantage (hβ : β.IsGround) (g : AdvMachine M τs β) (u₁ u₂ : VecRV M τs)
    (v₁ v₂ : RV M β) (η : ℕ) :
    deduceAdv g.eval u₁ v₁ η ≤ deduceAdv g.eval u₂ v₂ η +
      advantage (Machine.deduce hβ g).test (VecRV.snoc u₁ v₁) (VecRV.snoc u₂ v₂) η := by
  have hp : ∀ (u : VecRV M τs) (v : RV M β),
      Pr{let ρ ← $ᵗ (M.Tape η)}[(Machine.deduce hβ g).test η (VecRV.snoc u v η ρ) ρ.1 = true] =
        deduceAdv g.eval u v η := fun u v =>
    prEvent_congr _ _ _ fun ρ => by
      rw [VecRV.snoc, Machine.test, Machine.run_deduce]
      exact @decide_eq_true_iff _ (Ty.decEqValue hβ _ _)
  have h := (ENNReal.absDiff_le_iff.1 (le_refl (advantage (Machine.deduce hβ g).test
    (VecRV.snoc u₁ v₁) (VecRV.snoc u₂ v₂) η))).1
  rw [hp, hp] at h
  exact h

/-! ## The laws -/

namespace AdvClass

variable {C : AdvClass M} {u : VecRV M τs} {v w : RV M β}

/-- **Neg1** (CCS26 Fig. 3): `u⃗ ⊬ v` refutes `u⃗ ▷ v`. The witness of `▷` would compute `v` with
probability negligibly close to one, and `1` is not negligible. -/
theorem NonDed.not_ded (h : C.NonDed u v) : ¬ C.Ded u v := fun ⟨g, hg, herr⟩ =>
  not_negligible_one (negligible_of_le (fun η => (deduceAdv_add_deduceErr g.eval u v η).ge)
    (negligible_add (h g hg) herr))

/-- **Neg2** (CCS26 Fig. 3): `u⃗ ▷ v` refutes `u⃗ ⊬ v`. -/
theorem Ded.not_nonDed (h : C.Ded u v) : ¬ C.NonDed u v := fun h' => h'.not_ded h

/-- **Ineq** (CCS26 Fig. 3): if `u⃗ ⊬ v` and `u⃗ ▷ w`, then `v` and `w` agree with negligible
probability, by `prEvent_eq_le_deduceAdv_add_deduceErr` at the witness of `u⃗ ▷ w`. -/
theorem NonDed.negligible_eq (h : C.NonDed u v) (h' : C.Ded u w) :
    negligible fun η => Pr{let ρ ← $ᵗ (M.Tape η)}[v η ρ = w η ρ] := by
  obtain ⟨g, hg, herr⟩ := h'
  exact negligible_of_le (prEvent_eq_le_deduceAdv_add_deduceErr g.eval u v w)
    (negligible_add (h g hg) herr)

/-- **Trans** (CCS26 Fig. 3): `u⃗ ▷ v` and `v ▷ w` give `u⃗ ▷ w`, by the reduction
`AdvMachine.comp` of the two witnesses. -/
theorem Ded.trans {w : RV M γ} (h₁ : C.Ded u v) (h₂ : C.Ded (VecRV.single v) w) : C.Ded u w := by
  obtain ⟨f, hf, hferr⟩ := h₁
  obtain ⟨k, hk, hkerr⟩ := h₂
  refine ⟨k.comp f, C.comp_mem hk hf, ?_⟩
  rw [AdvMachine.eval_comp]
  exact negligible_of_le (deduceErr_comp_le k.eval f.eval u v w) (negligible_add hferr hkerr)

/-- **WeakL** (CCS26 Fig. 3): `u⃗ ⊬ w` and `u⃗ ▷ v` give `v ⊬ w`, by the reduction
`AdvMachine.comp g f` from an attacker machine `g` against `v ⊬ w` and the witness `f`. -/
theorem NonDed.weakL {w : RV M γ} (h : C.NonDed u w) (h' : C.Ded u v) :
    C.NonDed (VecRV.single v) w := by
  obtain ⟨f, hf, hferr⟩ := h'
  intro g hg
  have hgf := h _ (C.comp_mem hg hf)
  rw [AdvMachine.eval_comp] at hgf
  exact negligible_of_le (deduceAdv_single_le g.eval f.eval u v w) (negligible_add hgf hferr)

/-- **WeakR** (CCS26 Fig. 3): `u⃗ ⊬ v` and `w ▷ v` give `u⃗ ⊬ w`, by the reduction
`AdvMachine.comp k g` from an attacker machine `g` against `u⃗ ⊬ w` and the witness `k`. -/
theorem NonDed.weakR {w : RV M γ} (h : C.NonDed u v) (h' : C.Ded (VecRV.single w) v) :
    C.NonDed u w := by
  obtain ⟨k, hk, hkerr⟩ := h'
  intro g hg
  have hkg := h _ (C.comp_mem hk hg)
  rw [AdvMachine.eval_comp] at hkg
  exact negligible_of_le (deduceAdv_le_comp g.eval k.eval u v w) (negligible_add hkg hkerr)

/-- **Rw-Equiv** (CCS26 Fig. 3), for a right side of Boolean or base type: `u⃗₂ ⊬ v₂` and
`u⃗₁, v₁ ∼ u⃗₂, v₂` give `u⃗₁ ⊬ v₁`, by the reduction `Machine.deduce`. -/
theorem NonDed.rwEquiv (hβ : β.IsGround) {u₁ u₂ : VecRV M τs} {v₁ v₂ : RV M β}
    (h : C.NonDed u₂ v₂) (h' : C.Indist (VecRV.snoc u₁ v₁) (VecRV.snoc u₂ v₂)) :
    C.NonDed u₁ v₁ := fun g hg =>
  negligible_of_le (deduceAdv_le_add_advantage hβ g u₁ u₂ v₁ v₂)
    (negligible_add (h g hg) (h' _ (C.deduce_mem hβ hg)))

end AdvClass

end Semantics

/-! ## The predicates as global formulas -/

variable {Γ : List (Kind B)} {τs : List (Ty B)} {β : Ty B}

/-- A term of the curried type `Ty.arrows τs β` applied to a vector of terms of the types
`τs`. -/
@[expose] def FTerm.apps : {τs : List (Ty B)} → FTerm D Γ (Ty.arrows τs β) → Vec D Γ τs →
    FTerm D Γ β
  | [], f, _ => f
  | _ :: _, f, u => FTerm.apps (FTerm.app f (u _ .zero)) fun _ x => u _ (.succ x)

/-- A vector weakened past one binder. -/
@[expose] def Vec.weaken (u : Vec D Γ τs) (s : Kind B) : Vec D (s :: Γ) τs :=
  fun _ x => (u _ x).weaken s

/-- A vector followed by one term: CCS26's `u⃗, v`. -/
@[expose] def Vec.snoc (u : Vec D Γ τs) (v : FTerm D Γ β) : Vec D Γ (τs ++ [β]) :=
  Env.append u (Env.cons v Env.empty)

/-- `u⃗ ⊬ v` (CCS26 §3.1): `∀̃ f. adv(f) ⇒̃ [¬ (f(u⃗) = v)]`, for `u⃗` and `v` of order at most
one, so that `f` has order at most two. -/
@[expose] def Form.nonDed (u : Vec D Γ τs) (v : FTerm D Γ β)
    (h : Ty.SecrecyOrder τs β := by exact of_decide_eq_true rfl) : Form D Γ :=
  .all (Ty.arrows τs β) (.imp (.adv (Term.var .zero) h.advOrder)
    (.box (FTerm.not (FTerm.eq (FTerm.apps (Term.var .zero) (u.weaken _)) (v.weaken _)))))

/-- `u⃗ ▷ v` (CCS26 §3.1): `∃̃ f. adv(f) ∧̃ [f(u⃗) = v]`, for `u⃗` and `v` of order at most one. -/
@[expose] def Form.ded (u : Vec D Γ τs) (v : FTerm D Γ β)
    (h : Ty.SecrecyOrder τs β := by exact of_decide_eq_true rfl) : Form D Γ :=
  .ex (Ty.arrows τs β) (.and (.adv (Term.var .zero) h.advOrder)
    (.box (FTerm.eq (FTerm.apps (Term.var .zero) (u.weaken _)) (v.weaken _))))

section Reading

variable {M : Model D} {C : AdvClass M} {env : Env (Kind.Value M) Γ}

/-- An application to a vector means the curried function applied to the vector's values. -/
theorem FTerm.denote_apps : ∀ {τs : List (Ty B)} (f : FTerm D Γ (Ty.arrows τs β))
    (u : Vec D Γ τs), (FTerm.apps f u).denote (fullInterp M C) env =
      fun η ρ => Ty.appVals (f.denote (fullInterp M C) env η ρ) (u.rv M C env η ρ)
  | [], _, _ => rfl
  | _ :: _, f, u => FTerm.denote_apps (FTerm.app f (u _ .zero)) _

theorem Vec.rv_weaken {s : Kind B} (u : Vec D Γ τs) (x : s.Value M) :
    (u.weaken s).rv M C (Env.cons x env) = u.rv M C env := by
  funext η ρ σ y
  exact congrFun (congrFun (denote_weaken_cons _ (u σ y) x env) η) ρ

theorem Vec.rv_append : ∀ {Ξ : List (Ty B)} (u : Vec D Γ Ξ) (w : Vec D Γ τs),
    Vec.rv M C (Env.append u w) env = fun η ρ => Env.append (u.rv M C env η ρ) (w.rv M C env η ρ)
  | [], _, _ => rfl
  | _ :: _, u, w => by
    funext η ρ σ x
    cases x with
    | zero => rfl
    | succ x => exact congrFun (congrFun (congrFun (congrFun
        (Vec.rv_append (fun _ y => u _ (.succ y)) w) η) ρ) σ) x

theorem Vec.rv_snoc (u : Vec D Γ τs) (v : FTerm D Γ β) :
    (Vec.snoc u v).rv M C env = VecRV.snoc (u.rv M C env) (v.denote (fullInterp M C) env) := by
  rw [Vec.snoc, Vec.rv_append]
  funext η ρ
  congr 1
  funext σ x
  cases x with
  | zero => rfl
  | succ x => exact nomatch x

theorem Vec.rv_single (v : FTerm D Γ β) :
    Vec.rv M C (Env.cons v Env.empty : Vec D Γ [β]) env =
      VecRV.single (v.denote (fullInterp M C) env) := by
  funext η ρ σ x
  cases x with
  | zero => rfl
  | succ x => exact nomatch x

/-- `¬ (t = u)` is false at a point exactly where `t` and `u` agree. -/
theorem FTerm.denote_not_eq_eq_false_iff {a : Ty B} (t u : FTerm D Γ a) (η : ℕ)
    (ρ : M.Tape η) :
    (FTerm.not (FTerm.eq t u)).denote (fullInterp M C) env η ρ = false ↔
      t.denote (fullInterp M C) env η ρ = u.denote (fullInterp M C) env η ρ := by
  simp only [FTerm.not, FTerm.denote_ite, FTerm.denote_eq, FTerm.denote_ff, FTerm.denote_tt]
  by_cases h : t.denote (fullInterp M C) env η ρ = u.denote (fullInterp M C) env η ρ <;> simp [h]

/-- The local equality under the binder of `⊬` and `▷`, at a value `X` of the bound function. -/
private theorem denote_eq_apps (u : Vec D Γ τs) (v : FTerm D Γ β) (X : RV M (Ty.arrows τs β)) :
    (FTerm.eq (FTerm.apps (Term.var .zero) (u.weaken (.loc (Ty.arrows τs β))))
        (v.weaken (.loc (Ty.arrows τs β)))).denote (fullInterp M C) (Env.cons X env) =
      fun η ρ => @decide (Ty.appVals (X η ρ) (u.rv M C env η ρ) =
        v.denote (fullInterp M C) env η ρ) (Classical.propDecidable _) := by
  rw [FTerm.denote_eq, FTerm.denote_apps, Vec.rv_weaken, denote_weaken_cons]
  rfl

/-- `u⃗ ⊬ v` holds when no admitted attacker machine computes `v` from `u⃗` with
non-negligible probability. -/
theorem Form.holds_nonDed {u : Vec D Γ τs} {v : FTerm D Γ β} {ho : Ty.SecrecyOrder τs β} :
    (Form.nonDed u v ho).Holds M C env ↔
      C.NonDed (u.rv M C env) (v.denote (fullInterp M C) env) := by
  have hX : ∀ X : RV M (Ty.arrows τs β), Overwhelming M.toTapeModel
      ((FTerm.not (FTerm.eq (FTerm.apps (Term.var .zero) (u.weaken (.loc (Ty.arrows τs β))))
        (v.weaken (.loc (Ty.arrows τs β))))).denote (fullInterp M C) (Env.cons X env)) ↔
      negligible fun η => Pr{let ρ ← $ᵗ (M.Tape η)}[Ty.appVals (X η ρ) (u.rv M C env η ρ) =
        v.denote (fullInterp M C) env η ρ] := fun X => by
    refine iff_of_eq (congrArg negligible (funext fun η => prEvent_congr _ _ _ fun ρ => ?_))
    rw [FTerm.denote_not_eq_eq_false_iff, FTerm.denote_apps, Vec.rv_weaken, denote_weaken_cons]
    rfl
  refine ⟨fun h g hg => (hX _).1 (h _ ⟨g, hg, fun _ _ => rfl⟩), fun h X hXg => ?_⟩
  obtain ⟨g, hg, hXg⟩ := hXg
  obtain rfl : X = fun η ρ => g.eval η ρ.1 := funext fun η => funext (hXg η)
  exact (hX _).2 (h g hg)

/-- `u⃗ ▷ v` holds when some admitted attacker machine computes `v` from `u⃗` with overwhelming
probability. -/
theorem Form.holds_ded {u : Vec D Γ τs} {v : FTerm D Γ β} {ho : Ty.SecrecyOrder τs β} :
    (Form.ded u v ho).Holds M C env ↔ C.Ded (u.rv M C env) (v.denote (fullInterp M C) env) := by
  have hX : ∀ X : RV M (Ty.arrows τs β), Overwhelming M.toTapeModel
      ((FTerm.eq (FTerm.apps (Term.var .zero) (u.weaken (.loc (Ty.arrows τs β))))
        (v.weaken (.loc (Ty.arrows τs β)))).denote (fullInterp M C) (Env.cons X env)) ↔
      negligible fun η => Pr{let ρ ← $ᵗ (M.Tape η)}[Ty.appVals (X η ρ) (u.rv M C env η ρ) ≠
        v.denote (fullInterp M C) env η ρ] := fun X => by
    refine iff_of_eq (congrArg negligible (funext fun η => prEvent_congr _ _ _ fun ρ => ?_))
    rw [denote_eq_apps]
    exact @decide_eq_false_iff_not _ (Classical.propDecidable _)
  refine ⟨fun ⟨X, ⟨g, hg, hXg⟩, hbox⟩ => ⟨g, hg, ?_⟩, fun ⟨g, hg, herr⟩ =>
    ⟨fun η ρ => g.eval η ρ.1, ⟨g, hg, fun _ _ => rfl⟩, (hX _).2 herr⟩⟩
  obtain rfl : X = fun η ρ => g.eval η ρ.1 := funext fun η => funext (hXg η)
  exact (hX _).1 hbox

end Reading

end Interop.Squirrel
