/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Squirrel.Global
public import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Read bounds and long attacker tapes

LICS23 takes the attacker tape `ρa` to be a finite bitstring "long enough" for the machines
considered (§II-A.3), and CCS26's proof of FreshL (App. C.2, footnote 2, p. 17) samples a fresh
name "from the adversarial randomness", from bits that the terms do not read. This module states
the two facts that argument needs; FreshL (`Interop.Squirrel.Rules.FreshL`) takes both as
hypotheses:

* `RV.ReadsBelow X b`: the random variable `X` depends on `ρa` only through its bits below `b η`
  (`VecRV.ReadsBelow` for every entry of a vector). An `adv` term has this property for a
  polynomial `b`, the read bound of its machine (`RV.readsBelow_of_eval`,
  `AdvClass.Adv.readsBelow`), from the closure field `AdvClass.readBound_mem`.
* `Model.LongTapes M`: the attacker tape is eventually longer than every polynomial, the formal
  counterpart of LICS23's "long enough" tapes and of the room that CCS26's footnote makes on the
  tape. It is a condition on models, taken as a hypothesis on the model restriction. Tapes of at
  least `2^η` bits are long (`Model.longTapes_of_two_pow_le`).

## The read bound of a term

FreshL asks that the terms `u⃗, v` read `ρa` only below a polynomial (`FTerm.ReadsPoly`). The
condition is discharged structurally, one constructor at a time:

* honest symbols, `true` and `false` read nothing of `ρa` (`FTerm.readsPoly_fn`, `readsPoly_tt`,
  `readsPoly_ff`), and a name reads only what its index reads (`FTerm.ReadsPoly.name`);
* application, conditionals, equality and negation take the sum of the bounds of their parts
  (`FTerm.ReadsPoly.app`, `.ite`, `.eq`, `.not`);
* a term whose random variable an admitted machine computes has that machine's bound
  (`FTerm.readsPoly_of_adv`).

Free variables range over all random variables, and an attacker symbol is an arbitrary function of
`ρa` (`Model.att`), so neither is bounded by itself. The caption of CCS26 Fig. 11 asks every
declared variable to be a name or adversarial (`E; Θ ⊢ adv(v)`), and LICS23 (p. 17) adds `adv(g)`
for every attacker symbol `g`; following them, the bound of a free variable or an attacker symbol
is derived from an `adv` hypothesis (`Valid.readsPoly_of_adv`), not imposed on models. λ and the
local quantifiers are not covered: their bodies are read at every value of the bound variable,
and a bound uniform in that value is not built here.

## References

* [LICS23] Baelde, Koutsos, Lallemand, *A Higher-Order Indistinguishability Logic for
  Cryptographic Reasoning*, LICS 2023: §II-A.3, §II-C.1 and p. 17.
* [CCS26] Hérouard, Jacomme, Koutsos, Lallemand, *Secrecy in Squirrel and the Post-Compromise
  Security of a Ratchet*, CCS 2026: Fig. 11 and App. C.2.
-/

public section

namespace Interop.Squirrel

open IPFunctor IPFunctor.ScopedSignature

variable {B : Type} {D : Decl B} {M : Model D} {τs : List (Ty B)} {β : Ty B}

/-! ## Random variables with a read bound -/

/-- The random variable `X` depends on the attacker tape only through its bits below `b η`. -/
@[expose] def RV.ReadsBelow {τ : Ty B} (X : RV M τ) (b : ℕ → ℕ) : Prop :=
  ∀ η (ρa ρa' : M.TapeA η) (ρh : M.TapeH η), (∀ i < b η, M.readBit ρa i = M.readBit ρa' i) →
    X η (ρa, ρh) = X η (ρa', ρh)

theorem RV.ReadsBelow.mono {τ : Ty B} {X : RV M τ} {b b' : ℕ → ℕ} (h : X.ReadsBelow b)
    (hb : ∀ η, b η ≤ b' η) : X.ReadsBelow b' :=
  fun η ρa ρa' ρh hρ => h η ρa ρa' ρh fun i hi => hρ i (lt_of_lt_of_le hi (hb η))

/-- A random variable computed by an attacker machine that reads below `b` depends on the
attacker tape only through its bits below `b η`. -/
theorem RV.readsBelow_of_eval {X : RV M (Ty.arrows τs β)} {A : AdvMachine M τs β}
    (hX : ∀ η ρ, X η ρ = A.eval η ρ.1) {b : ℕ → ℕ} (hA : Machine.ReadsBelow A b) :
    X.ReadsBelow b := fun η ρa ρa' ρh hρ =>
  (hX η (ρa, ρh)).trans ((AdvMachine.eval_eq_of_readsBelow hA hρ).trans (hX η (ρa', ρh)).symm)

/-- An `adv` term depends on the attacker tape only through its bits below a polynomial: the
read bound of the admitted machine that computes it. -/
theorem AdvClass.Adv.readsBelow {C : AdvClass M} {X : RV M (Ty.arrows τs β)} (h : C.Adv X) :
    ∃ p : Polynomial ℕ, X.ReadsBelow fun η => p.eval η :=
  let ⟨_, hA, hX⟩ := h
  let ⟨p, hp⟩ := C.readBound_mem hA
  ⟨p, RV.readsBelow_of_eval hX hp⟩

/-- Every entry of the vector `u` depends on the attacker tape only through its bits below
`b η`. -/
@[expose] def VecRV.ReadsBelow (u : VecRV M τs) (b : ℕ → ℕ) : Prop :=
  ∀ τ (x : ScopedVar τs τ), RV.ReadsBelow (fun η ρ => u η ρ τ x) b

/-- A vector whose entries each read below a polynomial reads below one polynomial, their sum. -/
theorem VecRV.exists_readsBelow : ∀ {τs : List (Ty B)} {u : VecRV M τs},
    (∀ τ (x : ScopedVar τs τ), ∃ p : Polynomial ℕ,
      RV.ReadsBelow (fun η ρ => u η ρ τ x) fun η => p.eval η) →
    ∃ p : Polynomial ℕ, u.ReadsBelow fun η => p.eval η
  | [], _, _ => ⟨0, fun _ x => nomatch x⟩
  | τ :: _, u, h => by
    obtain ⟨p, hp⟩ := h τ .zero
    obtain ⟨q, hq⟩ := VecRV.exists_readsBelow (u := fun η ρ => Vals.tail (u η ρ))
      fun σ x => h σ x.succ
    refine ⟨p + q, fun σ x => ?_⟩
    cases x with
    | zero => exact hp.mono fun η => by simp
    | succ x => exact (hq σ x).mono fun η => by simp

/-! ## Long attacker tapes -/

/-- Long attacker tapes: the length of `ρa` eventually exceeds every polynomial. -/
@[expose] def Model.LongTapes (M : Model D) : Prop :=
  ∀ p : Polynomial ℕ, ∀ᶠ η in Filter.atTop, p.eval η < M.lenA η

/-- Attacker tapes of length at least `2^η` are long: every polynomial is eventually below
`2^η`, since `p(η) · 2^{-η}` is negligible. -/
theorem Model.longTapes_of_two_pow_le (h : ∀ η, 2 ^ η ≤ M.lenA η) : M.LongTapes := by
  intro p
  have hneg := negligible_polynomial_mul (negligible_two_rpow_neg_mul one_pos) p
  filter_upwards [(hneg 0).eventually (gt_mem_nhds zero_lt_one)] with η hη
  rw [pow_zero, one_mul, one_mul, ENNReal.rpow_neg, ENNReal.rpow_natCast, ← div_eq_mul_inv,
    ENNReal.div_lt_iff (Or.inl (pow_ne_zero _ two_ne_zero)) (Or.inl (ENNReal.pow_ne_top
      ENNReal.ofNat_ne_top)), one_mul] at hη
  exact lt_of_lt_of_le (by exact_mod_cast hη) (h η)

/-! ## The read bound of a term -/

/-- The random variable of `t`, at the values `env` of its free variables, depends on the attacker
tape only through its bits below a polynomial: FreshL's side condition on terms (CCS26 Fig. 11,
p. 17). -/
@[expose] def FTerm.ReadsPoly (M : Model D) (C : AdvClass M) {Γ : List (Kind B)} {τ : Ty B}
    (t : FTerm D Γ τ) (env : Env (Kind.Value M) Γ) : Prop :=
  ∃ p : Polynomial ℕ, RV.ReadsBelow (t.denote (fullInterp M C) env) fun η => p.eval η

namespace FTerm

variable {C : AdvClass M} {Γ : List (Kind B)} {env : Env (Kind.Value M) Γ} {a b τ : Ty B}

/-- An honest symbol reads nothing of the attacker tape. -/
theorem readsPoly_fn (f : D.Fn τ) : (FTerm.fn f : FTerm D Γ τ).ReadsPoly M C env :=
  ⟨0, fun _ _ _ _ _ => rfl⟩

/-- `true` reads nothing of the attacker tape. -/
theorem readsPoly_tt : (FTerm.tt : FTerm D Γ .bool).ReadsPoly M C env := ⟨0, fun _ _ _ _ _ => rfl⟩

/-- `false` reads nothing of the attacker tape. -/
theorem readsPoly_ff : (FTerm.ff : FTerm D Γ .bool).ReadsPoly M C env := ⟨0, fun _ _ _ _ _ => rfl⟩

/-- A term computed by an admitted machine reads below the machine's bound. -/
theorem readsPoly_of_adv {τs : List (Ty B)} {β : Ty B} {t : FTerm D Γ (Ty.arrows τs β)}
    (h : C.Adv (t.denote (fullInterp M C) env)) : t.ReadsPoly M C env :=
  h.readsBelow

/-- Application reads below the sum of the bounds of its parts. -/
theorem ReadsPoly.app {f : FTerm D Γ (.arrow a b)} {t : FTerm D Γ a} (hf : f.ReadsPoly M C env)
    (ht : t.ReadsPoly M C env) : (FTerm.app f t).ReadsPoly M C env := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := ht
  refine ⟨p + q, fun η ρa ρa' ρh hρ => ?_⟩
  rw [FTerm.denote_app]
  exact congr ((hp.mono (b' := fun η => (p + q).eval η) fun η => by simp) η ρa ρa' ρh hρ)
    ((hq.mono (b' := fun η => (p + q).eval η) fun η => by simp) η ρa ρa' ρh hρ)

/-- A conditional reads below the sum of the bounds of its parts. -/
theorem ReadsPoly.ite {c : FTerm D Γ .bool} {t t' : FTerm D Γ a} (hc : c.ReadsPoly M C env)
    (ht : t.ReadsPoly M C env) (ht' : t'.ReadsPoly M C env) :
    (FTerm.ite c t t').ReadsPoly M C env := by
  obtain ⟨p, hp⟩ := hc
  obtain ⟨q, hq⟩ := ht
  obtain ⟨r, hr⟩ := ht'
  refine ⟨p + q + r, fun η ρa ρa' ρh hρ => ?_⟩
  rw [FTerm.denote_ite]
  dsimp only
  rw [(hp.mono (b' := fun η => (p + q + r).eval η) fun η => by simp; omega) η ρa ρa' ρh hρ,
    (hq.mono (b' := fun η => (p + q + r).eval η) fun η => by simp; omega) η ρa ρa' ρh hρ,
    (hr.mono (b' := fun η => (p + q + r).eval η) fun η => by simp) η ρa ρa' ρh hρ]

/-- An equality reads below the sum of the bounds of its sides. -/
theorem ReadsPoly.eq {t t' : FTerm D Γ a} (ht : t.ReadsPoly M C env)
    (ht' : t'.ReadsPoly M C env) : (FTerm.eq t t').ReadsPoly M C env := by
  obtain ⟨p, hp⟩ := ht
  obtain ⟨q, hq⟩ := ht'
  refine ⟨p + q, fun η ρa ρa' ρh hρ => ?_⟩
  rw [FTerm.denote_eq]
  dsimp only
  rw [(hp.mono (b' := fun η => (p + q).eval η) fun η => by simp) η ρa ρa' ρh hρ,
    (hq.mono (b' := fun η => (p + q).eval η) fun η => by simp) η ρa ρa' ρh hρ]

/-- A negation reads below the bound of its argument. -/
theorem ReadsPoly.not {φ : FTerm D Γ .bool} (h : φ.ReadsPoly M C env) :
    (FTerm.not φ).ReadsPoly M C env :=
  h.ite readsPoly_ff readsPoly_tt

/-- A name reads the honest tape, and of the attacker tape only what its index reads. -/
theorem ReadsPoly.name (n : D.Name a b) {i : FTerm D Γ a} (hi : i.ReadsPoly M C env) :
    (FTerm.name n i).ReadsPoly M C env := by
  obtain ⟨p, hp⟩ := hi
  refine ⟨p, fun η ρa ρa' ρh hρ => ?_⟩
  rw [FTerm.denote_name]
  dsimp only
  rw [hp η ρa ρa' ρh hρ]

end FTerm

/-- Every term of the vector `u` reads the attacker tape below a polynomial. -/
@[expose] def Vec.ReadsPoly (M : Model D) (C : AdvClass M) {Γ : List (Kind B)}
    (u : Vec D Γ τs) (env : Env (Kind.Value M) Γ) : Prop :=
  ∀ τ (x : ScopedVar τs τ), (u τ x).ReadsPoly M C env

/-- A vector of terms that each read below a polynomial reads below one polynomial. -/
theorem Vec.ReadsPoly.exists_readsBelow {C : AdvClass M} {Γ : List (Kind B)} {u : Vec D Γ τs}
    {env : Env (Kind.Value M) Γ} (h : u.ReadsPoly M C env) :
    ∃ p : Polynomial ℕ, (u.rv M C env).ReadsBelow fun η => p.eval η :=
  VecRV.exists_readsBelow h

/-- A term that `Θ` proves adversarial reads the attacker tape below a polynomial in every
admitted model of `Θ`. The caption of CCS26 Fig. 11 asks this of every declared variable that is
not a name, which covers free variables and attacker symbols. -/
theorem Valid.readsPoly_of_adv {R : Model D → Prop} {C : ∀ M : Model D, AdvClass M}
    {Γ : List (Kind B)} {Θ : List (Form D Γ)} {β : Ty B} {t : FTerm D Γ (Ty.arrows τs β)}
    {ha : Ty.AdvOrder τs β} (h : Valid R C Θ (.adv t ha)) {M : Model D} (hl : M.RespectsLabels)
    (hR : R M) {env : Env (Kind.Value M) Γ} (hΘ : ∀ θ ∈ Θ, θ.Holds M (C M) env) :
    t.ReadsPoly M (C M) env :=
  FTerm.readsPoly_of_adv (Form.holds_adv.1 (h M hl hR env hΘ))

end Interop.Squirrel
