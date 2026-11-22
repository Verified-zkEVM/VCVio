/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Squirrel.Test.SecrecyExamples

/-!
# FreshL in a model with long attacker tapes

The declaration is `SecrecyExamples.decl`: a base type `msg` labelled `large`, names
`k, m, n : bool → msg`, the honest index `idx`, the honest symbol `h` and an attacker symbol `a`
of type `msg`. `longModel` is `SecrecyExamples.model` with an attacker tape of `2^η` bits, of
which the attacker symbol reads the first `η` as a message. It has long tapes
(`Model.longTapes_of_two_pow_le`), and messages read `η` bits of the honest tape, a polynomial.

* `freshLDerivation`: from `adv(h)` and `adv(a)`, derive `h(h(a)), m ⊬ n`. FreshR gives `a ⊬ n`,
  `▷` from `adv(h)` twice and Trans give `a ▷ h(h(a))`, WeakL gives `h(h(a)) ⊬ n`, and FreshL adds
  the fresh name `m`. Its freshness premises hold by `decide`, and its read-bound premise is
  discharged structurally: `h` and the names read nothing of the attacker tape, and `a` has the
  bound of the machine that `adv(a)` provides (`FTerm.readsPoly_of_adv`).
* `valid_freshLWorked`: in `longModel` against all machines (`AdvClass.all`), both hypotheses
  hold (`SecrecyExamples.valid_advH`, `valid_advA`, where `a` is computed by the sampler of
  messages), so every hypothesis of FreshL holds jointly there and the conclusion is valid.
* `not_valid_freshL_n`: adding `n` itself in place of the fresh name `m` gives
  `h(h(a)), n ⊬ n`, which fails in `longModel`: the conclusion depends on freshness, and `decide`
  rejects the freshness premise FreshL would need for it (`not_avoidsNames_n`).

## References

* [CCS26] Hérouard, Jacomme, Koutsos, Lallemand, *Secrecy in Squirrel and the Post-Compromise
  Security of a Ratchet*, CCS 2026: Fig. 11 and App. C.2.
-/

public section

namespace Interop.Squirrel.FreshLExamples

open IPFunctor IPFunctor.ScopedSignature SecrecyExamples

/-- `SecrecyExamples.model` with an attacker tape of `2^η` bits; the attacker symbol reads its
first `η` bits as a message. -/
@[expose] noncomputable def longModel : Model decl where
  lenA η := 2 ^ η
  carrier := carrier
  nonempty := carrier_nonempty
  coinLen := model.coinLen
  sample := model.sample
  finite_index := model.finite_index
  fn := model.fn
  att η _ ρa :=
    ⟨List.ofFn fun j : Fin η => if h : j.1 < 2 ^ η then ρa ⟨j.1, h⟩ else false, List.length_ofFn⟩

theorem longModel_isLarge : longModel.IsLarge msg := model_isLarge

theorem longModel_respectsLabels : longModel.RespectsLabels := fun _ _ h => by
  subst h
  exact longModel_isLarge

theorem longModel_longTapes : longModel.LongTapes := Model.longTapes_of_two_pow_le fun _ => le_rfl

/-- Messages read `η` bits of the honest tape. -/
theorem longModel_polyCoins : longModel.PolyCoins msg :=
  ⟨Polynomial.X, fun η => (Polynomial.eval_X (x := η)).ge⟩

/-! ## The worked derivation -/

/-- The attacker symbol. -/
@[expose] def aT : FTerm decl [] msg := FTerm.att (D := decl) ()

/-- The hypothesis `adv(a)`. -/
@[expose] def advA : Form decl [] := Form.adv (τs := []) aT

/-- The models over which the derivation uses FreshL: long attacker tapes and polynomial bit
blocks for messages. -/
abbrev LongR (M : Model decl) : Prop := M.LongTapes ∧ M.PolyCoins msg

/-- The premise of FreshL in the worked derivation, from `adv(h)`: FreshR gives `a ⊬ n`; `▷` from
`adv(h)` gives `a ▷ h(a)` and `h(a) ▷ h(h(a))`; Trans gives `a ▷ h(h(a))`; WeakL gives
`h(h(a)) ⊬ n`. -/
@[expose] def workedPremise :
    Derivation decl (fun _ => False) (fun _ => False) LongR (Γ := []) [advH, advA]
      (.nonDed (one (hT (hT aT))) (nm Name.n)) :=
  .nonDedWeakL (.nonDedFreshR (one aT) Name.n Fn.idx (by decide) rfl (by decide))
    (.dedTrans (v := hT aT) (.dedApps (by decide) (.ax List.mem_cons_self))
      (.dedApps (by decide) (.ax List.mem_cons_self)))

/-- FreshL's read-bound premise in the worked derivation: `h` and the names read nothing of the
attacker tape, and `a` reads below the bound of the machine that `adv(a)` provides. -/
theorem worked_readsPoly (M : Model decl) (C : AdvClass M) (env : Env (Kind.Value M) [])
    (hΘ : ∀ θ ∈ [advH, advA], θ.Holds M C env) :
    Vec.ReadsPoly M C (one (hT (hT aT))) env ∧ (nm Name.n).ReadsPoly M C env := by
  have ha : aT.ReadsPoly M C env := FTerm.readsPoly_of_adv (τs := [])
    (Form.holds_adv.1 (hΘ advA (List.mem_cons_of_mem _ List.mem_cons_self)))
  refine ⟨fun τ x => ?_, (FTerm.readsPoly_fn _).name _⟩
  cases x with
  | zero => exact (FTerm.readsPoly_fn _).app ((FTerm.readsPoly_fn _).app ha)
  | succ x => exact nomatch x

/-- From `adv(h)` and `adv(a)`, derive `h(h(a)), m ⊬ n`: FreshL adds the fresh name `m` to
`workedPremise`. -/
@[expose] def freshLDerivation :
    Derivation decl (fun _ => False) (fun _ => False) LongR (Γ := []) [advH, advA]
      (.nonDed (Vec.snoc (one (hT (hT aT))) (nm Name.m)) (nm Name.n)) :=
  .nonDedFreshL (u := one (hT (hT aT))) (v := nm Name.n) (of_decide_eq_true rfl) Name.m Fn.idx
    (fun _ h => h) (fun M _ _ C env hΘ => worked_readsPoly M C env hΘ) (by decide) (by decide)
    workedPremise

/-- The worked derivation is valid over every restriction to models with long tapes and
polynomial bit blocks for messages, against every class. -/
theorem freshLDerivation_sound (R : Model decl → Prop) (C : ∀ M : Model decl, AdvClass M)
    (hR : ∀ M, R M → LongR M) :
    Valid R C [advH, advA] (.nonDed (Vec.snoc (one (hT (hT aT))) (nm Name.m)) (nm Name.n)) :=
  freshLDerivation.sound R C (fun _ h => h.elim) (fun _ h => h.elim) hR

/-- In `longModel`, against all machines, the hypothesis `adv(a)` holds: the sampler of messages,
run on the attacker tape, computes the attacker symbol. -/
theorem valid_advA : Valid (· = longModel) (fun M => AdvClass.all M) (Γ := []) [] advA := by
  rintro M - rfl env -
  refine Form.holds_adv.2 ⟨Machine.sampler msg (by decide),
    (AdvClass.all longModel).sampler_mem _ longModel_polyCoins, fun η ρ => ?_⟩
  refine Eq.trans ?_ (Machine.run_sampler (M := longModel) msg (by decide) Env.empty).symm
  refine Subtype.ext (congrArg List.ofFn (funext fun j => ?_))
  simp [Model.coinAt, Model.readBit, longModel]

/-- **Satisfiability.** In `longModel`, which respects the labels and has long tapes and
polynomial bit blocks for messages, both hypotheses of the worked derivation hold against all
machines; so do FreshL's read-bound and freshness conditions, and its conclusion
`h(h(a)), m ⊬ n` holds there. -/
theorem valid_freshLWorked :
    Valid (· = longModel) (fun M => AdvClass.all M) (Γ := []) []
      (.nonDed (Vec.snoc (one (hT (hT aT))) (nm Name.m)) (nm Name.n)) :=
  valid_advH.cut ((valid_advA.weaken (List.nil_subset _)).cut
    ((freshLDerivation_sound (· = longModel) _ fun _ h =>
      h ▸ ⟨longModel_longTapes, longModel_polyCoins⟩).weaken (List.Perm.swap advA advH []).subset))

/-- The name `n` is not fresh in itself: `decide` rejects FreshL's freshness premise for adding
`n` to the left of `⊬ n`. -/
theorem not_avoidsNames_n : ¬ (nm Name.n).AvoidsNames (· = ⟨_, _, Name.n⟩) := by decide

/-- The machine returning the second of two message inputs. -/
@[expose] noncomputable def sndMachine (M : Model decl) : AdvMachine M ([msg] ++ [msg]) msg :=
  Machine.input (.succ .zero) (Ty.isGround_base ())

/-- **The conclusion depends on freshness.** With `n` in place of the fresh name `m`,
`h(h(a)), n ⊬ n` fails in `longModel`: the machine returning its second input computes `n`. -/
theorem not_valid_freshL_n :
    ¬ Valid (· = longModel) (fun M => AdvClass.all M) (Γ := []) []
      (.nonDed (Vec.snoc (one (hT (hT aT))) (nm Name.n)) (nm Name.n)) := fun h =>
  not_nonDed_of_forall_eq (sndMachine longModel)
    ((AdvClass.all _).input_mem _ _)
    (fun _ _ => (AdvMachine.appVals_eval _ _).trans (Machine.run_input _ _ _))
    (Form.holds_nonDed.1 (h longModel longModel_respectsLabels rfl Env.empty (by simp)))

end Interop.Squirrel.FreshLExamples
