/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Squirrel.Derivation
import VCVio.OracleComp.EvalDist.Measure
import VCVio.OracleComp.Constructions.SampleableType.Measure
import Mathlib.Data.Set.Finite.List
import Mathlib.Data.Fintype.BigOperators

/-!
# Checks of the secrecy rules

The declaration has one base type `msg`, labelled `large`, three names `k`, `m`, `n : bool → msg`,
a Boolean name `b : bool → bool`, the honest index `idx : bool`, an honest symbol `h : msg → msg`
and an attacker symbol of type `msg`. In `model`, `msg` at `η` is the bitstrings of length `η`,
every name draws a uniform value of its type, `idx` is `false` and `h` is the identity. Then `msg`
is large with `c = 1` (`model_isLarge`), and `model` respects the labels. The attacker tape of
`model` is empty; `Interop.Squirrel.FreshLExamples` gives the same declaration a model with long
tapes.

* `workedDerivation`: from the hypothesis `adv(h)`, derive `h(h(k)) ⊬ n`, by FreshR (`k ⊬ n`),
  `▷` from `adv` twice (`k ▷ h(k)`, `h(k) ▷ h(h(k))`), Trans and WeakL. Its freshness side
  condition, that `k` does not use `n`, holds by `decide`. `workedDerivation_sound` is its
  validity from `Derivation.sound`, and `valid_worked` its conclusion in `model` against all
  machines, where the hypothesis holds (`valid_advH`).
* `nonDed_not_trans`: `⊬` is not transitive (CCS26 §3.2, p. 6): `n ⊬ m` and `m ⊬ n` hold, and
  `n ⊬ n` fails. The conclusion of the worked derivation is not trivial: `h(h(n)) ⊬ n`, the same
  conclusion with `k` replaced by `n`, fails (`not_valid_nonDed_hhn_n`), and `decide` rejects the
  freshness condition FreshR would need for it (`not_avoidsNames_n_n`).
* `freshL_needs_freshness`: FreshL without its side condition is unsound: `⊬ n`, with nothing on
  the left, holds by FreshR, and `n ⊬ n`, which adds `n` on the left although `n` is not fresh in
  the right side, fails.
* `freshR_needs_large`: FreshR without the label `large` is unsound: the Boolean name `b` is fresh
  in the empty vector, and `⊬ b` fails, since the constant `true` guesses `b` with probability one
  half.

The other rules of CCS26 Fig. 3 are used once each: Neg1 (`valid_neg1`: `¬ (k ▷ n)`), Neg2
(`valid_neg2`: `¬ (k ⊬ h(k))`), Ineq (`valid_ineq`: `[n ≠ h(k)]`), Rw-Equiv (`valid_rwEquiv`:
`k ⊬ h(h(n))` from `k, h(h(n)) ∼ k, n`, which holds in `model` since `h` is the identity) and
WeakR (`valid_weakR`: `k ⊬ h(n)` from `k ⊬ h(h(n))` and `h(n) ▷ h(h(n))`). Three checks show
premises needed: `neg1_needs_nonDed` (`¬ (k ▷ h(k))` fails), `ineq_needs_nonDed` (`[h(k) ≠ h(k)]`
fails, while `k ▷ h(k)` holds) and `rwEquiv_needs_equiv` (`k ⊬ n` holds and `k ⊬ k` fails, so
neither Rw-Equiv nor WeakR passes from one to the other without its second premise).

The deductions and local reasoning: `valid_ded_k_app_hk` deduces `h k` from `k` by an honest
symbol, an entry and an application, in every model against every class, with no `adv`
hypothesis; `rewriteDerivation` deduces `k` from `h(h(k))` in `model`, by the entry, local validity
twice, modus ponens under `[·]` and rewriting, and `valid_not_nonDed_hhk_k` draws Neg2 from it,
while `h(h(k)) ⊬ n` holds (`valid_worked`).

## References

* [CCS26] Hérouard, Jacomme, Koutsos, Lallemand, *Secrecy in Squirrel and the Post-Compromise
  Security of a Ratchet*, CCS 2026: §3.1, §3.2, Fig. 3 and Fig. 11.
-/

public section

namespace Interop.Squirrel.SecrecyExamples

open IPFunctor IPFunctor.ScopedSignature

/-- The base type of messages. -/
abbrev msg : Ty Unit := .base ()

/-- Three names of messages and a Boolean name, each indexed by a Boolean. -/
inductive Name : Ty Unit → Ty Unit → Type where
  /-- A message name. -/
  | k : Name .bool msg
  /-- A message name. -/
  | m : Name .bool msg
  /-- A message name. -/
  | n : Name .bool msg
  /-- A Boolean name. -/
  | b : Name .bool .bool

/-- The honest symbols: an index and a function on messages. -/
inductive Fn : Ty Unit → Type where
  /-- The index at which names are read. -/
  | idx : Fn .bool
  /-- A function on messages. -/
  | h : Fn (.arrow msg msg)

-- The decision procedure is exposed, so that `decide` evaluates it in other modules.
@[expose] public section

deriving instance DecidableEq for Name

end

/-- `msg` is labelled `large` and has no other label; there is one attacker symbol, of type
`msg`. -/
@[expose, reducible] def decl : Decl Unit where
  labels _ l := l = .large
  Name := Name
  nameDom_finite := fun n => match n with | .k | .m | .n | .b => nofun
  finite_names := Finite.of_injective (β := Bool × Bool)
    (fun n => match n with
      | ⟨_, _, .k⟩ => (false, false) | ⟨_, _, .m⟩ => (false, true)
      | ⟨_, _, .n⟩ => (true, false) | ⟨_, _, .b⟩ => (true, true))
    fun | ⟨_, _, .k⟩, ⟨_, _, .k⟩, _ => rfl | ⟨_, _, .m⟩, ⟨_, _, .m⟩, _ => rfl
        | ⟨_, _, .n⟩, ⟨_, _, .n⟩, _ => rfl | ⟨_, _, .b⟩, ⟨_, _, .b⟩, _ => rfl
  Fn := Fn
  Att := Unit
  attTy _ := msg

/-- Messages at `η` are the bitstrings of length `η`. -/
@[expose] def carrier : Unit → ℕ → Set (List Bool) := fun _ η => {l | l.length = η}

theorem carrier_finite (b : Unit) (η : ℕ) : (carrier b η).Finite := List.finite_length_eq Bool η

theorem carrier_nonempty (b : Unit) (η : ℕ) : (carrier b η).Nonempty :=
  ⟨List.replicate η false, List.length_replicate⟩

/-- A name of type `msg` reads `η` bits and returns them as a message, and a Boolean name reads
one bit; so every name draws a uniform value of its type. `idx` is `false` and `h` the identity.
The attacker tape is empty, and the attacker symbol is the message of `η` zeros. -/
@[expose] noncomputable def model : Model decl where
  lenA _ := 0
  carrier := carrier
  nonempty := carrier_nonempty
  coinLen η τ := match τ with
    | .base _ => η
    | .bool => 1
    | .arrow _ _ => 0
  sample η τ := match τ with
    | .base _ => fun c => ⟨List.ofFn c, List.length_ofFn⟩
    | .bool => fun c => c 0
    | .arrow _ _ => fun _ => Classical.choice ((Ty.arrow _ _).nonempty_value carrier_nonempty η)
  finite_index η {a _} _ := a.finite_value_of_finite carrier_finite η
  fn _ {τ} f := match τ, f with
    | _, .idx => false
    | _, .h => id
  att η _ _ := ⟨List.replicate η false, List.length_replicate⟩

/-- `msg` is large in `model`, with `c = 1`: each message is drawn with probability `2^{-η}`. -/
theorem model_isLarge : model.IsLarge msg := by
  refine ⟨1, one_pos, fun η y => le_of_eq ?_⟩
  obtain ⟨l, hl⟩ := y
  change l.length = η at hl
  subst hl
  have hc : ∀ c : model.Coin l.length msg,
      (model.sample l.length msg c = ⟨l, rfl⟩) ↔ c = l.get := fun c => by
    change (⟨List.ofFn c, _⟩ : carrier () l.length) = ⟨l, rfl⟩ ↔ _
    refine ⟨fun h => List.ofFn_inj.1 ((congrArg Subtype.val h).trans (List.ofFn_get l).symm),
      fun h => ?_⟩
    subst h
    exact Subtype.ext (List.ofFn_get l)
  rw [prEvent_congr _ _ _ hc]
  refine (SampleableType.prEvent_uniformSample_eq_singleton_natCard (α := model.Coin l.length msg)
    l.get).trans ?_
  rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool, one_mul,
    ENNReal.rpow_neg, ENNReal.rpow_natCast, Nat.cast_pow, Nat.cast_ofNat]
  rfl

theorem model_respectsLabels : model.RespectsLabels := fun _ _ h => by
  subst h
  exact model_isLarge

/-! ## Terms -/

/-- A message name at the index `idx`. -/
@[expose] def nm (x : Name .bool msg) : FTerm decl [] msg :=
  FTerm.name (D := decl) x (FTerm.fn (D := decl) Fn.idx)

/-- The Boolean name at the index `idx`. -/
@[expose] def bT : FTerm decl [] .bool :=
  FTerm.name (D := decl) Name.b (FTerm.fn (D := decl) Fn.idx)

/-- The honest symbol `h`, as a function of a tuple of one message. -/
@[expose] def hFn : FTerm decl [] (Ty.arrows [msg] msg) := FTerm.fn (D := decl) Fn.h

/-- `h` applied to a message. -/
@[expose] def hT (t : FTerm decl [] msg) : FTerm decl [] msg :=
  FTerm.apps hFn (Env.cons t Env.empty)

/-- The vector of one term. -/
abbrev one {τ : Ty Unit} (t : FTerm decl [] τ) : Vec decl [] [τ] := Env.cons t Env.empty

/-- The hypothesis `adv(h)`. -/
@[expose] def advH : Form decl [] := .adv hFn

/-- A message name other than `x` does not use `x`: `decide` checks each pair. -/
theorem one_nm_avoidsNames {x y : Name .bool msg} (hxy : x ≠ y) :
    (one (nm y)).AvoidsNames (· = ⟨_, _, x⟩) := by
  cases x <;> cases y <;> first | exact absurd rfl hxy | decide

/-- A message name uses itself: `decide` rejects FreshR's freshness condition for `n ⊬ n`. -/
theorem not_avoidsNames_n_n : ¬ (one (nm Name.n)).AvoidsNames (· = ⟨_, _, Name.n⟩) := by
  decide

/-! ## The worked derivation -/

/-- From `adv(h)`, derive `h(h(k)) ⊬ n`: FreshR gives `k ⊬ n`; `▷` from `adv` gives `k ▷ h(k)` and
`h(k) ▷ h(h(k))`; Trans gives `k ▷ h(h(k))`; WeakL gives `h(h(k)) ⊬ n`. -/
@[expose] def workedDerivation {R₀ : Model decl → Prop} :
    Derivation decl (fun _ => False) R₀ (Γ := []) [advH]
      (.nonDed (one (hT (hT (nm Name.k)))) (nm Name.n)) :=
  .nonDedWeakL (.nonDedFreshR (one (nm Name.k)) Name.n Fn.idx (by decide) rfl (by decide))
    (.dedTrans (v := hT (nm Name.k)) (.dedApps (by decide) (.ax List.mem_cons_self))
      (.dedApps (by decide) (.ax List.mem_cons_self)))

/-- The worked derivation is valid in every model restriction, against every class. -/
theorem workedDerivation_sound (R : Model decl → Prop) (C : ∀ M : Model decl, AdvClass M) :
    Valid R C [advH] (.nonDed (one (hT (hT (nm Name.k)))) (nm Name.n)) :=
  (workedDerivation (R₀ := R)).sound R C (fun _ h => h.elim) fun _ h => h

/-- The machine applying `h` to its input: FA-App of the input to the input, answered by the
honest symbol. -/
@[expose] noncomputable def hMachine (M : Model decl) : AdvMachine M [msg] msg :=
  ((Machine.input .zero (Ty.isGround_base ())).app (Ty.isGround_base ())).fn Fn.h

theorem hMachine_mem (M : Model decl) : (AdvClass.all M).mem (hMachine M) :=
  (AdvClass.all M).fn_mem _ ((AdvClass.all M).app_mem _ ((AdvClass.all M).input_mem _ _))

/-- In every model, against all machines, the hypothesis `adv(h)` holds: `hMachine` computes
`h`. -/
theorem valid_advH {R : Model decl → Prop} :
    Valid R (fun M => AdvClass.all M) (Γ := []) [] advH := by
  rintro M - - env -
  refine Form.holds_adv.2 ⟨hMachine M, hMachine_mem M, fun η ρ => funext fun x => ?_⟩
  change M.fn η Fn.h x = (hMachine M).run η ρ.1 (Env.cons x Env.empty)
  rw [hMachine]
  refine Eq.symm ((Machine.run_fn _ _ _).trans ((Machine.run_app _ _ _).trans ?_))
  exact Machine.run_input _ _ _

/-- **Satisfiability.** The hypothesis of the worked derivation holds in `model`, which respects
the labels, so its conclusion `h(h(k)) ⊬ n` holds there against all machines. -/
theorem valid_worked :
    Valid (· = model) (fun M => AdvClass.all M) (Γ := []) []
      (.nonDed (one (hT (hT (nm Name.k)))) (nm Name.n)) :=
  valid_advH.cut (workedDerivation_sound _ _)

/-! ## Countermodels -/

/-- An admitted attacker machine that computes `v` from `u` everywhere refutes `u ⊬ v` against all
machines. -/
theorem not_nonDed_of_forall_eq {M : Model decl} {τs : List (Ty Unit)} {β : Ty Unit}
    {u : VecRV M τs} {v : RV M β} (g : AdvMachine M τs β) (hg : (AdvClass.all M).mem g)
    (h : ∀ η ρ, Ty.appVals (g.eval η ρ.1) (u η ρ) = v η ρ) : ¬ (AdvClass.all M).NonDed u v :=
  fun hn => not_negligible_one (negligible_of_le (fun η => le_of_eq
    ((prEvent_congr _ _ (fun _ => True) fun ρ => iff_true_intro (h η ρ)).trans
      (OracleComp.prEvent_true_eq_one _)).symm) (hn g hg))

/-- The machine returning its message input. -/
@[expose] noncomputable def idMachine (M : Model decl) : AdvMachine M [msg] msg :=
  Machine.input .zero (Ty.isGround_base ())

theorem idMachine_mem (M : Model decl) : (AdvClass.all M).mem (idMachine M) :=
  (AdvClass.all M).input_mem _ _

/-- `n ⊬ n` fails in `model`: the identity computes `n` from `n`. -/
theorem not_valid_nonDed_n_n :
    ¬ Valid (· = model) (fun M => AdvClass.all M) (Γ := []) []
      (.nonDed (one (nm Name.n)) (nm Name.n)) :=
  fun h => not_nonDed_of_forall_eq (idMachine model) (idMachine_mem model)
    (fun _ _ => (AdvMachine.appVals_eval _ _).trans (Machine.run_input _ _ _))
    (Form.holds_nonDed.1 (h model model_respectsLabels rfl Env.empty (by simp)))

/-- `h(h(n)) ⊬ n` fails in `model`, where `h` is the identity: the conclusion of the worked
derivation needs `n` fresh. -/
theorem not_valid_nonDed_hhn_n :
    ¬ Valid (· = model) (fun M => AdvClass.all M) (Γ := []) []
      (.nonDed (one (hT (hT (nm Name.n)))) (nm Name.n)) := fun h => by
  have hn := Form.holds_nonDed.1 (h model model_respectsLabels rfl Env.empty (by simp))
  exact not_nonDed_of_forall_eq (idMachine model) (idMachine_mem model)
    (fun _ _ => (AdvMachine.appVals_eval _ _).trans (Machine.run_input _ _ _)) hn

/-- `y ⊬ x` for distinct message names, by FreshR, in every model against every class. -/
theorem valid_nonDed_nm {R : Model decl → Prop} {C : ∀ M : Model decl, AdvClass M}
    {x y : Name .bool msg} (hxy : x ≠ y) : Valid R C (Γ := []) [] (.nonDed (one (nm y)) (nm x)) :=
  Valid.nonDed_freshR (D := decl) x Fn.idx rfl (one_nm_avoidsNames hxy)

/-- **`⊬` is not transitive** (CCS26 §3.2, p. 6): `n ⊬ m` and `m ⊬ n` hold in `model` against
all machines, and `n ⊬ n` fails. -/
theorem nonDed_not_trans :
    Valid (· = model) (fun M => AdvClass.all M) (Γ := []) []
        (.nonDed (one (nm Name.n)) (nm Name.m)) ∧
      Valid (· = model) (fun M => AdvClass.all M) (Γ := []) []
        (.nonDed (one (nm Name.m)) (nm Name.n)) ∧
      ¬ Valid (· = model) (fun M => AdvClass.all M) (Γ := []) []
        (.nonDed (one (nm Name.n)) (nm Name.n)) :=
  ⟨valid_nonDed_nm nofun, valid_nonDed_nm nofun, not_valid_nonDed_n_n⟩

/-- **FreshL needs freshness.** `⊬ n`, with nothing on the left, holds by FreshR; adding `n`
itself on the left, which is not fresh in the right side, gives `n ⊬ n`, which fails. -/
theorem freshL_needs_freshness :
    Valid (· = model) (fun M => AdvClass.all M) (Γ := []) [] (.nonDed Env.empty (nm Name.n)) ∧
      ¬ Valid (· = model) (fun M => AdvClass.all M) (Γ := []) []
        (.nonDed (one (nm Name.n)) (nm Name.n)) :=
  ⟨Valid.nonDed_freshR (D := decl) Name.n Fn.idx rfl (by decide), not_valid_nonDed_n_n⟩

/-- The Boolean name is `true` with probability one half. -/
theorem prEvent_bT_eq_true (η : ℕ) :
    Pr{let ρ ← $ᵗ (model.Tape η)}[true = model.nameAt (D := decl) Name.b Fn.idx η ρ] = 2⁻¹ := by
  refine (prEvent_nameAt (M := model) Name.b Fn.idx η fun v => true = v).trans ?_
  have hc : ∀ c : model.Coin η .bool, true = model.sample η .bool c ↔ c = fun _ => true :=
    fun c => ⟨fun h => funext fun i => (Subsingleton.elim (α := Fin 1) i 0) ▸ h.symm,
      fun h => h ▸ rfl⟩
  refine ((prEvent_congr _ _ _ hc).trans
    (SampleableType.prEvent_uniformSample_eq_singleton_natCard (α := model.Coin η .bool)
      fun _ => true)).trans ?_
  change ((Nat.card (Fin 1 → Bool) : ℕ) : ENNReal)⁻¹ = 2⁻¹
  rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, pow_one,
    Nat.cast_ofNat]

/-- **FreshR needs `large`.** The Boolean name `b` is fresh in the empty vector, and `⊬ b` fails
in `model` against all machines: the constant `true` guesses `b` with probability one half. -/
theorem freshR_needs_large :
    ¬ Valid (· = model) (fun M => AdvClass.all M) (Γ := []) [] (.nonDed Env.empty bT) := fun h => by
  have hn := Form.holds_nonDed.1 (h model model_respectsLabels rfl Env.empty (by simp))
    (Machine.const true) ((AdvClass.all _).const_mem _)
  refine not_negligible_one (negligible_of_le (fun η => ?_)
    (negligible_const_mul hn (c := 2) ENNReal.ofNat_ne_top))
  change 1 ≤ 2 * Pr{let ρ ← $ᵗ (model.Tape η)}[true = model.nameAt (D := decl) Name.b Fn.idx η ρ]
  rw [prEvent_bT_eq_true, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top]

/-! ## Uses of Neg1, Neg2, Ineq, Rw-Equiv and WeakR -/

/-- `k ▷ h(k)` in every model against all machines: `▷` from `adv(h)`. -/
theorem valid_ded_k_hk {R : Model decl → Prop} :
    Valid R (fun M => AdvClass.all M) (Γ := []) [] (.ded (one (nm Name.k)) (hT (nm Name.k))) :=
  Valid.ded_apps (u := one (nm Name.k)) valid_advH

/-- **Neg1**: `¬ (k ▷ n)`, from `k ⊬ n`. -/
theorem valid_neg1 {R : Model decl → Prop} {C : ∀ M : Model decl, AdvClass M} :
    Valid R C (Γ := []) [] (.not (.ded (one (nm Name.k)) (nm Name.n))) :=
  Valid.not_ded (valid_nonDed_nm (x := Name.n) (y := Name.k) nofun)

/-- **Neg1 needs `⊬`.** `¬ (k ▷ h(k))` fails in `model`: `k ▷ h(k)` holds. -/
theorem neg1_needs_nonDed :
    ¬ Valid (· = model) (fun M => AdvClass.all M) (Γ := []) []
      (.not (.ded (one (nm Name.k)) (hT (nm Name.k)))) := fun h =>
  Form.holds_not.1 (h model model_respectsLabels rfl Env.empty (by simp))
    (valid_ded_k_hk model model_respectsLabels rfl Env.empty (by simp))

/-- **Neg2**: `¬ (k ⊬ h(k))`, from `k ▷ h(k)`. -/
theorem valid_neg2 {R : Model decl → Prop} :
    Valid R (fun M => AdvClass.all M) (Γ := []) []
      (.not (.nonDed (one (nm Name.k)) (hT (nm Name.k)))) :=
  Valid.not_nonDed valid_ded_k_hk

/-- **Ineq**: `[n ≠ h(k)]`, from `k ⊬ n` and `k ▷ h(k)`. -/
theorem valid_ineq {R : Model decl → Prop} :
    Valid R (fun M => AdvClass.all M) (Γ := []) []
      (.box (FTerm.not (FTerm.eq (nm Name.n) (hT (nm Name.k))))) :=
  Valid.box_not_eq (valid_nonDed_nm (x := Name.n) (y := Name.k) nofun) valid_ded_k_hk

/-- **Ineq needs `⊬`.** `[h(k) ≠ h(k)]`, Ineq's conclusion from `k ⊬ h(k)` and `k ▷ h(k)`, fails in
`model`: the second premise holds (`valid_ded_k_hk`), and the first is what Neg2 refutes. -/
theorem ineq_needs_nonDed :
    ¬ Valid (· = model) (fun M => AdvClass.all M) (Γ := []) []
      (.box (FTerm.not (FTerm.eq (hT (nm Name.k)) (hT (nm Name.k))))) := fun h => by
  have hb := Form.holds_box.1 (h model model_respectsLabels rfl Env.empty (by simp))
  refine not_negligible_one (negligible_of_le (fun η => le_of_eq ?_) hb)
  refine ((prEvent_congr _ _ (fun _ => True) fun ρ => iff_true_intro ?_).trans
    (OracleComp.prEvent_true_eq_one _)).symm
  exact (FTerm.denote_not_eq_eq_false_iff _ _ η ρ).2 rfl

/-- `k, h(h(n)) ∼ k, n` in `model`, where `h` is the identity: the two vectors are the same random
variables. -/
theorem valid_equiv_k_hhn :
    Valid (· = model) (fun M => AdvClass.all M) (Γ := []) []
      (.equiv (Vec.snoc (one (nm Name.k)) (hT (hT (nm Name.n))))
        (Vec.snoc (one (nm Name.k)) (nm Name.n))) := by
  rintro M - rfl env -
  refine Form.holds_equiv.2 ?_
  rw [Vec.rv_snoc, Vec.rv_snoc]
  exact AdvClass.Indist.refl _

/-- **Rw-Equiv**: `k ⊬ h(h(n))` in `model`, from `k ⊬ n` and `k, h(h(n)) ∼ k, n`. -/
theorem valid_rwEquiv :
    Valid (· = model) (fun M => AdvClass.all M) (Γ := []) []
      (.nonDed (one (nm Name.k)) (hT (hT (nm Name.n)))) :=
  Valid.nonDed_rwEquiv (Ty.isGround_base ()) (valid_nonDed_nm (x := Name.n) (y := Name.k) nofun)
    valid_equiv_k_hhn

/-- **WeakR**: `k ⊬ h(n)` in `model`, from `k ⊬ h(h(n))` and `h(n) ▷ h(h(n))`. -/
theorem valid_weakR :
    Valid (· = model) (fun M => AdvClass.all M) (Γ := []) []
      (.nonDed (one (nm Name.k)) (hT (nm Name.n))) :=
  Valid.nonDed_weakR valid_rwEquiv
    (Valid.ded_apps (u := one (hT (nm Name.n))) (ho := of_decide_eq_true rfl) valid_advH)

/-- **Rw-Equiv and WeakR need their second premise.** `k ⊬ n` holds in `model`, and `k ⊬ k` fails:
Rw-Equiv from `k ⊬ n` to `k ⊬ k` would need `k, k ∼ k, n`, and WeakR would need `k ▷ n`. -/
theorem rwEquiv_needs_equiv :
    Valid (· = model) (fun M => AdvClass.all M) (Γ := []) []
        (.nonDed (one (nm Name.k)) (nm Name.n)) ∧
      ¬ Valid (· = model) (fun M => AdvClass.all M) (Γ := []) []
        (.nonDed (one (nm Name.k)) (nm Name.k)) :=
  ⟨valid_nonDed_nm nofun, fun h => not_nonDed_of_forall_eq (idMachine model) (idMachine_mem model)
    (fun _ _ => (AdvMachine.appVals_eval _ _).trans (Machine.run_input _ _ _))
    (Form.holds_nonDed.1 (h model model_respectsLabels rfl Env.empty (by simp)))⟩

/-! ## Deductions and local reasoning -/

/-- `k ▷ h k` by the deductions of an honest symbol, an entry and an application, in every model
against every class: deductions need no `adv` hypothesis. -/
theorem valid_ded_k_app_hk {R : Model decl → Prop} {C : ∀ M : Model decl, AdvClass M} :
    Valid R C (Γ := []) []
      (.ded (one (nm Name.k)) (FTerm.app (FTerm.fn (D := decl) Fn.h) (nm Name.k))) := by
  have hk := Valid.ded_input (R := R) (C := C) (Θ := []) (u := one (nm Name.k))
    (ho := of_decide_eq_true rfl) (ScopedVar.zero : ScopedVar [msg] msg)
  have hf := Valid.ded_fn (R := R) (C := C) (Θ := []) (u := one (nm Name.k))
    (ho := (of_decide_eq_true rfl : Ty.SecrecyOrder [msg] (.arrow msg msg)))
    (Fn.h : decl.Fn (.arrow msg msg))
  exact Valid.ded_app hf hk

/-- In `model`, where `h` is the identity, `h(h(k)) = h(k)` at every tape. -/
theorem denote_hhk_eq_hk (C : AdvClass model) (env : Env (Kind.Value model) []) (η : ℕ)
    (ρ : model.Tape η) :
    (FTerm.eq (hT (hT (nm Name.k))) (hT (nm Name.k))).denote (fullInterp model C) env η ρ =
      true := by
  rw [FTerm.denote_eq]
  exact (@decide_eq_true_iff _ (Classical.propDecidable _)).2 rfl

/-- In `model`, `h(k) = k` at every tape, so `h(h(k)) = h(k)` implies `h(h(k)) = k`. -/
theorem denote_imp_hhk_eq_k (C : AdvClass model) (env : Env (Kind.Value model) []) (η : ℕ)
    (ρ : model.Tape η) :
    (FTerm.imp (FTerm.eq (hT (hT (nm Name.k))) (hT (nm Name.k)))
        (FTerm.eq (hT (hT (nm Name.k))) (nm Name.k))).denote (fullInterp model C) env η ρ =
      true := by
  have hψ : (FTerm.eq (hT (hT (nm Name.k))) (nm Name.k)).denote (fullInterp model C) env η ρ =
      true := by
    rw [FTerm.denote_eq]
    exact (@decide_eq_true_iff _ (Classical.propDecidable _)).2 rfl
  simp only [FTerm.imp, FTerm.denote_ite, FTerm.denote_tt, hψ, Bool.cond_self]

/-- From the vector `h(h(k))`, deduce `k` in `model`: the entry is deducible, and it equals `k`
overwhelmingly, which local reasoning gives in two steps, `[h(h(k)) = h(k)]` and
`[h(h(k)) = h(k) ⇒ h(h(k)) = k]`, both true at every tape of `model`. -/
@[expose] def rewriteDerivation :
    Derivation decl (fun _ => False) (· = model) (Γ := []) []
      (.ded (one (hT (hT (nm Name.k)))) (nm Name.k)) :=
  .dedRewrite (v := hT (hT (nm Name.k))) (.dedInput _ .zero (by decide))
    (.boxMP (φ := FTerm.eq (hT (hT (nm Name.k))) (hT (nm Name.k)))
      (.boxValid _ fun _ _ hM C env η ρ => by subst hM; exact denote_hhk_eq_hk C env η ρ)
      (.boxValid _ fun _ _ hM C env η ρ => by subst hM; exact denote_imp_hhk_eq_k C env η ρ))

/-- `rewriteDerivation` is valid in `model`, against every class. -/
theorem rewriteDerivation_sound (C : ∀ M : Model decl, AdvClass M) :
    Valid (· = model) C (Γ := []) [] (.ded (one (hT (hT (nm Name.k)))) (nm Name.k)) :=
  rewriteDerivation.sound _ C (fun _ h => h.elim) fun _ h => h

/-- **The deduction is not trivial.** `h(h(k)) ⊬ k` fails in `model` against all machines, as
Neg2 gives from `rewriteDerivation`; while `h(h(k)) ⊬ n` holds there (`valid_worked`). -/
theorem valid_not_nonDed_hhk_k :
    Valid (· = model) (fun M => AdvClass.all M) (Γ := []) []
      (.not (.nonDed (one (hT (hT (nm Name.k)))) (nm Name.k))) :=
  Valid.not_nonDed (rewriteDerivation_sound _)

end Interop.Squirrel.SecrecyExamples
