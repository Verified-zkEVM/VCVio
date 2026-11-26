/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Squirrel.Rules.Secrecy
import VCVio.EvalDist.ProbabilityBounds

/-!
# Deduction of inputs, honest symbols and applications, and local reasoning

CCS26 (§2.3, p. 5) proves `leakage ▷ frame(τ)` by building the frame from the leakage: honest
symbols, the attacker's own function `att`, and calls of the leaked oracle. With `u⃗ ▷ v` defined
as `∃̃ f. adv(f) ∧̃ [f(u⃗) = v]` (CCS26 §3.1), such a deduction is a choice of `f`, and the closure
fields of `AdvClass` give the machines that compute it:

* `Valid.ded_input` (`u⃗ ▷ uᵢ`): an entry of order at most one is deducible. Its machine is the
  entry applied to its arguments (`Machine.project`), built from the input projection
  (`AdvClass.input_mem`, LICS23's PT.Input) and one query of an input at another input
  (`AdvClass.app_mem`) per argument.
* `Valid.ded_fn` (`u⃗ ▷ f`): an honest symbol of order at most one is deducible, by the same
  machine with the input answered by the symbol (`AdvClass.fn_mem`).
* `Valid.ded_app` (`u⃗ ▷ f` and `u⃗ ▷ t` give `u⃗ ▷ f t`): the machine computing the function
  has its argument's input answered by the machine computing the argument, on the same attacker
  tape (`Machine.subst`, `AdvClass.subst_mem`). The failure probability is at most the sum of the
  two premises'.
* `Valid.ded_rewrite` (`u⃗ ▷ v` and `[v = v']` give `u⃗ ▷ v'`): the same machine, at the cost of
  the probability that `v ≠ v'`.

With `Valid.ded_trans` and `Valid.ded_apps` for attacker symbols, these build every deduction of
a term from honest symbols, attacker symbols and the entries of the vector.

The local reasoning of the papers (LICS23's local sequent calculus, and the tool's rewriting with
the equations of its builtin symbols) is not formalized as a calculus. Two rules stand for it:

* `Valid.box_valid`: `[φ]` for a local formula true at every tape in every model of the
  restriction. Equations such as `fst(⟨x, y⟩) = x` are conditions on models (as LICS23 restricts
  the models of its declared symbols), and this rule makes them available.
* `Valid.box_mp`: from `[φ]` and `[φ ⇒ ψ]`, `[ψ]`, overwhelming truth being closed under modus
  ponens.

## References

* [CCS26] Hérouard, Jacomme, Koutsos, Lallemand, *Secrecy in Squirrel and the Post-Compromise
  Security of a Ratchet*, CCS 2026: §2.3 and §3.1.
* [LICS23] Baelde, Koutsos, Lallemand, *A Higher-Order Indistinguishability Logic for
  Cryptographic Reasoning*, LICS 2023: Fig. 7 and Fig. 10.
-/

public section

namespace Interop.Squirrel

open IPFunctor IPFunctor.ScopedSignature

variable {B : Type} {D : Decl B} {M : Model D} {τs : List (Ty B)} {a b β τ : Ty B} {η : ℕ}

/-! ## The machines -/

namespace Machine

/-- The first input, of a type of order at most one, applied to the remaining inputs, its
arguments: the input projection (`Machine.input`) for a Boolean or base type, and one query of an
input at another input (`Machine.app`) per argument. -/
@[expose] def project : (τ : Ty B) → τ.order ≤ 1 → Machine M (τ :: τ.args) τ.res
  | .bool, _ => input .zero trivial
  | .base _, _ => input .zero trivial
  | .arrow a b, h => (project b (le_trans (Ty.order_cod_le a b) h)).app
      (Ty.isGround_of_order_arrow_le_one h)

theorem run_project {ρa : M.TapeA η} : ∀ (τ : Ty B) (hτ : τ.order ≤ 1) (v : τ.Value M.carrier η)
    (q : Vals M η τ.args),
    (project τ hτ : Machine M (τ :: τ.args) τ.res).run η ρa (Env.cons v q) = Ty.apply v q
  | .bool, _, _, _ => run_input _ _ _
  | .base _, _, _, _ => run_input _ _ _
  | .arrow _ b, _, _, _ => (run_app _ _ _).trans (run_project b _ _ _)

end Machine

/-- `Machine.project` is admitted. -/
theorem AdvClass.project_mem (C : AdvClass M) :
    ∀ (τ : Ty B) (hτ : τ.order ≤ 1), C.mem (Machine.project τ hτ)
  | .bool, _ => C.input_mem _ _
  | .base _, _ => C.input_mem _ _
  | .arrow _ b, _ => C.app_mem _ (AdvClass.project_mem C b _)

namespace AdvMachine

/-- The attacker machine returning the entry `y` of its inputs, of order at most one. -/
@[expose] def ofInput (y : ScopedVar τs τ) (hτ : τ.order ≤ 1) : AdvMachine M τs τ :=
  (Machine.project τ hτ).rename (Env.cons (y.appendLeft τ.args) fun _ x => x.weakenMany τs)

/-- The attacker machine returning an honest symbol of order at most one. -/
@[expose] def ofFn (f : D.Fn τ) (hτ : τ.order ≤ 1) : AdvMachine M τs τ :=
  ((Machine.project τ hτ).rename
    (Env.cons (.zero : ScopedVar (τ :: (τs ++ τ.args)) τ) fun _ x => .succ (x.weakenMany τs))).fn f

/-- The application of the function that `F` computes to the argument that `T` computes, from the
same inputs, on the same attacker tape: `F`'s input for the argument is answered by `T`. -/
@[expose] def ofApp (F : AdvMachine M τs (.arrow a b)) (T : AdvMachine M τs a) :
    AdvMachine M τs b :=
  Machine.subst (as := []) (ρ := a)
    (F.rename (Env.append (fun _ x => .succ (x.appendLeft b.args))
      (Env.cons (.zero : ScopedVar (Ty.arrows [] a :: (τs ++ b.args)) a)
        fun _ x => .succ (x.weakenMany τs))))
    (T.rename (Env.append (fun _ x => (x.appendLeft b.args).weakenMany a.args)
      fun _ y => y.appendLeft (τs ++ b.args)))

variable {ρa : M.TapeA η}

theorem appVals_eval_ofInput (y : ScopedVar τs τ) (hτ : τ.order ≤ 1) (e : Vals M η τs) :
    Ty.appVals ((ofInput y hτ : AdvMachine M τs τ).eval η ρa) e = e τ y := by
  rw [appVals_eval]
  conv_rhs => rw [← Ty.curry_apply (e τ y)]
  congr 1
  funext q
  rw [ofInput, Machine.run_rename]
  have hr : Env.rename (Env.cons (y.appendLeft τ.args) fun _ x => x.weakenMany τs)
      (Env.append e q) = Env.cons (e τ y) q := by
    funext σ x
    cases x with
    | zero => exact Env.append_appendLeft _ _ _
    | succ x => exact Env.append_weakenMany _ _ _
  rw [hr]
  exact Machine.run_project τ hτ _ _

theorem appVals_eval_ofFn (f : D.Fn τ) (hτ : τ.order ≤ 1) (e : Vals M η τs) :
    Ty.appVals ((ofFn f hτ : AdvMachine M τs τ).eval η ρa) e = M.fn η f := by
  rw [appVals_eval]
  conv_rhs => rw [← Ty.curry_apply (M.fn η f)]
  congr 1
  funext q
  rw [ofFn, Machine.run_fn, Machine.run_rename]
  have hr : Env.rename (Env.cons (.zero : ScopedVar (τ :: (τs ++ τ.args)) τ)
      fun _ x => .succ (x.weakenMany τs)) (Env.cons (M.fn η f) (Env.append e q)) =
      Env.cons (M.fn η f) q := by
    funext σ x
    cases x with
    | zero => rfl
    | succ x => exact Env.append_weakenMany _ _ _
  rw [hr]
  exact Machine.run_project τ hτ _ _

theorem appVals_eval_ofApp (F : AdvMachine M τs (.arrow a b)) (T : AdvMachine M τs a)
    (e : Vals M η τs) :
    Ty.appVals ((ofApp F T).eval η ρa) e =
      Ty.appVals (F.eval η ρa) e (Ty.appVals (T.eval η ρa) e) := by
  have hr₁ : ∀ (v : a.Value M.carrier η) (q : Vals M η b.args),
      Env.rename (Env.append (fun _ x => .succ (x.appendLeft b.args))
        (Env.cons (.zero : ScopedVar (Ty.arrows [] a :: (τs ++ b.args)) a)
          fun _ x => .succ (x.weakenMany τs))) (Env.cons v (Env.append e q)) =
        Env.append e (Env.cons v q) := fun v q => by
    rw [Env.rename_append_renaming]
    congr 1
    · funext σ x
      exact Env.append_appendLeft _ _ _
    · funext σ x
      cases x with
      | zero => rfl
      | succ x => exact Env.append_weakenMany _ _ _
  have hr₂ : ∀ (q : Vals M η b.args) (y : Vals M η a.args),
      Env.rename (Env.append (fun _ x => (x.appendLeft b.args).weakenMany a.args)
        fun _ y => y.appendLeft (τs ++ b.args)) (Env.append y (Env.append e q)) =
        Env.append e y :=
    fun q y => by
      rw [Env.rename_append_renaming, Env.rename_appendLeft_append]
      congr 1
      funext σ x
      exact (Env.append_weakenMany _ _ _).trans (Env.append_appendLeft _ _ _)
  rw [appVals_eval, appVals_eval, appVals_eval]
  refine congrArg (Ty.curry (τ := b)) (funext fun q => ?_)
  refine ((Machine.run_subst (as := []) (ρ := a) _ _ _).trans
    ((Machine.run_rename _ F _).trans (congrArg (F.run η ρa) (hr₁ _ q)))).trans ?_
  exact congrArg (fun v => F.run η ρa (Env.append e (Env.cons v q)))
    (congrArg Ty.curry (funext fun y => (Machine.run_rename _ T _).trans
      (congrArg (T.run η ρa) (hr₂ q y))))

end AdvMachine

/-! ## The laws -/

namespace AdvClass

variable {C : AdvClass M} {u : VecRV M τs}

/-- `u⃗ ▷ uᵢ`, by the machine `AdvMachine.ofInput`, which never fails. -/
theorem ded_input (C : AdvClass M) (u : VecRV M τs) (y : ScopedVar τs τ) (hτ : τ.order ≤ 1) :
    C.Ded u (fun η ρ => u η ρ τ y) :=
  ⟨AdvMachine.ofInput y hτ, C.rename_mem _ (C.project_mem τ hτ), negligible_of_zero fun _ =>
    prEvent_eq_zero_of_forall_not _ _ fun _ hρ => hρ (AdvMachine.appVals_eval_ofInput y hτ _)⟩

/-- `u⃗ ▷ f` for an honest symbol, by the machine `AdvMachine.ofFn`, which never fails. -/
theorem ded_fn (C : AdvClass M) (u : VecRV M τs) (f : D.Fn τ) (hτ : τ.order ≤ 1) :
    C.Ded u (fun η _ => M.fn η f) :=
  ⟨AdvMachine.ofFn f hτ, C.fn_mem f (C.rename_mem _ (C.project_mem τ hτ)),
    negligible_of_zero fun _ =>
      prEvent_eq_zero_of_forall_not _ _ fun _ hρ => hρ (AdvMachine.appVals_eval_ofFn f hτ _)⟩

/-- `u⃗ ▷ F` and `u⃗ ▷ T` give `u⃗ ▷ F T`, by the machine `AdvMachine.ofApp` of the two
witnesses: it fails only where one of them does. -/
theorem Ded.app {F : RV M (.arrow a b)} {T : RV M a} (hF : C.Ded u F) (hT : C.Ded u T) :
    C.Ded u (fun η ρ => F η ρ (T η ρ)) := by
  obtain ⟨f, hf, hferr⟩ := hF
  obtain ⟨t, ht, hterr⟩ := hT
  refine ⟨AdvMachine.ofApp f t, C.subst_mem (C.rename_mem _ hf) (C.rename_mem _ ht),
    negligible_of_le (fun η => ?_) (negligible_add hferr hterr)⟩
  refine (prEvent_mono _ _ _ fun ρ hρ => ?_).trans (prEvent_or_le _ _ _)
  rw [AdvMachine.appVals_eval_ofApp] at hρ
  by_contra hc
  push Not at hc
  exact hρ (by rw [hc.1, hc.2])

/-- `u⃗ ▷ v` gives `u⃗ ▷ v'` where `v = v'` overwhelmingly: the same machine fails only where it
fails on `v` or where `v ≠ v'`. -/
theorem Ded.rewrite {v v' : RV M β} (h : C.Ded u v)
    (heq : negligible fun η => Pr{let ρ ← $ᵗ (M.Tape η)}[v η ρ ≠ v' η ρ]) : C.Ded u v' := by
  obtain ⟨g, hg, herr⟩ := h
  refine ⟨g, hg, negligible_of_le (fun η => ?_) (negligible_add herr heq)⟩
  refine (prEvent_mono _ _ _ fun ρ hρ => ?_).trans (prEvent_or_le _ _ _)
  by_contra hc
  push Not at hc
  exact hρ (hc.1.trans hc.2)

end AdvClass

namespace Valid

variable {Γ : List (Kind B)} {R : Model D → Prop} {C : ∀ M : Model D, AdvClass M}
  {Θ : List (Form D Γ)} {u : Vec D Γ τs}

/-- **Deducing an entry**: `u⃗ ▷ uᵢ`, for an entry of order at most one. -/
theorem ded_input (y : ScopedVar τs τ) {ho : Ty.SecrecyOrder τs τ} :
    Valid R C Θ (.ded u (u τ y) ho) := fun M _ _ env _ =>
  Form.holds_ded.2 ((C M).ded_input (u.rv M (C M) env) y ho.2)

/-- **Deducing an honest symbol**: `u⃗ ▷ f`, for an honest symbol of order at most one. -/
theorem ded_fn (f : D.Fn τ) {ho : Ty.SecrecyOrder τs τ} :
    Valid R C Θ (.ded u (FTerm.fn f) ho) := fun M _ _ env _ =>
  Form.holds_ded.2 ((C M).ded_fn (u.rv M (C M) env) f ho.2)

/-- **Deducing an application**: from `u⃗ ▷ f` and `u⃗ ▷ t`, conclude `u⃗ ▷ f t`. -/
theorem ded_app {f : FTerm D Γ (.arrow a b)} {t : FTerm D Γ a}
    {hof : Ty.SecrecyOrder τs (.arrow a b)} {hot : Ty.SecrecyOrder τs a}
    {ho : Ty.SecrecyOrder τs b} (hf : Valid R C Θ (.ded u f hof))
    (ht : Valid R C Θ (.ded u t hot)) : Valid R C Θ (.ded u (FTerm.app f t) ho) :=
  fun M hl hR env hΘ => Form.holds_ded.2
    ((Form.holds_ded.1 (hf M hl hR env hΘ)).app (Form.holds_ded.1 (ht M hl hR env hΘ)))

/-- **Rewriting a deduced term**: from `u⃗ ▷ v` and `[v = v']`, conclude `u⃗ ▷ v'`. -/
theorem ded_rewrite {v v' : FTerm D Γ β} {ho : Ty.SecrecyOrder τs β}
    (h : Valid R C Θ (.ded u v ho)) (heq : Valid R C Θ (.box (FTerm.eq v v'))) :
    Valid R C Θ (.ded u v' ho) := fun M hl hR env hΘ => by
  refine Form.holds_ded.2 ((Form.holds_ded.1 (h M hl hR env hΘ)).rewrite
    (negligible_of_le (fun η => le_of_eq (prEvent_congr _ _ _ fun ρ => ?_))
      (Form.holds_box.1 (heq M hl hR env hΘ))))
  rw [FTerm.denote_eq]
  exact (@decide_eq_false_iff_not _ (Classical.propDecidable _)).symm

/-- **Local validity**: `[φ]` for a local formula true at every tape of every admitted model. -/
theorem box_valid {φ : FTerm D Γ .bool}
    (h : ∀ M : Model D, M.RespectsLabels → R M → ∀ env η ρ,
      φ.denote (fullInterp M (C M)) env η ρ = true) :
    Valid R C Θ (.box φ) := fun M hl hR env _ =>
  Form.holds_box.2 (negligible_of_zero fun η =>
    prEvent_eq_zero_of_forall_not _ _ fun ρ hρ => by
      rw [h M hl hR env η ρ] at hρ
      exact Bool.noConfusion hρ)

/-- **Modus ponens under `[·]`**: from `[φ]` and `[φ ⇒ ψ]`, conclude `[ψ]`. Where `ψ` fails,
`φ` or the implication fails. -/
theorem box_mp {φ ψ : FTerm D Γ .bool} (h : Valid R C Θ (.box φ))
    (h' : Valid R C Θ (.box (FTerm.imp φ ψ))) : Valid R C Θ (.box ψ) := fun M hl hR env hΘ => by
  refine Form.holds_box.2 (negligible_of_le (fun η => ?_)
    (negligible_add (Form.holds_box.1 (h M hl hR env hΘ))
      (Form.holds_box.1 (h' M hl hR env hΘ))))
  refine (prEvent_mono _ _ _ fun ρ hρ => ?_).trans (prEvent_or_le _ _ _)
  simp only [FTerm.imp, FTerm.denote_ite, FTerm.denote_tt]
  cases hc : φ.denote (fullInterp M (C M)) env η ρ
  · exact Or.inl rfl
  · exact Or.inr (by simpa using hρ)

end Valid

end Interop.Squirrel
