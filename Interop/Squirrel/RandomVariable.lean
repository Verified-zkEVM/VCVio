/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Squirrel.Model

/-!
# Local terms as random variables

LICS23 interprets a local term as a family of random variables `(ρ ↦ ⟦t⟧^{η,ρ})_η` over the
finite tapes, and the free variables of a global formula range over random variables (§II-A.3,
§II-C). `rvInterp M` is that reading, as one interpretation of `localSig D` in `Kind.Value M`:
random variables at local types, propositions at the global sort. As in LICS23, an abstraction
reads its bound variable as `RV.constAt η a`, the paper's `1^η_a`: the constant `a` at `η`, and an
arbitrary value at other parameters.

`eval_denote_rvInterp` shows that the reading at `(η, ρ)` is the pointwise reading
`interp M η ρ` of the environment's values at `(η, ρ)`. Its proof is PolyFun's relational fold
`IFreeM.fold_rel`, with no induction on terms. Pointwise laws therefore hold of random
variables; `LTerm.denote_rvInterp_app_lam` is β.

## References

* [LICS23] Baelde, Koutsos, Lallemand, *A Higher-Order Indistinguishability Logic for
  Cryptographic Reasoning*, LICS 2023: §II-A.3 and §II-C.
-/

public section

namespace Interop.Squirrel

open IPFunctor IPFunctor.ScopedSignature

variable {B : Type} {D : Decl B}

/-- Families of random variables of type `τ`, one per security parameter (LICS23 `RV_M(τ)`). -/
abbrev RV (M : Model D) (τ : Ty B) : Type := (η : ℕ) → M.Tape η → τ.Value M.carrier η

/-- The meaning of a sort: random variables at local types, propositions at the global sort. -/
@[expose, reducible] def Kind.Value (M : Model D) : Kind B → Type
  | .loc τ => RV M τ
  | .glob => Prop

variable {M : Model D}

/-- LICS23's `1^η_a`: the value `a` at the parameter `η` and every tape, and an arbitrary value
at other parameters. -/
@[expose] noncomputable def RV.constAt {τ : Ty B} (η : ℕ) (a : τ.Value M.carrier η) : RV M τ :=
  fun η' _ => if h : η = η' then h ▸ a else Classical.choice (τ.nonempty_value M.nonempty η')

@[simp] theorem RV.constAt_apply_self {τ : Ty B} (η : ℕ) (a : τ.Value M.carrier η)
    (ρ : M.Tape η) : RV.constAt η a η ρ = a := by
  simp [RV.constAt]

/-- A sort's meaning, read at one parameter and tape. -/
@[expose] def Kind.eval (M : Model D) (η : ℕ) (ρ : M.Tape η) :
    (s : Kind B) → s.Value M → s.PtValue M η
  | .loc _, X => X η ρ
  | .glob, _ => PUnit.unit

/-- A pointwise meaning at `η`, as a meaning constant across tapes. -/
@[expose] noncomputable def Kind.embed (M : Model D) (η : ℕ) :
    (s : Kind B) → s.PtValue M η → s.Value M
  | .loc _, a => RV.constAt η a
  | .glob, _ => True

@[simp] theorem Kind.eval_embed (η : ℕ) (ρ : M.Tape η) :
    ∀ (s : Kind B) (x : s.PtValue M η), s.eval M η ρ (s.embed M η x) = x
  | .loc _, a => RV.constAt_apply_self η a ρ
  | .glob, _ => rfl

/-- Local syntax as random variables (LICS23 §II-A.3). -/
@[expose] noncomputable def rvInterp (M : Model D) : Interpretation (localSig D) (Kind.Value M)
  | .loc _, o, next => fun η ρ => interp M η ρ o fun p e =>
      Kind.eval M η ρ _ (next p fun s x => Kind.embed M η s (e s x))
  | .glob, o, _ => nomatch o

/-- An environment of random variables, read at one parameter and tape. -/
@[expose] def evalEnv (M : Model D) (η : ℕ) (ρ : M.Tape η) {Γ : List (Kind B)}
    (env : Env (Kind.Value M) Γ) : Env (Kind.PtValue M η) Γ :=
  fun s x => s.eval M η ρ (env s x)

variable {η : ℕ} {ρ : M.Tape η}

theorem evalEnv_append {Ξ Γ : List (Kind B)} (ξ : Env (Kind.Value M) Ξ)
    (env : Env (Kind.Value M) Γ) :
    evalEnv M η ρ (Env.append ξ env) = Env.append (evalEnv M η ρ ξ) (evalEnv M η ρ env) := by
  induction Ξ with
  | nil => rfl
  | cons s Ξ ih =>
    funext t x
    cases x with
    | zero => rfl
    | succ x => exact congrFun (congrFun (ih fun b v => ξ b (.succ v)) t) x

theorem evalEnv_embed {Γ : List (Kind B)} (e : Env (Kind.PtValue M η) Γ) :
    evalEnv M η ρ (fun s x => Kind.embed M η s (e s x)) = e := by
  funext s x
  exact Kind.eval_embed η ρ s (e s x)

/-- **Locality.** A local term's random variable, at `(η, ρ)`, is its pointwise meaning at the
environment's values at `(η, ρ)`. -/
theorem eval_denote_rvInterp (M : Model D) (η : ℕ) (ρ : M.Tape η) {Γ : List (Kind B)}
    {s : Kind B} (t : (localSig D).Term Γ s) (env : Env (Kind.Value M) Γ) :
    s.eval M η ρ (t.denote (rvInterp M) env) = t.denote (interp M η ρ) (evalEnv M η ρ env) := by
  refine IFreeM.fold_rel (P := (localSig D).polynomial)
    (D := fun j : Judgment (Kind B) => Env (Kind.Value M) j.1 → Kind.Value M j.2)
    (E := fun j : Judgment (Kind B) => Env (Kind.PtValue M η) j.1 → Kind.PtValue M η j.2)
    (fun j f g => ∀ env, j.2.eval M η ρ (f env) = g (evalEnv M η ρ env))
    (fun _ x env => env _ x) (fun _ x env => env _ x)
    (fun _ o next env => rvInterp M o fun p ξ => next p (Env.append ξ env))
    (fun _ o next env => interp M η ρ o fun p ξ => next p (Env.append ξ env))
    (fun _ _ _ => rfl) ?_ t env
  rintro ⟨Γ, s⟩ o ds es h env
  cases s with
  | glob => exact nomatch o
  | loc τ =>
    change interp M η ρ o _ = interp M η ρ o _
    congr 1
    funext p e
    rw [h p, evalEnv_append, evalEnv_embed]

/-- **β**, for random variables: from the pointwise law and locality. -/
theorem LTerm.denote_rvInterp_app_lam {Γ : List (Kind B)} {a b : Ty B}
    (body : LTerm D (.loc a :: Γ) b) (v : LTerm D Γ a) (env : Env (Kind.Value M) Γ) :
    (app (lam body) v).denote (rvInterp M) env = (body.substOne v).denote (rvInterp M) env := by
  funext η ρ
  exact (eval_denote_rvInterp M η ρ _ env).trans
    ((denote_app_lam body v).trans (eval_denote_rvInterp M η ρ _ env).symm)

end Interop.Squirrel
