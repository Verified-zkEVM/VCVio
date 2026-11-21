/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Squirrel.RandomVariable
public import Interop.Squirrel.Machine
public import VCVio.CryptoFoundations.Asymptotics.Negligible
public import ToMathlib.Data.ENNReal.AbsDiff
public import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Indistinguishability over a class of machines

LICS23's `u⃗ ∼ v⃗` (§II-C, Fig. 2) says that no polynomial-time machine tells the two vectors
apart, and `adv(t)` that some polynomial-time machine computes `t`. The machines read the attacker
tape `ρa`, and their inputs at `η` are values of `⟦τ⟧_η`, whose type depends on `η`. Here the
machines are those of `Interop.Squirrel.Machine`, free programs over the tape and the inputs:

* `advantage A u v η` is `|Pr[A(u) = 1] − Pr[A(v) = 1]|` over uniform tapes, for a distinguisher
  `A` given as a function (`Distinguisher`);
* `AdvClass M` is the class of admitted machines, a predicate on machines. `C.Indist u v` says
  that every admitted machine returning a Boolean has negligible advantage as a distinguisher
  (`Machine.test`), and `C.Adv X` that an admitted machine computes `X` everywhere
  (`AdvMachine.eval`).

The class is a parameter of the semantics, and polynomial time is not imposed on it: the
structural rules (`Interop.Squirrel.Global`) hold for every class. `AdvClass.all` admits every
machine with polynomial read and query bounds (`Machine.ReadsBelow`, `Machine.QueryBound`): the
information-theoretic class of the satisfiability models and countermodels.

## References

* [LICS23] Baelde, Koutsos, Lallemand, *A Higher-Order Indistinguishability Logic for
  Cryptographic Reasoning*, LICS 2023: §II-C and Fig. 2.
-/

public section

namespace Interop.Squirrel

open IPFunctor IPFunctor.ScopedSignature

variable {B : Type} {D : Decl B} {M : Model D}

/-- A vector of random variables of the types `τs`. -/
abbrev VecRV (M : Model D) (τs : List (Ty B)) : Type := (η : ℕ) → M.Tape η → Vals M η τs

variable {τ : Ty B} {τs : List (Ty B)}

/-- Prepend a random variable. -/
@[expose] def VecRV.cons (X : RV M τ) (u : VecRV M τs) : VecRV M (τ :: τs) :=
  fun η ρ => Env.cons (X η ρ) (u η ρ)

/-- The advantage of a distinguisher between two vectors at `η`, over uniform tapes. -/
@[expose] noncomputable def advantage (A : Distinguisher M τs) (u v : VecRV M τs) (η : ℕ) :
    ENNReal :=
  ENNReal.absDiff (Pr{let ρ ← $ᵗ (M.Tape η)}[A η (u η ρ) ρ.1 = true])
    (Pr{let ρ ← $ᵗ (M.Tape η)}[A η (v η ρ) ρ.1 = true])

/-- The machines of a model admitted for `adv` and `∼`, standing for LICS23's polynomial-time
machines: a predicate on machines. -/
structure AdvClass (M : Model D) where
  /-- The admitted machines. -/
  mem : {τs : List (Ty B)} → {β : Ty B} → Machine M τs β → Prop

namespace AdvClass

/-- Every machine with polynomial read and query bounds: the information-theoretic class. -/
@[expose] def all (M : Model D) : AdvClass M where
  mem A := (∃ p : Polynomial ℕ, A.ReadsBelow fun η => p.eval η) ∧
    ∃ q : Polynomial ℕ, A.QueryBound fun η => q.eval η

/-- The input projections are in `AdvClass.all`: they read nothing of the tape and make one
input query. -/
theorem all_mem_input {a : Ty B} (y : ScopedVar τs a) (ha : a.IsGround) :
    (all M).mem (Machine.input y ha) :=
  ⟨⟨0, Machine.readsBelow_input y ha⟩, 1, (Machine.queryBound_input y ha).mono fun η => by simp⟩

/-- `adv t` (LICS23 Fig. 2), at the type `τ₁ → … → τₙ → β`: an admitted machine with inputs `τs`
and the arguments of `β` computes `t` everywhere. -/
@[expose] def Adv (C : AdvClass M) {β : Ty B} (X : RV M (Ty.arrows τs β)) : Prop :=
  ∃ A : AdvMachine M τs β, C.mem A ∧ ∀ η ρ, X η ρ = A.eval η ρ.1

/-- `u⃗ ∼ v⃗` (LICS23 Fig. 2): every admitted machine returning a Boolean has negligible
advantage. -/
@[expose] def Indist (C : AdvClass M) (u v : VecRV M τs) : Prop :=
  ∀ A : Machine M τs .bool, C.mem A → negligible (advantage A.test u v)

end AdvClass

end Interop.Squirrel
