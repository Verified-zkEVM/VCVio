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
import VCVio.EvalDist.ProbabilityBounds

/-!
# Indistinguishability over a class of machines

LICS23's `u⃗ ∼ v⃗` (§II-C, Fig. 2) says that no polynomial-time machine tells the two vectors
apart, and `adv(t)` that some polynomial-time machine computes `t`. The machines read the attacker
tape `ρa`, and their inputs at `η` are values of `⟦τ⟧_η`, whose type depends on `η`. Here the
machines are those of `Interop.Squirrel.Machine`, free programs over the tape and the inputs:

* `advantage A u v η` is `|Pr[A(u) = 1] − Pr[A(v) = 1]|` over uniform tapes, for a distinguisher
  `A` given as a function (`Distinguisher`);
* `AdvClass M` is the class of admitted machines, a predicate on machines with closure fields.
  `C.Indist u v` says that every admitted machine returning a Boolean has negligible advantage as
  a distinguisher (`Machine.test`), and `C.Adv X` that an admitted machine computes `X`
  everywhere (`AdvMachine.eval`).

Each rule about `∼` reduces a machine against its conclusion to machines against its premises. The
reductions are named twice: as functions of the input values (`Distinguisher.app`, `.fn`, `.adv`,
`.ite`, `.rename`, `.guard`), on which the advantage is computed, and as machines
(`Machine.app`, …), whose `test` is that function (`Machine.test_app`, …). The first five keep the
advantage at every `η`; the case split (`AdvClass.Indist.caseStudy`, with BC14's If1 as
`AdvClass.Indist.if1`) uses `guard true` and `guard false`, and at every `η` the advantage is at
most the sum of theirs (`advantage_cons_cond_le`). These are the concrete statements.

The closure fields of `AdvClass` are the program constructions of `Interop.Squirrel.Machine` that
these reductions use: relabelling the inputs, running one machine to answer another's input
queries (substitution into a handler), querying an input at another input, answering by an honest
symbol, branching on a Boolean input and the Boolean constants. The reductions of the rules are
built from them (`AdvClass.adv_mem`, `AdvClass.ite_mem`, `AdvClass.guard_mem`). No field admits an
`η`-indexed constant: the only values a field supplies are Booleans, the model's honest symbols
and the arguments of a machine's own queries.

The class is a parameter of the semantics, and polynomial time is not imposed on it.
`AdvClass.all` admits every machine with polynomial read and query bounds (`Machine.ReadsBelow`,
`Machine.QueryBound`) and meets every field: the information-theoretic class of the satisfiability
models and countermodels.

## References

* [LICS23] Baelde, Koutsos, Lallemand, *A Higher-Order Indistinguishability Logic for
  Cryptographic Reasoning*, LICS 2023: §II-C, Fig. 2 and Fig. 8.
* [BC14] Bana, Comon-Lundh, *A Computationally Complete Symbolic Attacker for Equivalence
  Properties*, CCS 2014: Fig. 2 and Prop. 2.
-/

public section

namespace Interop.Squirrel

open IPFunctor IPFunctor.ScopedSignature

variable {B : Type} {D : Decl B} {M : Model D}

/-- A vector of random variables of the types `τs`. -/
abbrev VecRV (M : Model D) (τs : List (Ty B)) : Type := (η : ℕ) → M.Tape η → Vals M η τs

variable {η : ℕ} {a b τ : Ty B} {τs : List (Ty B)}

/-- Drop the first entry of a vector. -/
@[expose] def Vals.tail (e : Vals M η (τ :: τs)) : Vals M η τs := fun _ x => e _ (.succ x)

/-! ## Named reductions -/

namespace Distinguisher

/-- The reduction for FA-App: apply the first entry to the second, then test. -/
@[expose] def app (A : Distinguisher M (b :: τs)) : Distinguisher M (.arrow a b :: a :: τs) :=
  fun η e ρa => A η (Env.cons (e _ .zero (e _ (.succ .zero))) e.tail.tail) ρa

/-- The reduction for FA-Fn: prepend the value of an honest symbol, then test. -/
@[expose] def fn (f : D.Fn τ) (A : Distinguisher M (τ :: τs)) : Distinguisher M τs :=
  fun η e ρa => A η (Env.cons (M.fn η f) e) ρa

/-- The reduction for FA-Adv: prepend an attacker function run on the same attacker tape,
then test. -/
@[expose] def adv (g : AttackerFn M τ) (A : Distinguisher M (τ :: τs)) : Distinguisher M τs :=
  fun η e ρa => A η (Env.cons (g η ρa) e) ρa

/-- The reduction for If: evaluate a conditional from the first three entries. -/
@[expose] def ite (A : Distinguisher M (a :: τs)) : Distinguisher M (.bool :: a :: a :: τs) :=
  fun η e ρa => A η
    (Env.cons (cond (e _ .zero) (e _ (.succ .zero)) (e _ (.succ (.succ .zero)))) e.tail.tail.tail)
    ρa

/-- The reduction for Perm: reindex the vector along a map of positions that preserves types
(PolyFun's `Renaming`). Permutation, projection and duplication are instances. -/
@[expose] def rename {τs' : List (Ty B)} (r : Renaming τs' τs) (A : Distinguisher M τs') :
    Distinguisher M τs :=
  fun η e ρa => A η (Env.rename r e) ρa

/-- The reduction for the case split: when the Boolean first entry is `c`, test the rest;
otherwise return `false`. The two halves of a case split on `b` are `guard true`, which is
`b && A(v⃗)`, and `guard false`, which is `!b && A(v⃗)`. -/
@[expose] def guard (c : Bool) (A : Distinguisher M τs) : Distinguisher M (.bool :: τs) :=
  fun η e ρa => (e _ .zero == c) && A η e.tail ρa

end Distinguisher

/-- The advantage of a distinguisher between two vectors at `η`, over uniform tapes. -/
@[expose] noncomputable def advantage (A : Distinguisher M τs) (u v : VecRV M τs) (η : ℕ) :
    ENNReal :=
  ENNReal.absDiff (Pr{let ρ ← $ᵗ (M.Tape η)}[A η (u η ρ) ρ.1 = true])
    (Pr{let ρ ← $ᵗ (M.Tape η)}[A η (v η ρ) ρ.1 = true])

/-! ## Machines as distinguishers -/

namespace Machine

variable {τs' : List (Ty B)}

theorem test_input (y : ScopedVar τs .bool) :
    (input y Ty.isGround_bool : Machine M τs .bool).test = fun _ e _ => e .bool y :=
  funext fun _ => funext fun _ => funext fun _ => run_input y Ty.isGround_bool _

theorem test_rename (r : Renaming τs τs') (A : Machine M τs .bool) :
    (A.rename r).test = A.test.rename r :=
  funext fun _ => funext fun _ => funext fun _ => run_rename r A _

theorem test_app (ha : a.IsGround) (A : Machine M (b :: τs) .bool) :
    (A.app ha).test = A.test.app :=
  funext fun _ => funext fun _ => funext fun _ => run_app ha A _

theorem test_fn (f : D.Fn τ) (A : Machine M (τ :: τs) .bool) : (A.fn f).test = A.test.fn f :=
  funext fun _ => funext fun _ => funext fun _ => run_fn f A _

theorem test_adv {τs₀ : List (Ty B)} {β : Ty B} (A : Machine M (Ty.arrows τs₀ β :: τs) .bool)
    (g : AdvMachine M τs₀ β) : (A.adv g).test = A.test.adv g.eval :=
  funext fun _ => funext fun _ => funext fun _ => run_adv A g _

theorem test_ite (A : Machine M (a :: τs) .bool) : A.ite.test = A.test.ite :=
  funext fun _ => funext fun _ => funext fun _ => run_ite A _

theorem test_guard (c : Bool) (A : Machine M τs .bool) : (A.guard c).test = A.test.guard c :=
  funext fun _ => funext fun _ => funext fun _ => run_guard c A _

end Machine

/-! ## The class of machines -/

/-- The machines of a model admitted for `adv` and `∼`, standing for LICS23's polynomial-time
machines: a predicate on machines, closed under the program constructions of
`Interop.Squirrel.Machine` that the reductions of the rules use. Each field names the rules it
serves and the property of a class of polynomial-time machines that gives it. -/
structure AdvClass (M : Model D) where
  /-- The admitted machines. -/
  mem : {τs : List (Ty B)} → {β : Ty B} → Machine M τs β → Prop
  /-- Relabelling the inputs (`Machine.rename`): Perm, Restr and Dup (`Valid.equiv_rename`,
  `Valid.equiv_tail`, `Valid.equiv_dup`), and through the derived reductions FA-Adv, If and the
  case split. Polynomial time: closing the input interface through the handler that forwards each
  query along the renaming, a single query per query (`OracleComp.Complexity.closeHandler` with a
  dispatcher of constant cost). -/
  rename_mem {τs τs' : List (Ty B)} {β : Ty B} (r : Renaming τs τs') {A : Machine M τs β} :
    mem A → mem (A.rename r)
  /-- Substitution into a handler (`Machine.subst`): the queries to the first input are answered
  by running an admitted machine on the query's arguments and the remaining inputs, on the same
  attacker tape. FA-Adv (`AdvClass.adv_mem`, `Valid.equiv_adv`). Polynomial time: VCVio's
  proof-bearing handler closure, `OracleComp.Complexity.closeHandler` with a `HandlerCertificate`
  for the handler, and the sequencing of `IsOraclePPTBy.bind`; answers are values of Boolean or
  base types, whose size is polynomial. -/
  subst_mem {as : List (Ty B)} {ρ : Ty B} {τs : List (Ty B)} {β : Ty B}
    {A : Machine M (Ty.arrows as ρ :: τs) β} {K : Machine M (as ++ (ρ.args ++ τs)) ρ.res} :
    mem A → mem K → mem (A.subst K)
  /-- Querying an input at another input (`Machine.app`): FA-App (`Valid.equiv_app`). The input
  read is of a Boolean or base type, as in every vector of order at most one. Polynomial time: a
  handler making two queries per query. -/
  app_mem {a b : Ty B} {τs : List (Ty B)} {β : Ty B} (ha : a.IsGround)
    {A : Machine M (b :: τs) β} : mem A → mem (A.app ha)
  /-- Answering an input by an honest symbol (`Machine.fn`): FA-Fn (`Valid.equiv_fn`), and
  through it BC14's FA (`Valid.equiv_fa`). Polynomial time: LICS23 interprets honest symbols by
  polynomial-time functions, so the handler is a pure polynomial-time function of the query
  (VCVio's `PureCertificate`). -/
  fn_mem {τ : Ty B} {τs : List (Ty B)} {β : Ty B} (f : D.Fn τ) {A : Machine M (τ :: τs) β} :
    mem A → mem (A.fn f)
  /-- Branching on a Boolean input (`Machine.branch`): If (`AdvClass.ite_mem`,
  `Valid.equiv_ite`) and the case split (`AdvClass.guard_mem`, `Valid.equiv_caseStudy`,
  `Valid.equiv_if1`). Polynomial time: one query, then either machine (`IsOraclePPTBy.bind` with
  a two-way continuation). -/
  branch_mem {τs : List (Ty B)} {β : Ty B} {x y : Machine M τs β} :
    mem x → mem y → mem (Machine.branch x y)
  /-- The Boolean constants (`Machine.const`): the case split (`AdvClass.guard_mem`), whose
  reduction returns `false` when the condition fails. Polynomial time: `PureCertificate` of a
  constant. -/
  const_mem {τs : List (Ty B)} (c : Bool) : mem (Machine.const c : Machine M τs .bool)

namespace AdvClass

/-- Every machine with polynomial read and query bounds: the information-theoretic class, which
meets every closure field. -/
@[expose] def all (M : Model D) : AdvClass M where
  mem A := (∃ p : Polynomial ℕ, A.ReadsBelow fun η => p.eval η) ∧
    ∃ q : Polynomial ℕ, A.QueryBound fun η => q.eval η
  rename_mem r := fun ⟨⟨p, hp⟩, q, hq⟩ => ⟨⟨p, hp.rename r⟩, q, hq.rename r⟩
  subst_mem := fun ⟨⟨p, hp⟩, q, hq⟩ ⟨⟨p', hp'⟩, q', hq'⟩ => ⟨⟨p + p',
    (hp.mono fun η => by simp).subst (hp'.mono fun η => by simp)⟩, q * (q' + 1),
    (hq.subst hq').mono fun η => by simp⟩
  app_mem ha := fun ⟨⟨p, hp⟩, q, hq⟩ => ⟨⟨p, hp.app ha⟩, q * 2, (hq.app ha).mono fun η => by simp⟩
  fn_mem f := fun ⟨⟨p, hp⟩, q, hq⟩ => ⟨⟨p, hp.fn f⟩, q, hq.fn f⟩
  branch_mem := fun ⟨⟨p, hp⟩, q, hq⟩ ⟨⟨p', hp'⟩, q', hq'⟩ => ⟨⟨p + p',
    (hp.mono fun η => by simp).branch (hp'.mono fun η => by simp)⟩, 1 + (q + q'),
    (hq.branch hq').mono fun η => by simp⟩
  const_mem _ := ⟨⟨0, Machine.readsBelow_const _⟩, 0, Machine.queryBound_const _⟩

/-- A machine that never reads the tape and makes boundedly many input queries is in
`AdvClass.all`. -/
theorem all_mem_of_readsBelow_zero {β : Ty B} {A : Machine M τs β}
    (h : A.ReadsBelow fun _ => 0) {n : ℕ} (hq : A.QueryBound fun _ => n) : (all M).mem A :=
  ⟨⟨0, by simpa using h⟩, n, by simpa using hq⟩

/-- The input projections are in `AdvClass.all`: they read nothing of the tape and make one
input query. -/
theorem all_mem_input (y : ScopedVar τs a) (ha : a.IsGround) :
    (all M).mem (Machine.input y ha) :=
  all_mem_of_readsBelow_zero (Machine.readsBelow_input y ha) (Machine.queryBound_input y ha)

/-- `adv t` (LICS23 Fig. 2), at the type `τ₁ → … → τₙ → β`: an admitted machine with inputs `τs`
and the arguments of `β` computes `t` everywhere. -/
@[expose] def Adv (C : AdvClass M) {β : Ty B} (X : RV M (Ty.arrows τs β)) : Prop :=
  ∃ A : AdvMachine M τs β, C.mem A ∧ ∀ η ρ, X η ρ = A.eval η ρ.1

/-- `u⃗ ∼ v⃗` (LICS23 Fig. 2): every admitted machine returning a Boolean has negligible
advantage. -/
@[expose] def Indist (C : AdvClass M) (u v : VecRV M τs) : Prop :=
  ∀ A : Machine M τs .bool, C.mem A → negligible (advantage A.test u v)

variable (C : AdvClass M)

/-- The reduction of FA-Adv is admitted. -/
theorem adv_mem {τs₀ : List (Ty B)} {β γ : Ty B} {A : Machine M (Ty.arrows τs₀ β :: τs) γ}
    {g : AdvMachine M τs₀ β} (hA : C.mem A) (hg : C.mem g) : C.mem (A.adv g) :=
  C.subst_mem hA (C.rename_mem _ hg)

/-- The reduction of If is admitted. -/
theorem ite_mem {β : Ty B} {A : Machine M (a :: τs) β} (hA : C.mem A) : C.mem A.ite :=
  C.branch_mem (C.rename_mem _ hA) (C.rename_mem _ hA)

/-- The reductions of the case split are admitted. -/
theorem guard_mem (c : Bool) {A : Machine M τs .bool} (hA : C.mem A) : C.mem (A.guard c) := by
  cases c
  · exact C.branch_mem (C.const_mem false) hA
  · exact C.branch_mem hA (C.const_mem false)

end AdvClass

/-! ## Vectors of random variables -/

namespace VecRV

/-- FA-App on vectors: the first entry applied to the second. -/
@[expose] def app (u : VecRV M (.arrow a b :: a :: τs)) : VecRV M (b :: τs) :=
  fun η ρ => Env.cons (u η ρ _ .zero (u η ρ _ (.succ .zero))) (u η ρ).tail.tail

/-- Prepend a random variable. -/
@[expose] def cons (X : RV M τ) (u : VecRV M τs) : VecRV M (τ :: τs) :=
  fun η ρ => Env.cons (X η ρ) (u η ρ)

/-- Drop the first entry. -/
@[expose] def tail (u : VecRV M (τ :: τs)) : VecRV M τs := fun η ρ => (u η ρ).tail

/-- Duplicate the first entry. -/
@[expose] def dup (u : VecRV M (τ :: τs)) : VecRV M (τ :: τ :: τs) :=
  fun η ρ => Env.cons (u η ρ _ .zero) (u η ρ)

/-- The conditional of the first three entries. -/
@[expose] def ite (u : VecRV M (.bool :: a :: a :: τs)) : VecRV M (a :: τs) :=
  fun η ρ => Env.cons (cond (u η ρ _ .zero) (u η ρ _ (.succ .zero)) (u η ρ _ (.succ (.succ .zero))))
    (u η ρ).tail.tail.tail

/-- Reindex along a map of positions. -/
@[expose] def rename {τs' : List (Ty B)} (r : Renaming τs' τs) (u : VecRV M τs) : VecRV M τs' :=
  fun η ρ => Env.rename r (u η ρ)

end VecRV

/-! ## Concrete statements: each reduction keeps or bounds the advantage at every `η` -/

section Reductions

theorem advantage_app (A : Distinguisher M (b :: τs)) (u v : VecRV M (.arrow a b :: a :: τs)) :
    advantage A u.app v.app = advantage A.app u v := rfl

theorem advantage_fn (f : D.Fn τ) (A : Distinguisher M (τ :: τs)) (u v : VecRV M τs) :
    advantage A (VecRV.cons (fun η _ => M.fn η f) u) (VecRV.cons (fun η _ => M.fn η f) v) =
      advantage (A.fn f) u v := rfl

theorem advantage_adv (g : AttackerFn M τ) (A : Distinguisher M (τ :: τs)) (u v : VecRV M τs) :
    advantage A (VecRV.cons (fun η ρ => g η ρ.1) u) (VecRV.cons (fun η ρ => g η ρ.1) v) =
      advantage (A.adv g) u v := rfl

theorem advantage_ite (A : Distinguisher M (a :: τs)) (u v : VecRV M (.bool :: a :: a :: τs)) :
    advantage A u.ite v.ite = advantage A.ite u v := rfl

theorem advantage_rename {τs' : List (Ty B)} (r : Renaming τs' τs) (A : Distinguisher M τs')
    (u v : VecRV M τs) : advantage A (u.rename r) (v.rename r) = advantage (A.rename r) u v := rfl

/-- Changing a vector where it is rarely different changes an advantage by at most the
probability that it differs. -/
theorem advantage_le_add_prEvent_ne (A : Distinguisher M τs) (u u' v : VecRV M τs) (η : ℕ) :
    advantage A u v η ≤
      advantage A u' v η + Pr{let ρ ← $ᵗ (M.Tape η)}[u η ρ ≠ u' η ρ] := by
  have step : ∀ x y : VecRV M τs, (∀ ρ, x η ρ ≠ y η ρ → u η ρ ≠ u' η ρ) →
      Pr{let ρ ← $ᵗ (M.Tape η)}[A η (x η ρ) ρ.1 = true] ≤
        Pr{let ρ ← $ᵗ (M.Tape η)}[A η (y η ρ) ρ.1 = true] +
          Pr{let ρ ← $ᵗ (M.Tape η)}[u η ρ ≠ u' η ρ] := fun x y hxy =>
    (prEvent_le_prEvent_add_prEvent_and_not _ _ _).trans (add_le_add le_rfl
      (prEvent_mono _ _ _ fun ρ h => hxy ρ fun he => h.2 (he ▸ h.1)))
  refine (ENNReal.absDiff_triangle _
    (Pr{let ρ ← $ᵗ (M.Tape η)}[A η (u' η ρ) ρ.1 = true]) _).trans ?_
  rw [add_comm (advantage A u' v η)]
  exact add_le_add (ENNReal.absDiff_le_iff.2
    ⟨step u u' fun _ => id, step u' u fun _ h he => h he.symm⟩) le_rfl

/-- A test of a conditional splits along its condition:
`Pr[A(if b then x else y, u⃗)] = Pr[b ∧ A(x, u⃗)] + Pr[¬b ∧ A(y, u⃗)]`. -/
private theorem prEvent_cons_cond (A : Distinguisher M (a :: τs)) (b : RV M .bool)
    (x y : RV M a) (u : VecRV M τs) (η : ℕ) :
    Pr{let ρ ← $ᵗ (M.Tape η)}[A η (VecRV.cons (fun η ρ => cond (b η ρ) (x η ρ) (y η ρ)) u η ρ)
        ρ.1 = true] =
      Pr{let ρ ← $ᵗ (M.Tape η)}[A.guard true η (VecRV.cons b (VecRV.cons x u) η ρ) ρ.1 =
        true] +
      Pr{let ρ ← $ᵗ (M.Tape η)}[A.guard false η (VecRV.cons b (VecRV.cons y u) η ρ) ρ.1 =
        true] := by
  rw [prEvent_eq_prEvent_and_add_prEvent_and_not _ _ fun ρ => b η ρ = true]
  congr 1 <;> refine prEvent_congr _ _ _ fun ρ => ?_ <;>
    simp only [VecRV.cons, Distinguisher.guard] <;> cases b η ρ <;> simp <;> rfl

/-- The case split at one `η`: the advantage against two conditionals is at most the sum of the
advantages of the named reductions `A.guard true` and `A.guard false` against the two premises.
The factor is one. -/
theorem advantage_cons_cond_le (A : Distinguisher M (a :: τs)) (b b' : RV M .bool)
    (x y x' y' : RV M a) (u v : VecRV M τs) (η : ℕ) :
    advantage A (VecRV.cons (fun η ρ => cond (b η ρ) (x η ρ) (y η ρ)) u)
        (VecRV.cons (fun η ρ => cond (b' η ρ) (x' η ρ) (y' η ρ)) v) η ≤
      advantage (A.guard true) (VecRV.cons b (VecRV.cons x u))
          (VecRV.cons b' (VecRV.cons x' v)) η +
        advantage (A.guard false) (VecRV.cons b (VecRV.cons y u))
          (VecRV.cons b' (VecRV.cons y' v)) η := by
  simp only [advantage, prEvent_cons_cond]
  exact ENNReal.absDiff_add_add_le _ _ _ _

end Reductions

/-! ## Laws of indistinguishability -/

namespace AdvClass

variable {C : AdvClass M} {u v w : VecRV M τs}

/-- Refl. -/
theorem Indist.refl (u : VecRV M τs) : C.Indist u u :=
  fun _ _ => negligible_of_zero fun _ => ENNReal.absDiff_self _

/-- Sym. -/
theorem Indist.symm (h : C.Indist u v) : C.Indist v u :=
  fun A hA => negligible_of_le (fun _ => le_of_eq (ENNReal.absDiff_comm _ _)) (h A hA)

/-- Trans: the advantage against the ends is at most the sum of the two advantages. -/
theorem Indist.trans (h₁ : C.Indist u v) (h₂ : C.Indist v w) : C.Indist u w :=
  fun A hA => negligible_of_le (fun _ => ENNReal.absDiff_triangle _ _ _)
    (negligible_add (h₁ A hA) (h₂ A hA))

/-- FA-App, by the reduction `Machine.app`, for an argument of a Boolean or base type. -/
theorem Indist.app (ha : a.IsGround) {u v : VecRV M (.arrow a b :: a :: τs)} (h : C.Indist u v) :
    C.Indist u.app v.app := fun A hA => by
  rw [advantage_app, ← Machine.test_app ha]
  exact h _ (C.app_mem ha hA)

/-- FA-Fn, by the reduction `Machine.fn`. -/
theorem Indist.fn (f : D.Fn τ) (h : C.Indist u v) :
    C.Indist (VecRV.cons (fun η _ => M.fn η f) u) (VecRV.cons (fun η _ => M.fn η f) v) :=
  fun A hA => by
  rw [advantage_fn, ← Machine.test_fn]
  exact h _ (C.fn_mem f hA)

/-- FA-Adv, by the reduction `Machine.adv` at the machine that `adv` provides. -/
theorem Indist.adv {τs₀ : List (Ty B)} {β : Ty B} {X : RV M (Ty.arrows τs₀ β)} (hX : C.Adv X)
    (h : C.Indist u v) : C.Indist (VecRV.cons X u) (VecRV.cons X v) := by
  obtain ⟨g, hg, hXg⟩ := hX
  obtain rfl : X = fun η ρ => g.eval η ρ.1 := funext fun η => funext (hXg η)
  intro A hA
  rw [advantage_adv, ← Machine.test_adv]
  exact h _ (C.adv_mem hA hg)

/-- If, by the reduction `Machine.ite`. -/
theorem Indist.ite {u v : VecRV M (.bool :: a :: a :: τs)} (h : C.Indist u v) :
    C.Indist u.ite v.ite := fun A hA => by
  rw [advantage_ite, ← Machine.test_ite]
  exact h _ (C.ite_mem hA)

/-- Perm, by the reduction `Machine.rename`. -/
theorem Indist.rename {τs' : List (Ty B)} (r : Renaming τs' τs) (h : C.Indist u v) :
    C.Indist (u.rename r) (v.rename r) := fun A hA => by
  rw [advantage_rename, ← Machine.test_rename]
  exact h _ (C.rename_mem r hA)

/-- Restr: `Distinguisher.rename` at the renaming that skips the first position. -/
theorem Indist.tail {u v : VecRV M (τ :: τs)} (h : C.Indist u v) : C.Indist u.tail v.tail :=
  h.rename fun _ x => .succ x

/-- Dup: `Distinguisher.rename` at the renaming that repeats the first position. -/
theorem Indist.dup {u v : VecRV M (τ :: τs)} (h : C.Indist u v) : C.Indist u.dup v.dup := by
  have hu : ∀ w : VecRV M (τ :: τs),
      w.dup = w.rename (Env.cons .zero fun _ x => x : Renaming (τ :: τ :: τs) (τ :: τs)) :=
    fun w => by funext η ρ σ x; cases x <;> rfl
  rw [hu u, hu v]
  exact h.rename _

/-- Case split (LICS23's G.Case-Study:ITE), by the reductions `Machine.guard true` and
`Machine.guard false`: if `b, x, u⃗ ∼ b', x', v⃗` and `b, y, u⃗ ∼ b', y', v⃗`, then
`if b then x else y, u⃗ ∼ if b' then x' else y', v⃗`. -/
theorem Indist.caseStudy {b b' : RV M .bool} {x y x' y' : RV M a} {u v : VecRV M τs}
    (h₁ : C.Indist (VecRV.cons b (VecRV.cons x u)) (VecRV.cons b' (VecRV.cons x' v)))
    (h₂ : C.Indist (VecRV.cons b (VecRV.cons y u)) (VecRV.cons b' (VecRV.cons y' v))) :
    C.Indist (VecRV.cons (fun η ρ => cond (b η ρ) (x η ρ) (y η ρ)) u)
      (VecRV.cons (fun η ρ => cond (b' η ρ) (x' η ρ) (y' η ρ)) v) := fun A hA =>
  negligible_of_le (advantage_cons_cond_le A.test b b' x y x' y' u v)
    (negligible_add (Machine.test_guard true A ▸ h₁ _ (C.guard_mem true hA))
      (Machine.test_guard false A ▸ h₂ _ (C.guard_mem false hA)))

/-- BC14's If1, from the case split with both right-hand branches `z`: if `b, x, u⃗ ∼ b', z, v⃗`
and `b, y, u⃗ ∼ b', z, v⃗`, then `if b then x else y, u⃗ ∼ z, v⃗`. -/
theorem Indist.if1 {b b' : RV M .bool} {x y z : RV M a} {u v : VecRV M τs}
    (h₁ : C.Indist (VecRV.cons b (VecRV.cons x u)) (VecRV.cons b' (VecRV.cons z v)))
    (h₂ : C.Indist (VecRV.cons b (VecRV.cons y u)) (VecRV.cons b' (VecRV.cons z v))) :
    C.Indist (VecRV.cons (fun η ρ => cond (b η ρ) (x η ρ) (y η ρ)) u) (VecRV.cons z v) := by
  have h := Indist.caseStudy (x' := z) (y' := z) h₁ h₂
  rwa [show (fun η ρ => cond (b' η ρ) (z η ρ) (z η ρ)) = z from
    funext fun _ => funext fun _ => Bool.cond_self _ _] at h

/-- Rewriting under an overwhelming equality: if `u` and `u'` differ with negligible probability,
`u` is indistinguishable from whatever `u'` is. -/
theorem Indist.of_negligible_ne {u' : VecRV M τs}
    (hne : negligible fun η => Pr{let ρ ← $ᵗ (M.Tape η)}[u η ρ ≠ u' η ρ]) (h : C.Indist u' v) :
    C.Indist u v :=
  fun A hA => negligible_of_le (fun η => advantage_le_add_prEvent_ne A.test u u' v η)
    (negligible_add (h A hA) hne)

end AdvClass

end Interop.Squirrel
