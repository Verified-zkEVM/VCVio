/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.Coinductive.PolyTime
import ToMathlib.Computability.PolyTimeTM

/-!
# Closure Properties of Polynomial-Time Adversaries

This file provides closure of `PolyTimeAdversary` — and hence of
`OracleComp.IsPolyTime` — under precomposition with a pure input map on per-parameter
finite input types: `PolyTimeAdversary.precomp` reuses the machine family unchanged
except for its initialization, which becomes `init ∘ f` with machine witness discharged
by `Computability.EncPolyTime.ofFintype`.

This is the machine content of the standard "the reduction runs in polynomial time
because the given adversary does" step, for reductions that only reshape their input
before invoking the adversary (e.g. discarding auxiliary state, or projecting one
component of a pair).

Two observations make the reuse cheap:

* The table machine's running time depends only on the encoded *output* length
  (`EncPolyTime.time_ofFintype_eval_le`), and the output of the new initialization is a
  round-zero machine state, whose encoded length the existing invariant
  `encState_length_le` already bounds by `sizeBound`. The handler family `h₀` merely
  instantiates that invariant at round zero, where the state does not depend on the
  handler.
* No field of `PolyTimeAdversary` constrains the length of *input* encodings (inputs
  are handler-side data), so the new input encoding is unconstrained.

As with all `ofFintype` witnesses, the table machine's description grows with the input
type's cardinality; only round counts, state sizes, and per-step times are certified
polynomial, in line with the non-uniform adversary model in the design notes of
`PolyTimeAdversary`.
-/

open OracleSpec Computability

variable {ι : Type} [DecidableEq ι]

omit [DecidableEq ι] in
/-- The probabilistic run of a machine ignores the initialization field: replacing
`init` (possibly changing the input type) leaves `runK` unchanged from any state. -/
theorem OracleMachine.runK_setInit {spec : OracleSpec.{0, 0} ι} {α α' β : Type}
    (M : OracleMachine spec α β) (g : α' → M.State) (H : ProbHandler spec) (k : ℕ)
    (s : M.State) :
    OracleMachine.runK ⟨M.toStrategy, g, M.output⟩ H k s = M.runK H k s := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
    cases hb : M.output s with
    | some b =>
      rw [M.runK_succ_of_output_eq_some H hb]
      exact OracleMachine.runK_succ_of_output_eq_some
        (M := ⟨M.toStrategy, g, M.output⟩) H hb k
    | none =>
      rw [M.runK_succ_of_output_eq_none H hb,
        OracleMachine.runK_succ_of_output_eq_none
          (M := ⟨M.toStrategy, g, M.output⟩) H hb k]
      exact bind_congr fun s' => ih s'

namespace PolyTimeAdversary

variable {spec : ℕ → OracleSpec.{0, 0} ι} {α β γ : ℕ → Type}

/-- Precompose a polynomial-time adversary with a pure input map on per-parameter
finite input types. The machine family is reused with only its initialization changed
to `fun x => init (f n x)`, witnessed by a finite table; every bound except the
initialization time is inherited verbatim, and that one is absorbed by enlarging
`stepTime` with an explicit linear-plus-`sizeBound` summand. -/
noncomputable def precomp (D : PolyTimeAdversary spec α β)
    (f : (n : ℕ) → γ n → α n) [∀ n, Fintype (γ n)]
    (encIn' : (n : ℕ) → FinEncoding (γ n))
    (h₀ : (n : ℕ) → OracleHandler (spec n)) :
    PolyTimeAdversary spec γ β where
  M n := { D.M n with init := fun x => (D.M n).init (f n x) }
  steps := D.steps
  stable n := D.stable n
  steady n h x := D.steady n h (f n x)
  encState := D.encState
  encIn := encIn'
  encOut := D.encOut
  encIface := D.encIface
  sizeBound := D.sizeBound
  encState_length_le n h x j hj := D.encState_length_le n h (f n x) j hj
  initTM n := .ofFintype ((encIn' n).boolify) ((encIn' n).boolify_injective)
    ((D.encState n).boolify) fun x => (D.M n).init (f n x)
  exposeTM n := D.exposeTM n
  updateTM n := D.updateTM n
  outputTM n := D.outputTM n
  stepTime := D.stepTime + (.X + D.sizeBound + .C 1)
  initTM_time_le n k := by
    have hB : ∀ x : γ n,
        (((D.encState n).boolify) ((D.M n).init (f n x))).length ≤
          D.sizeBound.eval n := fun x => by
      simpa using D.encState_length_le n (h₀ n) (f n x) 0 (Nat.zero_le _)
    refine (EncPolyTime.time_ofFintype_eval_le ((encIn' n).boolify_injective) hB k).trans ?_
    have hmono : D.sizeBound.eval n ≤ D.sizeBound.eval (n + k) :=
      Polynomial.eval_le_eval (Nat.le_add_right n k)
    simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
    omega
  exposeTM_time_le n k := (D.exposeTM_time_le n k).trans (by
    simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
    omega)
  updateTM_time_le n k := (D.updateTM_time_le n k).trans (by
    simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
    omega)
  outputTM_time_le n k := (D.outputTM_time_le n k).trans (by
    simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
    omega)

variable (f : (n : ℕ) → γ n → α n) [∀ n, Fintype (γ n)]
  (encIn' : (n : ℕ) → FinEncoding (γ n)) (h₀ : (n : ℕ) → OracleHandler (spec n))

@[simp] theorem precomp_M (D : PolyTimeAdversary spec α β) (n : ℕ) :
    (D.precomp f encIn' h₀).M n =
      ⟨(D.M n).toStrategy, fun x => (D.M n).init (f n x), (D.M n).output⟩ := rfl

@[simp] theorem precomp_steps (D : PolyTimeAdversary spec α β) :
    (D.precomp f encIn' h₀).steps = D.steps := rfl

/-- The precomposed adversary implements the precomposed program family: the machine
run is unchanged except that it starts from `init (f n x)`. -/
theorem precomp_implements {D : PolyTimeAdversary spec α β}
    {oa : (n : ℕ) → α n → OracleComp (spec n) (β n)} (h : D.Implements oa) :
    (D.precomp f encIn' h₀).Implements fun n x => oa n (f n x) := by
  intro n H x
  rw [precomp_steps, precomp_M]
  exact (OracleMachine.runK_setInit (D.M n) _ H _ _).trans (h n H (f n x))

end PolyTimeAdversary

/-- `OracleComp.IsPolyTime` is closed under precomposition with a pure map on
per-parameter finite input types: the standard "the reduction is polynomial time since
the adversary is" step for input-reshaping reductions. -/
theorem OracleComp.IsPolyTime.precomp {spec : ℕ → OracleSpec.{0, 0} ι}
    {α β γ : ℕ → Type} {oa : (n : ℕ) → α n → OracleComp (spec n) (β n)}
    (hoa : OracleComp.IsPolyTime oa) (f : (n : ℕ) → γ n → α n) [∀ n, Finite (γ n)]
    (encIn' : (n : ℕ) → FinEncoding (γ n))
    (h₀ : (n : ℕ) → OracleHandler (spec n)) :
    OracleComp.IsPolyTime fun n x => oa n (f n x) := by
  letI : ∀ n, Fintype (γ n) := fun n => Fintype.ofFinite (γ n)
  obtain ⟨D, hImp, hqb⟩ := hoa
  exact ⟨D.precomp f encIn' h₀, PolyTimeAdversary.precomp_implements f encIn' h₀ hImp,
    fun n x => hqb n (f n x)⟩
