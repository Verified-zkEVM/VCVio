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

namespace Computability.EncPolyTime

/-- The finite-table witness that `Option.map g` is polynomial-time computable relative to the
boolified option encodings, for a function `g` on a **finite** domain. This is the post-map witness
composed onto an adversary's `outputTM` by `PolyTimeAdversary.mapComp`: the domain finiteness is on
the adversary's *output* type, never on its state. -/
noncomputable def optionMap {β γ : Type} [Fintype β] (encβ : FinEncoding β)
    (encγ : FinEncoding γ) (g : β → γ) :
    EncPolyTime ((finEncodingOption encβ).boolify) ((finEncodingOption encγ).boolify)
      (Option.map g) :=
  EncPolyTime.ofFintype ((finEncodingOption encβ).boolify)
    ((finEncodingOption encβ).boolify_injective) ((finEncodingOption encγ).boolify) (Option.map g)

/-- The `optionMap` table machine runs in time linear in the input plus its longest encoded output:
given a pointwise bound `B` on the boolified output lengths, evaluation at `k` is at most
`k + (B + 1)`. -/
theorem time_optionMap_eval_le {β γ : Type} [Fintype β] (encβ : FinEncoding β)
    (encγ : FinEncoding γ) (g : β → γ) {B : ℕ}
    (hB : ∀ x : Option β, ((finEncodingOption encγ).boolify (Option.map g x)).length ≤ B) (k : ℕ) :
    (optionMap encβ encγ g).time.eval k ≤ k + (B + 1) :=
  EncPolyTime.time_ofFintype_eval_le ((finEncodingOption encβ).boolify_injective) hB k

end Computability.EncPolyTime

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

omit [DecidableEq ι] in
/-- The probabilistic run of a machine commutes with post-composing a pure map on the
read-out: replacing `output` by `Option.map g ∘ output` maps every run's result by `g`. -/
theorem OracleMachine.runK_setOutput {spec : OracleSpec.{0, 0} ι} {α β γ : Type}
    (M : OracleMachine spec α β) (g : β → γ) (H : ProbHandler spec) (k : ℕ) (s : M.State) :
    OracleMachine.runK ⟨M.toStrategy, M.init, fun s => (M.output s).map g⟩ H k s
      = Option.map g <$> M.runK H k s := by
  induction k generalizing s with
  | zero => simp only [OracleMachine.runK_zero, map_pure]
  | succ k ih =>
    cases hb : M.output s with
    | some b =>
      rw [OracleMachine.runK_succ_of_output_eq_some
            (M := ⟨M.toStrategy, M.init, fun s => (M.output s).map g⟩) H
            (show (⟨M.toStrategy, M.init, fun s => (M.output s).map g⟩ :
              OracleMachine spec α γ).output s = some (g b) by simp [hb]) k,
        M.runK_succ_of_output_eq_some H hb]
      simp
    | none =>
      rw [OracleMachine.runK_succ_of_output_eq_none
            (M := ⟨M.toStrategy, M.init, fun s => (M.output s).map g⟩) H (by simp [hb]) k,
        M.runK_succ_of_output_eq_none H hb, map_bind]
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

omit [∀ n, Fintype (γ n)] in
/-- Post-compose a polynomial-time adversary with a pure output map. The machine family is
reused with only its read-out changed to `Option.map (g n) ∘ output`; the new `outputTM` is
a finite table over the (finite) state, so its running time is bounded by the caller's
`Sγ` on the mapped output length. Requires the machine's state type to be a `Fintype` — the
finite-state constructions (`coinFold`, pure-function adversaries) provide this. -/
noncomputable def map (D : PolyTimeAdversary spec α β) (g : (n : ℕ) → β n → γ n)
    [∀ n, Fintype (D.M n).State] (encOut' : (n : ℕ) → FinEncoding (γ n)) (Sγ : Polynomial ℕ)
    (hbound : ∀ (n : ℕ) (s : (D.M n).State),
      ((finEncodingOption (encOut' n)).boolify (((D.M n).output s).map (g n))).length
        ≤ Sγ.eval n) :
    PolyTimeAdversary spec α γ where
  M n := ⟨(D.M n).toStrategy, (D.M n).init, fun s => ((D.M n).output s).map (g n)⟩
  steps := D.steps
  stable n := by
    intro s c hc r
    obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp hc
    exact Option.map_eq_some_iff.mpr ⟨b, (D.stable n) hb r, rfl⟩
  steady n h x := by simpa only [OracleMachine.SteadyBy, Option.isSome_map] using D.steady n h x
  encState := D.encState
  encIn := D.encIn
  encOut := encOut'
  encIface := D.encIface
  sizeBound := D.sizeBound
  encState_length_le := D.encState_length_le
  initTM := D.initTM
  exposeTM := D.exposeTM
  updateTM := D.updateTM
  outputTM n := .ofFintype ((D.encState n).boolify) ((D.encState n).boolify_injective)
    ((finEncodingOption (encOut' n)).boolify) fun s => ((D.M n).output s).map (g n)
  stepTime := D.stepTime + (.X + Sγ + .C 1)
  initTM_time_le n k := (D.initTM_time_le n k).trans (by
    simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]; omega)
  exposeTM_time_le n k := (D.exposeTM_time_le n k).trans (by
    simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]; omega)
  updateTM_time_le n k := (D.updateTM_time_le n k).trans (by
    simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]; omega)
  outputTM_time_le n k := by
    refine (EncPolyTime.time_ofFintype_eval_le ((D.encState n).boolify_injective)
      (hbound n) k).trans ?_
    have hmono : Sγ.eval n ≤ Sγ.eval (n + k) := Polynomial.eval_le_eval (Nat.le_add_right n k)
    simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
    omega

omit [∀ n, Fintype (γ n)] in
@[simp] theorem map_M (D : PolyTimeAdversary spec α β) (g : (n : ℕ) → β n → γ n)
    [∀ n, Fintype (D.M n).State] (encOut' : (n : ℕ) → FinEncoding (γ n)) (Sγ : Polynomial ℕ)
    (hbound : ∀ (n : ℕ) (s : (D.M n).State),
      ((finEncodingOption (encOut' n)).boolify (((D.M n).output s).map (g n))).length ≤ Sγ.eval n)
    (n : ℕ) :
    (D.map g encOut' Sγ hbound).M n =
      ⟨(D.M n).toStrategy, (D.M n).init, fun s => ((D.M n).output s).map (g n)⟩ := rfl

omit [∀ n, Fintype (γ n)] in
@[simp] theorem map_steps (D : PolyTimeAdversary spec α β) (g : (n : ℕ) → β n → γ n)
    [∀ n, Fintype (D.M n).State] (encOut' : (n : ℕ) → FinEncoding (γ n)) (Sγ : Polynomial ℕ)
    (hbound : ∀ (n : ℕ) (s : (D.M n).State),
      ((finEncodingOption (encOut' n)).boolify (((D.M n).output s).map (g n))).length ≤ Sγ.eval n) :
    (D.map g encOut' Sγ hbound).steps = D.steps := rfl

omit [∀ n, Fintype (γ n)] in
/-- The mapped adversary implements the mapped program family: the machine run is unchanged
except that its result is post-composed with `g`. -/
theorem map_implements {D : PolyTimeAdversary spec α β} (g : (n : ℕ) → β n → γ n)
    [∀ n, Fintype (D.M n).State] (encOut' : (n : ℕ) → FinEncoding (γ n)) (Sγ : Polynomial ℕ)
    (hbound : ∀ (n : ℕ) (s : (D.M n).State),
      ((finEncodingOption (encOut' n)).boolify (((D.M n).output s).map (g n))).length ≤ Sγ.eval n)
    {oa : (n : ℕ) → α n → OracleComp (spec n) (β n)} (h : D.Implements oa) :
    (D.map g encOut' Sγ hbound).Implements fun n x => g n <$> oa n x := by
  intro n H x
  rw [map_steps, map_M, OracleMachine.runK_setOutput, h n H x]
  simp [simulateQ_map, Functor.map_map, Function.comp]

/-! ### Output-map on an abstract adversary via composition

`map` above needs the machine's *state* to be a `Fintype` (it retables the whole output over the
state). `mapComp` instead **composes** the adversary's own `outputTM` with the
`EncPolyTime.optionMap` witness for the post-map, via `EncPolyTime.comp`. The finiteness required is
only on the adversary's
*output* type `β` (so `optionMap`'s table is over the finite `Option (β n)`), never on the state —
which is exactly what lets it fire on an abstract `OracleComp.IsPolyTime` hypothesis, whose machine
state carries only a `FinEncoding`. -/

omit [∀ n, Fintype (γ n)] in
/-- Post-compose a polynomial-time adversary with a pure output map, from a **supplied** encoded
poly-time witness `wit n` for `Option.map (g n)` and a linear time bound on it. The machine is
reused with its read-out post-composed with `Option.map (g n)`; the new `outputTM` is
`(D.outputTM n).comp (wit n)`, its time bound from `EncPolyTime.comp_time_eval`. Taking the witness
abstractly (rather than rebuilding it here) is essential: it keeps the `outputTM` field and its
`_time_le` proof referring to the *same* term, avoiding the `Fintype`-instance mismatch that a
re-synthesized witness triggers. No finiteness of the state — the point of this over `map`. The
caller (`IsPolyTime.map`) supplies `EncPolyTime.optionMap` for a finite output type. -/
noncomputable def mapComp (D : PolyTimeAdversary spec α β) (g : (n : ℕ) → β n → γ n)
    (encOut' : (n : ℕ) → FinEncoding (γ n))
    (wit : (n : ℕ) → EncPolyTime ((finEncodingOption (D.encOut n)).boolify)
      ((finEncodingOption (encOut' n)).boolify) (Option.map (g n)))
    (Sγ : Polynomial ℕ) (hwit : ∀ n k, (wit n).time.eval k ≤ k + (Sγ.eval n + 1)) :
    PolyTimeAdversary spec α γ where
  M n := ⟨(D.M n).toStrategy, (D.M n).init, fun s => ((D.M n).output s).map (g n)⟩
  steps := D.steps
  stable n := by
    intro s c hc r
    obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp hc
    exact Option.map_eq_some_iff.mpr ⟨b, (D.stable n) hb r, rfl⟩
  steady n h x := by simpa only [OracleMachine.SteadyBy, Option.isSome_map] using D.steady n h x
  encState := D.encState
  encIn := D.encIn
  encOut := encOut'
  encIface := D.encIface
  sizeBound := D.sizeBound
  encState_length_le := D.encState_length_le
  initTM := D.initTM
  exposeTM := D.exposeTM
  updateTM := D.updateTM
  outputTM n := (D.outputTM n).comp (wit n)
  stepTime := 2 * D.stepTime + (.X + Sγ + .C 2)
  initTM_time_le n k := (D.initTM_time_le n k).trans (by
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X,
      Polynomial.eval_C]; omega)
  exposeTM_time_le n k := (D.exposeTM_time_le n k).trans (by
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X,
      Polynomial.eval_C]; omega)
  updateTM_time_le n k := (D.updateTM_time_le n k).trans (by
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X,
      Polynomial.eval_C]; omega)
  outputTM_time_le n k := by
    show Polynomial.eval k ((D.outputTM n).comp (wit n)).time ≤ _
    rw [EncPolyTime.comp_time_eval]
    have h1 : (D.outputTM n).time.eval k ≤ D.stepTime.eval (n + k) := D.outputTM_time_le n k
    have h2 := hwit n (1 + k + (D.outputTM n).time.eval k)
    have hmono : Sγ.eval n ≤ Sγ.eval (n + k) := Polynomial.eval_le_eval (Nat.le_add_right n k)
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X,
      Polynomial.eval_C]
    omega

omit [∀ n, Fintype (γ n)] in
@[simp] theorem mapComp_M (D : PolyTimeAdversary spec α β) (g : (n : ℕ) → β n → γ n)
    (encOut' : (n : ℕ) → FinEncoding (γ n))
    (wit : (n : ℕ) → EncPolyTime ((finEncodingOption (D.encOut n)).boolify)
      ((finEncodingOption (encOut' n)).boolify) (Option.map (g n)))
    (Sγ : Polynomial ℕ) (hwit : ∀ n k, (wit n).time.eval k ≤ k + (Sγ.eval n + 1)) (n : ℕ) :
    (D.mapComp g encOut' wit Sγ hwit).M n =
      ⟨(D.M n).toStrategy, (D.M n).init, fun s => ((D.M n).output s).map (g n)⟩ := rfl

omit [∀ n, Fintype (γ n)] in
@[simp] theorem mapComp_steps (D : PolyTimeAdversary spec α β) (g : (n : ℕ) → β n → γ n)
    (encOut' : (n : ℕ) → FinEncoding (γ n))
    (wit : (n : ℕ) → EncPolyTime ((finEncodingOption (D.encOut n)).boolify)
      ((finEncodingOption (encOut' n)).boolify) (Option.map (g n)))
    (Sγ : Polynomial ℕ) (hwit : ∀ n k, (wit n).time.eval k ≤ k + (Sγ.eval n + 1)) :
    (D.mapComp g encOut' wit Sγ hwit).steps = D.steps := rfl

omit [∀ n, Fintype (γ n)] in
/-- The `mapComp` adversary implements the output-mapped program family, identically to `map`
(the machine — hence its run — is the same; only the `outputTM` witness differs). -/
theorem mapComp_implements {D : PolyTimeAdversary spec α β} (g : (n : ℕ) → β n → γ n)
    (encOut' : (n : ℕ) → FinEncoding (γ n))
    (wit : (n : ℕ) → EncPolyTime ((finEncodingOption (D.encOut n)).boolify)
      ((finEncodingOption (encOut' n)).boolify) (Option.map (g n)))
    (Sγ : Polynomial ℕ) (hwit : ∀ n k, (wit n).time.eval k ≤ k + (Sγ.eval n + 1))
    {oa : (n : ℕ) → α n → OracleComp (spec n) (β n)} (h : D.Implements oa) :
    (D.mapComp g encOut' wit Sγ hwit).Implements fun n x => g n <$> oa n x := by
  intro n H x
  rw [mapComp_steps, mapComp_M, OracleMachine.runK_setOutput, h n H x]
  simp [simulateQ_map, Functor.map_map, Function.comp]

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

/-- `OracleComp.IsPolyTime` for a pure output map, from a finite-state adversary bundle
implementing the base family: `g n <$> oa n x` is polynomial time. The finite-state
constructions (`coinFoldAdversary`, pure-function adversaries) expose exactly such a bundle,
so this is the compositional "then map the result" primitive for them. -/
theorem OracleComp.IsPolyTime.map_of_adversary {spec : ℕ → OracleSpec.{0, 0} ι}
    {α β γ : ℕ → Type} (D : PolyTimeAdversary spec α β) (g : (n : ℕ) → β n → γ n)
    [∀ n, Fintype (D.M n).State] (encOut' : (n : ℕ) → FinEncoding (γ n)) (Sγ : Polynomial ℕ)
    (hbound : ∀ (n : ℕ) (s : (D.M n).State),
      ((finEncodingOption (encOut' n)).boolify (((D.M n).output s).map (g n))).length ≤ Sγ.eval n)
    {oa : (n : ℕ) → α n → OracleComp (spec n) (β n)} (hImp : D.Implements oa)
    (hqb : ∀ n x, OracleComp.IsTotalQueryBound (oa n x) (D.steps.eval n)) :
    OracleComp.IsPolyTime fun n x => g n <$> oa n x :=
  ⟨D.map g encOut' Sγ hbound, D.map_implements g encOut' Sγ hbound hImp, fun n x => by
    simp only [PolyTimeAdversary.map_steps]
    rw [map_eq_bind_pure_comp]
    exact isTotalQueryBound_bind (n₂ := 0) (hqb n x) fun _ => trivial⟩

/-- `OracleComp.IsPolyTime` is closed under a pure **output** map on per-parameter **finite** output
types — *without* the finite-state requirement of `map_of_adversary`, so it fires on an abstract
`IsPolyTime` hypothesis. The witness for `Option.map (g n)` is the finite table
`EncPolyTime.optionMap` over the finite `Option (β n)`, composed onto the (abstract) adversary's own
`outputTM` via `EncPolyTime.comp`. This is the "then post-process the Boolean result" primitive that
reductions such as output negation (`!`) and challenge comparison (`· == b`) need. -/
theorem OracleComp.IsPolyTime.map {spec : ℕ → OracleSpec.{0, 0} ι}
    {α β γ : ℕ → Type} {oa : (n : ℕ) → α n → OracleComp (spec n) (β n)}
    (hoa : OracleComp.IsPolyTime oa) (g : (n : ℕ) → β n → γ n) [∀ n, Finite (β n)]
    (encOut' : (n : ℕ) → FinEncoding (γ n)) (Sγ : Polynomial ℕ)
    (hbound : ∀ (n : ℕ) (x : Option (β n)),
      ((finEncodingOption (encOut' n)).boolify (Option.map (g n) x)).length ≤ Sγ.eval n) :
    OracleComp.IsPolyTime fun n x => g n <$> oa n x := by
  letI : ∀ n, Fintype (β n) := fun n => Fintype.ofFinite (β n)
  obtain ⟨D, hImp, hqb⟩ := hoa
  refine ⟨D.mapComp g encOut'
      (fun n => EncPolyTime.optionMap (D.encOut n) (encOut' n) (g n)) Sγ
      (fun n k => EncPolyTime.time_optionMap_eval_le (D.encOut n) (encOut' n) (g n) (hbound n) k),
    D.mapComp_implements g encOut' _ Sγ _ hImp, fun n x => by
      simp only [PolyTimeAdversary.mapComp_steps]
      rw [map_eq_bind_pure_comp]
      exact isTotalQueryBound_bind (n₂ := 0) (hqb n x) fun _ => trivial⟩
