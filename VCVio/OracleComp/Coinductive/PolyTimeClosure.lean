/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.Coinductive.PolyTime

/-!
# Closure Properties of Polynomial-Time Adversaries

Closure of `MachineAdversary` — and hence of `OracleComp.IsPolyTime` — under input
precomposition and output maps, at pinned canonical boundaries:

* `MachineAdversary.precomp` / `IsPolyTime.precomp`: precompose with a pure input map
  on per-parameter input types of polynomially bounded cardinality. The machine family
  is reused with only its initialization changed to `init ∘ f`, witnessed by a finite
  table; the cardinality bound is what keeps the table within the advice budget —
  precomposition on a superpolynomially large input type (e.g. bitstring ciphertexts)
  is *not* closed and needs a real projection machine.
* `MachineAdversary.mapComp`: post-compose the readout with a supplied uniform machine
  family for `Option.map g` — the general engine; all time and size accounting is
  `Computability.EncPolyTimeFam.comp`.
* `EncPolyTimeFam.optionMap` / `IsPolyTime.map`: the output-map closure on an
  **abstract** `IsPolyTime` hypothesis, for finite output types of polynomially
  bounded cardinality. This is derivable *because* the output boundary is canonical:
  the post-map table reads the pinned fixed-width output encoding, whose lengths are
  known — with existential output encodings (the pre-canonicalization model) no such
  table could be bounded, which was both a compositionality wall and a soundness leak.

The remaining missing closure is sequential composition (`bind`), which needs the
two-phase machine construction; with canonical boundaries its statement is finally
well-formed (the mid boundary is shared by construction).
-/

open OracleSpec Computability

variable {ι : Type} [DecidableEq ι]

/-- `IsPolyTime` transports along pointwise program equality: a family equal to a
polynomial-time family is polynomial time. Lets a call site name its program directly
and bridge to a combinator's canonical form. -/
theorem OracleComp.IsPolyTime.congr {spec : ℕ → OracleSpec.{0, 0} ι}
    {α β : ℕ → Type} {bd : BoundaryData spec α β}
    {oa oa' : (n : ℕ) → α n → OracleComp (spec n) (β n)} (h : ∀ n x, oa n x = oa' n x)
    (hp : OracleComp.IsPolyTime bd oa) : OracleComp.IsPolyTime bd oa' :=
  (funext fun n => funext fun x => h n x : oa = oa') ▸ hp

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

namespace MachineAdversary

variable {spec : ℕ → OracleSpec.{0, 0} ι} {α β γ : ℕ → Type} {bd : BoundaryData spec α β}

/-- Precompose an adversary with a pure input map on per-parameter finite input types
of polynomially bounded cardinality. The machine family is reused with only its
initialization changed to `init ∘ f`, witnessed by a finite table; the table stays
within the advice budget because the new inputs are canonically fixed-width and the
state encoding is polynomially bounded over *all* states. -/
noncomputable def precomp (D : MachineAdversary bd)
    (f : (n : ℕ) → γ n → α n) [∀ n, Fintype (γ n)] (eIn' : BitEncFam γ)
    (cardIn : Polynomial ℕ) (hcard : ∀ n, Fintype.card (γ n) ≤ cardIn.eval n) :
    MachineAdversary (bd.withIn eIn') where
  M n := { D.M n with init := fun x => (D.M n).init (f n x) }
  steps := D.steps
  stable n := D.stable n
  state := D.state
  initF := .ofFintype eIn'.enc_injective (fun n x => (D.M n).init (f n x))
    cardIn hcard eIn'.widBound
    (fun n x => (eIn'.len_eq n x).le.trans (eIn'.wid_le n))
    D.state.bound (fun n _ => D.state.len_le n _)
  exposeF := D.exposeF
  updateF := D.updateF
  outputF := D.outputF

@[simp] theorem precomp_M (D : MachineAdversary bd) (f : (n : ℕ) → γ n → α n)
    [∀ n, Fintype (γ n)] (eIn' : BitEncFam γ) (cardIn : Polynomial ℕ)
    (hcard : ∀ n, Fintype.card (γ n) ≤ cardIn.eval n) (n : ℕ) :
    (D.precomp f eIn' cardIn hcard).M n =
      ⟨(D.M n).toStrategy, fun x => (D.M n).init (f n x), (D.M n).output⟩ := rfl

@[simp] theorem precomp_steps (D : MachineAdversary bd) (f : (n : ℕ) → γ n → α n)
    [∀ n, Fintype (γ n)] (eIn' : BitEncFam γ) (cardIn : Polynomial ℕ)
    (hcard : ∀ n, Fintype.card (γ n) ≤ cardIn.eval n) :
    (D.precomp f eIn' cardIn hcard).steps = D.steps := rfl

/-- The precomposed adversary implements the precomposed program family: the machine
run is unchanged except that it starts from `init (f n x)`. -/
theorem precomp_implements {D : MachineAdversary bd} (f : (n : ℕ) → γ n → α n)
    [∀ n, Fintype (γ n)] (eIn' : BitEncFam γ) (cardIn : Polynomial ℕ)
    (hcard : ∀ n, Fintype.card (γ n) ≤ cardIn.eval n)
    {oa : (n : ℕ) → α n → OracleComp (spec n) (β n)} (h : D.Implements oa) :
    (D.precomp f eIn' cardIn hcard).Implements fun n x => oa n (f n x) := by
  intro n H x
  rw [precomp_steps, precomp_M]
  exact (OracleMachine.runK_setInit (D.M n) _ H _ _).trans (h n H (f n x))

/-- Post-compose an adversary with a pure output map, from a supplied uniform machine
family for `Option.map g` between the canonical optional output encodings. The machine
is reused with its read-out post-composed; the new output family is the composition,
with all time and size accounting inside `EncPolyTimeFam.comp`. -/
noncomputable def mapComp (D : MachineAdversary bd) (g : (n : ℕ) → β n → γ n)
    (eOut' : BitEncFam γ)
    (wit : EncPolyTimeFam (bd.eOut.option).enc (eOut'.option).enc
      (fun n => Option.map (g n))) :
    MachineAdversary (bd.withOut eOut') where
  M n := ⟨(D.M n).toStrategy, (D.M n).init, fun s => ((D.M n).output s).map (g n)⟩
  steps := D.steps
  stable n := by
    intro s c hc r
    obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp hc
    exact Option.map_eq_some_iff.mpr ⟨b, (D.stable n) hb r, rfl⟩
  state := D.state
  initF := D.initF
  exposeF := D.exposeF
  updateF := D.updateF
  outputF := (D.outputF.comp wit).copy _ fun n s => rfl

@[simp] theorem mapComp_M (D : MachineAdversary bd) (g : (n : ℕ) → β n → γ n)
    (eOut' : BitEncFam γ)
    (wit : EncPolyTimeFam (bd.eOut.option).enc (eOut'.option).enc
      (fun n => Option.map (g n))) (n : ℕ) :
    (D.mapComp g eOut' wit).M n =
      ⟨(D.M n).toStrategy, (D.M n).init, fun s => ((D.M n).output s).map (g n)⟩ := rfl

@[simp] theorem mapComp_steps (D : MachineAdversary bd) (g : (n : ℕ) → β n → γ n)
    (eOut' : BitEncFam γ)
    (wit : EncPolyTimeFam (bd.eOut.option).enc (eOut'.option).enc
      (fun n => Option.map (g n))) :
    (D.mapComp g eOut' wit).steps = D.steps := rfl

/-- The output-mapped adversary implements the output-mapped program family: the
machine run is unchanged except that its result is post-composed with `g`. -/
theorem mapComp_implements {D : MachineAdversary bd} (g : (n : ℕ) → β n → γ n)
    (eOut' : BitEncFam γ)
    (wit : EncPolyTimeFam (bd.eOut.option).enc (eOut'.option).enc
      (fun n => Option.map (g n)))
    {oa : (n : ℕ) → α n → OracleComp (spec n) (β n)} (h : D.Implements oa) :
    (D.mapComp g eOut' wit).Implements fun n x => g n <$> oa n x := by
  intro n H x
  rw [mapComp_steps, mapComp_M, OracleMachine.runK_setOutput, h n H x]
  simp [simulateQ_map, Functor.map_map]

end MachineAdversary

/-! ## Closure of the abstract predicate -/

namespace Computability.EncPolyTimeFam

/-- The finite-table family for `Option.map g` between canonical optional boundaries:
domain cardinality and both encoded lengths are pinned, so the table's time and
description bounds are automatic. -/
noncomputable def optionMap {β γ : ℕ → Type} [∀ n, Fintype (β n)]
    (eβ : BitEncFam β) (eγ : BitEncFam γ) (g : (n : ℕ) → β n → γ n)
    (cardβ : Polynomial ℕ) (hcard : ∀ n, Fintype.card (β n) ≤ cardβ.eval n) :
    EncPolyTimeFam (eβ.option).enc (eγ.option).enc (fun n => Option.map (g n)) :=
  .ofFintype (eβ.option).enc_injective (fun n => Option.map (g n))
    (cardβ + .C 1)
    (fun n => by
      have := hcard n
      simp only [Fintype.card_option, Polynomial.eval_add, Polynomial.eval_C]
      omega)
    (eβ.option).widBound
    (fun n x => ((eβ.option).len_eq n x).le.trans ((eβ.option).wid_le n))
    (eγ.option).widBound
    (fun n x => ((eγ.option).len_eq n _).le.trans ((eγ.option).wid_le n))

end Computability.EncPolyTimeFam

/-- `OracleComp.IsPolyTime` is closed under precomposition with a pure map on
per-parameter finite input types of polynomially bounded cardinality: the standard
"the reduction is polynomial time since the adversary is" step for input-reshaping
reductions. -/
theorem OracleComp.IsPolyTime.precomp {spec : ℕ → OracleSpec.{0, 0} ι}
    {α β γ : ℕ → Type} {bd : BoundaryData spec α β}
    {oa : (n : ℕ) → α n → OracleComp (spec n) (β n)}
    (hoa : OracleComp.IsPolyTime bd oa) (f : (n : ℕ) → γ n → α n) [∀ n, Finite (γ n)]
    (eIn' : BitEncFam γ)
    (cardIn : Polynomial ℕ) (hcard : ∀ n, Nat.card (γ n) ≤ cardIn.eval n) :
    OracleComp.IsPolyTime (bd.withIn eIn') fun n x => oa n (f n x) := by
  letI : ∀ n, Fintype (γ n) := fun n => Fintype.ofFinite (γ n)
  have hcard' : ∀ n, Fintype.card (γ n) ≤ cardIn.eval n := fun n => by
    simpa [Nat.card_eq_fintype_card] using hcard n
  obtain ⟨w⟩ := hoa
  exact ⟨{
    A := w.A.precomp f eIn' cardIn hcard'
    implements := MachineAdversary.precomp_implements f eIn' cardIn hcard' w.implements
    queryBound := fun n x => w.queryBound n (f n x) }⟩

/-- `OracleComp.IsPolyTime` is closed under a pure **output** map on per-parameter
finite output types of polynomially bounded cardinality, on an abstract hypothesis:
the post-map is a finite table between the *canonical* optional output encodings, whose
widths are pinned — exactly what an existential output encoding could never provide.
This is the "post-process the Boolean result" primitive reductions need (output
negation, challenge comparison). -/
theorem OracleComp.IsPolyTime.map {spec : ℕ → OracleSpec.{0, 0} ι}
    {α β γ : ℕ → Type} {bd : BoundaryData spec α β}
    {oa : (n : ℕ) → α n → OracleComp (spec n) (β n)}
    (hoa : OracleComp.IsPolyTime bd oa) (g : (n : ℕ) → β n → γ n) [∀ n, Finite (β n)]
    (eOut' : BitEncFam γ)
    (cardβ : Polynomial ℕ) (hcard : ∀ n, Nat.card (β n) ≤ cardβ.eval n) :
    OracleComp.IsPolyTime (bd.withOut eOut') fun n x => g n <$> oa n x := by
  letI : ∀ n, Fintype (β n) := fun n => Fintype.ofFinite (β n)
  have hcard' : ∀ n, Fintype.card (β n) ≤ cardβ.eval n := fun n => by
    simpa [Nat.card_eq_fintype_card] using hcard n
  obtain ⟨w⟩ := hoa
  exact ⟨{
    A := w.A.mapComp g eOut' (.optionMap bd.eOut eOut' g cardβ hcard')
    implements := MachineAdversary.mapComp_implements g eOut' _ w.implements
    queryBound := fun n x => by
      simp only [MachineAdversary.mapComp_steps]
      rw [map_eq_bind_pure_comp]
      exact isTotalQueryBound_bind (n₂ := 0) (w.queryBound n x) fun _ => trivial }⟩
