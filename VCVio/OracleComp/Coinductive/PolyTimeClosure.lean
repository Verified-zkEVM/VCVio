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
  table; the cardinality bound is what keeps the table within the advice budget.
* `MachineAdversary.precompComp` / `IsPolyTime.precompComp`: precompose with a pure
  input map carrying its **own machine witness** between the canonical input encodings
  — the unbounded-input sibling, for maps on superpolynomially large types (bitstring
  glue, projections) that a finite table can never certify.
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

open OracleSpec OracleComp Computability

variable {ι : ℕ → Type} [∀ n, DecidableEq (ι n)] [∀ n, Inhabited (ι n)]

/-- `IsPolyTime` transports along pointwise program equality: a family equal to a
polynomial-time family is polynomial time. Lets a call site name its program directly
and bridge to a combinator's canonical form. -/
theorem OracleComp.IsPolyTime.congr {spec : (n : ℕ) → OracleSpec.{0, 0} (ι n)}
    {α β : ℕ → Type} {bd : BoundaryData spec α β}
    {oa oa' : (n : ℕ) → α n → OracleComp (spec n) (β n)} (h : ∀ n x, oa n x = oa' n x)
    (hp : OracleComp.IsPolyTime bd oa) : OracleComp.IsPolyTime bd oa' :=
  (funext fun n => funext fun x => h n x : oa = oa') ▸ hp

section SingleSpec

variable {ι : Type}

namespace OracleComp.OracleMachine

variable {spec : OracleSpec.{0, 0} ι} {m : Type → Type} [Monad m]

/-- Fuelled unrolling ignores the initialization field: replacing `init` (possibly
changing the input type) leaves `unroll` unchanged from any state. Upstream candidate
for `DynComputation/Bounded`. -/
theorem unroll_setInit {α α' β : Type}
    (M : OracleMachine spec α β) (g : α' → M.State) (k : ℕ) (s : M.State) :
    PFunctor.DynSystem.DynComputation.unroll ⟨M.toMachine, g⟩ k s = M.unroll k s := by
  induction k generalizing s with
  | zero =>
    rw [PFunctor.DynSystem.DynComputation.unroll_zero,
      PFunctor.DynSystem.DynComputation.unroll_zero]
    cases hview : M.view s with
    | inl b =>
      rw [show PFunctor.DynSystem.DynComputation.view
          (⟨M.toMachine, g⟩ : OracleMachine spec α' β) s = Sum.inl b from hview]
    | inr q =>
      rw [show PFunctor.DynSystem.DynComputation.view
          (⟨M.toMachine, g⟩ : OracleMachine spec α' β) s = Sum.inr q from hview]
  | succ k ih =>
    rw [PFunctor.DynSystem.DynComputation.unroll_succ,
      PFunctor.DynSystem.DynComputation.unroll_succ]
    cases hview : M.view s with
    | inl b =>
      rw [show PFunctor.DynSystem.DynComputation.view
          (⟨M.toMachine, g⟩ : OracleMachine spec α' β) s = Sum.inl b from hview]
    | inr q =>
      rw [show PFunctor.DynSystem.DynComputation.view
          (⟨M.toMachine, g⟩ : OracleMachine spec α' β) s = Sum.inr q from hview]
      exact congrArg (PFunctor.FreeM.liftBind q.1) (funext fun d => ih (q.2 d))

/-- The TM-facing accessors ignore the initialization field, definitionally: they
scrutinize `toMachine`, which `⟨M.toMachine, g⟩` shares with `M`. -/
theorem output_setInit {α α' β : Type} (M : OracleMachine spec α β) (g : α' → M.State)
    (s : M.State) :
    output (⟨M.toMachine, g⟩ : OracleMachine spec α' β) s = M.output s := rfl

@[simp] theorem expose_setInit [Inhabited ι] {α α' β : Type} (M : OracleMachine spec α β)
    (g : α' → M.State) (s : M.State) :
    expose (⟨M.toMachine, g⟩ : OracleMachine spec α' β) s = M.expose s := rfl

theorem updateFlat_setInit [DecidableEq ι] {α α' β : Type} (M : OracleMachine spec α β)
    (g : α' → M.State) (p : M.State × ((t : ι) × spec.Range t)) :
    updateFlat (⟨M.toMachine, g⟩ : OracleMachine spec α' β) p = M.updateFlat p := rfl

/-- The run of a machine ignores the initialization field, in any monad. -/
theorem runWith_setInit {α α' β : Type}
    (M : OracleMachine spec α β) (g : α' → M.State) (H : QueryImpl spec m) (k : ℕ)
    (s : M.State) :
    PFunctor.DynSystem.DynComputation.runWith ⟨M.toMachine, g⟩ H k s =
      M.runWith H k s := by
  change PFunctor.FreeM.liftM H
      (PFunctor.DynSystem.DynComputation.unroll ⟨M.toMachine, g⟩ k s) = _
  rw [unroll_setInit]
  rfl

variable {α β γ : Type}

/-- Post-composing the result map commutes with fuelled unrolling, at the syntactic
(`FreeM`) level. Upstream candidate for `DynComputation/Bounded`. -/
theorem unroll_mapResult (M : OracleMachine spec α β) (g : β → γ) (k : ℕ)
    (s : M.State) :
    (M.mapResult g).unroll k s = Option.map g <$> M.unroll k s := by
  induction k generalizing s with
  | zero =>
    cases hview : M.view s with
    | inl b =>
      rw [M.unroll_return 0 s b hview,
        (M.mapResult g).unroll_return 0 s (g b) (by simp [hview])]
      rfl
    | inr q =>
      obtain ⟨t, next⟩ := q
      rw [M.unroll_query_zero s t next hview,
        (M.mapResult g).unroll_query_zero s t next (by simp [hview])]
      rfl
  | succ k ih =>
    cases hview : M.view s with
    | inl b =>
      rw [M.unroll_return (k + 1) s b hview,
        (M.mapResult g).unroll_return (k + 1) s (g b) (by simp [hview])]
      rfl
    | inr q =>
      obtain ⟨t, next⟩ := q
      rw [M.unroll_query_succ k s t next hview,
        (M.mapResult g).unroll_query_succ k s t next (by simp [hview])]
      exact congrArg (PFunctor.FreeM.liftBind t) (funext fun d => ih (next d))

/-- Post-composing the result map maps the fuelled run's result, through any lawful
handler. -/
theorem runWith_mapResult [LawfulMonad m] (M : OracleMachine spec α β) (g : β → γ)
    (H : QueryImpl spec m) (k : ℕ) (s : M.State) :
    (M.mapResult g).runWith H k s = Option.map g <$> M.runWith H k s := by
  change PFunctor.FreeM.liftM H ((M.mapResult g).unroll k s) = _
  rw [unroll_mapResult, PFunctor.FreeM.liftM_map]
  rfl

@[simp] theorem output_mapResult (M : OracleMachine spec α β) (g : β → γ)
    (s : M.State) : output (M.mapResult g) s = (M.output s).map g := by
  cases hview : M.view s <;> simp only [output, hview,
    PFunctor.DynSystem.DynComputation.mapResult_view] <;> rfl

@[simp] theorem expose_mapResult [Inhabited ι] (M : OracleMachine spec α β) (g : β → γ)
    (s : M.State) : expose (M.mapResult g) s = M.expose s := by
  cases hview : M.view s <;> simp only [expose, hview,
    PFunctor.DynSystem.DynComputation.mapResult_view] <;> rfl

@[simp] theorem updateFlat_mapResult [DecidableEq ι] (M : OracleMachine spec α β)
    (g : β → γ) : updateFlat (M.mapResult g) = M.updateFlat := by
  funext p
  cases hview : M.view p.1 <;> simp only [OracleMachine.updateFlat, hview,
    PFunctor.DynSystem.DynComputation.mapResult_view] <;> rfl

end OracleComp.OracleMachine

end SingleSpec

namespace MachineAdversary

variable {spec : (n : ℕ) → OracleSpec.{0, 0} (ι n)} {α β γ : ℕ → Type}
  {bd : BoundaryData spec α β}

/-- Precompose an adversary with a pure input map on per-parameter finite input types
of polynomially bounded cardinality. The machine family is reused with only its
initialization changed to `init ∘ f`, witnessed by a finite table; the table stays
within the advice budget because the new inputs are canonically fixed-width and the
state encoding is polynomially bounded over *all* states. -/
noncomputable def precomp (D : MachineAdversary bd)
    (f : (n : ℕ) → γ n → α n) [∀ n, Fintype (γ n)] (eIn' : BitEncFam γ)
    (cardIn : Polynomial ℕ) (hcard : ∀ n, Fintype.card (γ n) ≤ cardIn.eval n) :
    MachineAdversary (bd.withIn eIn') where
  M n := ⟨(D.M n).toMachine, fun x => (D.M n).init (f n x)⟩
  steps := D.steps
  state := D.state
  initF := .ofFintype eIn'.enc_injective (fun n x => (D.M n).init (f n x))
    cardIn hcard eIn'.widBound
    (fun n x => (eIn'.len_eq n x).le.trans (eIn'.wid_le n))
    D.state.bound (fun n _ => D.state.len_le n _)
  exposeF := D.exposeF.copy _ fun n s =>
    (OracleMachine.expose_setInit (D.M n) _ s).symm
  updateF := D.updateF.copy _ fun n p =>
    (OracleMachine.updateFlat_setInit (D.M n) _ p).symm
  outputF := D.outputF.copy _ fun n s =>
    (OracleMachine.output_setInit (D.M n) _ s).symm

@[simp] theorem precomp_M (D : MachineAdversary bd) (f : (n : ℕ) → γ n → α n)
    [∀ n, Fintype (γ n)] (eIn' : BitEncFam γ) (cardIn : Polynomial ℕ)
    (hcard : ∀ n, Fintype.card (γ n) ≤ cardIn.eval n) (n : ℕ) :
    (D.precomp f eIn' cardIn hcard).M n =
      ⟨(D.M n).toMachine, fun x => (D.M n).init (f n x)⟩ := rfl

@[simp] theorem precomp_steps (D : MachineAdversary bd) (f : (n : ℕ) → γ n → α n)
    [∀ n, Fintype (γ n)] (eIn' : BitEncFam γ) (cardIn : Polynomial ℕ)
    (hcard : ∀ n, Fintype.card (γ n) ≤ cardIn.eval n) :
    (D.precomp f eIn' cardIn hcard).steps = D.steps := rfl

/-- The precomposed adversary implements the precomposed program family: the machine
run is unchanged except that it starts from `init (f n x)`. -/
theorem precomp_implements {D : MachineAdversary bd} (f : (n : ℕ) → γ n → α n)
    [∀ n, Fintype (γ n)] (eIn' : BitEncFam γ) (cardIn : Polynomial ℕ)
    (hcard : ∀ n, Fintype.card (γ n) ≤ cardIn.eval n)
    {oa : (n : ℕ) → α n → OracleComp (spec n) (β n)} (h : D ⊨ oa) :
    D.precomp f eIn' cardIn hcard ⊨ fun n x => oa n (f n x) := by
  intro n x
  change PFunctor.DynSystem.DynComputation.unroll
      (⟨(D.M n).toMachine, fun x => (D.M n).init (f n x)⟩ :
        OracleMachine (spec n) (γ n) (β n)) (D.steps.eval n) ((D.M n).init (f n x)) = _
  rw [OracleMachine.unroll_setInit]
  exact h n (f n x)

/-- Precompose an adversary with a pure input map from a **supplied machine witness**
between the canonical input encodings — the sibling of `precomp` for input types too
large for a table (`precomp` needs polynomially many inputs; here the map carries its
own machine). The machine family is reused with only its initialization changed to
`init ∘ f`; the new initialization family is the composition. -/
noncomputable def precompComp (D : MachineAdversary bd) (f : (n : ℕ) → γ n → α n)
    (eIn' : Computability.BitEncFam γ)
    (wit : Computability.EncPolyTimeFam eIn'.enc bd.eIn.enc f) :
    MachineAdversary (bd.withIn eIn') where
  M n := ⟨(D.M n).toMachine, fun x => (D.M n).init (f n x)⟩
  steps := D.steps
  state := D.state
  initF := wit.comp D.initF
  exposeF := D.exposeF.copy _ fun n s =>
    (OracleMachine.expose_setInit (D.M n) _ s).symm
  updateF := D.updateF.copy _ fun n p =>
    (OracleMachine.updateFlat_setInit (D.M n) _ p).symm
  outputF := D.outputF.copy _ fun n s =>
    (OracleMachine.output_setInit (D.M n) _ s).symm

@[simp] theorem precompComp_M (D : MachineAdversary bd) (f : (n : ℕ) → γ n → α n)
    (eIn' : Computability.BitEncFam γ)
    (wit : Computability.EncPolyTimeFam eIn'.enc bd.eIn.enc f) (n : ℕ) :
    (D.precompComp f eIn' wit).M n =
      ⟨(D.M n).toMachine, fun x => (D.M n).init (f n x)⟩ := rfl

@[simp] theorem precompComp_steps (D : MachineAdversary bd) (f : (n : ℕ) → γ n → α n)
    (eIn' : Computability.BitEncFam γ)
    (wit : Computability.EncPolyTimeFam eIn'.enc bd.eIn.enc f) :
    (D.precompComp f eIn' wit).steps = D.steps := rfl

/-- The witness-precomposed adversary implements the precomposed program family: the
machine run is unchanged except that it starts from `init (f n x)`. -/
theorem precompComp_implements {D : MachineAdversary bd} (f : (n : ℕ) → γ n → α n)
    (eIn' : Computability.BitEncFam γ)
    (wit : Computability.EncPolyTimeFam eIn'.enc bd.eIn.enc f)
    {oa : (n : ℕ) → α n → OracleComp (spec n) (β n)} (h : D ⊨ oa) :
    D.precompComp f eIn' wit ⊨ fun n x => oa n (f n x) := by
  intro n x
  change PFunctor.DynSystem.DynComputation.unroll
      (⟨(D.M n).toMachine, fun x => (D.M n).init (f n x)⟩ :
        OracleMachine (spec n) (γ n) (β n)) (D.steps.eval n) ((D.M n).init (f n x)) = _
  rw [OracleMachine.unroll_setInit]
  exact h n (f n x)

/-- Post-compose an adversary with a pure output map, from a supplied uniform machine
family for `Option.map g` between the canonical optional output encodings. The machine
is reused with its read-out post-composed; the new output family is the composition,
with all time and size accounting inside `EncPolyTimeFam.comp`. -/
noncomputable def mapComp (D : MachineAdversary bd) (g : (n : ℕ) → β n → γ n)
    (eOut' : BitEncFam γ)
    (wit : EncPolyTimeFam (bd.eOut.option).enc (eOut'.option).enc
      (fun n => Option.map (g n))) :
    MachineAdversary (bd.withOut eOut') where
  M n := (D.M n).mapResult (g n)
  steps := D.steps
  state := D.state
  initF := D.initF
  exposeF := D.exposeF.copy _ fun n s =>
    (OracleMachine.expose_mapResult (D.M n) (g n) s).symm
  updateF := D.updateF.copy _ fun n p =>
    congrFun (OracleMachine.updateFlat_mapResult (D.M n) (g n)).symm p
  outputF := (D.outputF.comp wit).copy _ fun n s =>
    (OracleMachine.output_mapResult (D.M n) (g n) s).symm

@[simp] theorem mapComp_M (D : MachineAdversary bd) (g : (n : ℕ) → β n → γ n)
    (eOut' : BitEncFam γ)
    (wit : EncPolyTimeFam (bd.eOut.option).enc (eOut'.option).enc
      (fun n => Option.map (g n))) (n : ℕ) :
    (D.mapComp g eOut' wit).M n = (D.M n).mapResult (g n) := rfl

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
    {oa : (n : ℕ) → α n → OracleComp (spec n) (β n)} (h : D ⊨ oa) :
    D.mapComp g eOut' wit ⊨ fun n x => g n <$> oa n x := by
  intro n x
  change ((D.M n).mapResult (g n)).unroll (D.steps.eval n) ((D.M n).init x) = _
  rw [OracleMachine.unroll_mapResult]
  change Option.map (g n) <$>
      PFunctor.DynSystem.DynComputation.run (D.M n) (D.steps.eval n) x = _
  rw [h n x]
  simp only [← PFunctor.FreeM.map_eq_map, ← PFunctor.FreeM.comp_map,
    Function.comp_def, Option.map_some]

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
theorem OracleComp.IsPolyTime.precomp {spec : (n : ℕ) → OracleSpec.{0, 0} (ι n)}
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

/-- `OracleComp.IsPolyTime` is closed under pure input precomposition from a supplied
machine witness between the canonical input encodings — the unbounded-input sibling of
`IsPolyTime.precomp`, for input maps on superpolynomially large types (bitstring glue,
projections) that a finite table can never certify. -/
theorem OracleComp.IsPolyTime.precompComp {spec : (n : ℕ) → OracleSpec.{0, 0} (ι n)}
    {α β γ : ℕ → Type} {bd : BoundaryData spec α β}
    {oa : (n : ℕ) → α n → OracleComp (spec n) (β n)}
    (hoa : OracleComp.IsPolyTime bd oa) (f : (n : ℕ) → γ n → α n)
    (eIn' : Computability.BitEncFam γ)
    (wit : Computability.EncPolyTimeFam eIn'.enc bd.eIn.enc f) :
    OracleComp.IsPolyTime (bd.withIn eIn') fun n x => oa n (f n x) := by
  obtain ⟨w⟩ := hoa
  exact ⟨{
    A := w.A.precompComp f eIn' wit
    implements := MachineAdversary.precompComp_implements f eIn' wit w.implements
    queryBound := fun n x => w.queryBound n (f n x) }⟩

/-- `OracleComp.IsPolyTime` is closed under a pure **output** map on per-parameter
finite output types of polynomially bounded cardinality, on an abstract hypothesis:
the post-map is a finite table between the *canonical* optional output encodings, whose
widths are pinned — exactly what an existential output encoding could never provide.
This is the "post-process the Boolean result" primitive reductions need (output
negation, challenge comparison). -/
theorem OracleComp.IsPolyTime.map {spec : (n : ℕ) → OracleSpec.{0, 0} (ι n)}
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
