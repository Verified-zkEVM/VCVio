/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Quantum.Comp.QueryBound

/-!
# Quantum combs

A `q`-query comb on a memory register `M` is the textbook form of a quantum query algorithm: an
initial substate, `q + 1` lossless steps on `M`, and a final lossless instrument. Run against a
query step `Q`, it interleaves the steps with `q` copies of `Q` and then applies the final
instrument:

`step 0, Q, step 1, Q, …, Q, step q, final`.

With normalized input, finite qubit registers, unitary steps
(`Quantum.SubInstrument.ofIsometry`), XOR queries and the usual final output measurement, this
has the fixed-query circuit form of Boneh et al., *Random Oracles in a Quantum World*
(arXiv:1008.0931v2, §2.1, PDF p. 7). No efficient circuit-family condition is imposed here.
The external sequence and number of query slots are fixed, and all queries go to one port.
Intermediate channels report no classical result to the syntax, but may measure internally,
store a record in memory, and act on it later. "Comb" here means this concrete sequential form,
not the Choi-operator formalism of general quantum combs.

## Combs embed as programs

The model of quantum oracle algorithms is the program (`Quantum.QuantumComp`) run against a runtime.
Combs are a restricted form of program:

* `Quantum.QuantumComb.toComp` embeds a comb as a straight-line program whose queries go to port `i`
  through `ℓ : M ≃ In i × E` and return to `M` through `ℓ' : Out i × E ≃ M`.
* `Quantum.QuantumComb.run_toComp`: running that program against a runtime `R` is running the comb,
  framed by `R.D`, against the query step `R.combQuery i E ℓ ℓ'`, which discards the classical
  result of each call. So theorems about combs apply to the programs they embed as, against every
  runtime.

The converse, that a program can be put in comb form, is not proved here, and fails without
hypotheses: a comb makes the same number of calls on every path and ignores call results, while a
program need not.

## Main definitions

* `Quantum.interleave Q q s`: the composite `s 0, Q, s 1, …, Q, s q`.
* `Quantum.QuantumComb M α q`, with `Quantum.QuantumComb.run`.
* `Quantum.QuantumComb.stateAfterStep`: the substate after step `i`, on which query `i` acts.
* `Quantum.QuantumComb.ofClassical`: the comb that runs a deterministic classical algorithm on basis
  states.
* `Quantum.QuantumComb.toComp`: the program of a comb.

## Main results

* `Quantum.QuantumComb.outcomeMeasure_run_congr`: two query steps that act in the same way on the
  substates the comb presents to them give the same outcome measure.
* `Quantum.QuantumComb.outcomeMeasure_run_ofClassical`: against a query step that permutes basis
  states, a classical comb returns the output of the classical run with certainty.
* `Quantum.QuantumComb.run_toComp` and `Quantum.QuantumComb.evalDist_toComp`: the run and the
  distribution of the program of a comb against a runtime.
-/

public section

open MeasureTheory
open scoped ComplexOrder

universe u₁ v₁ w

namespace Quantum

section comb

variable {M : Type*}

section run

variable [Fintype M] {α : Type*} {q : ℕ}

/-! ## Interleaving steps with queries -/

/-- The composite `s 0, Q, s 1, Q, …, Q, s q` of `q + 1` steps interleaved with `q` copies of
the query step `Q`. -/
@[expose]
noncomputable def interleave (Q : SubInstrument M M Unit) :
    (q : ℕ) → (Fin (q + 1) → SubInstrument M M Unit) → SubInstrument M M Unit
  | 0, s => s 0
  | q + 1, s => ((interleave Q q (Fin.init s)).bind fun _ ↦ Q).bind fun _ ↦ s (Fin.last _)

/-- Without queries, the composite is the single step. -/
@[simp]
theorem interleave_zero (Q : SubInstrument M M Unit) (s : Fin 1 → SubInstrument M M Unit) :
    interleave Q 0 s = s 0 :=
  rfl

/-- The composite with one more query: all steps but the last, a query, and the last step. -/
theorem interleave_succ (Q : SubInstrument M M Unit) (s : Fin (q + 2) → SubInstrument M M Unit) :
    interleave Q (q + 1) s =
      ((interleave Q q (Fin.init s)).bind fun _ ↦ Q).bind fun _ ↦ s (Fin.last _) :=
  rfl

/-- The composite with one more query, split at the first query: the first step, a query, and
the composite of the remaining steps. -/
theorem interleave_succ' (Q : SubInstrument M M Unit) (s : Fin (q + 2) → SubInstrument M M Unit) :
    interleave Q (q + 1) s =
      (s 0).bind fun _ ↦ Q.bind fun _ ↦ interleave Q q (Fin.tail s) := by
  induction q with
  | zero => exact SubInstrument.bind_assoc ..
  | succ q ih =>
    rw [interleave_succ, ih, interleave_succ, SubInstrument.bind_assoc,
      SubInstrument.bind_assoc]
    simp only [SubInstrument.bind_assoc]
    rfl

/-- Interleaving lossless steps with a lossless query step is lossless. -/
theorem lossless_interleave {Q : SubInstrument M M Unit} (hQ : Q.Lossless) :
    ∀ {q : ℕ} {s : Fin (q + 1) → SubInstrument M M Unit}, (∀ i, (s i).Lossless) →
      (interleave Q q s).Lossless
  | 0, _, hs => hs 0
  | _ + 1, _, hs =>
    ((lossless_interleave hQ fun i ↦ hs i.castSucc).bind fun _ ↦ hQ).bind fun _ ↦ hs _

/-- The substates after each step of `s 0, Q, s 1, …, Q, s q` run on `ρ`: the entry at `i` is
the substate after step `i`, on which the next query acts. -/
@[expose]
noncomputable def interleavePost (Q : SubInstrument M M Unit) (ρ : SubState M)
    (s : Fin (q + 1) → SubInstrument M M Unit) : Fin (q + 1) → SubState M :=
  Fin.induction ((s 0).post ρ ()) fun i σ ↦ (s i.succ).post (Q.post σ ()) ()

/-- The substate after step `0` is step `0` applied to the initial substate. -/
@[simp]
theorem interleavePost_zero (Q : SubInstrument M M Unit) (ρ : SubState M)
    (s : Fin (q + 1) → SubInstrument M M Unit) : interleavePost Q ρ s 0 = (s 0).post ρ () :=
  rfl

/-- The substate after step `i + 1` is the query step and then step `i + 1` applied to the
substate after step `i`. -/
theorem interleavePost_succ (Q : SubInstrument M M Unit) (ρ : SubState M)
    (s : Fin (q + 1) → SubInstrument M M Unit) (i : Fin q) :
    interleavePost Q ρ s i.succ =
      (s i.succ).post (Q.post (interleavePost Q ρ s i.castSucc) ()) () :=
  Fin.induction_succ ..

/-- Dropping the last step does not change the substates after the earlier steps. -/
theorem interleavePost_init (Q : SubInstrument M M Unit) (ρ : SubState M)
    (s : Fin (q + 2) → SubInstrument M M Unit) (i : Fin (q + 1)) :
    interleavePost Q ρ (Fin.init s) i = interleavePost Q ρ s i.castSucc := by
  induction i using Fin.induction with
  | zero => rfl
  | succ i ih =>
    rw [interleavePost_succ, ih, ← Fin.succ_castSucc, interleavePost_succ]
    rfl

/-- The substate left by the composite is the substate after the last step. -/
theorem post_interleave (Q : SubInstrument M M Unit) (ρ : SubState M) :
    ∀ {q : ℕ} (s : Fin (q + 1) → SubInstrument M M Unit),
      (interleave Q q s).post ρ () = interleavePost Q ρ s (Fin.last q)
  | 0, _ => rfl
  | q + 1, s => by
    rw [interleave_succ, DSubInstrument.post_bind_unit, DSubInstrument.post_bind_unit,
      post_interleave Q ρ (Fin.init s), interleavePost_init, ← Fin.succ_last,
      interleavePost_succ]

/-! ## Combs -/

/-- A fixed-slot query strategy on finite memory `M`, returning a classical value in `α`.
It consists of an initial substate, channels `step 0, …, step q` on `M`, and a lossless final
instrument. Against a query subinstrument `Q`, execution is
`step 0, Q, step 1, …, Q, step q, final`, with exactly `q` query slots.

Intermediate steps report only `Unit`, so the external schedule cannot depend on a reported
result. Channels may nevertheless measure internally, store a record in `M`, and act on that
record later. The initial substate may have trace below one, and `Q` may lose trace.

With normalized input, qubit registers, unitary steps and XOR queries, this has the fixed-query
circuit form in Boneh et al., Random Oracles in a Quantum World, §2.1 (PDF p. 7).
No efficient circuit-family condition is imposed here. This is a concrete sequential strategy,
not a Choi-operator representation. `toComp` and `run_toComp` give its program embedding;
no converse is proved. -/
structure QuantumComb (M : Type*) [Fintype M] (α : Type*) (q : ℕ) where
  /-- The substate of the register before the first step. -/
  init : SubState M
  /-- The steps: step `0` precedes the first query and step `i + 1` follows query `i`. -/
  step : Fin (q + 1) → SubInstrument M M Unit
  /-- Every step is lossless. -/
  lossless_step : ∀ i, (step i).Lossless
  /-- The final instrument, reporting the output. -/
  final : SubInstrument M M α
  /-- The final instrument is lossless. -/
  lossless_final : final.Lossless

namespace QuantumComb

variable (c : QuantumComb M α q) (Q : SubInstrument M M Unit)

/-- The interaction of the comb with the query step `Q`, before the final instrument:
`step 0, Q, step 1, …, Q, step q`. -/
@[expose]
noncomputable def body : SubInstrument M M Unit :=
  interleave Q q c.step

/-- The comb run against the query step `Q`: the steps interleaved with `q` copies of `Q`,
then the final instrument. -/
@[expose]
noncomputable def run : SubInstrument M M α :=
  (c.body Q).bind fun _ ↦ c.final

/-- The substate after step `i` of the run against `Q`, having made `i` queries. For `i < q` it
is the substate on which query `i` acts; for `i = q` the final instrument acts on it. -/
@[expose]
noncomputable def stateAfterStep : Fin (q + 1) → SubState M :=
  interleavePost Q c.init c.step

/-- The substate after step `0` is step `0` applied to the initial substate. -/
@[simp]
theorem stateAfterStep_zero : c.stateAfterStep Q 0 = (c.step 0).post c.init () :=
  rfl

/-- The substate after step `i + 1` is the query step and then step `i + 1` applied to the
substate after step `i`. -/
theorem stateAfterStep_succ (i : Fin q) :
    c.stateAfterStep Q i.succ =
      (c.step i.succ).post (Q.post (c.stateAfterStep Q i.castSucc) ()) () :=
  interleavePost_succ ..

/-- The interaction leaves the substate after the last step. -/
theorem post_body : (c.body Q).post c.init () = c.stateAfterStep Q (Fin.last q) :=
  post_interleave Q c.init c.step

/-- The outcome measure of a run is that of the final instrument on the substate after the last
step. -/
theorem outcomeMeasure_run [MeasurableSpace α] :
    (c.run Q).outcomeMeasure c.init =
      c.final.outcomeMeasure (c.stateAfterStep Q (Fin.last q)) := by
  rw [run, DSubInstrument.outcomeMeasure_bind_unit, post_body]

variable {Q}

/-- The interaction with a lossless query step is lossless. -/
theorem lossless_body (hQ : Q.Lossless) : (c.body Q).Lossless :=
  lossless_interleave hQ c.lossless_step

/-- The run against a lossless query step is lossless. -/
theorem lossless_run (hQ : Q.Lossless) : (c.run Q).Lossless :=
  (c.lossless_body hQ).bind fun _ ↦ c.lossless_final

/-- Against a lossless query step, the comb reports an output with total weight the trace
of its initial substate. -/
theorem outcomeMeasure_run_apply_univ [MeasurableSpace α] (hQ : Q.Lossless) :
    (c.run Q).outcomeMeasure c.init Set.univ = ENNReal.ofReal c.init.matrix.trace.re :=
  (c.lossless_run hQ).outcomeMeasure_apply_univ _

/-- Two query steps that act in the same way on each substate the comb presents to the
first of them lead to the same substates after every step. -/
theorem stateAfterStep_congr {Q' : SubInstrument M M Unit}
    (h : ∀ i : Fin q, Q'.post (c.stateAfterStep Q i.castSucc) () =
      Q.post (c.stateAfterStep Q i.castSucc) ()) (i : Fin (q + 1)) :
    c.stateAfterStep Q' i = c.stateAfterStep Q i := by
  induction i using Fin.induction with
  | zero => rfl
  | succ i ih => rw [stateAfterStep_succ, stateAfterStep_succ, ih, h i]

/-- Two query steps that act in the same way on each substate the comb presents to the
first of them give the same outcome measure. -/
theorem outcomeMeasure_run_congr [MeasurableSpace α] {Q' : SubInstrument M M Unit}
    (h : ∀ i : Fin q, Q'.post (c.stateAfterStep Q i.castSucc) () =
      Q.post (c.stateAfterStep Q i.castSucc) ()) :
    (c.run Q').outcomeMeasure c.init = (c.run Q).outcomeMeasure c.init := by
  rw [outcomeMeasure_run, outcomeMeasure_run, c.stateAfterStep_congr h]

/-! ## Removing the last query -/

/-- The comb without its last query and last step, stopping before the final instrument:
its run is the interaction up to step `q`. -/
@[expose]
noncomputable def dropLast (c : QuantumComb M α (q + 1)) : QuantumComb M Unit q where
  init := c.init
  step := Fin.init c.step
  lossless_step i := c.lossless_step i.castSucc
  final := SubInstrument.pure ()
  lossless_final := by
    simpa only [SubInstrument.pure] using DSubInstrument.lossless_ret (fun _ : Unit ↦ M) ()

/-- The interaction of a comb with `q + 1` queries: the interaction of the comb
without its last query, one query, and the last step. -/
theorem body_succ (c : QuantumComb M α (q + 1)) (Q : SubInstrument M M Unit) :
    c.body Q = ((c.dropLast.body Q).bind fun _ ↦ Q).bind fun _ ↦ c.step (Fin.last _) :=
  rfl

/-- The run of the comb without its last query is its interaction. -/
@[simp]
theorem run_dropLast (c : QuantumComb M α (q + 1)) (Q : SubInstrument M M Unit) :
    c.dropLast.run Q = c.dropLast.body Q :=
  SubInstrument.bind_pure _

/-- Removing the last query does not change the substates after the earlier steps. -/
theorem stateAfterStep_dropLast (c : QuantumComb M α (q + 1)) (Q : SubInstrument M M Unit)
    (i : Fin (q + 1)) : c.dropLast.stateAfterStep Q i = c.stateAfterStep Q i.castSucc :=
  interleavePost_init ..

/-! ## Framing by an ancilla -/

/-- The comb acting on `M × R`: the ancilla `R` starts in `σ`, and every step and the final
instrument leave it untouched. -/
@[expose]
noncomputable def frame (c : QuantumComb M α q) (R : Type*) [Fintype R] (σ : SubState R) :
    QuantumComb (M × R) α q where
  init := c.init.prod σ
  step i := (c.step i).frame R
  lossless_step i := (c.lossless_step i).frame R
  final := c.final.frame R
  lossless_final := c.lossless_final.frame R

end QuantumComb

end run

/-! ## Classical combs -/

namespace QuantumComb

section classicalTrajectory

variable {q : ℕ}

/-- The contents of the register after each step of a classical algorithm whose queries rewrite
the register by `π`: start at `m₀`, apply `f 0`, and alternate `π` with the later `f i`. -/
@[expose]
def classicalTrajectory (π : M → M) (m₀ : M) (f : Fin (q + 1) → M → M) : Fin (q + 1) → M :=
  Fin.induction (f 0 m₀) fun i m ↦ f i.succ (π m)

/-- The register after step `0` is `f 0` of the initial contents. -/
@[simp]
theorem classicalTrajectory_zero (π : M → M) (m₀ : M) (f : Fin (q + 1) → M → M) :
    classicalTrajectory π m₀ f 0 = f 0 m₀ :=
  rfl

/-- The register after step `i + 1` is `π` and then `f (i + 1)` of the register after step
`i`. -/
theorem classicalTrajectory_succ (π : M → M) (m₀ : M) (f : Fin (q + 1) → M → M) (i : Fin q) :
    classicalTrajectory π m₀ f i.succ = f i.succ (π (classicalTrajectory π m₀ f i.castSucc)) :=
  Fin.induction_succ ..

end classicalTrajectory

section ofClassical

variable [Fintype M] {α : Type*} {q : ℕ} {Q : SubInstrument M M Unit} [DecidableEq M]

/-- The comb that runs a classical deterministic algorithm on basis states: it starts in
the basis state at `m₀`, step `i` reads the register in the computational basis and rewrites it
by `f i`, and the final instrument reads the register and reports `g` of it. -/
@[expose]
noncomputable def ofClassical (m₀ : M) (f : Fin (q + 1) → M → M) (g : M → α) :
    QuantumComb M α q where
  init := SubState.basis m₀
  step i := DSubInstrument.classical (B := fun _ ↦ M) (fun _ ↦ ()) (f i)
  lossless_step _ := DSubInstrument.lossless_classical _ _
  final := DSubInstrument.classical (B := fun _ ↦ _) g id
  lossless_final := DSubInstrument.lossless_classical _ _

variable {π : M → M} (hQ : ∀ m, Q.post (SubState.basis m) () = SubState.basis (π m))
include hQ

/-- Against a query step that sends the basis state at `m` to the basis state at `π m`, the
register of a classical comb is in the basis state of the classical trajectory after every
step. -/
theorem stateAfterStep_ofClassical (m₀ : M) (f : Fin (q + 1) → M → M) (g : M → α)
    (i : Fin (q + 1)) :
    (ofClassical m₀ f g).stateAfterStep Q i = SubState.basis (classicalTrajectory π m₀ f i) := by
  induction i using Fin.induction with
  | zero => exact DSubInstrument.post_classical_basis _ _
  | succ i ih =>
    rw [stateAfterStep_succ, ih, hQ, classicalTrajectory_succ]
    exact DSubInstrument.post_classical_basis _ _

/-- Against a query step that sends the basis state at `m` to the basis state at `π m`, a
classical comb reports `g` of the last entry of the classical trajectory with certainty. -/
theorem outcomeMeasure_run_ofClassical [MeasurableSpace α] (m₀ : M) (f : Fin (q + 1) → M → M)
    (g : M → α) :
    ((ofClassical m₀ f g).run Q).outcomeMeasure (SubState.basis m₀) =
      Measure.dirac (g (classicalTrajectory π m₀ f (Fin.last q))) := by
  rw [← DSubInstrument.outcomeMeasure_classical_basis (B := fun _ ↦ M) g id,
    ← stateAfterStep_ofClassical hQ m₀ f g]
  exact (ofClassical m₀ f g).outcomeMeasure_run Q

end ofClassical

end QuantumComb

end comb

/-! ## Combs as programs -/

namespace QuantumRuntime

variable {spec : QuantumOracleSpec.{u₁, v₁}} (R : QuantumRuntime spec) {M : Type} [Fintype M]
  [DecidableEq M]

/-- A call of port `i` as a query step on the joint register `M × D` of a comb and the runtime:
expose the port's input register through `ℓ`, call the port, forget its result, and return to
`M` through `ℓ'`. -/
@[expose]
noncomputable def combQuery (i : spec.Port) (E : QReg) (ℓ : M ≃ spec.In i × E)
    (ℓ' : spec.Out i × E ≃ M) : SubInstrument (M × R.D) (M × R.D) Unit :=
  (R.queryStep (A := QReg.of M) i E ℓ).bind fun _ ↦ (SubInstrument.relabel ℓ').frame R.D

end QuantumRuntime

section toComp

variable {spec : QuantumOracleSpec.{u₁, v₁}} {M : Type} [Fintype M] [DecidableEq M] {α : Type w}
  {q : ℕ}

/-- The straight-line program `s 0, call, s 1, …, call, s q`: each call goes to port `i` on the
factor of `M` exposed by `ℓ`, and the register returns to `M` through `ℓ'` before the next step. -/
@[expose]
noncomputable def interleaveComp (i : spec.Port) (E : QReg) (ℓ : M ≃ spec.In i × E)
    (ℓ' : spec.Out i × E ≃ M) :
    (q : ℕ) → (Fin (q + 1) → SubInstrument M M Unit) →
      QComp spec (QReg.of M) (QReg.of M) Unit
  | 0, s => QComp.act (s 0)
  | q + 1, s =>
    ((interleaveComp i E ℓ ℓ' q (Fin.init s)).bind fun _ ↦
      QuantumComp₂.query (L := LocalSig.instruments) (A := QReg.of M) i E ℓ).bind fun _ ↦
        QComp.act ((SubInstrument.relabel ℓ').bind fun _ ↦ s (Fin.last _))

/-- Running the straight-line program interleaves the framed steps with the runtime's query
step. -/
theorem run_interleaveComp (R : QuantumRuntime spec) (i : spec.Port) (E : QReg)
    (ℓ : M ≃ spec.In i × E) (ℓ' : spec.Out i × E ≃ M) :
    ∀ (q : ℕ) (s : Fin (q + 1) → SubInstrument M M Unit),
      R.run₂ .instruments (interleaveComp i E ℓ ℓ' q s) =
        interleave (R.combQuery i E ℓ ℓ') q fun j ↦ (s j).frame R.D
  | 0, s => by
    rw [interleaveComp, QuantumRuntime.run₂_act, SubInstrument.bind_pure, interleave_zero]
  | q + 1, s => by
    rw [interleaveComp, QuantumRuntime.run₂_bind, QuantumRuntime.run₂_bind,
      run_interleaveComp R i E ℓ ℓ' q, QuantumRuntime.run₂_query, SubInstrument.bind_pure,
      QuantumRuntime.run₂_act, SubInstrument.bind_pure, SubInstrument.frame_bind, interleave_succ,
      QuantumRuntime.combQuery]
    simp only [SubInstrument.bind_assoc]
    rfl

/-- Interleaving lossless steps with calls is a lossless program. -/
theorem lossless_interleaveComp (i : spec.Port) (E : QReg) (ℓ : M ≃ spec.In i × E)
    (ℓ' : spec.Out i × E ≃ M) :
    ∀ {q : ℕ} {s : Fin (q + 1) → SubInstrument M M Unit}, (∀ j, (s j).Lossless) →
      (interleaveComp i E ℓ ℓ' q s).Lossless .instruments
  | 0, _, hs => QComp.lossless_act (hs 0)
  | _ + 1, _, hs =>
    QuantumComp₂.lossless_bind (QuantumComp₂.lossless_bind
      (lossless_interleaveComp i E ℓ ℓ' fun j ↦ hs j.castSucc) fun _ ↦
        QuantumComp₂.lossless_query _ _ _) fun _ ↦
      QComp.lossless_act ((SubInstrument.lossless_relabel _).bind fun _ ↦ hs _)

/-- The straight-line program with `q` calls makes `q` calls of port `i` and none of any other
port. -/
theorem isQueryBound_interleaveComp [DecidableEq spec.Port] (i : spec.Port) (E : QReg)
    (ℓ : M ≃ spec.In i × E) (ℓ' : spec.Out i × E ≃ M) :
    ∀ (q : ℕ) (s : Fin (q + 1) → SubInstrument M M Unit),
      (interleaveComp i E ℓ ℓ' q s).IsQueryBound (Pi.single i q)
  | 0, s => by
    rw [Pi.single_zero]
    exact QComp.isQueryBound_act _ _
  | q + 1, s => by
    rw [interleaveComp]
    refine (QuantumComp₂.isQueryBound_bind (QuantumComp₂.isQueryBound_bind
      (isQueryBound_interleaveComp i E ℓ ℓ' q (Fin.init s)) fun _ ↦
        (QuantumComp₂.isQueryBound_query_iff (A := QReg.of M) i E ℓ (Pi.single i 1)).mpr
          (by simp)) fun _ ↦ QComp.isQueryBound_act _ 0).mono (le_of_eq ?_)
    rw [add_zero, Pi.single_add]

/-- Run a one-outcome step using instrument outcomes in universe `w`. -/
@[expose]
noncomputable def actUnit {A B : QReg} (p : SubInstrument A B Unit) :
    QuantumComp₂ LocalSig.instruments.{w} spec A B Unit :=
  (QComp.act (p.map (ULift.up : Unit → ULift.{w} Unit))).bind fun _ ↦
    QuantumComp₂.pure ()

/-- Lifting the internal unit outcome preserves the executed subinstrument. -/
theorem run_actUnit {A B : QReg} (R : QuantumRuntime spec) (p : SubInstrument A B Unit) :
    R.run₂ .instruments (actUnit.{u₁, v₁, w} p) = p.frame R.D := by
  rw [actUnit, QuantumRuntime.run₂_bind, QuantumRuntime.run₂_act,
    SubInstrument.bind_pure, SubInstrument.map_eq_bind_pure, SubInstrument.frame_bind,
    SubInstrument.bind_assoc]
  simp only [SubInstrument.frame_pure, SubInstrument.pure_bind, QuantumRuntime.run₂_pure]
  exact SubInstrument.bind_pure _

/-- A lifted one-outcome step is lossless when its instrument is lossless. -/
theorem lossless_actUnit {A B : QReg} {p : SubInstrument A B Unit} (hp : p.Lossless) :
    (actUnit.{u₁, v₁, w} (spec := spec) p).Lossless .instruments :=
  QuantumComp₂.lossless_bind
    (QComp.lossless_act (hp.map ULift.up.{w})) fun _ ↦
    QuantumComp₂.lossless_pure _

/-- Lifting a local outcome introduces no oracle calls. -/
theorem isQueryBound_actUnit {A B : QReg} (p : SubInstrument A B Unit)
    (b : spec.Port → ℕ) : (actUnit.{u₁, v₁, w} p).IsQueryBound b := by
  exact (QuantumComp₂.isQueryBound_bind (b₁ := b) (b₂ := 0)
    (QComp.isQueryBound_act _ _) fun _ ↦ QuantumComp₂.isQueryBound_pure _ _).mono
      (add_zero b).le

/-- Interleave comb steps and calls with local outcomes in an arbitrary universe. -/
@[expose]
noncomputable def interleaveCompLift (i : spec.Port) (E : QReg)
    (ℓ : M ≃ spec.In i × E) (ℓ' : spec.Out i × E ≃ M) :
    (q : ℕ) → (Fin (q + 1) → SubInstrument M M Unit) →
      QuantumComp₂ LocalSig.instruments.{w} spec (QReg.of M) (QReg.of M) Unit
  | 0, s => actUnit (s 0)
  | q + 1, s =>
    ((interleaveCompLift i E ℓ ℓ' q (Fin.init s)).bind fun _ ↦
      QuantumComp₂.query i E ℓ).bind fun _ ↦
        actUnit ((SubInstrument.relabel ℓ').bind fun _ ↦ s (Fin.last _))

/-- Lifting the internal outcomes preserves the interleaved execution. -/
theorem run_interleaveCompLift (R : QuantumRuntime spec) (i : spec.Port) (E : QReg)
    (ℓ : M ≃ spec.In i × E) (ℓ' : spec.Out i × E ≃ M) :
    ∀ (q : ℕ) (s : Fin (q + 1) → SubInstrument M M Unit),
      R.run₂ .instruments (interleaveCompLift.{u₁, v₁, w} i E ℓ ℓ' q s) =
        interleave (R.combQuery i E ℓ ℓ') q fun j ↦ (s j).frame R.D
  | 0, s => by rw [interleaveCompLift, run_actUnit, interleave_zero]
  | q + 1, s => by
    rw [interleaveCompLift, QuantumRuntime.run₂_bind, QuantumRuntime.run₂_bind,
      run_interleaveCompLift R i E ℓ ℓ' q, QuantumRuntime.run₂_query,
      SubInstrument.bind_pure, run_actUnit, SubInstrument.frame_bind, interleave_succ,
      QuantumRuntime.combQuery]
    simp only [SubInstrument.bind_assoc]
    rfl

/-- Lossless comb steps remain lossless after lifting their internal outcomes. -/
theorem lossless_interleaveCompLift (i : spec.Port) (E : QReg)
    (ℓ : M ≃ spec.In i × E) (ℓ' : spec.Out i × E ≃ M) :
    ∀ {q : ℕ} {s : Fin (q + 1) → SubInstrument M M Unit}, (∀ j, (s j).Lossless) →
      (interleaveCompLift.{u₁, v₁, w} i E ℓ ℓ' q s).Lossless .instruments
  | 0, _, hs => lossless_actUnit (hs 0)
  | _ + 1, _, hs =>
    QuantumComp₂.lossless_bind (QuantumComp₂.lossless_bind
      (lossless_interleaveCompLift i E ℓ ℓ' fun j ↦ hs j.castSucc) fun _ ↦
        QuantumComp₂.lossless_query _ _ _) fun _ ↦
      lossless_actUnit ((SubInstrument.lossless_relabel _).bind fun _ ↦ hs _)

/-- Lifting internal outcomes preserves the comb's per-port query budget. -/
theorem isQueryBound_interleaveCompLift [DecidableEq spec.Port] (i : spec.Port) (E : QReg)
    (ℓ : M ≃ spec.In i × E) (ℓ' : spec.Out i × E ≃ M) :
    ∀ (q : ℕ) (s : Fin (q + 1) → SubInstrument M M Unit),
      (interleaveCompLift.{u₁, v₁, w} i E ℓ ℓ' q s).IsQueryBound (Pi.single i q)
  | 0, s => by rw [Pi.single_zero]; exact isQueryBound_actUnit _ _
  | q + 1, s => by
    rw [interleaveCompLift]
    refine (QuantumComp₂.isQueryBound_bind (QuantumComp₂.isQueryBound_bind
      (isQueryBound_interleaveCompLift i E ℓ ℓ' q (Fin.init s)) fun _ ↦
        (QuantumComp₂.isQueryBound_query_iff (A := QReg.of M) i E ℓ (Pi.single i 1)).mpr
          (by simp)) fun _ ↦ isQueryBound_actUnit _ 0).mono (le_of_eq ?_)
    rw [add_zero, Pi.single_add]

namespace QuantumComb

/-- **The program of a comb.** Its queries go to port `i` on the factor of `M` exposed by `ℓ`,
and the register returns to `M` through `ℓ'` after each call; the comb's initial substate is not
part of the program, which is observed from a substate of its starting register. -/
@[expose]
noncomputable def toComp (c : QuantumComb M α q) (i : spec.Port) (E : QReg)
    (ℓ : M ≃ spec.In i × E) (ℓ' : spec.Out i × E ≃ M) :
    QComp spec (QReg.of M) (QReg.of M) α :=
  (interleaveCompLift i E ℓ ℓ' q c.step).bind fun _ ↦ QComp.act c.final

/-- The program embedding preserves the whole outcome-indexed quantum operation.
Running `c.toComp i E ℓ ℓ'` against `R` gives the same subinstrument on `M × R.D` as
interleaving the comb's steps, framed by `R.D`, with `R.combQuery i E ℓ ℓ'`.

Each query's classical result is discarded by this embedding. The equality holds on every
joint input operator, including entangled inputs; initialization is used only when the
subinstrument is observed. This is the comb-to-program direction only. -/
theorem run_toComp (c : QuantumComb M α q) (R : QuantumRuntime spec) (i : spec.Port) (E : QReg)
    (ℓ : M ≃ spec.In i × E) (ℓ' : spec.Out i × E ≃ M) :
    R.run₂ .instruments (c.toComp i E ℓ ℓ') =
      (c.frame R.D R.init).run (R.combQuery i E ℓ ℓ') := by
  rw [toComp, QuantumRuntime.run₂_bind, run_interleaveCompLift, QuantumRuntime.run₂_act,
    SubInstrument.bind_pure]
  rfl

/-- The outcome distribution of the program of a comb, observed from the comb's initial substate, is
the outcome measure of the framed comb against the runtime's query step. -/
theorem evalDist_toComp [MeasurableSpace α] (c : QuantumComb M α q) (R : QuantumRuntime spec)
    (i : spec.Port) (E : QReg) (ℓ : M ≃ spec.In i × E) (ℓ' : spec.Out i × E ≃ M) :
    R.evalDist₂ .instruments (c.toComp i E ℓ ℓ') c.init =
      ((c.frame R.D R.init).run (R.combQuery i E ℓ ℓ')).outcomeMeasure
        (c.frame R.D R.init).init := by
  rw [QuantumRuntime.evalDist₂, run_toComp]
  rfl

/-- The program of a comb is lossless. -/
theorem lossless_toComp (c : QuantumComb M α q) (i : spec.Port) (E : QReg)
    (ℓ : M ≃ spec.In i × E) (ℓ' : spec.Out i × E ≃ M) :
    (c.toComp i E ℓ ℓ').Lossless .instruments :=
  QuantumComp₂.lossless_bind (lossless_interleaveCompLift i E ℓ ℓ' c.lossless_step) fun _ ↦
    QComp.lossless_act c.lossless_final

/-- The program of a `q`-query comb makes `q` calls of port `i` and none of any other port. -/
theorem isQueryBound_toComp [DecidableEq spec.Port] (c : QuantumComb M α q) (i : spec.Port)
    (E : QReg) (ℓ : M ≃ spec.In i × E) (ℓ' : spec.Out i × E ≃ M) :
    (c.toComp i E ℓ ℓ').IsQueryBound (Pi.single i q) :=
  (QuantumComp₂.isQueryBound_bind (isQueryBound_interleaveCompLift i E ℓ ℓ' q c.step) fun _ ↦
    QComp.isQueryBound_act _ 0).mono (add_zero _).le

end QuantumComb

end toComp

end Quantum
