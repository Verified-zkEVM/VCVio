/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.OracleComp.EvalDist.Sum
public import VCVio.OracleComp.SimSemantics.StateT.Basic
public import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# Probability bounds through binds, uniform draws and stateful runs

Event bounds in the shapes upper-bound and exact-probability proofs meet, with each hypothesis
stated where the proof has it:

* **Union bound through a bind**: `prEvent_bind_le_add_iSup` bounds an event after a bind by the
  first draw's bad event plus the worst good continuation.
* **Uniform draws**: `prEvent_uniformSample_bind_eq` averages the continuations of a finite
  uniform draw, and `prEvent_uniformSample_bind_le_add` charges `d / |β|` for `d` bad values and
  `ε` for every good continuation (the fresh-draw bound).
* **Stateful runs**: `prEvent_run_bind_le_add_of_support`, `prEvent_run_bind_le_of_forall_le` and
  `prEvent_run_bind_eq_tsum` for `StateT` runs, and their `simulateQ` forms
  `prEvent_simulateQ_run_bind_le_add_of_support` and `prEvent_simulateQ_run_bind_eq_tsum`, whose
  hypotheses range over the support of the first run; `prEvent_run'_eq_prEvent_run` reads an
  output event of `run'` on the full run.
* **Reordering**: `evalDistEq_run_liftM_bind_swap` swaps a state-independent draw past a stateful
  computation in a `StateT` run.

The bind rules take a `Prop`-valued continuation, `prEvent (mx >>= g)`: a multi-draw event
`Pr{let x ← mx; let y ← f x}[q x y]` elaborates to that form, with an event that may depend on the
first draw.
-/

@[expose] public section

open OracleSpec MeasureTheory
open scoped ENNReal

universe u

namespace OracleComp

variable {ι : Type u} {spec : OracleSpec.{u, 0} ι} [AnswerMeasure spec] {α β γ σ : Type}

/-! ## Binds and uniform draws -/

/-- **Union bound through a bind**: the first draw's bad event plus the worst continuation event
on a good possible output (the event may depend on the first draw). -/
theorem prEvent_bind_le_add_iSup (mx : OracleComp spec α) (g : α → OracleComp spec Prop)
    (bad : α → Prop) :
    prEvent (mx >>= g) ≤
      Pr{let x ← mx}[bad x] + ⨆ x ∈ support mx, ⨆ (_ : ¬bad x), prEvent (g x) := by
  simpa only [id_map] using prEvent_bind_le_prEvent_add_of_support mx g bad id fun x hx hb =>
    (le_of_eq (by rw [id_map])).trans (le_iSup₂_of_le x hx (le_iSup_of_le hb le_rfl))

/-- A finite uniform draw averages the event probabilities of its continuations. -/
theorem prEvent_uniformSample_bind_eq [SampleableType α] [Fintype α] (g : α → ProbComp Prop) :
    prEvent (($ᵗ α : ProbComp α) >>= g) = (∑ x, prEvent (g x)) / Fintype.card α := by
  have h := prEvent_bind_eq_sum_fintype ($ᵗ α : ProbComp α) g id
  simp only [id_map] at h
  rw [h, ENNReal.div_eq_inv_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by
    rw [SampleableType.prEvent_uniformSample_eq_singleton]

/-- **Fresh uniform draw.** A uniform draw that is bad on at most `d` values is charged
`d / |α|`, and every continuation event off the bad values is charged `ε`. -/
theorem prEvent_uniformSample_bind_le_add [SampleableType α] [Fintype α]
    (g : α → ProbComp Prop) (bad : α → Prop) [DecidablePred bad]
    {d : ℕ} (hd : (Finset.univ.filter bad).card ≤ d) {ε : ℝ≥0∞}
    (h : ∀ x, ¬bad x → prEvent (g x) ≤ ε) :
    prEvent (($ᵗ α : ProbComp α) >>= g) ≤ d / Fintype.card α + ε := by
  refine (prEvent_bind_le_add_iSup _ g bad).trans (add_le_add ?_ ?_)
  · rw [SampleableType.prEvent_uniformSample]
    exact ENNReal.div_le_div_right (by exact_mod_cast hd) _
  · exact iSup₂_le fun x _ => iSup_le fun hx => h x hx

/-! ## Stateful runs -/

/-- An output event of `run'` is the event of the output component of `run`. -/
theorem prEvent_run'_eq_prEvent_run (mx : StateT σ (OracleComp spec) α) (s : σ)
    (p : α → Prop) :
    Pr{let x ← mx.run' s}[p x] = Pr{let z ← mx.run s}[p z.1] := by
  rw [StateT.run'_eq, prEvent_map]

/-- **Union bound through a stateful bind**: the first run's bad event plus a bound on every good
continuation run from a possible output-state pair. -/
theorem prEvent_run_bind_le_add_of_support (mx : StateT σ (OracleComp spec) α)
    (f : α → StateT σ (OracleComp spec) β) (s : σ) (bad : α × σ → Prop) (q : β × σ → Prop)
    {ε : ℝ≥0∞} (h : ∀ z ∈ support (mx.run s), ¬bad z → Pr{let w ← (f z.1).run z.2}[q w] ≤ ε) :
    Pr{let w ← (mx >>= f).run s}[q w] ≤ Pr{let z ← mx.run s}[bad z] + ε := by
  rw [StateT.run_bind]
  exact prEvent_bind_le_prEvent_add_of_support _ _ bad q h

/-- A bound on every continuation run from a possible output-state pair bounds a stateful
bind. -/
theorem prEvent_run_bind_le_of_forall_le (mx : StateT σ (OracleComp spec) α)
    (f : α → StateT σ (OracleComp spec) β) (s : σ) (q : β × σ → Prop) {ε : ℝ≥0∞}
    (h : ∀ z ∈ support (mx.run s), Pr{let w ← (f z.1).run z.2}[q w] ≤ ε) :
    Pr{let w ← (mx >>= f).run s}[q w] ≤ ε := by
  rw [StateT.run_bind]
  exact prEvent_bind_le_of_forall_le_of_support _ _ q h

/-- A stateful bind's event is the sum over the first run's output-state pairs. -/
theorem prEvent_run_bind_eq_tsum [∀ t, Finite (spec.Range t)] (mx : StateT σ (OracleComp spec) α)
    (f : α → StateT σ (OracleComp spec) β) (s : σ) (q : β × σ → Prop) :
    Pr{let w ← (mx >>= f).run s}[q w] =
      ∑' z, Pr{let z' ← mx.run s}[z' = z] * Pr{let w ← (f z.1).run z.2}[q w] := by
  rw [StateT.run_bind, prEvent_bind_eq_tsum]

/-- **Union bound through a simulated bind**: the first simulation's bad event plus a bound on
every good continuation simulated from a possible output-state pair. -/
theorem prEvent_simulateQ_run_bind_le_add_of_support {ι' : Type*} {spec' : OracleSpec ι'}
    (impl : QueryImpl spec' (StateT σ (OracleComp spec))) (oa : OracleComp spec' α)
    (f : α → OracleComp spec' β) (s : σ) (bad : α × σ → Prop) (q : β × σ → Prop) {ε : ℝ≥0∞}
    (h : ∀ z ∈ support ((simulateQ impl oa).run s), ¬bad z →
      Pr{let w ← (simulateQ impl (f z.1)).run z.2}[q w] ≤ ε) :
    Pr{let w ← (simulateQ impl (oa >>= f)).run s}[q w] ≤
      Pr{let z ← (simulateQ impl oa).run s}[bad z] + ε := by
  rw [simulateQ_bind]
  exact prEvent_run_bind_le_add_of_support _ _ s bad q h

/-- A simulated bind's event is the sum over the first simulation's output-state pairs. -/
theorem prEvent_simulateQ_run_bind_eq_tsum [∀ t, Finite (spec.Range t)] {ι' : Type*}
    {spec' : OracleSpec ι'}
    (impl : QueryImpl spec' (StateT σ (OracleComp spec))) (oa : OracleComp spec' α)
    (f : α → OracleComp spec' β) (s : σ) (q : β × σ → Prop) :
    Pr{let w ← (simulateQ impl (oa >>= f)).run s}[q w] =
      ∑' z, Pr{let z' ← (simulateQ impl oa).run s}[z' = z] *
        Pr{let w ← (simulateQ impl (f z.1)).run z.2}[q w] := by
  rw [simulateQ_bind, prEvent_run_bind_eq_tsum]

/-- **Reordering in a stateful run.** A state-independent draw commutes with a stateful
computation in a `StateT` run, in distribution. -/
theorem evalDistEq_run_liftM_bind_swap [∀ t, Countable (spec.Range t)]
    (mx : OracleComp spec α) (my : StateT σ (OracleComp spec) β)
    (f : α → β → StateT σ (OracleComp spec) γ) (s : σ) :
    (do let a ← (liftM mx : StateT σ (OracleComp spec) α); let b ← my; f a b).run s =ᵈ
      (do let b ← my; let a ← (liftM mx : StateT σ (OracleComp spec) α); f a b).run s := by
  let : MeasurableSpace (γ × σ) := ⊤
  refine EvalDistEq.of_evalDist_eq ?_
  simp only [StateT.run_bind, liftM_run_StateT, bind_assoc, pure_bind]
  exact evalDist_bind_bind_swap mx (my.run s) fun a p => (f a p.1).run p.2

end OracleComp
