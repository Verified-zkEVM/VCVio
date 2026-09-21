/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.OracleComp.Constructions.SampleableType.NativeMeasure
public import VCVio.OracleComp.SimSemantics.StateT.Measure
public import VCVio.OracleComp.QueryTracking.LoggingOracle.Core
public import VCVio.OracleComp.SimSemantics.OptionT.Basic

/-!
# Event bounds, support characterizations, and uniform counting

These checks exercise the `Pr{…}[…]` forms of union bounds, conditioning on a common draw,
support characterizations of probability-one and probability-zero events, wrapped optional
games simulated from a sampled state, and counting statements about uniform samples. Nothing
here imports a discrete probability backend. The game shapes follow interactive-protocol
security definitions: a stateful oracle implementation, an initial state sampled once, and an
`OptionT`-wrapped execution whose failures are excluded from the observed event.
-/

public section

open MeasureTheory ProbabilityTheory OracleSpec OracleComp
open scoped ENNReal

run_cmd do
  let env ← Lean.getEnv
  for name in [`PMF, `SPMF, `NeverFail, `EvalDistCompatible, `DiscreteEvalDistCompatible] do
    if env.contains name then
      throwError "native event bounds unexpectedly import {name}"

namespace VCVioTest.EventBounds

universe v

section monad

variable {m : Type → Type v} [Monad m] [LawfulMonad m]
  [EvalDistSemantics m] [LawfulEvalDistSemantics m] {α β : Type}

example (mx : m α) (p q : α → Prop) :
    Pr{let x ← mx}[p x ∨ q x] ≤ Pr{let x ← mx}[p x] + Pr{let x ← mx}[q x] :=
  prEvent_or_le mx p q

example (mx : m α) (p : Fin 5 → α → Prop) {ε : ℝ≥0∞} (h : ∀ i, Pr{let x ← mx}[p i x] ≤ ε) :
    Pr{let x ← mx}[∃ i, p i x] ≤ 5 * ε := by
  simpa using prEvent_exists_le_card_mul mx p h

example (mx : m α) (p : α → Prop) : Pr{let x ← mx}[p x] ≤ 1 := by simp

/-- Conditioning on a bad event of the common draw. -/
example (mx : m α) (f : α → m β) (bad : α → Prop) (q : β → Prop) {ε : ℝ≥0∞}
    (h : ∀ a, ¬ bad a → Pr{let y ← f a}[q y] ≤ ε) :
    Pr{let y ← mx >>= f}[q y] ≤ Pr{let a ← mx}[bad a] + ε :=
  prEvent_bind_le_prEvent_add mx f bad q h

/-- The conditional bound only needs to hold on reachable draws. -/
example [MonadAttach m] [WeaklyLawfulMonadAttach m]
    (mx : m α) (f : α → m β) (q : β → Prop) {ε : ℝ≥0∞}
    (h : ∀ a ∈ support mx, Pr{let y ← f a}[q y] ≤ ε) :
    Pr{let y ← mx >>= f}[q y] ≤ ε :=
  prEvent_bind_le_of_forall_le_of_support mx f q h

end monad

/-! ## Games in `OptionT ProbComp`

A verifier that reads a state-dependent answer through a stateful implementation and rejects
by failing. Completeness is a support statement about the unsimulated program. -/

section game

/-- An oracle with a single query returning a natural number. -/
@[expose, reducible] def counterSpec : OracleSpec Unit := fun _ ↦ Nat

/-- A stateful implementation answering with the current counter and incrementing it. -/
@[expose] def counterImpl : QueryImpl counterSpec (StateT Nat ProbComp) := fun _ ↦
  StateT.mk fun n ↦ pure (n, n + 1)

/-- A program that queries twice and returns the first answer with the sum of both after a
check that every answer passes. -/
@[expose] def twoQueries : OptionT (OracleComp counterSpec) (Nat × Nat) := do
  let a ← (query () : OracleComp counterSpec (counterSpec.Range ()))
  let b ← (query () : OracleComp counterSpec (counterSpec.Range ()))
  if a ≤ a + b then pure (a, a + b) else failure

/-- The completeness game samples a starting counter and runs the program. -/
@[expose] def game (init : ProbComp Nat) : OptionT ProbComp (Nat × Nat) :=
  OptionT.mk (do let s ← init; (simulateQ counterImpl twoQueries.run).run' s)

/-- A property of every present value of the unsimulated program holds with probability one in
the simulated game, whatever the initial state and implementation. -/
example (init : ProbComp Nat) :
    Pr{let r ← game init}[r.1 ≤ r.2] = 1 := by
  refine OptionT.prEvent_mk_simulateQ_run'_eq_one_of_support init counterImpl _ _ ?_
  intro o ho
  simp only [twoQueries, HasQuery.instOfMonadLift_query, le_add_iff_nonneg_right, zero_le,
    ↓reduceIte, bind_pure_comp, OptionT.run_bind, OptionT.run_monadLift, monadLift_self,
    OptionT.run_map, Functor.map_map, Option.map_some, Option.elimM_map, Option.elim_some,
    MonadAttach.support_bind, support_liftM, OracleQuery.input_query, OracleQuery.cont_query,
    Set.range_id, Set.mem_univ, MonadAttach.support_map, Set.image_univ, Set.iUnion_true,
    Set.mem_iUnion, Set.mem_range] at ho
  obtain ⟨a, b, rfl⟩ := ho
  exact ⟨(a, a + b), rfl, Nat.le_add_right a b⟩

/-- A failing game still admits support-indexed event comparison, without a losslessness
assumption or a measurable space on the payload. -/
example {α : Type} (mx : OptionT ProbComp α) (p q : α → Prop)
    (h : ∀ a ∈ support mx, p a → q a) :
    Pr{let a ← mx}[p a] ≤ Pr{let a ← mx}[q a] :=
  prEvent_mono_of_support mx p q h

/-- A potentially failing optional prefix preserves the honest product lower bound: only the
mass of the prefix event contributes, and every continuation reached under that event satisfies
the conditional lower bound. -/
example {α β : Type} (mx : OptionT ProbComp α) (f : α → OptionT ProbComp β)
    (p : α → Prop) (q : β → Prop) {r r' : ℝ≥0∞}
    (h : r ≤ Pr{let a ← mx}[p a])
    (h' : ∀ a, p a → r' ≤ Pr{let b ← f a}[q b]) :
    r * r' ≤ Pr{let b ← mx >>= f}[q b] :=
  mul_le_prEvent_bind_of_forall mx f p q h h'

/-- Two reductions share the adversary's draw; the draw's payload needs no measurable space. -/
example {α : Type} (mx : ProbComp α) (win left right : α → Bool)
    (h : ∀ a ∈ support mx, win a = true → left a = true ∨ right a = true) :
    𝒟[mx >>= fun a ↦ pure (win a)] {true} ≤
      𝒟[mx >>= fun a ↦ pure (left a)] {true} +
        𝒟[mx >>= fun a ↦ pure (right a)] {true} := by
  refine evalDist_bind_apply_le_add_of_support mx _ _ _ (measurableSet_singleton true) ?_
  exact fun a ha ↦ evalDist_pure_apply_le_add_of_imp _ _ _ (h a ha)

end game

/-! ## Uniform counting -/

section uniform

example (p : Fin 7 → Prop) [DecidablePred p] (h : (Finset.univ.filter p).card < 3) :
    Pr{let x ← $ᵗ Fin 7}[p x] < 3 / 7 := by
  rw [show (7 : ℝ≥0∞) = Fintype.card (Fin 7) by simp]
  exact (SampleableType.prEvent_uniformSample_lt_div_iff p).mpr h

example (p : Fin 7 → Prop) (h : ∀ x, p x) : Pr{let x ← $ᵗ Fin 7}[p x] = 1 :=
  (SampleableType.prEvent_uniformSample_eq_one_iff p).mpr h

example (a : Fin 7) : Pr{let x ← $ᵗ Fin 7}[x = a] = 7⁻¹ := by
  rw [SampleableType.prEvent_uniformSample_eq_singleton]
  simp

example (p : Fin 3 × Fin 5 → Prop) :
    Pr{let z ← $ᵗ (Fin 3 × Fin 5)}[p z] = Pr{let x ← $ᵗ Fin 3; let y ← $ᵗ Fin 5}[p (x, y)] :=
  SampleableType.prEvent_uniformSample_prod p

example (p : Fin 3 × Fin 5 → Prop) {ε : ℝ≥0∞}
    (h : ∀ x, Pr{let y ← $ᵗ Fin 5}[p (x, y)] ≤ ε) :
    Pr{let z ← $ᵗ (Fin 3 × Fin 5)}[p z] ≤ ε :=
  SampleableType.prEvent_uniformSample_prod_le_of_forall_fst p h

example (p : Fin 3 × Fin 5 → Prop) {ε : ℝ≥0∞}
    (h : ∀ y, Pr{let x ← $ᵗ Fin 3}[p (x, y)] ≤ ε) :
    Pr{let z ← $ᵗ (Fin 3 × Fin 5)}[p z] ≤ ε :=
  SampleableType.prEvent_uniformSample_prod_le_of_forall_snd p h

example (p : (Fin 4 → Fin 3) → Prop) :
    Pr{let v ← $ᵗ (Fin 4 → Fin 3)}[p v] =
      Pr{let w ← $ᵗ (Fin 3 → Fin 3); let x ← $ᵗ Fin 3}[p (Fin.snoc w x)] :=
  SampleableType.prEvent_uniformSample_finSnoc p

example (event : (Fin 4 → Fin 3) → Prop) (bad : (Fin 3 → Fin 3) → Prop) {ε : ℝ≥0∞}
    (h : ∀ y, ¬ bad y → Pr{let x ← $ᵗ Fin 3}[event (Fin.snoc y x)] ≤ ε) :
    Pr{let z ← $ᵗ (Fin 4 → Fin 3)}[event z] ≤
      Pr{let y ← $ᵗ (Fin 3 → Fin 3)}[bad y] + ε :=
  SampleableType.prEvent_uniformSample_finSnoc_le_add event bad h

/-- The conditional snoc bound includes the empty-prefix boundary. -/
example (event : (Fin 1 → Fin 3) → Prop) (bad : (Fin 0 → Fin 3) → Prop) {ε : ℝ≥0∞}
    (h : ∀ y, ¬ bad y → Pr{let x ← $ᵗ Fin 3}[event (Fin.snoc y x)] ≤ ε) :
    Pr{let z ← $ᵗ (Fin 1 → Fin 3)}[event z] ≤
      Pr{let y ← $ᵗ (Fin 0 → Fin 3)}[bad y] + ε :=
  SampleableType.prEvent_uniformSample_finSnoc_le_add event bad h

/-- Any two samplers of the same type agree on every event. -/
example (i₁ i₂ : SampleableType (Fin 5)) (p : Fin 5 → Prop) :
    Pr{let x ← @uniformSample (Fin 5) i₁}[p x] = Pr{let x ← @uniformSample (Fin 5) i₂}[p x] :=
  SampleableType.prEvent_uniformSample_inst_irrel i₁ i₂ p

/-- Subtypes of finite types have an enumeration sampler. -/
noncomputable example : SampleableType {n : Fin 10 // n.val % 2 = 0} :=
  haveI : Nonempty {n : Fin 10 // n.val % 2 = 0} := ⟨⟨0, rfl⟩⟩
  SampleableType.subtype (Fin 10) _

/-- Dependent finite products have an explicit enumeration sampler without a global fallback. -/
noncomputable example : SampleableType (∀ i : Fin 3, Fin (i + 1)) :=
  SampleableType.piOfFintype _

/-- The dependent-product constructor includes an empty product even when its unreachable fibers
are empty. -/
noncomputable example : SampleableType (∀ _i : Fin 0, Empty) := by
  letI : ∀ _i : Fin 0, Nonempty Empty := fun i => Fin.elim0 i
  exact SampleableType.piOfFintype _

end uniform

end VCVioTest.EventBounds
