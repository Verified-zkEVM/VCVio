/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.ProgramLogic.Library.T1.Bisim
public meta import VCVio.ProgramLogic.Tactics

/-!
# Bisimulation rules: usage tests

Each rule closes a handler-equivalence goal in one application, leaving the per-query facts,
which `simp` discharges for these handlers.
-/

@[expose] public section

open OracleSpec OracleComp OracleComp.ProgramLogic.Relational

namespace VCVioTest.ProgramLogic.Library.Bisim

/-- A fair coin that counts its calls. -/
def countingCoin : QueryImpl coinSpec (StateT ℕ ProbComp) := fun _ =>
  StateT.mk fun n => (fun b => (b, n + 1)) <$> ($ᵗ Bool)

/-- A counting coin that answers `false` before it is primed (counter zero). -/
def guardedCoin : QueryImpl coinSpec (StateT ℕ ProbComp) := fun _ =>
  StateT.mk fun n => if 0 < n then (fun b => (b, n + 1)) <$> ($ᵗ Bool) else pure (false, n)

/-- A primed counting coin that answers with the negated draw. -/
def flippedCoin : QueryImpl coinSpec (StateT ℕ ProbComp) := fun _ =>
  StateT.mk fun n => if 0 < n then (fun b => (!b, n + 1)) <$> ($ᵗ Bool) else pure (false, n)

/-- A flipped counting coin that also logs its draws. -/
def loggedFlippedCoin : QueryImpl coinSpec (StateT (ℕ × List Bool) ProbComp) := fun _ =>
  StateT.mk fun s => (fun b => (!b, (s.1 + 1, b :: s.2))) <$> ($ᵗ Bool)

lemma countingCoin_run (t : Unit) (n : ℕ) :
    (countingCoin t).run n = (fun b => (b, n + 1)) <$> ($ᵗ Bool) := rfl

lemma countingCoin_pres (t : Unit) (n : ℕ) (_ : 0 < n) :
    ∀ z ∈ support ((countingCoin t).run n), 0 < z.2 := by
  intro z hz
  rw [countingCoin_run, support_map] at hz
  obtain ⟨b, -, rfl⟩ := hz
  exact n.succ_pos

lemma map_not_uniformBool {β : Type} (f : Bool → β) :
    (fun b => f (!b)) <$> ($ᵗ Bool : ProbComp Bool) =ᵈ f <$> ($ᵗ Bool : ProbComp Bool) := by
  have h := (SampleableType.map_uniformSample_evalDistEq_of_bijective
    (f := Bool.not) Bool.involutive_not.bijective).map f
  simpa only [Functor.map_map, Function.comp_def] using h

/-- Exact bisimulation on an invariant: from a primed state the guard never fires. -/
example {α : Type} (oa : OracleComp coinSpec α) (n : ℕ) (hn : 0 < n) :
    (simulateQ guardedCoin oa).run' n = (simulateQ countingCoin oa).run' n :=
  simulateQ_run'_eq_of_impl_eq_on_inv _ _ (0 < ·)
    (fun _ n hn => by simp [guardedCoin, countingCoin, hn])
    countingCoin_pres oa n hn

/-- Bisimulation in distribution on an invariant: the negated coin is still a fair coin. -/
example {α : Type} (oa : OracleComp coinSpec α) (n : ℕ) (hn : 0 < n) (p : α → Prop) :
    Pr{let x ← (simulateQ flippedCoin oa).run' n}[p x] =
      Pr{let x ← (simulateQ countingCoin oa).run' n}[p x] :=
  (evalDistEq_simulateQ_run'_of_impl_evalDistEq_on_inv _ _ (0 < ·)
    (fun _ n hn => by
      simpa only [flippedCoin, countingCoin, StateT.run_mk, hn, ↓reduceIte] using
        map_not_uniformBool fun b => (b, n + 1))
    countingCoin_pres oa n hn).prEvent_eq p

/-- The relational form, through `rvcstep with`. -/
example {α : Type} (oa : OracleComp coinSpec α) (n : ℕ) (hn : 0 < n) :
    RelTriple ((simulateQ flippedCoin oa).run' n) ((simulateQ countingCoin oa).run' n)
      (EqRel α) := by
  rvcstep with relTriple_simulateQ_run'_of_impl_evalDistEq_on_inv _ _ (0 < ·)
    (fun _ n hn => by
      simpa only [flippedCoin, countingCoin, StateT.run_mk, hn, ↓reduceIte] using
        map_not_uniformBool fun b => (b, n + 1))
    countingCoin_pres oa n hn

/-- Bisimulation through a projection, in distribution: forgetting the log of the flipped coin
leaves a fair counting coin. -/
example {α : Type} (oa : OracleComp coinSpec α) (s : ℕ × List Bool) :
    (simulateQ loggedFlippedCoin oa).run' s =ᵈ (simulateQ countingCoin oa).run' s.1 :=
  evalDistEq_run'_simulateQ_of_query_map_evalDistEq _ _ (fun _ => True) Prod.fst
    (fun _ _ _ _ _ => trivial)
    (fun _ s _ => by
      simpa [loggedFlippedCoin, countingCoin, Functor.map_map] using
        map_not_uniformBool (fun b => (b, s.1 + 1)))
    oa s trivial

/-- A bad flag set by a `true` coin; once set, the two handlers answer differently. -/
def flagCoin (afterBad : Bool) : QueryImpl coinSpec (StateT Bool ProbComp) := fun _ =>
  StateT.mk fun bad => if bad then pure (afterBad, true) else (fun b => (b, b)) <$> ($ᵗ Bool)

/-- Identical until bad, as a game hop. -/
example {α : Type} (oa : OracleComp coinSpec α) (p : α → Prop) :
    Pr{let x ← (simulateQ (flagCoin true) oa).run' false}[p x] ≤
      Pr{let x ← (simulateQ (flagCoin false) oa).run' false}[p x] +
        Pr{let z ← (simulateQ (flagCoin true) oa).run false}[z.2 = true] :=
  prEvent_simulateQ_run'_le_add_prEvent_bad_of_run_eq _ _ (· = true)
    (fun _ s hs => by simp [flagCoin, hs])
    (fun _ s hs z hz => by simp_all [flagCoin]) (fun _ s hs z hz => by simp_all [flagCoin])
    oa false p

/-- Cross-type bijection coupling, then a pure leaf closed by `rvcgen`. -/
example : RelTriple (($ᵗ Bool : ProbComp Bool) >>= fun b => pure (finTwoEquiv.symm b))
    (($ᵗ (Fin 2) : ProbComp (Fin 2)) >>= fun i => pure i) (EqRel (Fin 2)) := by
  rvcstep with relTriple_bind_uniformSample_bij_cross (f := finTwoEquiv.symm) ?_
    finTwoEquiv.symm.bijective
  intro b
  rvcgen

/-- The same goal in one `rvcgen with` call, which also closes the pure leaf. (A hint
`rvcstep using finTwoEquiv.symm` is read as a same-type bijection and times out.) -/
example : RelTriple (($ᵗ Bool : ProbComp Bool) >>= fun b => pure (finTwoEquiv.symm b))
    (($ᵗ (Fin 2) : ProbComp (Fin 2)) >>= fun i => pure i) (EqRel (Fin 2)) := by
  rvcgen with relTriple_bind_uniformSample_bij_cross (f := finTwoEquiv.symm) ?_
    finTwoEquiv.symm.bijective

/-- The coupling rule alone, through `exact`. -/
example : RelTriple ($ᵗ (Fin 2) : ProbComp (Fin 2)) ($ᵗ Bool : ProbComp Bool)
    (fun i b => finTwoEquiv i = b) :=
  relTriple_uniformSample_bij_cross finTwoEquiv.bijective _ fun _ => rfl

end VCVioTest.ProgramLogic.Library.Bisim
