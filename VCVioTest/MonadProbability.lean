/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio

/-!
# Generic-monad probability tactic gate

The companion of `VCVioTest/ProbabilityTactics.lean` over an abstract monad
`m` with a lawful measure semantics (`[EvalDistSemantics m] [LawfulEvalDistSemantics m]`), and over
the concrete carriers `Id`, `OptionT ProbComp` and `ExceptT Bool ProbComp`. The rules are those
of *Normal forms and the tactic contract* in `docs/agents/probability.md`.

The generic setting exposes what `ProbComp` masks: a discarded computation contributes its success
mass `𝒟[mx] Set.univ`, which is one only for a lossless carrier. `grind` closes the structural and
pushforward families; it has no Dirac or success-mass rules, so those families are `simp`-only.
-/

public section

open MeasureTheory OracleComp
open scoped ENNReal

namespace VCVioTest.MonadProbability

/-! ## Generic monad `m` -/

section generic

variable {α β : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
  [EvalDistSemantics m] [LawfulEvalDistSemantics m]

/-! ### `pure` -/

example [MeasurableSpace α] (x : α) : 𝒟[(pure x : m α)] = Measure.dirac x := by
  fail_if_success grind  -- gap(grind, 2026-09-26): Dirac and success masses, covers the section
  simp
example (p : α → Prop) (x : α) : Pr{let y ← (pure x : m α)}[p y] = propInd (p x) := by simp
example (p : α → Prop) (x : α) : Pr{let y ← (pure x : m α)}[p y] = propInd (p x) := by grind
example (p : α → Prop) [DecidablePred p] (x : α) :
    Pr{let y ← (pure x : m α)}[p y] = if p x then 1 else 0 := by simp [propInd_eq_ite]
example [MeasurableSpace α] (x : α) : 𝒟[(pure x : m α)] Set.univ = 1 := by simp
example (x : α) : Pr{let _ ← (pure x : m α)}[True] = 1 := by simp

/-! ### Bounds and constant events -/

example (mx : m α) (p : α → Prop) : Pr{let x ← mx}[p x] ≤ 1 := by
  fail_if_success grind  -- gap(grind, 2026-09-26): no measure-side bound rules
  simp
example (mx : m α) : Pr{let _ ← mx}[False] = 0 := by simp
example (mx : m α) : Pr{let _ ← mx}[False] = 0 := by grind

/-! ### `bind` with a constant continuation — the success factor
A discarded computation scales the continuation by its success mass. -/

example [MeasurableSpace α] [MeasurableSpace β] (mx : m α) (my : m β) :
    𝒟[mx >>= fun _ => my] = 𝒟[mx] Set.univ • 𝒟[my] := by
  fail_if_success grind  -- gap(grind, 2026-09-26): success masses
  simp

/-! ### `bind`/`pure` normalisation -/

example [MeasurableSpace α] (mx : m α) : 𝒟[do let a ← mx; pure a] = 𝒟[mx] := by simp
example [MeasurableSpace α] (mx : m α) : 𝒟[do let a ← mx; pure a] = 𝒟[mx] := by grind
example [MeasurableSpace α] (mx : m α) :
    𝒟[do let a ← mx; let b ← pure a; let c ← pure b; pure c] = 𝒟[mx] := by simp
example [MeasurableSpace α] (mx : m α) :
    𝒟[do let a ← mx; let b ← pure a; let c ← pure b; pure c] = 𝒟[mx] := by grind

/-! ### `map` (`<$>`)
The event of a map is the pulled-back event; mapping preserves the success mass. -/

example (f : α → β) (mx : m α) (q : β → Prop) :
    Pr{let y ← f <$> mx}[q y] = Pr{let x ← mx}[q (f x)] := by simp
example (f : α → β) (mx : m α) (q : β → Prop) :
    Pr{let y ← f <$> mx}[q y] = Pr{let x ← mx}[q (f x)] := by grind
example (f : α → β) (mx : m α) : Pr{let _ ← f <$> mx}[True] = Pr{let _ ← mx}[True] := by simp
example (f : α → β) (mx : m α) : Pr{let _ ← f <$> mx}[True] = Pr{let _ ← mx}[True] := by grind

/-! ### `seqLeft` (`<*`), `seqRight` (`*>`) and `seq` (`<*>`)
The discarded computation contributes only its success mass; the `Prod.mk` product is the
product measure. -/

example (mx : m α) (my : m β) (p : β → Prop) :
    Pr{let y ← mx *> my}[p y] = Pr{let y ← my}[p y] * Pr{let _ ← mx}[True] := by simp
example (mx : m α) (my : m β) (p : β → Prop) :
    Pr{let y ← mx *> my}[p y] = Pr{let y ← my}[p y] * Pr{let _ ← mx}[True] := by
  grind
example (mx : m α) (my : m β) (p : α → Prop) :
    Pr{let x ← mx <* my}[p x] = Pr{let x ← mx}[p x] * Pr{let _ ← my}[True] := by simp
example (mx : m α) (my : m β) (p : α → Prop) :
    Pr{let x ← mx <* my}[p x] = Pr{let x ← mx}[p x] * Pr{let _ ← my}[True] := by
  grind
example [MeasurableSpace α] [MeasurableSpace β] (mx : m α) (my : m β) :
    𝒟[Prod.mk <$> mx <*> my] = 𝒟[mx].prod 𝒟[my] := by simp
example [MeasurableSpace α] [MeasurableSpace β] (mx : m α) (my : m β) :
    𝒟[Prod.mk <$> mx <*> my] = 𝒟[mx].prod 𝒟[my] := by grind

/-! ### Failure probability
`prFail` is the missing mass; `pure` and maps are closed by `simp` and `grind`. -/

example (x : α) : prFail (pure x : m α) = 0 := by simp
example (x : α) : prFail (pure x : m α) = 0 := by grind
example (f : α → β) (mx : m α) : prFail (f <$> mx) = prFail mx := by simp
example (f : α → β) (mx : m α) : prFail (f <$> mx) = prFail mx := by grind
example (mx : m α) : Pr{let _ ← mx}[True] + prFail mx = 1 := by simp
example [MeasurableSpace α] [DiscreteMeasurableSpace α] (mx : m α) (f : α → m β) :
    prFail (mx >>= f) = prFail mx + ∫⁻ x, prFail (f x) ∂𝒟[mx] :=
  prFail_bind_eq_add_lintegral_of_discrete mx f

end generic

/-! ## Concrete carriers
For the lossless carriers the success factor collapses; for `OptionT` it does not.

gap(grind): the concrete Dirac, success-mass and `guard` families are `simp`-only, as in the
generic section; the first entry carries the guard. -/

example (x : Bool) : 𝒟[(pure x : Id Bool)] {x} = 1 := by
  fail_if_success grind  -- gap(grind, 2026-09-26): concrete masses, covers the section
  simp
example (mx my : Id Bool) (y : Bool) : 𝒟[mx *> my] {y} = 𝒟[my] {y} := by simp

example (x : Bool) : 𝒟[(pure x : OptionT ProbComp Bool)] {x} = 1 := by simp
example : 𝒟[(failure : OptionT ProbComp Bool)] Set.univ = 0 := by simp
example : 𝒟[(failure : OptionT ProbComp Bool)] Set.univ = 0 := by grind
example (mx my : OptionT ProbComp Bool) (y : Bool) :
    𝒟[mx *> my] {y} = 𝒟[mx] Set.univ * 𝒟[my] {y} := by simp

example (x : Bool) : 𝒟[(pure x : ExceptT Bool ProbComp Bool)] {x} = 1 := by simp

example (p : Prop) [Decidable p] :
    𝒟[(guard p : OptionT ProbComp Unit)] Set.univ = if p then 1 else 0 := by simp
example (p : Prop) [Decidable p] :
    support (guard p : OptionT ProbComp Unit) = if p then {()} else ∅ := by simp

example (oa : ProbComp Bool) : prFail oa = 0 := by simp
example (oa : ProbComp Bool) : prFail oa = 0 := by grind
example : prFail (failure : OptionT ProbComp Bool) = 1 := by simp
example (p : Prop) [Decidable p] :
    prFail (guard p : OptionT ProbComp Unit) = if p then 0 else 1 := by simp
example (oa : ProbComp Bool) : prFail (OptionT.lift oa) = 0 := by simp

end VCVioTest.MonadProbability
