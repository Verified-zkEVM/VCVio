/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio

/-!
# Fail-fast and opt-in gates for `grind` on probability goals

Companion to the probability benchmarks (`VCVioTest/ProbabilityTactics.lean`,
`VCVioTest/MonadProbability.lean`, `VCVioTest/LongChainPrograms.lean`), which gate what
`grind` *solves*. This file gates the other half of the design: what `grind` deliberately does
**not** solve, and that it fails **fast** when it doesn't.

Each support characterization kept out of the default `grind` set gets one example of the form

```
example : <the lemma's own statement> := by
  fail_if_success grind   -- the lemma is really out of the default set
  grind [<the lemma>]     -- and the documented opt-in really closes the goal
```

The gate is loud in both failure directions:

* If someone tags one of these lemmas `@[grind]`, bare `grind` starts *succeeding* on its statement
  and `fail_if_success` fails the build.
* If a change to the default set makes bare `grind` *saturate* instead of failing fast on one of
  these statements, the resulting `(deterministic) timeout` is a runtime exception that escapes
  `fail_if_success` and fails the build. The unbounded support quantifiers in these statements are
  why they stay opt-in.
-/

public section

open OracleComp ProbComp ENNReal

namespace VCVioTest.GrindFailFast

/-! ## Support characterizations under uniform answers

Bare `grind` must fail (fast); the documented opt-in `grind [<lemma>]` must close the goal. -/

section uniform

variable {ι : Type} {spec : OracleSpec ι} [OracleSpec.UniformAnswerMeasure spec] {α : Type}
  (p : α → Prop) (mx : OracleComp spec α) (x : α)

example : Pr{let y ← mx}[p y] = 0 ↔ ∀ y ∈ support mx, ¬ p y := by
  fail_if_success grind
  grind [OracleComp.prEvent_eq_zero_iff]

example : Pr{let y ← mx}[p y] ≠ 0 ↔ ∃ y ∈ support mx, p y := by
  fail_if_success grind
  grind [OracleComp.prEvent_eq_zero_iff]

example : 0 < Pr{let y ← mx}[p y] ↔ ∃ y ∈ support mx, p y := by
  fail_if_success grind
  grind [OracleComp.prEvent_pos_iff]

example : Pr{let y ← mx}[p y] = 1 ↔ ∀ y ∈ support mx, p y := by
  fail_if_success grind
  grind [OracleComp.prEvent_eq_one_iff]

example : 1 = Pr{let y ← mx}[p y] ↔ ∀ y ∈ support mx, p y := by
  fail_if_success grind
  grind [OracleComp.prEvent_eq_one_iff]

example : Pr{let y ← mx}[y = x] = 1 ↔ ∀ y ∈ support mx, y = x := by
  fail_if_success grind
  grind [OracleComp.prEvent_eq_one_iff]

-- mirror: `mem_support_bind_iff` is a default `grind` rule.
example (my : α → OracleComp spec α) (y : α) :
    y ∈ support (mx >>= my) ↔ ∃ z ∈ support mx, y ∈ support (my z) := by grind

end uniform

/-! ## `finSupport` gates and `ProbComp` mirrors -/

section probComp

variable (p : Bool → Prop) [DecidablePred p] (mx : ProbComp Bool)

example : Pr{let y ← mx}[p y] = 0 ↔ ∀ y ∈ finSupport mx, ¬ p y := by
  fail_if_success grind
  grind [OracleComp.prEvent_eq_zero_iff]

-- mirror: the kept `finSupport` bind rule closes this under bare `grind`
example (my : Bool → ProbComp Bool) (y : Bool) :
    y ∈ finSupport (mx >>= my) ↔ ∃ z ∈ finSupport mx, y ∈ finSupport (my z) := by grind

end probComp

/-! ## Structural additions to the default `grind` set

Capability gates for the confluent structural rewrites tagged `@[grind =]` beyond the original
monad-law block: `replicate` unfolds, `Functor.map_map`, and the `simulateQ` routing layer
(`QueryImpl.add` / instrumentation wrappers). Each example is a shape bare `grind` could not close
before the corresponding tag (the routing example previously *saturated* — it is also a fail-fast
gate). -/

section structural

variable (oa : ProbComp Bool)

example : oa.replicate 1 = (do let x ← oa; pure [x]) := by grind
example (x : Bool) : (pure x : ProbComp Bool).replicate 3 = pure [x, x, x] := by grind
example (xs : List Bool) : xs ∈ support (oa.replicate 0) ↔ xs = [] := by grind
example : oa.replicateTR 1 = (do let x ← oa; pure [x]) := by grind

section mapMap

variable {α : Type} {m : Type → Type} [Monad m] [LawfulMonad m] [EvalDistSemantics m]
  [LawfulEvalDistSemantics m]

example (mx : m α) (f g : α → α) : g <$> (f <$> mx) = (fun x => g (f x)) <$> mx := by grind
example (mx : m α) (f g : α → α) :
    Pr{let _ ← g <$> (f <$> mx)}[True] = Pr{let _ ← mx}[True] := by grind

end mapMap

section routing

variable {ι₁ ι₂ : Type} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂} {α β σ : Type}
  {m : Type → Type} [Monad m] [LawfulMonad m]
  (impl₁ : QueryImpl spec₁ m) (impl₂ : QueryImpl spec₂ m)

-- formerly a saturating shape: bare `grind` timed out here before
-- `simulateQ_add_liftComp_left` was tagged `@[grind =]`
example (oa : OracleComp spec₁ α) :
    simulateQ (impl₁ + impl₂) (do let x ← liftComp oa (spec₁ + spec₂); pure x) =
      simulateQ impl₁ oa := by grind

example (ob : OracleComp spec₂ α) :
    simulateQ (impl₁ + impl₂) (liftComp ob (spec₁ + spec₂) >>= pure) =
      simulateQ impl₂ ob := by grind

example (impl : QueryImpl spec₁ (StateT σ m)) (t : spec₁.Domain) (s : σ) (b : Bool) :
    (impl.withBadFlag t).run (s, b) =
      (fun (vs : spec₁.Range t × σ) => (vs.1, vs.2, b)) <$> (impl t).run s := by grind

example (impl : QueryImpl spec₁ m) (x : Option α) (my : OracleComp spec₁ β)
    (my' : α → OracleComp spec₁ β) :
    simulateQ impl (x.elim my my' >>= pure) =
      x.elim (simulateQ impl my) (fun a => simulateQ impl (my' a)) := by grind

end routing

end structural

end VCVioTest.GrindFailFast
