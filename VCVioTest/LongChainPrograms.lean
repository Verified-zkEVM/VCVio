/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio

/-!
# Long-chain probability tactic benchmark

A probability benchmark (companion to `VCVioTest/ProbabilityTactics.lean` and
`VCVioTest/MonadProbability.lean`) that exercises `simp` and `grind` over programs with
**ten or more sequential binds**, rather than the one/two-step shapes of the other two files. The
point is to pin down *where* on a long chain each tactic is strong: a regression in either surfaces
here in isolation.

On measure semantics both tactics keep pace on the structural work of a long chain: the total
successful mass of a twelve-step `ProbComp`, abstract monad-law normalization over an opaque monad,
and the collapse of a ten-deep redundant-`pure` tower even under a concrete `$ᵗ Bool` head. What
remains is arithmetic at the bottom of a chain: the exact mass of a guarded `OptionT` chain and a
concrete outcome value are recorded as `target(...)` notes.

Conventions (as in the sibling files):
* **Mirrors.** Where both `simp` and `grind` close a goal, both are kept.
* **Single tactic + target.** Where only one closes it, that tactic is used and the gap is recorded
  with a `target(...)` note.
* **Only stable tactics.** No example hangs or explodes.
-/

public section

open OracleComp ProbComp ENNReal MeasureTheory

namespace VCVioTest.LongChainPrograms

/-! ## Programs

The named computations the benchmark reasons about. `chain12` / `chain12Opt` are twelve-step uniform
chains (over `ProbComp` and the failing carrier `OptionT ProbComp`); `coinPadded` a ten-deep tower
of redundant `pure` binds that is secretly just `$ᵗ Bool`; `longAbort` is a ten-step `OptionT` chain
with a single guard, so it fails with probability one half. -/

/-- A twelve-step chain of independent uniform draws. -/
def chain12 : ProbComp Bool := do
  let a ← $ᵗ Bool; let b ← $ᵗ Bool; let c ← $ᵗ Bool; let d ← $ᵗ Bool
  let e ← $ᵗ Bool; let f ← $ᵗ Bool; let g ← $ᵗ Bool; let h ← $ᵗ Bool
  let i ← $ᵗ Bool; let j ← $ᵗ Bool; let k ← $ᵗ Bool; let l ← $ᵗ Bool
  pure (a && b && c && d && e && f && g && h && i && j && k && l)

/-- The same twelve-step chain over the failing carrier `OptionT ProbComp`; it still never fails. -/
def chain12Opt : OptionT ProbComp Bool := do
  let a ← $ᵗ Bool; let b ← $ᵗ Bool; let c ← $ᵗ Bool; let d ← $ᵗ Bool
  let e ← $ᵗ Bool; let f ← $ᵗ Bool; let g ← $ᵗ Bool; let h ← $ᵗ Bool
  let i ← $ᵗ Bool; let j ← $ᵗ Bool; let k ← $ᵗ Bool; let l ← $ᵗ Bool
  pure (a && b && c && d && e && f && g && h && i && j && k && l)

/-- A ten-deep tower of redundant `pure` binds: `bind_pure`/`pure_bind` collapse it to `$ᵗ Bool`. -/
def coinPadded : ProbComp Bool := do
  let a ← $ᵗ Bool
  let b ← pure a; let c ← pure b; let d ← pure c; let e ← pure d
  let f ← pure e; let g ← pure f; let h ← pure g; let i ← pure h
  let j ← pure i; let k ← pure j
  pure k

/-- A ten-step `OptionT` chain with a single guard at the fifth step: fails with probability one
half, regardless of the nine surrounding uniform draws. -/
def longAbort : OptionT ProbComp Bool := do
  let a ← $ᵗ Bool; let b ← $ᵗ Bool; let c ← $ᵗ Bool; let d ← $ᵗ Bool
  let e ← $ᵗ Bool; guard e
  let f ← $ᵗ Bool; let g ← $ᵗ Bool; let h ← $ᵗ Bool; let i ← $ᵗ Bool; let j ← $ᵗ Bool
  pure (a && b && c && d && f && g && h && i && j)

/-! ## 1. Total mass of a deep chain

The successful mass of `chain12` is one: every `OracleComp` step is lossless. Both tactics close it
without unfolding the chain, which is the main regression gate of the file. -/

example : Pr{let _ ← chain12}[True] = 1 := by simp
example : Pr{let _ ← chain12}[True] = 1 := by grind

/-! ## 2. The same chain over a failing carrier

Over `OptionT ProbComp` the lossless chain still has full successful mass under `simp`.

target(simp+grind): the guarded `longAbort` has mass `2⁻¹`; neither tactic shows even that it is
below one, since the guard's mass sits under nine surrounding draws. -/

example : Pr{let _ ← chain12Opt}[True] = 1 := by simp [chain12Opt]

/-! ## 3. Structural normalization — abstract chain and concrete head

A redundant-`pure` chain is pure monad-law rewriting. Over an **opaque** lawful monad, over a free
`ProbComp` head, and under the **concrete** `$ᵗ Bool` head of `coinPadded`, both tactics collapse
it. -/

section abstractHead

variable {α : Type} {m : Type → Type} [Monad m] [LawfulMonad m] [EvalDistSemantics m]
  [LawfulEvalDistSemantics m] [MeasurableSpace α]

example (mx : m α) : 𝒟[do let a ← mx; pure a] = 𝒟[mx] := by simp
example (mx : m α) : 𝒟[do let a ← mx; pure a] = 𝒟[mx] := by grind

example (mx : m α) :
    𝒟[do let a ← mx; let b ← pure a; let c ← pure b; pure c] = 𝒟[mx] := by simp
example (mx : m α) :
    𝒟[do let a ← mx; let b ← pure a; let c ← pure b; pure c] = 𝒟[mx] := by grind

end abstractHead

example (mx : ProbComp Bool) : 𝒟[do let a ← mx; pure a] = 𝒟[mx] := by simp
example (mx : ProbComp Bool) : 𝒟[do let a ← mx; pure a] = 𝒟[mx] := by grind

example : 𝒟[coinPadded] = 𝒟[($ᵗ Bool)] := by simp [coinPadded]
example : 𝒟[coinPadded] = 𝒟[($ᵗ Bool)] := by grind [coinPadded]
example : Pr{coinPadded}[= true] = Pr{$ᵗ Bool}[= true] := by simp [coinPadded]
example : support coinPadded = support ($ᵗ Bool) := by simp [coinPadded]

/-! ## 4. Support of a deep chain

A specific reachable point of `chain12`'s support is decided by `simp`.

target(simp+grind): the full `support chain12 = Set.univ` needs that the twelve-fold `&&` realises
both booleans and that the union telescopes to the universe. -/

example : (false : Bool) ∈ support chain12 := by simp [chain12]

/-! ## 5. Outcome value of a multi-step chain — `target(simp+grind)`

Computing a concrete outcome probability of a multi-step bind chain is the one shape **neither**
terminal tactic closes: `simp` normalises the chain step by step but stops before collapsing the
nested integrals to a number, and `grind` does no `ℝ≥0∞` arithmetic. `chain12` returns `true` only
when all twelve coins do, so

  `Pr{chain12}[= true] = (2 ^ 12)⁻¹`   -- target(simp+grind)

is the representative outcome-value target. -/

end VCVioTest.LongChainPrograms
