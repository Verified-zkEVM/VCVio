/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.OracleComp.Constructions.SampleableType.Basic
public import VCVio.OracleComp.EvalDist

/-!
# Memberships in the support of a computation that samples a large type

`support mx` is `{a | CanReturn mx a}`, and on `OracleComp` the return predicate is PolyFun's
inductive `PFunctor.FreeM.CanReturn`. Neither the kernel nor the elaborator reduces it, so
comparing `r ∈ support mx` with `r ∈ support my` compares `mx` with `my` and does not run either
computation. Running `$ᵗ BitVec (2 ^ 32)` would evaluate `2 ^ (2 ^ 32)`, which the kernel refuses
to do.

The proofs below compare memberships in three ways: `simp` unfolds a definition and rewrites the
`do` block with `mem_support_bind_iff`, whose `Bind` instance differs from the one `do` notation
elaborates; a hypothesis is passed to a lemma whose statement has the same type; and `unfold`
changes the goal by definitional equality.
-/

public section

namespace VCVioTest.SupportKernel

open OracleComp

/-- Sample a salt of `2 ^ 32` bits, then return a constant. It has no compiled code, so loading
the test executable does not enumerate `BitVec (2 ^ 32)`. -/
noncomputable def sampleThenFive : ProbComp ℕ := do
  let _salt ← $ᵗ BitVec (2 ^ 32)
  return 5

/-- `simp` unfolds the definition and rewrites the `do` block. -/
theorem sampleThenFive_support (r : ℕ) : r ∈ support sampleThenFive → r = 5 := by
  simp only [sampleThenFive, mem_support_bind_iff, support_pure, Set.mem_singleton_iff]
  rintro ⟨_, _, rfl⟩
  rfl

/-- A hypothesis about the support, passed to a lemma. -/
example (r : ℕ) (h : r ∈ support sampleThenFive) : r = 5 :=
  sampleThenFive_support r h

/-- `sampleThenFive`, one delta step away. -/
noncomputable abbrev sampleAgain : ProbComp ℕ := sampleThenFive

/-- A hypothesis about an `abbrev`, passed to a lemma about the definition it names. -/
example (r : ℕ) (h : r ∈ support sampleAgain) : r = 5 :=
  sampleThenFive_support r h

/-- `unfold` changes the goal by definitional equality. -/
example (r : ℕ) : r ∈ support sampleThenFive → r = 5 := by
  unfold sampleThenFive
  exact sampleThenFive_support r

end VCVioTest.SupportKernel
