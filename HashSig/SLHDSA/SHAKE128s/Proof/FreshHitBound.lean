/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.KeygenUniform
public import VCVio.OracleComp.QueryTracking.QueryBound

/-!
# Linear charge for hitting a fixed digest with a hash call

A computation over the shared world makes free uniform-coin queries and charged hash
queries. Fix a target digest for every possible input, `targetOf : Bytes → Digest`. If the
computation's hash queries are bounded by `count`, and the starting cache holds no answer
truncating to its own input's target, then the probability that the run ends with any
cached answer truncating to its own input's target is at most `count / 2 ^ 128`.

Because the starting cache is clean, such an answer must have been installed during the
run, so this is the union bound over cache misses: each miss draws a fresh uniform 30-byte
answer whose truncation is uniform on 128 bits, costing `2 ^ -128`. The bound is linear in
the query count rather than quadratic, which is what the target `q / 2 ^ 127` requires.

The target is *optional*: inputs mapped to `none` are never hits. This is essential,
because the honest signer's own cache entries satisfy `truncate answer = <canonical parent
value>` by construction — a total target function would make the honest cache violate
`Clean` immediately. Sending every honestly-queried input to `none` keeps the honest cache
clean while still charging the adversary's deviating queries.

Crucially the charge does not grow with the number of honest values. A cache miss at
`input` can only match `targetOf input`, so an arbitrarily large table of honest node
values — all the FORS leaves and Merkle nodes revealed by up to `2 ^ 64` signatures —
costs the same `count / 2 ^ 128` as a single target would. A union bound over that table
instead of over the queries would be far too lossy.

Uniform-coin queries are free: they never touch the cache and never consume budget.
-/

public section

open OracleComp OracleSpec ENNReal

namespace SLHDSA.SHAKE128s.FreshHitBound

/-- The charged queries: those addressed to the shared hash oracle. -/
@[expose] def HashQuery : OracleWorld.Domain → Prop := fun query => query.isRight = true

/-- Whether a query is charged is decided by its oracle index. -/
instance : DecidablePred HashQuery := fun _ => inferInstanceAs (Decidable (_ = _))

/-- The final cache holds an answer truncating to the target of its own input.

The target may differ from input to input, so a single charge covers an arbitrarily large
table of honest values: each cache miss can only match the one target belonging to the
input being queried. This is what keeps the bound linear in the query count instead of
multiplying by the number of honest values. -/
@[expose] def Hit {α : Type} (targetOf : Bytes → Option Digest) :
    α × QueryCache HashSpec → Prop := fun result =>
  ∃ input output, result.2 input = some output ∧ targetOf input = some (Hashing.truncate output)

/-- A cache holding no answer that truncates to its own input's target. -/
@[expose] def Clean (targetOf : Bytes → Option Digest) (cache : QueryCache HashSpec) : Prop :=
  ∀ input output, cache input = some output → targetOf input ≠ some (Hashing.truncate output)

/-- One fresh hash answer truncates to a value fixed in advance with probability `2 ^ -128`. -/
theorem prob_truncate_eq (target : Digest) :
    Pr{let output ← ($ᵗ HashOutput : ProbComp HashOutput)}[Hashing.truncate output = target] =
      1 / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  have hmap : Pr{let output ← ($ᵗ HashOutput : ProbComp HashOutput)}[
        Hashing.truncate output = target] =
      Pr{let digest ← (Hashing.truncate <$> ($ᵗ HashOutput : ProbComp HashOutput))}[
        digest = target] := by
    rw [prEvent_map]
  let _ : MeasurableSpace Digest := ⊤
  rw [hmap, KeygenUniform.truncate_uniform.prEvent_eq, prEvent_eq_evalDist_singleton,
    SampleableType.evalDist_uniformSample, ProbabilityTheory.uniformOn_univ_apply_singleton,
    Fintype.card_bitVec, one_div]
  rfl

/-- One fresh answer matches the optional target of its own input with probability at most
`2 ^ -128`; an input with no target can never match. -/
theorem prob_target_match_le (optionalTarget : Option Digest) :
    Pr{let output ← ($ᵗ HashOutput : ProbComp HashOutput)}[
        some (Hashing.truncate output) = optionalTarget] ≤
      1 / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  cases optionalTarget with
  | none =>
    refine le_of_eq_of_le (b := 0) ?_ (by simp)
    exact prEvent_eq_zero_of_forall_mem_support _ _ fun _ _ hmatch => by simp at hmatch
  | some target =>
    refine le_of_eq_of_le ?_ (le_of_eq (prob_truncate_eq target))
    exact prEvent_congr _ _ _ fun _ => Option.some_inj

end SLHDSA.SHAKE128s.FreshHitBound
