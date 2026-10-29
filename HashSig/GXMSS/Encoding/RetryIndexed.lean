/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Encoding.Retry

/-!
# Indexed first-success encoding retries

A bounded indexed sampler records the first successful attempt and the exact consumed prefix.
The fixed-sampler output law preserves returned exhaustion and missing execution mass.
-/

public section

namespace GXMSS.Encoding.IncomparableEncoding

variable {PP M R E : Type} {n radix : ℕ}
variable {m : Type → Type*} [Monad m]

/-- The returned result of indexed first-success retry. The attempt is one-based and
`consumed` is exactly the ordered prefix reached before success or exhaustion. -/
inductive IndexedResult (R : Type) (n radix : ℕ) where
  | success (word : Codeword n radix) (randomizer : R) (attempt : ℕ)
      (consumed : List R)
  | exhausted (consumed : List R)

namespace IndexedResult

/-- Forget attempt and consumption while preserving returned exhaustion. -/
@[expose] def output : IndexedResult R n radix → Option (Codeword n radix × R)
  | .success word randomizer _ _ => some (word, randomizer)
  | .exhausted _ => none

/-- Observe the exact ordered consumed prefix. -/
@[expose] def consumed : IndexedResult R n radix → List R
  | .success _ _ _ consumed => consumed
  | .exhausted consumed => consumed

end IndexedResult

/-- Draw from each zero-based attempt index and stop at the first successful
encoding. A finite index prevents an out-of-budget draw. Returned success records
the one-based attempt and exact ordered consumed prefix. Monadic bind retains
missing mass and divergence. -/
@[expose] def retryIndexed (enc : IncomparableEncoding PP M R E n radix)
    (pp : PP) (msg : M) (ep : E) :
    (budget : ℕ) → (Fin budget → m R) → m (IndexedResult R n radix)
  | 0, _ => pure (.exhausted [])
  | k + 1, sample => do
      let r ← sample 0
      match enc.value pp msg r ep with
      | some word => pure (.success word r 1 [r])
      | none =>
          match ← retryIndexed enc pp msg ep k (fun i => sample i.succ) with
          | .success word selected first consumed =>
              pure (.success word selected (first + 1) (r :: consumed))
          | .exhausted consumed => pure (.exhausted (r :: consumed))

/-- Pure indexed retry exposes its first draw and recursive remainder exactly. -/
theorem retryIndexed_id_succ (enc : IncomparableEncoding PP M R E n radix)
    (pp : PP) (msg : M) (ep : E) (k : ℕ) (sample : Fin (k + 1) → Id R) :
    enc.retryIndexed pp msg ep (k + 1) sample =
      match enc.value pp msg (sample 0) ep with
      | some word => .success word (sample 0) 1 [sample 0]
      | none =>
          match enc.retryIndexed pp msg ep k (fun i => sample i.succ) with
          | .success word selected first consumed =>
              .success word selected (first + 1) (sample 0 :: consumed)
          | .exhausted consumed => .exhausted (sample 0 :: consumed) := rfl


/-- The established fixed-sampler retry is exactly the returned-output observation
of indexed retry with the same sampler at every attempt. This equality includes
returned exhaustion and preserves the monad's missing execution mass. -/
theorem retry_eq_indexed_constant [LawfulMonad m]
    (enc : IncomparableEncoding PP M R E n radix) (sample : m R)
    (pp : PP) (msg : M) (ep : E) (budget : ℕ) :
    enc.retry sample pp msg ep budget =
      IndexedResult.output <$> enc.retryIndexed pp msg ep budget (fun _ => sample) := by
  induction budget with
  | zero => simp [retry, retryIndexed, IndexedResult.output]
  | succ budget ih =>
      simp only [retry, retryIndexed, map_bind]
      congr 1
      funext r
      cases hv : enc.value pp msg r ep with
      | some word => simp [IndexedResult.output]
      | none =>
          rw [ih]
          simp only [map_eq_bind_pure_comp, bind_assoc]
          congr 1
          funext result
          cases result <;> simp [IndexedResult.output]


end GXMSS.Encoding.IncomparableEncoding
