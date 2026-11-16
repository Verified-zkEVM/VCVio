/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import VCVio.CryptoFoundations.IncomparableEncoding.Basic
public import VCVio.Algorithms.FirstSuccess.Basic
public import PolyFun.Control.Monad.Support

/-!
# Bounded encoding retries

The shared first-success search returns the selected word/randomizer pair. Indexed search uses
the common payload result, retaining its one-based attempt, ordered consumed prefix and returned
exhaustion. Native monadic failure remains an execution failure.
-/

public section

namespace IncomparableEncoding

open VCVio.Algorithms

variable {PP M R E : Type} {n radix : ℕ} {m : Type → Type*} [Monad m]

/-- Classify one randomizer, retaining it alongside any successfully encoded word. -/
@[expose] def attempt (enc : IncomparableEncoding PP M R E n radix)
    (pp : PP) (msg : M) (ep : E) (r : R) : Option (Codeword n radix × R) :=
  (enc.value pp msg r ep).map (fun word => (word, r))

/-- Optional payload observation of bounded first-success encoding. -/
@[expose] def retry (enc : IncomparableEncoding PP M R E n radix) (sample : m R)
    (pp : PP) (msg : M) (ep : E) (budget : ℕ) : m (Option (Codeword n radix × R)) :=
  FirstSuccess.runWith sample (enc.attempt pp msg ep) budget

/-- Indexed encoding search uses the common result payload and its exact prefix observations. -/
@[expose] def retryIndexed (enc : IncomparableEncoding PP M R E n radix)
    (pp : PP) (msg : M) (ep : E) (budget : ℕ) (sample : Fin budget → m R) :
    m (FirstSuccess.Result R (Codeword n radix × R)) :=
  FirstSuccess.indexed (enc.attempt pp msg ep) budget sample

/-- Pure indexed search exposes its first draw and accounts for a failed prefix draw. -/
theorem retryIndexed_id_succ (enc : IncomparableEncoding PP M R E n radix)
    (pp : PP) (msg : M) (ep : E) (k : ℕ) (sample : Fin (k + 1) → Id R) :
    enc.retryIndexed pp msg ep (k + 1) sample =
      match enc.value pp msg (sample 0) ep with
      | some word => FirstSuccess.Result.success (word, sample 0) 1 [sample 0]
      | none => (enc.retryIndexed pp msg ep k (fun i => sample i.succ)).prepend (sample 0) := by
  rw [retryIndexed, FirstSuccess.indexed_id_succ]
  unfold attempt
  cases enc.value pp msg (sample 0) ep <;> rfl

/-- Zero retries perform no draw and return exhaustion. -/
theorem retry_zero (enc : IncomparableEncoding PP M R E n radix) (sample : m R)
    (pp : PP) (msg : M) (ep : E) : enc.retry sample pp msg ep 0 = pure none := rfl

/-- A further attempt classifies one draw and continues only after returned encoding failure. -/
theorem retry_succ (enc : IncomparableEncoding PP M R E n radix) (sample : m R)
    (pp : PP) (msg : M) (ep : E) (k : ℕ) :
    enc.retry sample pp msg ep (k + 1) =
      sample >>= fun r => match enc.value pp msg r ep with
        | none => enc.retry sample pp msg ep k
        | some word => pure (some (word, r)) := by
  rw [retry, FirstSuccess.runWith_succ]
  congr 1
  funext r
  unfold attempt
  cases enc.value pp msg r ep <;> rfl

/-- One attempt returns the optional word paired with that attempt's randomizer. -/
theorem retry_one (enc : IncomparableEncoding PP M R E n radix) (sample : m R)
    (pp : PP) (msg : M) (ep : E) :
    enc.retry sample pp msg ep 1 = sample >>= fun r => pure (enc.attempt pp msg ep r) := by
  rw [retry_succ]
  congr 1
  funext r
  unfold attempt
  cases enc.value pp msg r ep <;> rfl

/-- Fixed-sampler retries have exactly the optional-output observation of indexed retries. -/
theorem retry_eq_indexed_constant [LawfulMonad m]
    (enc : IncomparableEncoding PP M R E n radix) (sample : m R)
    (pp : PP) (msg : M) (ep : E) (budget : ℕ) :
    enc.retry sample pp msg ep budget =
      FirstSuccess.Result.output <$> enc.retryIndexed pp msg ep budget (fun _ => sample) :=
  FirstSuccess.runWith_eq_output_indexed sample (enc.attempt pp msg ep) budget

namespace Retry

/-- Every returned word retains a randomizer that actually encodes that word. -/
theorem value_eq_some_of_mem_retry [LawfulMonad m] [MonadAttach m] [LawfulMonadAttach m]
    (enc : IncomparableEncoding PP M R E n radix) (sample : m R)
    (pp : PP) (msg : M) (ep : E) (k : ℕ) (word : Codeword n radix) (r : R)
    (hs : some (word, r) ∈ MonadAttach.support (enc.retry sample pp msg ep k)) :
    enc.value pp msg r ep = some word := by
  induction k with
  | zero =>
    have heq := LawfulMonadAttach.eq_of_canReturn_pure hs
    simp at heq
  | succ k ih =>
    rw [retry_succ] at hs
    obtain ⟨r', _, hs⟩ := LawfulMonadAttach.canReturn_bind_imp' hs
    cases hv : enc.value pp msg r' ep with
    | none => exact ih (by simpa [hv] using hs)
    | some word' =>
      have hpure := LawfulMonadAttach.eq_of_canReturn_pure (by simpa [hv] using hs)
      have heq : word = word' ∧ r = r' := by simpa using hpure.symm
      rcases heq with ⟨rfl, rfl⟩
      exact hv

end Retry

end IncomparableEncoding
