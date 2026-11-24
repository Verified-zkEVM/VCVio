/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import VCVio.CryptoFoundations.IncomparableEncoding.Code

/-!
# Incomparable encodings with explicit randomness and failure

The algorithm boundary of ePrint 2025/055, Definition 13, takes public parameters, a message,
explicit randomness and an epoch. All successful outputs belong to one global incomparable
code, which the field `mem_code_of_encode_eq_some` records. Returned `none` records failure.
Sampling, retries, efficiency, error probability and collision security are separate obligations.
-/

public section

open IncomparableEncoding

/-- A fallible encoding whose successful outputs share one global incomparable code. -/
structure IncomparableEncoding (PP M R E : Type*) (n radix : ℕ) where
  /-- The same code contains every successful output, for every input. -/
  code : Set (Codeword n radix)
  /-- Distinct members of the global code have strict coordinates in both directions. -/
  incomparable : IncomparableCode code
  /-- Encode to a word, or return `none` to report failure. -/
  encode : PP → M → R → E → Option (Codeword n radix)
  /-- Every successful output is a member of the global code. -/
  mem_code_of_encode_eq_some {pp : PP} {msg : M} {r : R} {ep : E} {x : Codeword n radix} :
    encode pp msg r ep = some x → x ∈ code

namespace IncomparableEncoding

variable {PP M R E : Type*} {n radix : ℕ}

/-- Distinct successful words are incomparable even when all four inputs differ. -/
theorem incomparableWords_of_successes
    (enc : IncomparableEncoding PP M R E n radix)
    {p p' : PP} {m m' : M} {r r' : R} {e e' : E}
    {x y : Codeword n radix} (hx : enc.encode p m r e = some x)
    (hy : enc.encode p' m' r' e' = some y) (hne : x ≠ y) : IncomparableWords x y :=
  enc.incomparable (enc.mem_code_of_encode_eq_some hx) (enc.mem_code_of_encode_eq_some hy) hne

/-- Encode with randomizer `r`, and on success return the word together with `r`. This is the
acceptance function that retries and encoding error masses pass to `FirstSuccess`. -/
@[expose] def attempt (enc : IncomparableEncoding PP M R E n radix)
    (pp : PP) (msg : M) (ep : E) (r : R) : Option (Codeword n radix × R) :=
  (enc.encode pp msg r ep).map (fun word => (word, r))

@[simp] theorem attempt_eq_none_iff (enc : IncomparableEncoding PP M R E n radix)
    (pp : PP) (msg : M) (ep : E) (r : R) :
    enc.attempt pp msg ep r = none ↔ enc.encode pp msg r ep = none := by
  simp [attempt]

@[simp] theorem isNone_attempt (enc : IncomparableEncoding PP M R E n radix)
    (pp : PP) (msg : M) (ep : E) (r : R) :
    (enc.attempt pp msg ep r).isNone = (enc.encode pp msg r ep).isNone := by
  simp [attempt]

end IncomparableEncoding
