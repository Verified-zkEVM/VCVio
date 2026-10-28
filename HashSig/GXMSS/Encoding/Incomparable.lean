/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Encoding.Basic

/-!
# Incomparable encodings with explicit randomness and failure

The algorithm boundary of ePrint 2025/055, Definition 13, takes public parameters, a message,
explicit randomness and an epoch. All successful outputs belong to one global incomparable
code. Returned `none` records failure. Sampling, retries, efficiency, error probability and
collision security are separate obligations.
-/

public section

namespace GXMSS.Encoding

/-- A fallible encoding whose successful outputs share one global incomparable code. -/
structure IncomparableEncoding (PP M R E : Type*) (n radix : ℕ) where
  /-- The same code contains every successful output, for every input. -/
  code : Set (Codeword n radix)
  /-- Distinct members of the global code have strict coordinates in both directions. -/
  incomparable : IncomparableCode code
  /-- Encode to a word with evidence of global code membership, or return explicit failure. -/
  encode : PP → M → R → E → Option {x // x ∈ code}

namespace IncomparableEncoding

variable {PP M R E : Type*} {n radix : ℕ}

/-- Observe the optional word, forgetting only its membership proof and preserving failure. -/
@[expose] def value (enc : IncomparableEncoding PP M R E n radix)
    (p : PP) (m : M) (r : R) (e : E) : Option (Codeword n radix) :=
  (enc.encode p m r e).map Subtype.val

/-- A successful observed output is a member of the global code. -/
theorem mem_code_of_value_eq_some (enc : IncomparableEncoding PP M R E n radix)
    (p : PP) (m : M) (r : R) (e : E) {x : Codeword n radix}
    (h : enc.value p m r e = some x) : x ∈ enc.code := by
  unfold value at h
  cases hresult : enc.encode p m r e with
  | none => simp [hresult] at h
  | some y =>
    have hy : y.val = x := by simpa [hresult] using h
    exact hy ▸ y.property

/-- Forgetting membership evidence preserves and reflects returned failure. -/
@[simp] theorem value_eq_none_iff (enc : IncomparableEncoding PP M R E n radix)
    (p : PP) (m : M) (r : R) (e : E) :
    enc.value p m r e = none ↔ enc.encode p m r e = none := by
  simp [value]

/-- An encoding with an empty global code returns failure on every input. -/
theorem encode_eq_none_of_code_eq_empty
    (enc : IncomparableEncoding PP M R E n radix) (h : enc.code = ∅)
    (p : PP) (m : M) (r : R) (e : E) :
    enc.encode p m r e = none := by
  cases hresult : enc.encode p m r e with
  | none => rfl
  | some x => simpa [h] using x.property

/-- Distinct successful words are incomparable even when all four inputs differ. -/
theorem incomparableWords_of_successes
    (enc : IncomparableEncoding PP M R E n radix)
    (p p' : PP) (m m' : M) (r r' : R) (e e' : E)
    {x y : Codeword n radix} (hx : enc.value p m r e = some x)
    (hy : enc.value p' m' r' e' = some y) (hne : x ≠ y) : IncomparableWords x y := by
  exact enc.incomparable (enc.mem_code_of_value_eq_some p m r e hx)
    (enc.mem_code_of_value_eq_some p' m' r' e' hy) hne

end IncomparableEncoding

end GXMSS.Encoding
