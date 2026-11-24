/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import ToMathlib.Data.Nat.Max

/-!
# Checks for nonzero maxima

Instance search finds `NeZero (max q 1)` at a variable `q` and at `q = 0`.
-/

public section

namespace VCVioTest.NatMax

example (q : ℕ) : NeZero (max q 1) := inferInstance

example : NeZero (max 0 1) := inferInstance

end VCVioTest.NatMax
