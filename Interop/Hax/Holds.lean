/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Hax
public import Interop.Rust.RustM

/-!
# Reading extracted `requires` and `ensures` clauses

hax extracts a function's `requires` and `ensures` clauses as `RustM Bool` computations `f.pre`
and `f.post`, and states its contract through `RustM.holds`, which reads a `RustM Prop` as the
proposition it returns. A clause built from total operations reduces to a returned Boolean, and
`Interop.Hax.holds_ok` reads that as the Boolean itself, so the clause becomes plain arithmetic.
-/

public section

open Aeneas Aeneas.Std Std.Do

namespace Interop.Hax

/-- A returned Boolean holds exactly when it is `true`. -/
@[simp] theorem holds_ok (b : Bool) : (RustM.ok b : RustM Bool).holds ↔ b = true := by
  simp [RustM.holds, Std.Do.Triple, WP.wp, PredTrans.apply, Functor.map, RustM.match.ok]

/-- A clause that returns a Boolean equivalent to `P` holds exactly when `P` does. This turns a
`hax_mvcgen` proof about a clause into its plain reading. -/
theorem holds_iff_of_triple {m : RustM Bool} {P : Prop}
    (h : ⦃⌜True⌝⦄ m ⦃⇓b => ⌜b = true ↔ P⌝⦄) : m.holds ↔ P := by
  simp only [Std.Do.Triple, WP.wp, PredTrans.apply] at h
  cases m using RustM.cases with
  | ret b =>
    simp only [RustM.match.ok] at h
    rw [holds_ok]
    exact h trivial
  | vis i k =>
    obtain ⟨e, he⟩ := Interop.Rust.RustM.vis_eq_fail i k
    rw [he] at h
    simp [RustM.match.fail] at h
  | div => simp [RustM.match.div] at h

end Interop.Hax
