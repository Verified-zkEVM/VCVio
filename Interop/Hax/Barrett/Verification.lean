/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Devon Tuma
-/

module

public import Hax
public import Interop.Hax.Barrett.Extraction.Specs
public import Interop.Hax.Holds
public import Interop.Rust.RustM
public import Interop.Rust.Triple
public import VCVio.ProgramLogic.Unary.WP.Necessary

/-!
# A Rust Barrett reduction, extracted by hax, in VCVio

hax's `barrett` example, signed Barrett reduction modulo ML-KEM's prime `3329`, vendored in the
crate next to this file (`Interop/Hax/Barrett/src/lib.rs`):

```rust
const BARRETT_SHIFT: i64 = 26;
const BARRETT_R: i64 = 0x4000000; // 2^26
const BARRETT_MULTIPLIER: i64 = 20159;
pub(crate) const FIELD_MODULUS: i32 = 3329;

#[hax::requires((i64::from(value) >= -BARRETT_R && i64::from(value) <= BARRETT_R))]
#[hax::ensures(|result| result > -FIELD_MODULUS && result < FIELD_MODULUS &&
                   result.rem_euclid(FIELD_MODULUS) == value.rem_euclid(FIELD_MODULUS))]
pub fn barrett_reduce(value: FieldElement) -> FieldElement {
    let t = i64::from(value) * BARRETT_MULTIPLIER;
    let t = t + (BARRETT_R >> 1);
    let quotient = t >> BARRETT_SHIFT;
    let quotient = quotient as i32;
    let sub = quotient * FIELD_MODULUS;
    value - sub
}
```

`scripts/regenerate-hax.sh` extracts it with the hax CLI into `Interop.Hax.Barrett.Extraction`:
the constants, the function `hax_barrett.barrett_reduce` (widening through core-models'
`From<i32> for i64`), its clauses `barrett_reduce.pre` and `barrett_reduce.post`, and its contract
`barrett_reduce.spec`.
- The contract is proved by hax's own proof of it, with `hax_mvcgen` and `grind`. That proof needs
  a spec for `i32::rem_euclid` that hax's core models lack, which hax's example states locally
  (`I32_rem_euclid_spec`).
- The clauses read as plain arithmetic (`barrettPost`), where `rem_euclid` by the positive modulus
  is `Int.emod`. Each reading is a `hax_mvcgen` proof about the clause, through
  `Interop.Hax.holds_iff_of_triple`.
- The contract reaches VCVio's program logic through `Interop.Rust.triple_liftRustM_of_imp`.

## Main results

* `Interop.Hax.Examples.Barrett.barrett_reduce_spec`: the extracted contract holds.
* `Interop.Hax.Examples.Barrett.barrett_reduce_pre_holds_iff`, `barrett_reduce_post_holds_iff`: its
  clauses in plain arithmetic.
* `Interop.Hax.Examples.Barrett.triple_barrett_reduce_lifted`: the contract for the lifted program,
  as a core `Std.WP` triple.
-/

public section

open Aeneas Aeneas.Std Std.Do CoreModels hax_barrett

namespace Interop.Hax.Examples.Barrett

set_option mvcgen.warning false in
set_option hax_mvcgen.warnings false in
/-- `i32::rem_euclid` by a nonzero divisor, away from the overflowing `MIN % -1`, is `Int.emod`.
hax's own Barrett example states this spec locally, as missing from its core models; it is a
`spec` only within this file's contract proofs. -/
theorem I32_rem_euclid_spec (x y : I32) (hy : y.val ≠ 0)
    (hov : ¬(x.val = I32.min ∧ y.val = -1)) :
    ⦃⌜True⌝⦄ core.num.I32.rem_euclid x y ⦃⇓ r => ⌜r.val = x.val % y.val⌝⦄ := by
  hax_mvcgen [core.num.I32.rem_euclid, rust_primitives.arithmetic.rem_euclid_i32, irem_euclid]
  all_goals grind [Int.emod_nonneg x.val hy, Int.emod_lt_abs x.val hy, IScalar.val]

section Contract

attribute [local spec] barrett_reduce core.I64.Insts.CoreConvertFromI32.from I32_rem_euclid_spec

attribute [local grind =]
  Int32.toInt_toInt64 Int64.ofBitVec_int32ToBitVec
  Int64.toInt_inj Int32.toInt_inj
  Int64.le_iff_toInt_le Int32.lt_iff_toInt_lt
  Int.shiftRight_eq_div_pow

local grind_pattern Int32.toInt64_ofNat => (@OfNat.ofNat Int32 n _).toInt64

set_option mvcgen.warning false in
set_option hax_mvcgen.warnings false in
/-- hax's proof obligation for `barrett_reduce`, by hax's own proof: the extracted contract
holds. -/
theorem barrett_reduce_spec (value : I32) : barrett_reduce.spec value := by
  unfold barrett_reduce.spec
  hax_mvcgen
    <;> try simp [BARRETT_MULTIPLIER, BARRETT_R, BARRETT_SHIFT, FIELD_MODULUS] at *
  all_goals try grind

/-- The postcondition of the Rust contract, in plain arithmetic: Rust's `rem_euclid` by the
positive modulus is `Int.emod`. -/
def barrettPost (value r : I32) : Prop :=
  -3329 < r.val ∧ r.val < 3329 ∧ r.val % 3329 = value.val % 3329

set_option mvcgen.warning false in
set_option hax_mvcgen.warnings false in
/-- The extracted `requires` clause: the input is at most `2 ^ 26` in absolute value. -/
theorem barrett_reduce_pre_holds_iff (value : I32) :
    (barrett_reduce.pre value).holds ↔ -2 ^ 26 ≤ value.val ∧ value.val ≤ 2 ^ 26 :=
  Interop.Hax.holds_iff_of_triple (by
    unfold barrett_reduce.pre
    hax_mvcgen
      <;> try simp [BARRETT_R] at *
    all_goals try grind)

set_option mvcgen.warning false in
set_option hax_mvcgen.warnings false in
/-- The extracted `ensures` clause is `barrettPost`. -/
theorem barrett_reduce_post_holds_iff (value r : I32) :
    (barrett_reduce.post value r).holds ↔ barrettPost value r :=
  Interop.Hax.holds_iff_of_triple (by
    unfold barrett_reduce.post barrettPost
    hax_mvcgen
      <;> try simp [FIELD_MODULUS] at *
    all_goals try grind)

end Contract

variable {ι : Type} {spec : OracleSpec ι}
  [Std.WP.WPMonad (OracleComp spec) Prop Std.WP.EStackEnd]

/-- The contract for the lifted program: on inputs of size at most `2 ^ 26`, it neither panics nor
diverges, and its result is reduced and congruent to the input. -/
theorem triple_barrett_reduce_lifted (value : I32) :
    Std.WP.Triple (Interop.Rust.liftRustM (barrett_reduce value) :
        Interop.Rust.RustOracleComp spec I32)
      (-2 ^ 26 ≤ value.val ∧ value.val ≤ 2 ^ 26) (barrettPost value)
      (fun _ => False, fun _ => False, ()) := by
  simpa only [barrett_reduce_pre_holds_iff, barrett_reduce_post_holds_iff] using
    Interop.Rust.triple_liftRustM_of_imp (spec := spec) (barrett_reduce_spec value)

end Interop.Hax.Examples.Barrett
