/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Devon Tuma
-/

module

public import Aeneas.Std.Scalar
public import Hax
public import Interop.Hax.CenteredBinomial.Extraction.Specs
public import Interop.Hax.Holds
public import Interop.Rust.RustM
public import Interop.Rust.Run
public import Interop.Rust.Triple
public import VCVio.OracleComp.ProbComp
public import VCVio.EvalDist.Monad.Basic
public import VCVio.ProgramLogic.Tactics

/-!
# A Rust centered-binomial sampler, extracted by hax, in VCVio

One step of ML-KEM's `SamplePolyCBD_η` at `η = 1`, as Rust, in the crate next to this file
(`Interop/Hax/CenteredBinomial/src/lib.rs`):

```rust
#[hax_lib::ensures(|result| -1 <= result && result <= 1)]
pub fn sample_cbd1(b: u8) -> i32 {
    let a = (b & 1) as i32;
    let c = ((b >> 1) & 1) as i32;
    a - c
}
```

`scripts/regenerate-hax.sh` extracts it with the hax CLI into
`Interop.Hax.CenteredBinomial.Extraction` as `hax_cbd.sample_cbd1`, with its `ensures` clause as
`sample_cbd1.post` and its contract `sample_cbd1.spec`: the bitwise `&&&` and the casts are pure,
lifted into `RustM`, while the shift and the subtraction are checked.

Lifted into `RustOracleComp unifSpec` by `Interop.Rust.liftRustM` and fed two uniform bits, it
returns `0` with probability `1/2` and `±1` with probability `1/4` each: the centered binomial
distribution with parameter `1`.

## Main results

* `Interop.Hax.Examples.CenteredBinomial.sample_cbd1_spec`: the extracted contract holds.
* `Interop.Hax.Examples.CenteredBinomial.sample_cbd1_post_holds_iff`: the contract's clause in plain
  arithmetic.
* `Interop.Hax.Examples.CenteredBinomial.triple_sample_cbd1_lifted`: the lifted program returns
  `-1`, `0` or `1`, as a core `Std.WP` triple.
* `Interop.Hax.Examples.CenteredBinomial.sample_cbd1_zero` (and `_one`, `_two`, `_three`): the
  four bit patterns that matter.
* `Interop.Hax.Examples.CenteredBinomial.prob_sampleRandomCbd1_zero`, `_pos_one`, `_neg_one`: the
  distribution.
* `Interop.Hax.Examples.CenteredBinomial.triple_sampleRandomCbd1`: the possible values, by core's
  `vcgen` through the Rust step.
-/

public section

open Aeneas Aeneas.Std Interop.Rust OracleSpec OracleComp OracleComp.ProgramLogic ENNReal hax_cbd

namespace Interop.Hax.Examples.CenteredBinomial

/-- Evaluate `sample_cbd1` on a literal: unfold the checked shift and subtraction and decide
their range tests. `RustM` is irreducible, so `decide` alone cannot. -/
local macro "cbd_eval" : tactic =>
  `(tactic| (simp (config := { decide := true }) only [sample_cbd1, lift, HShiftRight.hShiftRight,
    UScalar.shiftRight_IScalar, UScalar.shiftRight, HSub.hSub, IScalar.sub, IScalar.tryMk,
    ite_true, bind_tc_ok, bind_ok, RustM.ofOption, IScalar.tryMkOpt]; rfl))

theorem sample_cbd1_zero : sample_cbd1 0#u8 = RustM.ok 0#i32 := by cbd_eval

theorem sample_cbd1_one : sample_cbd1 1#u8 = RustM.ok 1#i32 := by cbd_eval

theorem sample_cbd1_two : sample_cbd1 2#u8 = RustM.ok (-1)#i32 := by cbd_eval

theorem sample_cbd1_three : sample_cbd1 3#u8 = RustM.ok 0#i32 := by cbd_eval

/-- A bit is its own balanced residue modulo `2 ^ 32`. -/
theorem bmod_emod_two (x : ℤ) : (x % 2).bmod 4294967296 = x % 2 :=
  Int.bmod_eq_of_le (by omega) (by omega)

set_option mvcgen.warning false in
set_option hax_mvcgen.warnings false in
/-- hax's proof obligation for `sample_cbd1`: the extracted contract holds, so the result lies in
`{-1, 0, 1}`. -/
theorem sample_cbd1_spec (b : U8) : sample_cbd1.spec b := by
  unfold sample_cbd1.spec sample_cbd1.post sample_cbd1
  hax_mvcgen
  all_goals
    simp_all only [IScalar.toNat, IScalar.ofInt_val_eq, Int.toNat_one, UScalarTy.U8_numBits_eq,
      Bvify.U8.UScalar_bv, Nat.one_lt_ofNat, UScalar.hcast_val_eq, UScalar.val_and,
      UScalar.ofNatCore_val_eq, Nat.and_one_is_mod, Int.natCast_emod, Nat.cast_ofNat,
      IScalarTy.I32_numBits_eq, Nat.reducePow, bmod_emod_two, Int.natCast_shiftRight, Int.reduceNeg,
      IScalar.le_equiv, neg_le_sub_iff_le_add, tsub_le_iff_right, decide_eq_true_eq, not_le,
      Bool.false_eq_true, IScalar.min_IScalarTy_I32_eq, IScalar.max_IScalarTy_I32_eq,
      Std.Do.ExceptConds.fst_false, Std.Do.SPred.down_pure_nil]
    scalar_tac

/-- The extracted `ensures` clause: the result is `-1`, `0` or `1`. -/
theorem sample_cbd1_post_holds_iff (b : U8) (r : I32) :
    (sample_cbd1.post b r).holds ↔ -1 ≤ r.val ∧ r.val ≤ 1 := by
  unfold sample_cbd1.post
  split_ifs with h <;>
    simp_all [IScalar.le_equiv, RustM.holds, Std.Do.Triple, Std.Do.WP.wp, Std.Do.PredTrans.apply,
      Functor.map, RustM.match.ok]

section Lifted

variable {ι : Type} {spec : OracleSpec ι} [Std.WP.WPMonad (OracleComp spec) Prop Std.WP.EStackEnd]

/-- The lifted program returns `-1`, `0` or `1`, and neither panics nor diverges. -/
theorem triple_sample_cbd1_lifted (b : U8) :
    Std.WP.Triple (Interop.Rust.liftRustM (sample_cbd1 b) : RustOracleComp spec I32)
      True (fun r => -1 ≤ r.val ∧ r.val ≤ 1) (fun _ => False, fun _ => False, ()) := by
  simpa only [sample_cbd1_post_holds_iff] using
    Interop.Rust.triple_liftRustM_of_imp (spec := spec) (fun _ => sample_cbd1_spec b)

end Lifted

/-- The two low bits of a byte, as a byte. -/
def lowBits : Fin 4 → U8
  | 0 => 0#u8
  | 1 => 1#u8
  | 2 => 2#u8
  | 3 => 3#u8

/-- The sampler fed two uniform bits. The six high bits of a byte are unused, so this has the
distribution of `sample_cbd1` on a uniform byte. -/
def sampleRandomCbd1 : RustOracleComp unifSpec I32 := do
  let n ← ($[0..3] : ProbComp (Fin 4))
  liftRustM (sample_cbd1 (lowBits n))

/-- The output for each pair of low bits. -/
def cbdOut : Fin 4 → I32
  | 0 => 0#i32
  | 1 => 1#i32
  | 2 => (-1)#i32
  | 3 => 0#i32

/-- The four draws decide the output. -/
theorem sampleRandomCbd1_run_run :
    sampleRandomCbd1.run.run =
      ((fun n => some (Except.ok (cbdOut n))) <$> ($[0..3] : ProbComp (Fin 4)) :
        OracleComp unifSpec (Option (Except Interop.Rust.Error I32))) := by
  unfold sampleRandomCbd1
  simp only [RustOracleComp.run_run_bind_liftM, map_eq_bind_pure_comp]
  refine bind_congr fun n => ?_
  fin_cases n <;>
    simp [lowBits, cbdOut, sample_cbd1_zero, sample_cbd1_one, sample_cbd1_two,
      sample_cbd1_three, RustOracleComp.ok]

/-- A uniform draw from `Fin 4` lands in a given set with probability its size over `4`. -/
theorem prob_uniformFin_four (p : Fin 4 → Prop) [DecidablePred p] :
    Pr{let n ← ($[0..3] : ProbComp (Fin 4))}[p n] =
      ((if p 0 then 1 else 0) + (if p 1 then 1 else 0) + (if p 2 then 1 else 0) +
        (if p 3 then 1 else 0)) * 4⁻¹ := by
  pvcgen
  simp only [ProbComp.uniformFin]
  rw [wp_query_uniform, Fin.sum_univ_four,
    show Fintype.card (unifSpec.Range 3) = 4 from rfl]
  push_cast
  ring

/-- An output event of the sampler is the event that the two bits produce that output. -/
theorem prob_sampleRandomCbd1 (a : I32) :
    Pr{let r ← sampleRandomCbd1.run.run}[r = some (Except.ok a)] =
      Pr{let n ← ($[0..3] : ProbComp (Fin 4))}[cbdOut n = a] := by
  rw [sampleRandomCbd1_run_run]
  simp only [Functor.map_map, Option.some.injEq, Except.ok.injEq]

/-- `0` with probability `1/2`: the bit patterns `00` and `11`. -/
theorem prob_sampleRandomCbd1_zero :
    Pr{let r ← sampleRandomCbd1.run.run}[r = some (Except.ok 0#i32)] = 2⁻¹ := by
  have half : ((1 : ℝ≥0∞) + 1) * 4⁻¹ = 2⁻¹ := by
    rw [one_add_one_eq_two, show (4 : ℝ≥0∞) = 2 * 2 by norm_num,
      ENNReal.mul_inv (Or.inl two_ne_zero) (Or.inl ENNReal.ofNat_ne_top), ← mul_assoc,
      ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]
  rw [prob_sampleRandomCbd1, prob_uniformFin_four]
  simpa (config := { decide := true }) using half

/-- `1` with probability `1/4`: the bit pattern `01`. -/
theorem prob_sampleRandomCbd1_pos_one :
    Pr{let r ← sampleRandomCbd1.run.run}[r = some (Except.ok 1#i32)] = 4⁻¹ := by
  rw [prob_sampleRandomCbd1, prob_uniformFin_four]
  simp (config := { decide := true })

/-- `-1` with probability `1/4`: the bit pattern `10`. -/
theorem prob_sampleRandomCbd1_neg_one :
    Pr{let r ← sampleRandomCbd1.run.run}[r = some (Except.ok (-1)#i32)] = 4⁻¹ := by
  rw [prob_sampleRandomCbd1, prob_uniformFin_four]
  simp (config := { decide := true })

section Necessary

open scoped OracleComp.Necessary

/-- Every value the sampler can return is `0`, `1` or `-1`, and it neither panics nor diverges,
whatever the exception postconditions. Core's `vcgen` steps through the uniform sample, and through
the Rust step by `Interop.Rust.Spec.liftRustM`; what remains is the Rust step's value at each input.
-/
theorem triple_sampleRandomCbd1
    (epost : (Interop.Rust.Error → Prop) × (Unit → Prop) × Std.WP.EStackEnd) :
    Std.WP.Triple sampleRandomCbd1 True (fun r => r = 0#i32 ∨ r = 1#i32 ∨ r = (-1)#i32) epost := by
  unfold sampleRandomCbd1
  vcgen
  fin_cases n <;> simp [lowBits, sample_cbd1_zero, sample_cbd1_one, sample_cbd1_two,
    sample_cbd1_three]

end Necessary

end Interop.Hax.Examples.CenteredBinomial
