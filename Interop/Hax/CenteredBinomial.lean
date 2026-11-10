/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Devon Tuma
-/

import Aeneas.Std.Scalar
import Interop.Rust.RustM
import Interop.Rust.Run
import VCVio.OracleComp.ProbComp
import VCVio.EvalDist.Monad.Basic
import VCVio.ProgramLogic.Tactics

/-!
# A Rust centered-binomial sampler, through `RustM`, in VCVio

One step of ML-KEM's `SamplePolyCBD_η` at `η = 1`, as Rust:

```rust
pub fn sample_cbd1(b: u8) -> i32 {
    let a = (b & 1) as i32;
    let c = ((b >> 1) & 1) as i32;
    a - c
}
```

`sample_cbd1` below is that function in the `RustM` code hax emits today, over Aeneas's scalars:
the bitwise `&&&` and the casts are pure, while the shift and the subtraction are checked and
return `RustM`. It is a transcription: `cargo hax into lean` was not run to produce it.

Lifted into `RustOracleComp unifSpec` by `Interop.Rust.liftRustM` and fed two uniform bits, it
returns `0` with probability `1/2` and `±1` with probability `1/4` each: the centered binomial
distribution with parameter `1`.

## Main results

* `Interop.Hax.Examples.CenteredBinomial.sample_cbd1_zero` (and `_one`, `_two`, `_three`): the
  four bit patterns that matter.
* `Interop.Hax.Examples.CenteredBinomial.probOutput_sampleRandomCbd1_zero`, `_pos_one`, `_neg_one`:
  the distribution.
-/

open Aeneas.Std Interop.Rust OracleSpec OracleComp OracleComp.ProgramLogic ENNReal

namespace Interop.Hax.Examples.CenteredBinomial

/-- The Rust `sample_cbd1` in `RustM`: the low two bits of `b`, widened to `i32`, subtracted. -/
def sample_cbd1 (b : U8) : RustM I32 := do
  let a : I32 := UScalar.hcast .I32 (b &&& 1#u8)
  let s ← b >>> 1#i32
  let c : I32 := UScalar.hcast .I32 (s &&& 1#u8)
  a - c

/-- Evaluate `sample_cbd1` on a literal: unfold the checked shift and subtraction and decide
their range tests. `RustM` is irreducible, so `decide` alone cannot. -/
local macro "cbd_eval" : tactic =>
  `(tactic| (simp (config := { decide := true }) only [sample_cbd1, HShiftRight.hShiftRight,
    UScalar.shiftRight_IScalar, UScalar.shiftRight, HSub.hSub, IScalar.sub, IScalar.tryMk,
    ite_true, bind_tc_ok]; rfl))

theorem sample_cbd1_zero : sample_cbd1 0#u8 = RustM.ok 0#i32 := by cbd_eval

theorem sample_cbd1_one : sample_cbd1 1#u8 = RustM.ok 1#i32 := by cbd_eval

theorem sample_cbd1_two : sample_cbd1 2#u8 = RustM.ok (-1)#i32 := by cbd_eval

theorem sample_cbd1_three : sample_cbd1 3#u8 = RustM.ok 0#i32 := by cbd_eval

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
  vcgen
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
  rw [prob_sampleRandomCbd1, prob_uniformFin_four]
  simp (config := { decide := true })
  rw [one_add_one_eq_two, show (4 : ℝ≥0∞) = 2 * 2 by norm_num,
    ENNReal.mul_inv (Or.inl two_ne_zero) (Or.inl ENNReal.ofNat_ne_top), ← mul_assoc,
    ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]

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

end Interop.Hax.Examples.CenteredBinomial
