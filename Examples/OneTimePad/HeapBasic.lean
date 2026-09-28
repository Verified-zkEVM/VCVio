/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.StateSeparating.MeasureDistEquiv
public import VCVio.OracleComp.Constructions.BitVec
public import VCVio.OracleComp.Constructions.SampleableType.Basic
public import VCVio.OracleComp.ProbComp.Basic
public import VCVio.OracleComp.SimSemantics.SimulateQ
public import VCVio.OracleComp.Constructions.UniformFinMeasure
public import VCVio.EvalDist.Monad.UniformTable
public import ToMathlib.Probability.UniformOn
public import ToMathlib.Data.FinEnum
public import Init.Data.UInt.Lemmas
public import Mathlib.Data.FinEnum
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Vector
public import ToMathlib.Data.Heap

/-!
# One-Time Pad as a state-separating handler

Pilot port of `Examples.OneTimePad.Basic` to the experimental `state-separating`
framework: the OTP perfect-secrecy story, rebuilt as a `state-separating.Handler`
"real vs ideal" pair, with the SSProve-style "single-call gate" idiom
applied so that distributional equivalence holds *unconditionally* at
the handler level.

## SSProve "single-call gate" idiom

OTP secrecy is structurally one-shot: encrypting two messages under the
same key reveals their XOR. To make `realImpl ≡ᵈ idealImpl` hold against
*every* adversary (rather than the "adversary issues at most one query"
fragment), both handlers bake the call-counting into their state. Each
handler carries a single `UsedFlag.used : Bool` cell, gated as follows:

* On the **first** `enc m` call (`h .used = false`), the handler does
  its real work (real: sample `k`, return `k ⊕ m`; ideal: sample a
  fresh `c`, return `c`) and flips `.used := true`.
* On **subsequent** calls (`h .used = true`), the handler short-circuits
  to a fixed dummy ciphertext (`0#sp`), with no further sampling.

Because the gate makes the second-and-later calls deterministic and
identical on both sides, and because the first call's outputs have the
same distribution (XOR with a uniform key is uniform), the two handlers
are distributionally equivalent against every adversary. This is the
standard SSProve playbook for bounded-query primitives: enforce the
bound *in the handler*, then quantify the equivalence over all
adversaries.

## Sampling deferred into the handler

A second SSProve-style choice: the real handler's key is **not** sampled
at `init` and stored in the heap. Instead, both `init`s are
`pure Heap.empty`, and the real handler samples its key locally on the
first call. This keeps the two `init`s measure-equal (so the simple
"per-handler" `MeasureDistEquiv.of_step` constructor applies) without any heap
bijection bookkeeping, and is observationally equivalent for OTP
because the key is single-use anyway.

## What this file builds

* `otpSpec sp` exposes a single export query `enc m` taking a plaintext
  `m : BitVec sp` and returning a ciphertext `BitVec sp`.
* `UsedFlag` is the single-cell identifier set carrying `.used : Bool`,
  shared by both handlers.
* `realImpl sp` and `idealImpl sp` are the gated real and ideal handlers
  on `UsedFlag`.
* `realImpl_distEquiv_idealImpl : realImpl sp ≡ᵈ₀ idealImpl sp` is the
  unconditional measure-equivalence headline, proved via
  `QueryImpl.Stateful.MeasureDistEquiv.of_step`.
* `encOnce sp m` is the canonical single-call adversary; the
  `evalDist_run_encOnce_eq` corollary on it is a one-line
  consequence of the equivalence.

## Comparison with `Examples.OneTimePad.Basic`

`Basic.lean` uses the `SymmEncAlg` abstraction layer (with
`perfectSecrecyExperiment`, `Complete`, `perfectSecrecyAt`); it does not use
the SSP handler layer. This file uses the state-separating handler layer
directly, in the SSProve-style "handler as bounded-query gate" idiom.
The arithmetic core, "XOR with a uniform key is uniform", is the uniform
reindexing law `evalDist_bind_bijective_of_uniform` against the XOR involution. -/

@[expose] public section

open OracleSpec OracleComp ENNReal
open scoped QueryImpl.Stateful

namespace VCVio.StateSeparating.OneTimePad

/-! ## Export oracle interface

A single export query `enc m` with `m : BitVec sp` carrying the
plaintext, returning a ciphertext `BitVec sp`. -/

/-- The OTP export query index: a single constructor `enc m` carrying
the plaintext. -/
inductive OTPOp (sp : ℕ)
  | enc (m : BitVec sp)

/-- The OTP export interface: each `enc _` query returns a `BitVec sp`
ciphertext. -/
@[reducible] def otpSpec (sp : ℕ) : OracleSpec.{0, 0} (OTPOp sp)
  | .enc _ => BitVec sp

/-! ## Single-call gate

Both `realImpl` and `idealImpl` use the same one-cell identifier set
`UsedFlag`. The lone cell `.used : Bool` records whether the (one)
encryption has already been issued. -/

/-- Cell directory carrying the single-call gate flag. -/
inductive UsedFlag
  | used
  deriving DecidableEq

/-- The cell `used` carries a `Bool`; the default value is `false`,
so a fresh `Heap.empty` represents "no encryption issued yet". -/
instance instCellSpecUsedFlag : CellSpec UsedFlag where
  type    | .used => Bool
  default | .used => false

/-! ## Real and ideal handlers with the call gate -/

/-- The **real-world OTP handler** with single-call gating.

* **State.** A single `UsedFlag.used : Bool` cell.
* **Init.** Trivial (`pure Heap.empty`); the key is sampled on demand.
* **Handler.** On the first `enc m` call (`h .used = false`), sample a
  uniform key `k` *locally*, return `k ⊕ m`, and flip `.used := true`.
  On subsequent calls (`h .used = true`), short-circuit to `0#sp`. -/
def realImpl (sp : ℕ) : QueryImpl.Stateful unifSpec (otpSpec sp) (Heap UsedFlag)
  | .enc m => StateT.mk fun (h : Heap UsedFlag) =>
        if h .used then
          pure (0#sp, h)
        else do
          let k ← ($ᵗ BitVec sp : ProbComp (BitVec sp))
          pure (k ^^^ m, h.update .used true)

/-- The **ideal-world OTP handler** with single-call gating.

* **State.** A single `UsedFlag.used : Bool` cell.
* **Init.** Trivial (`pure Heap.empty`).
* **Handler.** On the first `enc _` call, sample a fresh uniform
  ciphertext, return it, and flip `.used := true`. On subsequent calls,
  short-circuit to `0#sp`.

The same identifier set as `realImpl` is shared on purpose: it lets the
proof `realImpl_distEquiv_idealImpl` use the simple
`QueryImpl.Stateful.MeasureDistEquiv.of_step` constructor (per-handler measure
equality), avoiding any heap bijection bookkeeping. -/
def idealImpl (sp : ℕ) : QueryImpl.Stateful unifSpec (otpSpec sp) (Heap UsedFlag)
  | .enc _ => StateT.mk fun (h : Heap UsedFlag) =>
        if h .used then
          pure (0#sp, h)
        else do
          let c ← ($ᵗ BitVec sp : ProbComp (BitVec sp))
          pure (c, h.update .used true)

/-! ## XOR-by-`m` is a bijection on `BitVec sp` -/

/-- Right XOR by a fixed mask is a bijection on `BitVec sp`: it is its
own inverse via `(a ^^^ m) ^^^ m = a`. The key arithmetic fact behind
OTP perfect secrecy. -/
private lemma bitVec_xor_right_bijective (sp : ℕ) (m : BitVec sp) :
    Function.Bijective ((· ^^^ m) : BitVec sp → BitVec sp) := by
  refine ⟨fun a b hab => ?_, fun y => ⟨y ^^^ m, ?_⟩⟩
  · have h : a ^^^ m ^^^ m = b ^^^ m ^^^ m := congrArg (· ^^^ m) hab
    simpa [BitVec.xor_assoc] using h
  · change y ^^^ m ^^^ m = y
    rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

/-! ## Per-(query, heap) handler equivalence

The arithmetic core of OTP perfect secrecy at the handler layer:
on every (query, heap) pair, `realImpl`'s and `idealImpl`'s handlers
have the same output measure. Exposed as a stand-alone lemma so that
parallel-channel cutovers (e.g. `Examples.OneTimePad.HeapPar`) can
feed it to `QueryImpl.Stateful.MeasureDistEquiv.parSum_congr` without re-running
the case-split. -/

/-- **Per-handler equality in distribution** between `realImpl sp` and
`idealImpl sp`. On every input `(query, heap)`, the two handlers
produce the same distribution on replies and updated heaps.

Splits on `h .used`:

* `h .used = true` (gated): both handlers reduce to `pure (0#sp, h)`,
  with no sampling.
* `h .used = false` (live): both handlers sample a uniform value
  before tagging the heap; the inner `do`-blocks differ only by an
  XOR-with-`m` on the sampled value, which `(· ^^^ m)` being a
  bijection on `BitVec sp` makes invisible to the output measure (via
  `evalDist_bind_bijective_of_uniform`). -/
theorem realImpl_impl_evalDistEq_idealImpl (sp : ℕ) (q : (otpSpec sp).Domain)
    (h : Heap UsedFlag) :
    ((realImpl sp) q).run h =ᵈ ((idealImpl sp) q).run h := by
  let : MeasurableSpace ((otpSpec sp).Range q × Heap UsedFlag) := ⊤
  refine EvalDistEq.of_evalDist_eq ?_
  cases q with
  | enc m =>
    change 𝒟[if h .used then (pure (0#sp, h) : OracleComp unifSpec _)
         else do let k ← ($ᵗ BitVec sp : ProbComp (BitVec sp));
                 pure (k ^^^ m, h.update .used true)] =
      𝒟[if h .used then (pure (0#sp, h) : OracleComp unifSpec _)
         else do let c ← ($ᵗ BitVec sp : ProbComp (BitVec sp));
                 pure (c, h.update .used true)]
    by_cases hused : h .used
    · rw [ite_eq_left hused, ite_eq_left hused]
    · rw [ite_eq_right hused, ite_eq_right hused]
      -- The two `do`-blocks have the same measure via the XOR-by-`m`
      -- bijection on the uniform sample.
      exact evalDist_bind_bijective_of_uniform ($ᵗ BitVec sp : ProbComp (BitVec sp))
        (SampleableType.evalDist_bitVec sp) (· ^^^ m) (bitVec_xor_right_bijective sp m)
        (fun y => pure (y, h.update .used true))

/-! ## Unconditional distributional equivalence

The headline statement: `realImpl sp ≡ᵈ idealImpl sp`. Once the
`UsedFlag` gate is in place, the equivalence holds against *every*
adversary, not just single-call ones. -/

/-- **OTP unconditional distributional equivalence.** With the
single-call gate baked into both handlers, the real and ideal OTP
handlers produce identical output distributions against every
adversary, on every output type.

Proof shape: `QueryImpl.Stateful.MeasureDistEquiv.of_step` from the default initial
heap state, using the per-(query, heap) handler equivalence
`realImpl_impl_evalDistEq_idealImpl`. -/
theorem realImpl_distEquiv_idealImpl (sp : ℕ) :
    realImpl sp ≡ᵈ₀ idealImpl sp :=
  QueryImpl.Stateful.MeasureDistEquiv.of_step (realImpl_impl_evalDistEq_idealImpl sp) Heap.empty

/-! ## Single-call adversary and corollary -/

/-- The single-call adversary that issues one `enc m` query and
returns the ciphertext verbatim.

The body `(otpSpec sp).query (.enc m)` is an `OracleQuery (otpSpec sp) _`;
the implicit `MonadLift (OracleQuery spec) (OracleComp spec)` lifts it
into `OracleComp (otpSpec sp) (BitVec sp)`, matching the declared
return type. Going through the named `(otpSpec sp).query` (rather than
the bare `query (.enc m)`) is what pins down the `spec` for elaboration. -/
def encOnce (sp : ℕ) (m : BitVec sp) : OracleComp (otpSpec sp) (BitVec sp) :=
  (otpSpec sp).query (.enc m)

/-- **OTP single-query indistinguishability**, recovered as a corollary
of `realImpl_distEquiv_idealImpl` by specialising the universal `≡ᵈ` to
the canonical single-call adversary `encOnce sp m`.

The same content, framed as equality in distribution of
`SymmEncAlg.perfectSecrecyCipherGivenMsgExperiment` rows, is proved as `ciphertextRowsEqual` in
`Examples.OneTimePad.Basic`. The state-separating framing replaces the
"reductive bijection" of that proof with the "per-call gate" idiom: a
direct existence statement at the handler level rather than a
per-message reduction. -/
theorem evalDist_run_encOnce_eq (sp : ℕ) (m : BitVec sp) :
    𝒟[(realImpl sp).runProb₀ (encOnce sp m)] =
      𝒟[(idealImpl sp).runProb₀ (encOnce sp m)] :=
  realImpl_distEquiv_idealImpl sp (encOnce sp m)

end VCVio.StateSeparating.OneTimePad
