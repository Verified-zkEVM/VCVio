/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.Security.EncodedTargets
public import HashSig.SLHDSA.Security.TargetCounts

/-!
# The SLH-DSA-SHA2-128-24 profile

The SP 800-230 reduced parameter set `SLHDSA.slhdsaSha2_128_24`, validated as `limitedVp`, and the
FIPS SHA-2 primitive family at it, `limitedPrimitives`, together with the carrier instances the
`SM_DT_*` games ask for, the parameter values, the eight per-role target caps, and two profile
facts used by witness extraction and ledger commitment.

## Which bundle

`limitedPrimitives` is `Concrete.sha2Primitives` at this profile: the parameterised FIPS SHA-2
family, which is the bundle `limitedEncodedTargetLedgerConditions` and the reachable-target ledgers
of `HashSig.SLHDSA.Security.ReachableTargets` are stated at.

It is not `Concrete.shaPrimitives`, the hand-written SLH-DSA-SHA2-128-24 bundle of
`HashSig.SLHDSA.Concrete.Instance` that `HashSigTest.SLHDSA.Sha2KAT` executes and
`Concrete.shaWireCodec` encodes against. The two are different terms — `adrsToKey` is `shaAdrsKey`
in one and `sha2AdrsKey` in the other, and `Thash` is `shaThash` against `sha2Thash` — and no
theorem relates them, so no statement here transfers to the bundle the known-answer test runs.

## The profile

`slhdsaSha2_128_24` is `n = 16`, `h = 22`, `d = 1`, `hp = 22`, `a = 24`, `k = 6`, `lgw = 2`.
Because `d = 1` the hypertree is a single XMSS tree, with three consequences for the caps.

* The FORS-`T_k` and WOTS+-`T_len` compression caps are equal, `2 ^ 22`, as at every valid `d = 1`
  parameter set; the two compressions are separated by their arities, `p.k = 6` against
  `p.len = 68` (`limitedParams_k`, `limitedParams_len`, `limitedParams_k_ne_len`).
* The WOTS+-`F` undetectability and preimage caps are equal at every parameter set: `targetCount`
  gives both `wotsInstanceCount p * p.len` (`limitedTargetCount_wotsFUd`,
  `limitedTargetCount_wotsFPre`).
* The XMSS-`H` cap is `2 ^ 22 - 1`, one node short of the FORS-`T_k` cap, because a single tree of
  height `hp` has `2 ^ hp - 1` internal nodes.

## References

- NIST SP 800-230 (initial public draft) for the reduced `SLH-DSA-SHA2-128-24` profile
- NIST FIPS 205, §11.2.1 for the SHA-2 family this bundle instantiates
- Barbosa, Dupressoir, Hülsing, Meijers, and Strub, "A Tight Security Proof for SPHINCS+,
  Formally Verified" (`WOTS_TW_ES.ec`)
-/

public section

namespace SLHDSA.Security

open OracleComp OracleSpec

/-! ## The profile and its bundle -/

/-- The SP 800-230 reduced parameter set, validated.  This is
`SLHDSA.LimitedParameterSet.validatedParams` at the one constructor that inductive has, so it is the
same term `limitedEncodedTargetLedgerConditions` concludes at.

*Profile data.* -/
-- Exposed because `limitedVp_params` and the twelve equations below that read a field of
-- `limitedVp.params` are exported theorems proved by `rfl`, and an exported theorem may unfold only
-- exposed definitions; and because `limitedPrimitives_eq` is stated at its parameters.  The two
-- equations whose proofs are not `rfl` — `limitedParams_k_ne_len` and `limitedTargetCount_xmssH` —
-- do not need it.
@[expose] def limitedVp : ValidatedParams :=
  LimitedParameterSet.validatedParams .SLHDSA_SHA2_128_24

-- Exposed for code generation: the eight carrier instances below that generate code infer their
-- compilation type from it, and `limitedPrimitives_eq` is proved by `rfl`.  The ninth instance, the
-- noncomputable finiteness one, generates no code and does not need it.
/-- The FIPS SHA-2 primitive bundle at that profile: `n = 16`, so every seed and node carrier is
`Bytes 16`, and the compressed address key is `Bytes 22`.

*Profile data.* -/
@[expose] def limitedPrimitives : Primitives limitedVp.params :=
  Concrete.sha2Primitives limitedVp.params

/-- The validated profile's parameters are the named reduced set.

*Profile data.* -/
theorem limitedVp_params : limitedVp.params = slhdsaSha2_128_24 := rfl

/-- The bundle is the parameterised FIPS SHA-2 family at that set, and not the hand-written
`Concrete.shaPrimitives` of `HashSig.SLHDSA.Concrete.Instance`, which is a different term.

*Profile data.* -/
theorem limitedPrimitives_eq :
    limitedPrimitives = Concrete.sha2Primitives slhdsaSha2_128_24 := rfl

/-! ## The carrier instances

Instance search does not unfold `limitedPrimitives`, so none of the nine below is found by
`inferInstance`; each names the byte type its carrier is definitionally equal to — eight of them
directly, and the `Fintype` one through the `Finite` instance on that type, for the reason its own
comment gives.  Four carriers are `Bytes 16` and the address key is `Bytes 22`. -/

/-- Signing samples the per-signature `addrnd` from the node type. -/
instance : SampleableType limitedPrimitives.Y := inferInstanceAs (SampleableType (Bytes 16))

/-- Key generation samples the public seed. -/
instance : SampleableType limitedPrimitives.PkSeed := inferInstanceAs (SampleableType (Bytes 16))

/-- Key generation samples the secret seed. -/
instance : SampleableType limitedPrimitives.SkSeed := inferInstanceAs (SampleableType (Bytes 16))

/-- Key generation samples the message-`PRF` key. -/
instance : SampleableType limitedPrimitives.SkPrf := inferInstanceAs (SampleableType (Bytes 16))

/-- Node equality, which the signature type's decidable equality is derived from. -/
instance : DecidableEq limitedPrimitives.Y := inferInstanceAs (DecidableEq (Bytes 16))

/-- Public-seed equality, which the `H_msg` ITSR input type's own equality is derived from. -/
instance : DecidableEq limitedPrimitives.PkSeed := inferInstanceAs (DecidableEq (Bytes 16))

/-- Tweak equality, which every `SM_DT_*` advantage asks for.  The SHA-2 address key is the
compressed twenty-two-byte form. -/
instance : DecidableEq limitedPrimitives.AdrsKey := inferInstanceAs (DecidableEq (Bytes 22))

-- This one is not written like the other eight, and the spelling matters.  Lean evaluates a
-- top-level constant of non-function type when its module is initialised, before any `main` runs.
-- Written `inferInstanceAs (Fintype (Bytes 16))` like its neighbours, this instance is a
-- `Finset.univ` of `2 ^ 128` sixteen-byte vectors built at the start of every executable that
-- imports this module, however little of it that executable uses: so written,
-- `slhdsa_limited_profile_tests` reached 29.5 GB resident in 25 seconds without printing its first
-- check, and none of its checks reads a `Fintype`.  That figure is one run and is not re-measured
-- on every head; what does not depend on a run is the IR below.
--
-- Marking that term `noncomputable` does not fix it.  Over the constants this module adds, as
-- `Lean.IR.findEnvDecl` reports them: written plainly, both `instFintypeYLimitedPrimitives` and the
-- `_aux_1` the elaborator creates for it are computable and both have IR; written `noncomputable`,
-- the instance loses its IR but `_aux_1` keeps it and stays computable — and `_aux_1` is itself a
-- top-level constant of non-function type, so the module initialiser builds it whatever the
-- instance is marked.  The emitted C says the same.  Its size is not a property of the module — it
-- moves with the module name and the package prefix the invocation carries, so a figure from a
-- scratch module does not match `.lake/build/ir/`; what does not move is that `lean -c` on the
-- plain form names this instance on 59 lines and carries a `Fintype.piFinset` call, and on the
-- `noncomputable` form 54 lines and the same call.  Going through `Fintype.ofFinite`, whose
-- argument is the `Prop`-valued `Finite` and which is noncomputable by construction, creates no
-- `_aux_1` at all — only a `_proof_1`, which has no IR — and its C names the instance nowhere and
-- carries no `Fintype` call at all; with it the executable starts at once.  The `noncomputable`
-- form's behaviour here is read off its IR and emitted C, not from a run of it.  The three other
-- carrier instances that are constants are harmless — `SampleableType` is a sampling program and
-- `Inhabited` is one sixteen-byte vector — and `DecidableEq` is a function.
/-- Finiteness of the node type, which the `DSPR` advantage asks for.  It is a proof-level
instance: the type has `2 ^ 128` elements and nothing may enumerate it. -/
noncomputable instance : Fintype limitedPrimitives.Y :=
  @Fintype.ofFinite _ (inferInstanceAs (Finite (Bytes 16)))

/-- Inhabitedness of the node type, which the OpenPRE coupling asks for. -/
instance : Inhabited limitedPrimitives.Y := inferInstanceAs (Inhabited (Bytes 16))

/-! ## The profile's numbers -/

/-- One hypertree layer.

*Profile data.* -/
theorem limitedParams_d : limitedVp.params.d = 1 := rfl

/-- Winternitz width four, from `lgw = 2`.

*Profile data.* -/
theorem limitedParams_w : limitedVp.params.w = 4 := rfl

/-- **`w - 2` is two at this profile.**  The WOTS+-`F` undetectability term of the EasyCrypt
SPHINCS+ bound carries the coefficient `(p.w - 2 : ℕ)`; here that is `4 - 2`.  At every FIPS 205
set `lgw = 4` and the coefficient is `14` instead.

*Profile data.* -/
theorem limitedParams_wotsFUd_coefficient : (limitedVp.params.w - 2 : ℕ) = 2 := rfl

/-- Six FORS trees per instance.

*Profile data.* -/
theorem limitedParams_k : limitedVp.params.k = 6 := rfl

/-- Sixty-eight WOTS+ chains per instance, at `n = 16` and `lgw = 2`.

*Profile data.* -/
theorem limitedParams_len : limitedVp.params.len = 68 := rfl

/-- **The two `T_ℓ` compressions have different arities here**, which is what separates their two
games at a profile whose caps coincide.

*Profile data.* -/
theorem limitedParams_k_ne_len : limitedVp.params.k ≠ limitedVp.params.len := by decide

/-- The FORS-`F` cap: `2 ^ h · k · 2 ^ a`.

*Profile data.* -/
theorem limitedTargetCount_forsF :
    targetCount limitedVp.params .forsF = 6 * 2 ^ 46 := rfl

/-- The FORS-`H` cap: `2 ^ h · k · (2 ^ a − 1)`, one node per internal FORS node.

*Profile data.* -/
theorem limitedTargetCount_forsH :
    targetCount limitedVp.params .forsH = 2 ^ 22 * 6 * (2 ^ 24 - 1) := rfl

/-- The FORS-`T_k` cap: one root compression per FORS instance, so `2 ^ h`.

*Profile data.* -/
theorem limitedTargetCount_forsTl :
    targetCount limitedVp.params .forsTl = 2 ^ 22 := rfl

/-- The WOTS+-`F` undetectability cap: one per chain of every WOTS+ instance.

*Profile data.* -/
theorem limitedTargetCount_wotsFUd :
    targetCount limitedVp.params .wotsFUd = 2 ^ 22 * 68 := rfl

/-- The WOTS+-`F` target-collision cap: the undetectability cap times the width, since a chain is
walked at most `w` times.

*Profile data.* -/
theorem limitedTargetCount_wotsFTcr :
    targetCount limitedVp.params .wotsFTcr = 2 ^ 22 * 68 * 4 := rfl

/-- The WOTS+-`F` preimage cap, which is the undetectability cap.

*Profile data.* -/
theorem limitedTargetCount_wotsFPre :
    targetCount limitedVp.params .wotsFPre = 2 ^ 22 * 68 := rfl

/-- The WOTS+-`T_len` cap: one public-key compression per WOTS+ instance.  **It equals the
FORS-`T_k` cap here**, and at every valid `d = 1` set.

*Profile data.* -/
theorem limitedTargetCount_wotsTl :
    targetCount limitedVp.params .wotsTl = 2 ^ 22 := rfl

/-- The XMSS-`H` cap: the internal nodes of the one tree, `2 ^ hp − 1`.

*Profile data.* -/
theorem limitedTargetCount_xmssH :
    targetCount limitedVp.params .xmssH = 2 ^ 22 - 1 :=
  targetCount_xmssH_eq limitedVp.params limitedVp.valid

/-! ## The two profile facts the witness families need -/

/-- Fixed-width byte nodes satisfy the representation-coherence boundary, which is what
`SchemeWitnesses.findWitness_isSome` asks of a bundle.

Witness extraction in the `HashSig.SLHDSA.Security.*Witnesses` modules asks for it.

*Profile data.* -/
theorem limitedPrimitives_byteLaws : limitedPrimitives.core.ByteLaws :=
  Concrete.sha2Primitives_byteLaws _

/-- **The encoded target ledgers stay duplicate-free at this profile**, which is
`limitedEncodedTargetLedgerConditions` at its one constructor.

A reduction that commits the encoded ledger to a `SourceFinalValidity` game needs it: the
game's monitor clears the validity bit on a repeated target tweak.

*Profile data.* -/
theorem limitedEncodedConditions :
    EncodedTargetLedgerConditions limitedVp limitedPrimitives :=
  limitedEncodedTargetLedgerConditions .SLHDSA_SHA2_128_24

end SLHDSA.Security
