/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.Security.SufBound
public import HashSig.SLHDSA.Security.EncodedTargets

/-!
# The bound at the SLH-DSA-SHA2-128-24 profile

`HashSig.SLHDSA.Security.Composition` states the twelve-summand EUF-CMA bound for an arbitrary
validated parameter set and an arbitrary primitive bundle, and
`HashSig.SLHDSA.Security.SufBound` carries it across the SUF-to-EUF partition.  This module
instantiates both at one parameter set — the SP 800-230 reduced profile
`SLHDSA.slhdsaSha2_128_24` — and at one primitive bundle, the FIPS SHA-2 family at that profile.

## What instantiating does

Three things, and they are all this module does.

* **It discharges the instance obligations.**  `Certificate` asks for nine carrier instances, and
  at this bundle none of them is found by instance search: every one of the nine is stated with
  `inferInstanceAs` at the byte type the carrier is definitionally equal to.  Measured, the nine
  written with plain `inferInstance` instead give nine failures to synthesize, one per
  declaration, over the five distinct carriers `Y`, `PkSeed`, `SkSeed`, `SkPrf` and `AdrsKey`.
* **It turns the one `Params`-level coefficient into a numeral.**  `Summands.bound` carries
  `(p.w - 2 : ℕ)` on the WOTS+-`F` undetectability summand; here `lgw = 2`, so `w = 4` and the
  coefficient is `2`.  `limitedAdvantage_le_summands` is the bound with that numeral and with the
  library's `3` written out, in one inequality.
* **It turns the eight target caps into numerals.**  `limitedTargetCount_*` below.

## What instantiating does not do

It does not make the statement say anything about SLH-DSA-SHA2-128-24's security, and the reason
is not specific to this profile.  `Certificate` quantifies existentially over eleven adversaries
with nothing tying any of them to the adversary being bounded, so — as
`HashSig.SLHDSA.Security.Composition`'s module docstring records and
`HashSigTest.SLHDSA.Composition` checks — a closed certificate is constructible from an address
key and a public seed at *every* validated parameter set and *every* bundle carrying those nine
instances, and the bound it names is then at least one.  This profile and this bundle are one such
pair: `HashSigTest.SLHDSA.LimitedProfile` builds that certificate here and proves that the bound
it names is at least one, so at it `limitedAdvantage_le_bound` is `probOutput_le_one` with extra
steps.  Every deferral of the two general modules is inherited
unchanged: no reduction adversary is constructed, no challenge is recorded, no game's final
validity is established, neither PRF hop is taken, the undetectability hybrid is not performed,
the `MCO_ITSR` summand carries no query bound, the same-randomizer residual has no bound at all,
and the Lean branch assignment is not the source's.

So what is quoted below as "the bound at SLH-DSA-SHA2-128-24" is the *shape* of
`EUFCMA_SPHINCS_PLUS`'s right-hand side, with this profile's coefficient and this profile's caps
filled in.  It is not a security claim, and a reader who wants one should read the two
certificates the fixture builds first.

## Which bundle, and the other one

`limitedPrimitives` is `Concrete.sha2Primitives` at this profile: the parameterised FIPS SHA-2
family, which is the bundle slice 2's `limitedEncodedTargetLedgerConditions` and slice 1's ledgers
are stated at.

It is **not** `Concrete.shaPrimitives`, the hand-written SLH-DSA-SHA2-128-24 bundle of
`HashSig.SLHDSA.Concrete.Instance` that `HashSigTest.SLHDSA.Sha2KAT` executes and
`Concrete.shaWireCodec` encodes against.  The two are different terms — `adrsToKey` is
`shaAdrsKey` in one and `sha2AdrsKey` in the other, and `Thash` is `shaThash` against
`sha2Thash` — and nothing in this repository relates them: measured, no declaration mentions both,
and `shaPrimitives = sha2Primitives slhdsaSha2_128_24` is not closed by `rfl`.  So no statement
here transfers to the bundle the known-answer test runs, and none should be read as doing so.

## The profile, and the one cell that goes dark at it

`slhdsaSha2_128_24` is `n = 16`, `h = 22`, `d = 1`, `hp = 22`, `a = 24`, `k = 6`, `lgw = 2`.
Because `d = 1` the hypertree is a single XMSS tree, and two consequences matter for reading the
bound.

* The FORS-`T_k` and WOTS+-`T_len` compression games have **the same cap**, `2 ^ 22`.  That is not
  an accident of this profile: `HashSigTest.SLHDSA.Composition` proves the caps equal at every
  valid `d = 1` parameter set and strictly ordered at every valid set with `2 ≤ d`.  So at this
  profile a cap check cannot tell the two games apart, and what does is the arity — `p.k = 6`
  against `p.len = 68`, pinned here by `limitedParams_k`, `limitedParams_len` and
  `limitedParams_k_ne_len`, and read off the two games' own attacked-member equations in the
  fixture.
* The XMSS-`H` cap is `2 ^ 22 - 1`, one node short of the FORS-`T_k` cap, because a single tree of
  height `hp` has `2 ^ hp - 1` internal nodes.

## Labels

Thirty-four declarations, of which nine are instances.

*Profile data* — a statement about the parameter set, the bundle, or a cap at it.  Twenty:

* `limitedVp`, `limitedPrimitives`, `limitedVp_params`, `limitedPrimitives_eq`;
* `limitedParams_d`, `limitedParams_w`, `limitedParams_wotsFUd_coefficient`,
  `limitedParams_k`, `limitedParams_len`, `limitedParams_k_ne_len`;
* `limitedTargetCount_forsF`, `limitedTargetCount_forsH`, `limitedTargetCount_forsTl`,
  `limitedTargetCount_wotsFUd`, `limitedTargetCount_wotsFTcr`, `limitedTargetCount_wotsFPre`,
  `limitedTargetCount_wotsTl`, `limitedTargetCount_xmssH`;
* `limitedPrimitives_byteLaws`, `limitedEncodedConditions`.

*Profile corollary* — a general theorem of the two previous modules at this profile.  Five:

* `limitedAdvantage_le_bound`, `limitedBound_eq`, `limitedAdvantage_le_summands`;
* `limitedStrongAdvantage_le_bound_add_sameMessage`, `limitedStrongAdvantage_le_sufBound`.

None is `private`.  Two carry `@[expose]`, `limitedVp` and `limitedPrimitives`, and the comment
above each records the errors its removal alone produces.

## References

- NIST SP 800-230 (initial public draft) for the reduced `SLH-DSA-SHA2-128-24` profile
- NIST FIPS 205, §11.2.1 for the SHA-2 family this bundle instantiates
- Barbosa, Dupressoir, Hülsing, Meijers, and Strub, "A Tight Security Proof for SPHINCS+,
  Formally Verified" (`SPHINCS_PLUS.ec`, `WOTS_TW_ES.ec`)
-/

public section

namespace SLHDSA.Security

open OracleComp OracleSpec ENNReal SignatureAlg TweakableHash Security.CanonicalGames

/-! ## The profile and its bundle -/

/-- The SP 800-230 reduced parameter set, validated.  This is
`SLHDSA.LimitedParameterSet.validatedParams` at the one constructor that inductive has, so it is
the same term slice 2's `limitedEncodedTargetLedgerConditions` concludes at.

*Profile data.* -/
-- Exposed, and what the attribute is for was read off the errors its removal alone produces:
-- fourteen.  Thirteen are `Not a definitional equality`, at `limitedVp_params` and at the twelve
-- `rfl` equations below that read a field of `limitedVp.params`, each reporting that the
-- theorem is exported and so may unfold only exposed definitions; the fourteenth is a
-- `Type mismatch` at `limitedPrimitives_eq`.  The two equations that survive are the ones whose
-- proofs are not `rfl`: `limitedParams_k_ne_len` and `limitedTargetCount_xmssH`.
@[expose] def limitedVp : ValidatedParams :=
  LimitedParameterSet.validatedParams .SLHDSA_SHA2_128_24

-- Exposed, and what the attribute is for was read off the errors its removal alone produces:
-- nineteen.  Eighteen are code-generation failures, two at each of the nine instances below,
-- each reporting that the locally inferred compilation type differs from the one other modules
-- would infer and naming `limitedPrimitives` as the definition to expose; the nineteenth is a
-- `Not a definitional equality` at `limitedPrimitives_eq`.  No corollary moves.
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
`inferInstance`; each names the byte type its carrier is definitionally equal to.  Four carriers
are `Bytes 16` and the address key is `Bytes 22`. -/

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

-- **This one is not written like the other eight, and the reason was measured.**  Lean evaluates
-- a top-level constant of non-function type when its module is initialised, before any `main`
-- runs.  Written `inferInstanceAs (Fintype (Bytes 16))` like its neighbours, this instance is a
-- `Finset.univ` of `2 ^ 128` sixteen-byte vectors built at the start of every executable that
-- imports this module, however little of it that executable uses: so written,
-- `slhdsa_limited_profile_tests` reached 29.5 GB resident in 25 seconds without printing its
-- first check, and none of its checks reads a `Fintype`.  Marking that term `noncomputable` does
-- not fix it — the auxiliary definition the elaborator creates for it is compiled anyway, the
-- generated C still carries the product-`Fintype` call, and the binary still does not reach its
-- first check.  Going through `Fintype.ofFinite`, whose argument is the `Prop`-valued `Finite`
-- and which is noncomputable by construction, leaves no code to generate: measured, the module's
-- generated C then contains no product-`Fintype` call at all and the executable starts at once.
-- The three other carrier instances that are constants are harmless — `SampleableType` is a
-- sampling program and `Inhabited` is one sixteen-byte vector — and `DecidableEq` is a function.
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

/-- **The undetectability coefficient at this profile is two.**  `Summands.bound` carries
`(p.w - 2 : ℕ)`; here that is `4 - 2`.  At every FIPS 205 set `lgw = 4` and the coefficient is
`14` instead, so this numeral is a property of the reduced profile and not of the expression.

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

*Profile data.* -/
theorem limitedPrimitives_byteLaws : limitedPrimitives.core.ByteLaws :=
  Concrete.sha2Primitives_byteLaws _

/-- **The encoded target ledgers stay duplicate-free at this profile**, which is slice 2's
`limitedEncodedTargetLedgerConditions` at its one constructor.

It is stated here as a fact about the profile and is deliberately *not* a hypothesis of the
corollaries below: nothing in the bound's proof consumes it.  What consumes it is the adversary
construction that none of these modules performs — the `SourceFinalValidity` monitor kills a
game's validity bit on a repeated target tweak, so a reduction that commits the encoded ledger
needs exactly this.

*Profile data.* -/
theorem limitedEncodedConditions :
    EncodedTargetLedgerConditions limitedVp limitedPrimitives :=
  limitedEncodedTargetLedgerConditions .SLHDSA_SHA2_128_24

/-! ## The corollaries

Each is a general theorem of `HashSig.SLHDSA.Security.Composition` or
`HashSig.SLHDSA.Security.SufBound` applied at `limitedPrimitives`, with the instances above
discharging its instance hypotheses.  None strengthens what it instantiates, and each carries the
same `Certificate` hypothesis, which at this bundle costs an address key and a public seed. -/

section Corollary

variable {adv : unforgeableAdv (generalAlg limitedPrimitives)}

/-- **The conditional EUF-CMA bound at SLH-DSA-SHA2-128-24.**  For any adversary against the
external SLH-DSA algebra at this bundle and any certificate for it, the EUF-CMA advantage is at
most the twelve-summand expression that certificate names.

This is `Composition.advantage_le_bound` and nothing more.  Its antecedent is free here exactly as
it is there: `HashSigTest.SLHDSA.LimitedProfile` builds a closed `Certificate` at this bundle from
an address key and a public seed and proves the bound it names is at least one.

*Profile corollary.* -/
theorem limitedAdvantage_le_bound (c : Certificate limitedPrimitives adv) :
    adv.advantage ProbCompRuntime.probComp ≤ c.summands.bound limitedVp.params :=
  advantage_le_bound c

/-- **The bound written out at this profile**: `Certificate.bound_eq` with `(p.w - 2 : ℕ)`
evaluated to the numeral `2`.  The other coefficient, the `3` on the FORS-`F` target-collision
summand, is the library's and is not a property of the profile:
`SM_DT_OpenPRE_SourceFinalValidity.TCRDSPRBound` has it.

*Profile corollary.* -/
theorem limitedBound_eq (c : Certificate limitedPrimitives adv) :
    c.summands.bound limitedVp.params =
      prfAbsAdvantage (skPrfScheme limitedPrimitives c.pkSeed) c.skgAdv
        + prfAbsAdvantage (msgPrfScheme limitedPrimitives) c.mkgAdv
        + KeyedHash.ITSRAdvantage c.itsrAdv
        + SM_DT_DSPR_SourceFinalValidity.Advantage
            (SM_DT_OpenPRE_SourceFinalValidity.toDSPR c.openPreAdv)
        + 3 * SM_DT_TCR_SourceFinalValidity.Advantage
            (SM_DT_OpenPRE_SourceFinalValidity.toTCR c.openPreAdv)
        + SM_DT_TCR_SourceFinalValidity.Advantage c.forsHAdv
        + SM_DT_TCR_SourceFinalValidity.Advantage c.forsTlAdv
        + 2 * SM_DT_UD_SourceFinalValidity.AbsoluteAdvantage c.wotsFUdAdv
        + SM_DT_TCR_SourceFinalValidity.Advantage c.wotsFTcrAdv
        + SM_DT_PRE_SourceFinalValidity.Advantage c.wotsFPreAdv
        + SM_DT_TCR_SourceFinalValidity.Advantage c.wotsTlAdv
        + SM_DT_TCR_SourceFinalValidity.Advantage c.xmssHAdv := by
  rw [Certificate.bound_eq, limitedParams_wotsFUd_coefficient]
  norm_num

/-- **The reduced profile's bound, as one inequality.**  This is the form the corollary is quoted
in: twelve named advantages, the source's order, the source's `3`, and this profile's `2` where
the general expression carries `w − 2`.

Both coefficients are visible and neither is bounded by anything.  Read
`HashSigTest.SLHDSA.LimitedProfile`'s canary before quoting it: the eleven adversaries are the
certificate's, chosen with nothing tying them to `adv`, and at a certificate this file's fixture
builds the right-hand side is at least one.

*Profile corollary.* -/
theorem limitedAdvantage_le_summands (c : Certificate limitedPrimitives adv) :
    adv.advantage ProbCompRuntime.probComp ≤
      prfAbsAdvantage (skPrfScheme limitedPrimitives c.pkSeed) c.skgAdv
        + prfAbsAdvantage (msgPrfScheme limitedPrimitives) c.mkgAdv
        + KeyedHash.ITSRAdvantage c.itsrAdv
        + SM_DT_DSPR_SourceFinalValidity.Advantage
            (SM_DT_OpenPRE_SourceFinalValidity.toDSPR c.openPreAdv)
        + 3 * SM_DT_TCR_SourceFinalValidity.Advantage
            (SM_DT_OpenPRE_SourceFinalValidity.toTCR c.openPreAdv)
        + SM_DT_TCR_SourceFinalValidity.Advantage c.forsHAdv
        + SM_DT_TCR_SourceFinalValidity.Advantage c.forsTlAdv
        + 2 * SM_DT_UD_SourceFinalValidity.AbsoluteAdvantage c.wotsFUdAdv
        + SM_DT_TCR_SourceFinalValidity.Advantage c.wotsFTcrAdv
        + SM_DT_PRE_SourceFinalValidity.Advantage c.wotsFPreAdv
        + SM_DT_TCR_SourceFinalValidity.Advantage c.wotsTlAdv
        + SM_DT_TCR_SourceFinalValidity.Advantage c.xmssHAdv := by
  rw [← limitedBound_eq c]
  exact limitedAdvantage_le_bound c

end Corollary

section StrongCorollary

variable {sadv : strongUnforgeableAdv (generalAlg limitedPrimitives)}

/-- **The SUF-CMA bound at SLH-DSA-SHA2-128-24**, which is `SufBound`'s headline here: the
twelve-summand expression plus the same-message residual.

`SufBound.strongAdvantage_le_add_sameMessage_iff` says this is the existential corollary above and
nothing more — the residual on the right is the residual inside the left, and the two cancel.

*Profile corollary.* -/
theorem limitedStrongAdvantage_le_bound_add_sameMessage
    (c : Certificate limitedPrimitives sadv.toUnforgeableAdv) :
    sadv.advantage ProbCompRuntime.probComp ≤
      c.summands.bound limitedVp.params +
        sadv.sameMessageAdvantage ProbCompRuntime.probComp :=
  strongAdvantage_le_bound_add_sameMessage c

/-- **The SUF-CMA bound refined through the two named halves at this profile.**  The residual is
the fresh-randomizer half plus the same-randomizer half of
`HashSig.SLHDSA.Security.SchemeGames`, the second of which nothing in this repository bounds and
which has no counterpart in the source at all.

Like the statement it instantiates this one is a `≤` and may be strict; what would close it is the
two defining equations `SufBound.sufBound_eq_bound_add_sameMessage_of_unfoldings` takes.

*Profile corollary.* -/
theorem limitedStrongAdvantage_le_sufBound
    (c : Certificate limitedPrimitives sadv.toUnforgeableAdv) :
    sadv.advantage ProbCompRuntime.probComp ≤
      c.summands.sufBound limitedVp.params (freshRandomizerHalf sadv)
        (sameRandomizerHalf sadv) :=
  strongAdvantage_le_sufBound c

end StrongCorollary

end SLHDSA.Security
