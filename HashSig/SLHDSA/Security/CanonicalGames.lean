/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import HashSig.SLHDSA.Security
public import HashSig.SLHDSA.Security.Architecture
public import VCVio.CryptoFoundations.HardnessAssumptions.KeyedHash.ITSR
public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTDSPR
public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTPREFinalValidity
public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTTCRFinalValidity
public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTUDC

/-!
# Canonical SLH-DSA Component Games

This module instantiates VCVio's generic source-final-validity hash games with the primitive
families, encoded-address tweaks, collection members, and formula-derived target caps used by the
arbitrary-depth SLH-DSA security architecture.  It also packages the types of the component
reductions and their advantages.  It does not construct those reductions or state a master
inequality.

The component experiments and probability functions in `SLHDSA.Security.Architecture` continue to
own the proposed master-statement shell.  In particular, `TwoPhaseAdversary`, `tcrProbability`,
`tcrCProbability`, `dsprProbability`, `forsFSPprobability`, `preCProbability`, the two WOTS UD
probabilities, and `itsrComponentProbability` are not identified with the canonical games here.
Replacing those terms requires explicit program and experiment equivalences.

The target-game assignments are:

* standalone SM-DT-DSPR and SM-DT-TCR for FORS `F`;
* collection SM-DT-TCR for FORS `H`, FORS `T_l`, WOTS `F`, WOTS `T_l`, and XMSS `H`;
* collection SM-DT-UD and SM-DT-PRE for WOTS `F`; and
* generic keyed-hash ITSR for `H_msg`.

All tweakable-hash games use `Primitives.AdrsKey`, not structural `Adrs`.  Their collection oracle
is `Primitives.thashCollection`, and the attacked member's input type fixes its exact arity.
-/

@[expose] public section

open CollisionResistance ENNReal OracleComp OracleSpec

namespace SLHDSA.Security.CanonicalGames

variable {p : Params} (prims : Primitives p)

/-! ## Primitive evaluation bridges -/

/-- The canonical `F` family evaluates the one-input member of `Thash` at an encoded address. -/
@[simp]
theorem fHash_eval [SampleableType prims.PkSeed] (pkSeed : prims.PkSeed)
    (tweak : prims.AdrsKey) (input : prims.Y) :
    (prims.fHash).eval pkSeed tweak input = prims.Thash pkSeed tweak [input] := rfl

/-- The canonical `H` family evaluates the ordered two-input member of `Thash`. -/
@[simp]
theorem hHash_eval [SampleableType prims.PkSeed] (pkSeed : prims.PkSeed)
    (tweak : prims.AdrsKey) (input : prims.Y × prims.Y) :
    (prims.hHash).eval pkSeed tweak input =
      prims.Thash pkSeed tweak [input.1, input.2] := rfl

/-- A fixed-arity collection member evaluates `Thash` on exactly the vector's entries. -/
@[simp]
theorem thashMember_eval [SampleableType prims.PkSeed] (arity : ℕ)
    (pkSeed : prims.PkSeed) (tweak : prims.AdrsKey) (input : Vector prims.Y arity) :
    (prims.thashMember arity).eval pkSeed tweak input =
      prims.Thash pkSeed tweak input.toList := rfl

/-! ## FORS games -/

/-- FORS-`F` decisional second-preimage resistance with no collection oracle. -/
def forsFDsprProblem [SampleableType prims.PkSeed] :
    TweakableHash.SM_DT_DSPR_SourceFinalValidity.Problem Empty prims.PkSeed prims.AdrsKey
      prims.Y prims.Y :=
  .standalone prims.fHash (targetCount p .forsF)

/-- FORS-`F` target-collision resistance with no collection oracle. -/
def forsFTcrProblem [SampleableType prims.PkSeed] :
    TweakableHash.SM_DT_TCR_SourceFinalValidity.Problem Empty prims.PkSeed prims.AdrsKey
      prims.Y prims.Y :=
  .standalone prims.fHash (targetCount p .forsF)

/-- FORS-`H` target-collision resistance in the shared `Thash` collection. -/
def forsHTcrCProblem [SampleableType prims.PkSeed] :
    TweakableHash.SM_DT_TCR_SourceFinalValidity.Problem ℕ prims.PkSeed prims.AdrsKey
      (prims.Y × prims.Y) prims.Y where
  th := prims.hHash
  thColl := prims.thashCollection
  numTargets := targetCount p .forsH

/-- FORS-`T_l` target-collision resistance at arity `p.k` in the shared collection. -/
def forsTlTcrCProblem [SampleableType prims.PkSeed] :
    TweakableHash.SM_DT_TCR_SourceFinalValidity.Problem ℕ prims.PkSeed prims.AdrsKey
      (Vector prims.Y p.k) prims.Y where
  th := prims.thashMember p.k
  thColl := prims.thashCollection
  numTargets := targetCount p .forsTl

/-! ## WOTS+ and XMSS games -/

/-- WOTS-`F` undetectability in the shared collection, with uniform inputs and ideal outputs. -/
def wotsFUdCProblem [SampleableType prims.PkSeed] [SampleableType prims.Y] :
    TweakableHash.SM_DT_UD_C_SourceFinalValidity.Problem ℕ prims.PkSeed prims.AdrsKey
      prims.Y prims.Y where
  th := prims.fHash
  inputGen := $ᵗ prims.Y
  outputGen := $ᵗ prims.Y
  thColl := prims.thashCollection
  numTargets := targetCount p .wotsFUd

/-- WOTS-`F` target-collision resistance in the shared collection. -/
def wotsFTcrCProblem [SampleableType prims.PkSeed] :
    TweakableHash.SM_DT_TCR_SourceFinalValidity.Problem ℕ prims.PkSeed prims.AdrsKey
      prims.Y prims.Y where
  th := prims.fHash
  thColl := prims.thashCollection
  numTargets := targetCount p .wotsFTcr

/-- WOTS-`F` preimage resistance in the shared collection, over the full input space. -/
def wotsFPreCProblem [SampleableType prims.PkSeed] :
    TweakableHash.SM_DT_PRE_SourceFinalValidity.Problem ℕ prims.PkSeed prims.AdrsKey
      prims.Y prims.Y prims.Y where
  th := prims.fHash
  emb := id
  emb_injective := Function.injective_id
  thColl := prims.thashCollection
  numTargets := targetCount p .wotsFPre

/-- WOTS-`T_l` target-collision resistance at arity `p.len` in the shared collection. -/
def wotsTlTcrCProblem [SampleableType prims.PkSeed] :
    TweakableHash.SM_DT_TCR_SourceFinalValidity.Problem ℕ prims.PkSeed prims.AdrsKey
      (Vector prims.Y p.len) prims.Y where
  th := prims.thashMember p.len
  thColl := prims.thashCollection
  numTargets := targetCount p .wotsTl

/-- XMSS-`H` target-collision resistance in the shared collection. -/
def xmssHTcrCProblem [SampleableType prims.PkSeed] :
    TweakableHash.SM_DT_TCR_SourceFinalValidity.Problem ℕ prims.PkSeed prims.AdrsKey
      (prims.Y × prims.Y) prims.Y where
  th := prims.hHash
  thColl := prims.thashCollection
  numTargets := targetCount p .xmssH

/-! ## Target-cap and attacked-member bridges -/

@[simp]
theorem forsFDsprProblem_numTargets [SampleableType prims.PkSeed] :
    (forsFDsprProblem prims).numTargets = targetCount p .forsF := rfl

@[simp]
theorem forsFTcrProblem_numTargets [SampleableType prims.PkSeed] :
    (forsFTcrProblem prims).numTargets = targetCount p .forsF := rfl

@[simp]
theorem forsHTcrCProblem_numTargets [SampleableType prims.PkSeed] :
    (forsHTcrCProblem prims).numTargets = targetCount p .forsH := rfl

@[simp]
theorem forsTlTcrCProblem_numTargets [SampleableType prims.PkSeed] :
    (forsTlTcrCProblem prims).numTargets = targetCount p .forsTl := rfl

@[simp]
theorem wotsFUdCProblem_numTargets [SampleableType prims.PkSeed]
    [SampleableType prims.Y] :
    (wotsFUdCProblem prims).numTargets = targetCount p .wotsFUd := rfl

@[simp]
theorem wotsFTcrCProblem_numTargets [SampleableType prims.PkSeed] :
    (wotsFTcrCProblem prims).numTargets = targetCount p .wotsFTcr := rfl

@[simp]
theorem wotsFPreCProblem_numTargets [SampleableType prims.PkSeed] :
    (wotsFPreCProblem prims).numTargets = targetCount p .wotsFPre := rfl

@[simp]
theorem wotsTlTcrCProblem_numTargets [SampleableType prims.PkSeed] :
    (wotsTlTcrCProblem prims).numTargets = targetCount p .wotsTl := rfl

@[simp]
theorem xmssHTcrCProblem_numTargets [SampleableType prims.PkSeed] :
    (xmssHTcrCProblem prims).numTargets = targetCount p .xmssH := rfl

/-- Every `F`-based game attacks the same encoded-address evaluation as the construction. -/
@[simp]
theorem wotsFPreCProblem_eval_adrsToKey [SampleableType prims.PkSeed]
    (pkSeed : prims.PkSeed) (address : Adrs) (input : prims.Y) :
    (wotsFPreCProblem prims).th.eval pkSeed (prims.adrsToKey address) input =
      prims.F pkSeed address input := rfl

/-- The FORS `H` game uses the construction's ordered left/right node evaluation. -/
@[simp]
theorem forsHTcrCProblem_eval_adrsToKey [SampleableType prims.PkSeed]
    (pkSeed : prims.PkSeed) (address : Adrs) (input : prims.Y × prims.Y) :
    (forsHTcrCProblem prims).th.eval pkSeed (prims.adrsToKey address) input =
      prims.H pkSeed address input.1 input.2 := rfl

/-- The FORS `T_l` game fixes the collection member to the `p.k`-node public-key compression. -/
@[simp]
theorem forsTlTcrCProblem_eval_adrsToKey [SampleableType prims.PkSeed]
    (pkSeed : prims.PkSeed) (address : Adrs) (input : Vector prims.Y p.k) :
    (forsTlTcrCProblem prims).th.eval pkSeed (prims.adrsToKey address) input =
      prims.Tl pkSeed address input.toList := rfl

/-- The WOTS `T_l` game fixes the collection member to the `p.len`-node compression. -/
@[simp]
theorem wotsTlTcrCProblem_eval_adrsToKey [SampleableType prims.PkSeed]
    (pkSeed : prims.PkSeed) (address : Adrs) (input : Vector prims.Y p.len) :
    (wotsTlTcrCProblem prims).th.eval pkSeed (prims.adrsToKey address) input =
      prims.Tl pkSeed address input.toList := rfl

/-! ## `H_msg` ITSR -/

/-- Public `H_msg` parameters and the complete external request.  The independently sampled ITSR
key is the message randomizer. -/
structure HmsgITSRInput (PkSeed Y : Type) where
  publicSeed : PkSeed
  publicRoot : Y
  request : MessageInput
deriving DecidableEq

/-- `H_msg` as a keyed family whose key generator samples the per-message randomizer. -/
def hmsgKeyedHash [SampleableType prims.Y] (encode : MessageInput → List Byte) :
    KeyedHashFamily prims.Y (HmsgITSRInput prims.PkSeed prims.Y) (Bytes p.m) where
  keygen := $ᵗ prims.Y
  hash := fun randomizer input =>
    prims.Hmsg randomizer input.publicSeed input.publicRoot (encode input.request)

/-- Generic ITSR instantiated with the exact FIPS digest-to-FORS-target map. -/
noncomputable def hmsgItsrProblem [SampleableType prims.Y] (encode : MessageInput → List Byte) :
    KeyedHash.ITSRProblem prims.Y (HmsgITSRInput prims.PkSeed prims.Y) (Bytes p.m)
      (ITSRTarget p) where
  khf := hmsgKeyedHash prims encode
  indices := fun digest => (digestTargetSet p digest).toList

@[simp]
theorem hmsgItsrProblem_hash [SampleableType prims.Y]
    (encode : MessageInput → List Byte) (randomizer : prims.Y)
    (input : HmsgITSRInput prims.PkSeed prims.Y) :
    (hmsgItsrProblem prims encode).khf.hash randomizer input =
      prims.Hmsg randomizer input.publicSeed input.publicRoot (encode input.request) := rfl

@[simp]
theorem hmsgItsrProblem_indices [SampleableType prims.Y]
    (encode : MessageInput → List Byte) (digest : Bytes p.m) :
    (hmsgItsrProblem prims encode).indices digest = (digestTargetSet p digest).toList := rfl

/-! ## Typed reduction boundary -/

/-- Component reductions from an arbitrary classical scheme adversary into the canonical games.
The fields are only types for future programs; constructing a value supplies the actual
reductions. -/
structure ReductionAdversaries (scheme : SchemeInterface prims)
    [SampleableType prims.PkSeed] [SampleableType prims.Y]
    (encode : MessageInput → List Byte) where
  hmsgItsr : ClassicalAdversary prims scheme →
    KeyedHash.ITSRAdversary (hmsgItsrProblem prims encode)
  forsFDspr : ClassicalAdversary prims scheme →
    TweakableHash.SM_DT_DSPR_SourceFinalValidity.Adversary (forsFDsprProblem prims)
  forsFTcr : ClassicalAdversary prims scheme →
    TweakableHash.SM_DT_TCR_SourceFinalValidity.Adversary (forsFTcrProblem prims)
  forsHTcrC : ClassicalAdversary prims scheme →
    TweakableHash.SM_DT_TCR_SourceFinalValidity.Adversary (forsHTcrCProblem prims)
  forsTlTcrC : ClassicalAdversary prims scheme →
    TweakableHash.SM_DT_TCR_SourceFinalValidity.Adversary (forsTlTcrCProblem prims)
  wotsFUdC : ClassicalAdversary prims scheme →
    TweakableHash.SM_DT_UD_C_SourceFinalValidity.Adversary (wotsFUdCProblem prims)
  wotsFTcrC : ClassicalAdversary prims scheme →
    TweakableHash.SM_DT_TCR_SourceFinalValidity.Adversary (wotsFTcrCProblem prims)
  wotsFPreC : ClassicalAdversary prims scheme →
    TweakableHash.SM_DT_PRE_SourceFinalValidity.Adversary (wotsFPreCProblem prims)
  wotsTlTcrC : ClassicalAdversary prims scheme →
    TweakableHash.SM_DT_TCR_SourceFinalValidity.Adversary (wotsTlTcrCProblem prims)
  xmssHTcrC : ClassicalAdversary prims scheme →
    TweakableHash.SM_DT_TCR_SourceFinalValidity.Adversary (xmssHTcrCProblem prims)

/-! ## Canonical advantage terms -/

variable {prims : Primitives p} {scheme : SchemeInterface prims}
  [SampleableType prims.PkSeed] [SampleableType prims.Y]
  {encode : MessageInput → List Byte}

/-- The canonical `H_msg` ITSR term. -/
noncomputable def ReductionAdversaries.hmsgItsrAdvantage
    [DecidableEq prims.PkSeed] [DecidableEq prims.Y]
    (reductions : ReductionAdversaries prims scheme encode)
    (adversary : ClassicalAdversary prims scheme) : ℝ≥0∞ :=
  KeyedHash.ITSRAdvantage (reductions.hmsgItsr adversary)

/-- The canonical FORS-`F` DSPR term, including its `SPprob` subtraction. -/
noncomputable def ReductionAdversaries.forsFDsprAdvantage
    [Fintype prims.Y] [DecidableEq prims.AdrsKey] [DecidableEq prims.Y]
    (reductions : ReductionAdversaries prims scheme encode)
    (adversary : ClassicalAdversary prims scheme) : ℝ≥0∞ :=
  TweakableHash.SM_DT_DSPR_SourceFinalValidity.Advantage (reductions.forsFDspr adversary)

/-- The canonical standalone FORS-`F` TCR term. -/
noncomputable def ReductionAdversaries.forsFTcrAdvantage
    [DecidableEq prims.AdrsKey] [DecidableEq prims.Y]
    (reductions : ReductionAdversaries prims scheme encode)
    (adversary : ClassicalAdversary prims scheme) : ℝ≥0∞ :=
  TweakableHash.SM_DT_TCR_SourceFinalValidity.Advantage (reductions.forsFTcr adversary)

/-- The canonical collection FORS-`H` TCR term. -/
noncomputable def ReductionAdversaries.forsHTcrCAdvantage
    [DecidableEq prims.AdrsKey] [DecidableEq prims.Y]
    (reductions : ReductionAdversaries prims scheme encode)
    (adversary : ClassicalAdversary prims scheme) : ℝ≥0∞ :=
  TweakableHash.SM_DT_TCR_SourceFinalValidity.Advantage (reductions.forsHTcrC adversary)

/-- The canonical collection FORS-`T_l` TCR term. -/
noncomputable def ReductionAdversaries.forsTlTcrCAdvantage
    [DecidableEq prims.AdrsKey] [DecidableEq prims.Y]
    (reductions : ReductionAdversaries prims scheme encode)
    (adversary : ClassicalAdversary prims scheme) : ℝ≥0∞ :=
  TweakableHash.SM_DT_TCR_SourceFinalValidity.Advantage (reductions.forsTlTcrC adversary)

/-- The orientation-independent canonical WOTS-`F` UD-C term. -/
noncomputable def ReductionAdversaries.wotsFUdCAdvantage
    [DecidableEq prims.AdrsKey]
    (reductions : ReductionAdversaries prims scheme encode)
    (adversary : ClassicalAdversary prims scheme) : ℝ≥0∞ :=
  TweakableHash.SM_DT_UD_C_SourceFinalValidity.AbsoluteAdvantage (reductions.wotsFUdC adversary)

/-- The canonical collection WOTS-`F` TCR term. -/
noncomputable def ReductionAdversaries.wotsFTcrCAdvantage
    [DecidableEq prims.AdrsKey] [DecidableEq prims.Y]
    (reductions : ReductionAdversaries prims scheme encode)
    (adversary : ClassicalAdversary prims scheme) : ℝ≥0∞ :=
  TweakableHash.SM_DT_TCR_SourceFinalValidity.Advantage (reductions.wotsFTcrC adversary)

/-- The canonical collection WOTS-`F` PRE term. -/
noncomputable def ReductionAdversaries.wotsFPreCAdvantage
    [DecidableEq prims.AdrsKey] [DecidableEq prims.Y]
    (reductions : ReductionAdversaries prims scheme encode)
    (adversary : ClassicalAdversary prims scheme) : ℝ≥0∞ :=
  TweakableHash.SM_DT_PRE_SourceFinalValidity.Advantage (reductions.wotsFPreC adversary)

/-- The canonical collection WOTS-`T_l` TCR term. -/
noncomputable def ReductionAdversaries.wotsTlTcrCAdvantage
    [DecidableEq prims.AdrsKey] [DecidableEq prims.Y]
    (reductions : ReductionAdversaries prims scheme encode)
    (adversary : ClassicalAdversary prims scheme) : ℝ≥0∞ :=
  TweakableHash.SM_DT_TCR_SourceFinalValidity.Advantage (reductions.wotsTlTcrC adversary)

/-- The canonical collection XMSS-`H` TCR term. -/
noncomputable def ReductionAdversaries.xmssHTcrCAdvantage
    [DecidableEq prims.AdrsKey] [DecidableEq prims.Y]
    (reductions : ReductionAdversaries prims scheme encode)
    (adversary : ClassicalAdversary prims scheme) : ℝ≥0∞ :=
  TweakableHash.SM_DT_TCR_SourceFinalValidity.Advantage (reductions.xmssHTcrC adversary)

end SLHDSA.Security.CanonicalGames
