/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import HashSig.SLHDSA.Security
public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.OpenPREFromTCRDSPR

/-!
# Quantitative `d = 1` SLH-DSA reduction accounting

This module fixes the exact additive shape of the source-faithful security theorem while keeping
the unfinished program transformations visible as separately reviewable obligations.  It follows
the EasyCrypt decomposition in `SPHINCS_PLUS.ec`:

* the top-level hop pays the secret-key-generation PRF, message-randomization PRF, M-FORS, and
  fixed-length XMSS losses;
* M-FORS pays ITSR, OpenPRE for `F`, TCR for FORS `H`, and TCR for FORS-root compression;
* fixed-length XMSS pays WOTS, WOTS-public-key-compression TCR, and XMSS-tree TCR; and
* WOTS pays `(w - 2) * UD + TCR + PRE` for `F`.

The low-level source theorem replaces the OpenPRE term by the concrete reduction adversaries from
`OpenPREFromTCRDSPR.lean`, yielding `DSPR + 3 * TCR`.  No theorem in this file assumes the desired
headline inequality as a single opaque premise: `D1CompositionCertificate` exposes the three
component reductions independently, and `d1_eufCma_le_lowLevelBound` additionally requires only
the named OpenPRE counting step.

References:

* Barbosa, Dupressoir, Hülsing, Meijers, and Strub, "A Tight Security Proof for SPHINCS+,
  Formally Verified", Theorem 1 and the accompanying EasyCrypt artifact.
* Barbosa et al., "Machine-Checked Security for XMSS as in RFC 8391 and SPHINCS+",
  Security Theorems 1 and 2.
-/

@[expose] public section

open ENNReal

namespace SLHDSA

/-- Numerical advantages delivered by the high-level component reductions.  A later packaging
layer instantiates each field with the advantage of a concrete reduction adversary against the
corresponding game. -/
structure D1HighLevelTerms where
  skPrf : ℝ≥0∞
  msgPrf : ℝ≥0∞
  hmsgItsr : ℝ≥0∞
  forsOpenPre : ℝ≥0∞
  forsTreeTcr : ℝ≥0∞
  forsRootsTcr : ℝ≥0∞
  wotsUd : ℝ≥0∞
  wotsTcr : ℝ≥0∞
  wotsPre : ℝ≥0∞
  wotsPkTcr : ℝ≥0∞
  xmssTreeTcr : ℝ≥0∞

namespace D1HighLevelTerms

/-- The two PRF hybrid losses at the top level. -/
noncomputable def prfBound (terms : D1HighLevelTerms) : ℝ≥0∞ := terms.skPrf + terms.msgPrf

/-- The exact M-FORS high-level bound. -/
noncomputable def mForsBound (terms : D1HighLevelTerms) : ℝ≥0∞ :=
  terms.hmsgItsr + terms.forsOpenPre + terms.forsTreeTcr + terms.forsRootsTcr

/-- The exact WOTS-TW bound, including the source factor `w - 2` on UD. -/
noncomputable def wotsBound (p : Params) (terms : D1HighLevelTerms) : ℝ≥0∞ :=
  (p.w - 2) * terms.wotsUd + terms.wotsTcr + terms.wotsPre

/-- The fixed-length XMSS contribution after expanding its WOTS component. -/
noncomputable def xmssBound (p : Params) (terms : D1HighLevelTerms) : ℝ≥0∞ :=
  terms.wotsBound p + terms.wotsPkTcr + terms.xmssTreeTcr

/-- The exact high-level `d = 1` EUF-CMA right-hand side. -/
noncomputable def bound (p : Params) (terms : D1HighLevelTerms) : ℝ≥0∞ :=
  terms.prfBound + terms.mForsBound + terms.xmssBound p

end D1HighLevelTerms

/-- Independently auditable outputs of the top-level split and three program-level component
reductions.  These are
the obligations still produced by translating the EasyCrypt game hops to the repository's exact
SLH-DSA program; separating them prevents an aggregate theorem from laundering that work into one
field with the headline conclusion itself. -/
structure D1CompositionCertificate (p : Params) (eufAdv : ℝ≥0∞)
    (terms : D1HighLevelTerms) where
  /-- Loss of the M-FORS component before expanding it into hash assumptions. -/
  mForsLoss : ℝ≥0∞
  /-- Loss of the non-PRF fixed-length XMSS component. -/
  xmssLoss : ℝ≥0∞
  /-- Loss of its WOTS subcomponent. -/
  wotsLoss : ℝ≥0∞
  /-- Top-level PRF/M-FORS/XMSS case split. -/
  topLevel : eufAdv ≤ terms.prfBound + mForsLoss + xmssLoss
  /-- M-FORS reduction to ITSR, OpenPRE, FORS-tree TCR, and root-compression TCR. -/
  mFors : mForsLoss ≤ terms.mForsBound
  /-- Fixed-length XMSS reduction to WOTS and its two binding collisions. -/
  xmss : xmssLoss ≤ wotsLoss + terms.wotsPkTcr + terms.xmssTreeTcr
  /-- WOTS reduction to `(w - 2) * UD + TCR + PRE`. -/
  wots : wotsLoss ≤ terms.wotsBound p

/-- Composition of the top-level split and three component obligations gives the exact high-level
theorem. -/
theorem D1CompositionCertificate.eufAdv_le_bound {p : Params} {eufAdv : ℝ≥0∞}
    {terms : D1HighLevelTerms} (cert : D1CompositionCertificate p eufAdv terms) :
    eufAdv ≤ terms.bound p := by
  calc
    eufAdv ≤ terms.prfBound + cert.mForsLoss + cert.xmssLoss := cert.topLevel
    _ ≤ terms.prfBound + terms.mForsBound + cert.xmssLoss :=
      add_le_add (add_le_add le_rfl cert.mFors) le_rfl
    _ ≤ terms.prfBound + terms.mForsBound +
        (cert.wotsLoss + terms.wotsPkTcr + terms.xmssTreeTcr) :=
      add_le_add le_rfl cert.xmss
    _ ≤ terms.bound p := by
      unfold D1HighLevelTerms.bound D1HighLevelTerms.xmssBound
      exact add_le_add le_rfl (add_le_add (add_le_add cert.wots le_rfl) le_rfl)

/-- Low-level terms introduced by the concrete OpenPRE-to-DSPR/TCR reductions. -/
structure D1OpenPreReductionTerms where
  forsLeafDspr : ℝ≥0∞
  forsLeafTcr : ℝ≥0∞

namespace D1OpenPreReductionTerms

/-- The exact low-level replacement for OpenPRE. -/
noncomputable def bound (terms : D1OpenPreReductionTerms) : ℝ≥0∞ :=
  terms.forsLeafDspr + 3 * terms.forsLeafTcr

end D1OpenPreReductionTerms

/-- Replace only the M-FORS OpenPRE term, leaving every other source term unchanged. -/
noncomputable def D1HighLevelTerms.withOpenPreReduction (terms : D1HighLevelTerms)
    (openPre : D1OpenPreReductionTerms) : D1HighLevelTerms :=
  { terms with forsOpenPre := openPre.bound }

/-- Monotonicity of the full accounting theorem in its OpenPRE term. -/
theorem D1HighLevelTerms.bound_le_withOpenPreReduction {p : Params}
    {terms : D1HighLevelTerms} {openPre : D1OpenPreReductionTerms}
    (hopen : terms.forsOpenPre ≤ openPre.bound) :
    terms.bound p ≤ (terms.withOpenPreReduction openPre).bound p := by
  unfold D1HighLevelTerms.bound D1HighLevelTerms.prfBound D1HighLevelTerms.mForsBound
    D1HighLevelTerms.xmssBound D1HighLevelTerms.wotsBound withOpenPreReduction
  dsimp only
  gcongr

/-- Source-faithful low-level conclusion: the concrete EUF-CMA advantage is bounded by the exact
PRF/ITSR/UD/TCR/PRE/DSPR expression once the top-level split, three program-level component
reductions, and the OpenPRE counting lemma have been supplied. -/
theorem d1_eufCma_le_lowLevelBound {p : Params} {eufAdv : ℝ≥0∞}
    {terms : D1HighLevelTerms} {openPre : D1OpenPreReductionTerms}
    (cert : D1CompositionCertificate p eufAdv terms)
    (hopen : terms.forsOpenPre ≤ openPre.bound) :
    eufAdv ≤ (terms.withOpenPreReduction openPre).bound p :=
  cert.eufAdv_le_bound.trans (terms.bound_le_withOpenPreReduction hopen)

/-! ## Concrete adversary packaging

The declarations below connect every numerical field above to an adversary against a specific
game instance with the exact target cap from `Params.d1TargetProfile`. -/

section ConcreteAdversaries

variable {p : Params} (prims : Primitives p)
  [SampleableType prims.SkSeed] [SampleableType prims.SkPrf]
  [SampleableType prims.PkSeed] [SampleableType prims.Y] [Inhabited prims.Y]

/-- One concrete reduction adversary for every term of the high-level source theorem. -/
structure D1ReductionAdversaries where
  skPrf : PRFScheme.PRFAdversary (prims.PkSeed × Adrs) prims.Y
  msgPrf : PRFScheme.PRFAdversary (prims.Y × List Byte) prims.Y
  hmsgItsr : KeyedHash.ITSRAdversary (hmsgItsrProblem prims)
  forsOpenPre :
    TweakableHash.SM_DT_OpenPRE_Adversary (prims.d1ForsLeafOpenPreProblem)
  forsTreeTcr : TweakableHash.SM_DT_TCR_Adversary (prims.d1ForsTreeTcrProblem)
  forsRootsTcr : TweakableHash.SM_DT_TCR_Adversary (prims.d1ForsRootsTcrProblem)
  wotsUd : TweakableHash.SM_DT_UD_Adversary (prims.d1WotsChainUdProblem)
  wotsTcr : TweakableHash.SM_DT_TCR_Adversary (prims.d1WotsChainTcrProblem)
  wotsPre : TweakableHash.SM_DT_PRE_Adversary (prims.d1WotsChainPreProblem)
  wotsPkTcr : TweakableHash.SM_DT_TCR_Adversary (prims.d1WotsPkTcrProblem)
  xmssTreeTcr : TweakableHash.SM_DT_TCR_Adversary (prims.d1XmssTreeTcrProblem)

namespace D1ReductionAdversaries

variable [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [DecidableEq prims.Y]

/-- Evaluate the exact high-level RHS on the concrete reduction adversaries. -/
noncomputable def advantages (reds : D1ReductionAdversaries prims) : D1HighLevelTerms where
  skPrf := PRFScheme.prfAdvantageENNReal (skPrfScheme prims) reds.skPrf
  msgPrf := PRFScheme.prfAdvantageENNReal (msgPrfScheme prims) reds.msgPrf
  hmsgItsr := KeyedHash.ITSRAdvantage reds.hmsgItsr
  forsOpenPre := TweakableHash.SM_DT_OpenPRE_Advantage reds.forsOpenPre
  forsTreeTcr := TweakableHash.SM_DT_TCR_Advantage reds.forsTreeTcr
  forsRootsTcr := TweakableHash.SM_DT_TCR_Advantage reds.forsRootsTcr
  wotsUd := TweakableHash.SM_DT_UD_Advantage reds.wotsUd
  wotsTcr := TweakableHash.SM_DT_TCR_Advantage reds.wotsTcr
  wotsPre := TweakableHash.SM_DT_PRE_Advantage reds.wotsPre
  wotsPkTcr := TweakableHash.SM_DT_TCR_Advantage reds.wotsPkTcr
  xmssTreeTcr := TweakableHash.SM_DT_TCR_Advantage reds.xmssTreeTcr

variable [Fintype prims.Y]

/-- Evaluate the low-level OpenPRE replacement on the executable DSPR and TCR reductions. -/
noncomputable def openPreReductionTerms (reds : D1ReductionAdversaries prims) :
    D1OpenPreReductionTerms where
  forsLeafDspr := TweakableHash.SM_DT_DSPR_Advantage
    (TweakableHash.SM_DT_OpenPRE_toDSPR reds.forsOpenPre)
  forsLeafTcr := TweakableHash.SM_DT_TCR_Advantage
    (TweakableHash.SM_DT_OpenPRE_toTCR reds.forsOpenPre)

/-- The three concrete probability-decomposition/coupling obligations needed to justify replacing
OpenPRE by the executable DSPR/TCR reductions.  This is strictly finer than assuming the target
inequality: it exposes singleton and larger-fiber masses, the exact DSPR truncated subtraction,
and the collision-weighted TCR lower bound. -/
abbrev OpenPreCountingStatement (reds : D1ReductionAdversaries prims) :=
  TweakableHash.SM_DT_OpenPRE_CountingLemma reds.forsOpenPre

omit [SampleableType prims.SkSeed] [SampleableType prims.SkPrf]
  [DecidableEq prims.PkSeed] in
@[simp] theorem openPreReductionTerms_bound (reds : D1ReductionAdversaries prims) :
    reds.openPreReductionTerms.bound =
      TweakableHash.SM_DT_OpenPRE_TCR_DSPR_Bound reds.forsOpenPre := by
  rfl

end D1ReductionAdversaries

variable [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [DecidableEq prims.Y]
  [Fintype prims.Y]

/-- Reviewable boundary for the complete `d = 1` EUF-CMA reduction.  Besides the concrete game
adversaries, it requires the parameter profile, reachable encoded-target separation, the three
program-level component reductions, and the isolated OpenPRE counting lemma. -/
structure D1EufCmaReductionCertificate (adv : EufCmaAdversary prims)
    (reds : D1ReductionAdversaries prims) where
  profile : p.D1SecurityProfile
  /-- Distinct XMSS/WOTS node messages have distinct full-width message-digit encodings. -/
  wotsEncodingInjective : prims.core.WotsMessageEncodingInjective
  targetSeparation : Primitives.D1TargetTweakSeparation prims
  composition : D1CompositionCertificate p (concreteEufCmaAdvantage prims adv) reds.advantages
  openPreCounting : reds.OpenPreCountingStatement

/-- The concrete, quantitative, low-level EUF-CMA statement obtained from a checked reduction
certificate.  Every term is the advantage of the concrete adversary stored in `reds`; the FORS
leaf DSPR/TCR adversaries are executable transformations of its OpenPRE adversary. -/
theorem concreteEufCmaAdvantage_le_lowLevelBound (adv : EufCmaAdversary prims)
    (reds : D1ReductionAdversaries prims) (cert : D1EufCmaReductionCertificate prims adv reds) :
    concreteEufCmaAdvantage prims adv ≤
      (reds.advantages.withOpenPreReduction reds.openPreReductionTerms).bound p := by
  apply d1_eufCma_le_lowLevelBound cert.composition
  simpa [D1ReductionAdversaries.advantages] using
    TweakableHash.SM_DT_OpenPRE_le_TCR_DSPR reds.forsOpenPre cert.openPreCounting

/-- Fully expanded version of the concrete low-level theorem.  This is the reviewer-facing
statement of the exact primitive properties and coefficients: two PRFs, H_msg ITSR, FORS-leaf
DSPR and TCR (with coefficient three), FORS tree/root TCR, WOTS UD/TCR/PRE (with coefficient
`w - 2` on UD), WOTS-public-key TCR, and XMSS-tree TCR. -/
theorem concreteEufCmaAdvantage_le_explicitLowLevelBound (adv : EufCmaAdversary prims)
    (reds : D1ReductionAdversaries prims) (cert : D1EufCmaReductionCertificate prims adv reds) :
    concreteEufCmaAdvantage prims adv ≤
      (PRFScheme.prfAdvantageENNReal (skPrfScheme prims) reds.skPrf +
        PRFScheme.prfAdvantageENNReal (msgPrfScheme prims) reds.msgPrf) +
      (KeyedHash.ITSRAdvantage reds.hmsgItsr +
        (TweakableHash.SM_DT_DSPR_Advantage
            (TweakableHash.SM_DT_OpenPRE_toDSPR reds.forsOpenPre) +
          3 * TweakableHash.SM_DT_TCR_Advantage
            (TweakableHash.SM_DT_OpenPRE_toTCR reds.forsOpenPre)) +
        TweakableHash.SM_DT_TCR_Advantage reds.forsTreeTcr +
        TweakableHash.SM_DT_TCR_Advantage reds.forsRootsTcr) +
      (((p.w - 2) * TweakableHash.SM_DT_UD_Advantage reds.wotsUd +
          TweakableHash.SM_DT_TCR_Advantage reds.wotsTcr +
          TweakableHash.SM_DT_PRE_Advantage reds.wotsPre) +
        TweakableHash.SM_DT_TCR_Advantage reds.wotsPkTcr +
        TweakableHash.SM_DT_TCR_Advantage reds.xmssTreeTcr) := by
  simpa [D1ReductionAdversaries.advantages, D1ReductionAdversaries.openPreReductionTerms,
    D1HighLevelTerms.withOpenPreReduction, D1HighLevelTerms.bound,
    D1HighLevelTerms.prfBound, D1HighLevelTerms.mForsBound,
    D1HighLevelTerms.xmssBound, D1HighLevelTerms.wotsBound,
    D1OpenPreReductionTerms.bound] using
    concreteEufCmaAdvantage_le_lowLevelBound prims adv reds cert

/-! ## Strong-unforgeability corollary -/

/-- Most-general concrete SUF-CMA statement currently justified by the source reduction.  The
ordinary forgery branch receives the complete low-level EUF bound above; the only additional term
is the exact probability of returning a new valid signature for an already queried message.

This theorem deliberately does not call that residual term negligible.  Closing it requires a
new SLH-DSA-specific binding reduction beyond the cited EUF-CMA proof. -/
theorem concreteStrongEufCmaAdvantage_le_lowLevelBound_add_sameMessage
    (adv : StrongEufCmaAdversary prims) (reds : D1ReductionAdversaries prims)
    (cert : D1EufCmaReductionCertificate prims adv.toUnforgeableAdv reds) :
    concreteStrongEufCmaAdvantage prims adv ≤
      (reds.advantages.withOpenPreReduction reds.openPreReductionTerms).bound p +
        concreteSameMessageStrongAdvantage prims adv := by
  exact (concreteStrongEufCmaAdvantage_le_euf_add_sameMessage prims adv).trans
    (add_le_add (concreteEufCmaAdvantage_le_lowLevelBound prims
      adv.toUnforgeableAdv reds cert) le_rfl)

/-- Fully expanded SUF-CMA corollary.  It has exactly the EUF hash/PRF terms above plus the
scheme-specific same-message/new-signature probability, making the additional property needed
for a genuine SUF theorem syntactically visible. -/
theorem concreteStrongEufCmaAdvantage_le_explicitLowLevelBound_add_sameMessage
    (adv : StrongEufCmaAdversary prims) (reds : D1ReductionAdversaries prims)
    (cert : D1EufCmaReductionCertificate prims adv.toUnforgeableAdv reds) :
    concreteStrongEufCmaAdvantage prims adv ≤
      (PRFScheme.prfAdvantageENNReal (skPrfScheme prims) reds.skPrf +
        PRFScheme.prfAdvantageENNReal (msgPrfScheme prims) reds.msgPrf) +
      (KeyedHash.ITSRAdvantage reds.hmsgItsr +
        (TweakableHash.SM_DT_DSPR_Advantage
            (TweakableHash.SM_DT_OpenPRE_toDSPR reds.forsOpenPre) +
          3 * TweakableHash.SM_DT_TCR_Advantage
            (TweakableHash.SM_DT_OpenPRE_toTCR reds.forsOpenPre)) +
        TweakableHash.SM_DT_TCR_Advantage reds.forsTreeTcr +
        TweakableHash.SM_DT_TCR_Advantage reds.forsRootsTcr) +
      (((p.w - 2) * TweakableHash.SM_DT_UD_Advantage reds.wotsUd +
          TweakableHash.SM_DT_TCR_Advantage reds.wotsTcr +
          TweakableHash.SM_DT_PRE_Advantage reds.wotsPre) +
        TweakableHash.SM_DT_TCR_Advantage reds.wotsPkTcr +
        TweakableHash.SM_DT_TCR_Advantage reds.xmssTreeTcr) +
      concreteSameMessageStrongAdvantage prims adv := by
  exact (concreteStrongEufCmaAdvantage_le_euf_add_sameMessage prims adv).trans
    (add_le_add (concreteEufCmaAdvantage_le_explicitLowLevelBound prims
      adv.toUnforgeableAdv reds cert) le_rfl)

/-- Quantitative SUF-CMA theorem under an explicit bound `ε` for the sole additional
same-message/new-signature property. -/
theorem concreteStrongEufCmaAdvantage_le_explicitLowLevelBound_add
    (adv : StrongEufCmaAdversary prims) (reds : D1ReductionAdversaries prims)
    (cert : D1EufCmaReductionCertificate prims adv.toUnforgeableAdv reds)
    (ε : ℝ≥0∞) (hsame : concreteSameMessageStrongAdvantage prims adv ≤ ε) :
    concreteStrongEufCmaAdvantage prims adv ≤
      (PRFScheme.prfAdvantageENNReal (skPrfScheme prims) reds.skPrf +
        PRFScheme.prfAdvantageENNReal (msgPrfScheme prims) reds.msgPrf) +
      (KeyedHash.ITSRAdvantage reds.hmsgItsr +
        (TweakableHash.SM_DT_DSPR_Advantage
            (TweakableHash.SM_DT_OpenPRE_toDSPR reds.forsOpenPre) +
          3 * TweakableHash.SM_DT_TCR_Advantage
            (TweakableHash.SM_DT_OpenPRE_toTCR reds.forsOpenPre)) +
        TweakableHash.SM_DT_TCR_Advantage reds.forsTreeTcr +
        TweakableHash.SM_DT_TCR_Advantage reds.forsRootsTcr) +
      (((p.w - 2) * TweakableHash.SM_DT_UD_Advantage reds.wotsUd +
          TweakableHash.SM_DT_TCR_Advantage reds.wotsTcr +
          TweakableHash.SM_DT_PRE_Advantage reds.wotsPre) +
        TweakableHash.SM_DT_TCR_Advantage reds.wotsPkTcr +
        TweakableHash.SM_DT_TCR_Advantage reds.xmssTreeTcr) + ε :=
  (concreteStrongEufCmaAdvantage_le_explicitLowLevelBound_add_sameMessage
    prims adv reds cert).trans (add_le_add le_rfl hsame)

end ConcreteAdversaries

end SLHDSA
