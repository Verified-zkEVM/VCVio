/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.Security.PrfHops

/-!
# The EUF-CMA bound at the open-preimage advantage

This module states the SLH-DSA bound with the FORS leaf hash's contribution carried by the
**open-preimage** advantage itself, rather than by the `DSPR + 3 · TCR` pair that
`HashSig.SLHDSA.Security.Composition` converts it into.

## Why the FORS-`F` block is one summand here and two there

`Composition.openPre_le_summands_forsF` is `OpenPRE ≤ DSPR + 3 · TCR`, conditional on VCVio's
`CountingInterface`.  It is an upper bound, applied at the last step of `advantage_le_bound` to
reach the shape of the EasyCrypt development's `EUFCMA_SPHINCS_PLUS`.  Not applying it therefore
gives a bound that is never larger and is generally smaller, and it has three further
consequences.

* **The `counting` field disappears.**  `OpenPreCertificate` has no counterpart of
  `Certificate.counting`, so the fiber-counting coupling — the interface whose three fields are,
  in VCVio's own words, "the substantive probabilistic coupling still to be constructed" — is not
  required for the bound to hold.
* **The coefficient three disappears.**  It is the coefficient the conversion introduces; the
  FORS-`F` term here has coefficient one.
* **`sm-dspr` leaves the assumption set.**  The decisional second-preimage resistance of the
  FORS leaf hash is not named by this bound, so nothing here depends on it.

## What that means for the assumptions

For the construction FIPS 205 approves — `Th(P, T, M) = H(P ‖ T ‖ M)`, Construction 7 of the
SPHINCS+ framework paper — `sm-tcr` has a proof in the quantum random-oracle model (Theorem 11,
`Succ ≤ 8(2q+1)² / 2ⁿ`), while `sm-dspr` has only Conjecture 16, which is unproven.  A bound
that names `sm-dspr` therefore terminates at a conjecture for exactly the parameter sets the
standard approves.  This one does not name it.

What it names instead is `SM-DT-OpenPRE` of the FORS leaf hash, which is discharged at the same
layer and in the same model as `sm-tcr` is.  The `DSPR + 3 · TCR` shape remains available:
`Certificate.ofOpenPre` converts a certificate of this module into one of `Composition`'s given a
`CountingInterface`, and `bound_le_certificate_bound` records that the conversion only loses.

The interchange is sound for Construction 7 specifically because that construction is analysed by
modelling `H` as a random oracle outright, so no property of an underlying compression function is
being traded away.  The DSPR route exists to obtain preimage-level security from
*second*-preimage assumptions on a concrete compression function, which is what the robust
Construction 6 needs and Construction 7 does not.

## What this module does not establish

* It does not discharge `SM-DT-OpenPRE` of the FORS leaf hash.  That is the random-oracle
  instantiation step, and it is not in this repository.
* It does not bound `msgPrfIdealAdvantage`, the two branch quantities, or any other summand.  The
  remaining ten adversary fields are still supplied by the caller, exactly as in `Composition`.
* The `MKG_PRF` summand and the advantage that survives its hop are the only ones fixed at a
  construction; they come from `HashSig.SLHDSA.Security.PrfHops`.

## Labels

Nine declarations.

*Open-preimage bound* — the summand record, the certificate, and the bound:

* `OpenPreSummands`, `OpenPreSummands.bound`, `OpenPreSummands.bound_eq`;
* `OpenPreCertificate`, `OpenPreCertificate.summands`, `OpenPreCertificate.bound_eq`,
  `advantage_le_openPreBound`;
* `OpenPreCertificate.toCertificate`, `openPreBound_le_bound`.

## References

- NIST FIPS 205, §9, Algorithms 18--20
- Bernstein, Hülsing, Kölbl, Niederhagen, Rijneveld, and Schwabe, "The SPHINCS+ Signature
  Framework", CCS 2019 (Construction 7; Theorem 11; Conjecture 16)
- Bernstein and Hülsing, "Decisional Second-Preimage Resistance: When Does SPR Imply PRE?",
  Asiacrypt 2019
-/

public section

namespace SLHDSA.Security

open OracleComp OracleSpec ENNReal SignatureAlg TweakableHash Security.CanonicalGames

variable {vp : ValidatedParams} (prims : Primitives vp.params)
  [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.PkSeed]
  [SampleableType prims.Y] [DecidableEq prims.Y] [DecidableEq prims.PkSeed]
  [DecidableEq prims.AdrsKey] [Inhabited prims.Y]

/-! ## The eleven summands -/

/-- **The eleven named summands of the open-preimage bound.**  A bare record of eleven extended
non-negative reals, carrying no claim about where they come from.

It differs from `HashSig.SLHDSA.Security.Composition`'s `Summands` in one place: the FORS leaf
hash contributes a single `forsFOpenPre` term where that record has the pair `forsFDspr`,
`forsFTcr`.

*Open-preimage bound.* -/
structure OpenPreSummands where
  /-- `SKG_PRF` — the secret-value `PRF` hop. -/
  skgPrf : ℝ≥0∞
  /-- `MKG_PRF` — the message-randomizer `PRF_msg` hop. -/
  mkgPrf : ℝ≥0∞
  /-- `MCO_ITSR` — interleaved-target subset resilience of `H_msg`. -/
  hmsgItsr : ℝ≥0∞
  /-- Open-preimage resistance of the FORS leaf hash `F`. -/
  forsFOpenPre : ℝ≥0∞
  /-- Target-collision resistance of the FORS internal-node hash `H`. -/
  forsHTcr : ℝ≥0∞
  /-- Target-collision resistance of the FORS root compression `T_k`. -/
  forsTlTcr : ℝ≥0∞
  /-- Undetectability of the WOTS+ chain hash `F`, at coefficient `w − 2`. -/
  wotsFUd : ℝ≥0∞
  /-- Target-collision resistance of the WOTS+ chain hash `F`. -/
  wotsFTcr : ℝ≥0∞
  /-- Preimage resistance of the WOTS+ chain hash `F`. -/
  wotsFPre : ℝ≥0∞
  /-- Target-collision resistance of the WOTS+ compression `T_len`. -/
  wotsTlTcr : ℝ≥0∞
  /-- Target-collision resistance of the XMSS internal-node hash `H`. -/
  xmssHTcr : ℝ≥0∞

/-- **The open-preimage bound expression.**  `w − 2` on the WOTS+-`F` undetectability term is the
only coefficient; every other summand has coefficient one.

*Open-preimage bound.* -/
noncomputable def OpenPreSummands.bound (s : OpenPreSummands) (p : Params) : ℝ≥0∞ :=
  s.skgPrf + s.mkgPrf + s.hmsgItsr
    + s.forsFOpenPre + s.forsHTcr + s.forsTlTcr
    + (p.w - 2 : ℕ) * s.wotsFUd + s.wotsFTcr + s.wotsFPre + s.wotsTlTcr + s.xmssHTcr

/-- Unfolding equation for `OpenPreSummands.bound`.  The body is not exposed, so this is what a
consumer that needs the eleven-summand shape rewrites with.

*Open-preimage bound.* -/
theorem OpenPreSummands.bound_eq (s : OpenPreSummands) (p : Params) :
    s.bound p = s.skgPrf + s.mkgPrf + s.hmsgItsr
      + s.forsFOpenPre + s.forsHTcr + s.forsTlTcr
      + (p.w - 2 : ℕ) * s.wotsFUd + s.wotsFTcr + s.wotsFPre + s.wotsTlTcr + s.xmssHTcr := by
  rfl

/-! ## The certificate -/

/-- **A certificate for the open-preimage bound.**

Sixteen fields against `Certificate`'s twenty.  Four are gone: `mkgAdv` and `idealAdvantage` are
fixed at the constructions of `HashSig.SLHDSA.Security.PrfHops`, `prfHops` is discharged from
`advantage_le_msgPrf_add_ideal`, and `counting` is not needed because the `DSPR + 3 · TCR`
conversion is not applied.

The ten remaining adversary fields and the two branch bounds are hypotheses, exactly as in
`Composition`.  `split` is asked at the advantage that survives the `MKG_PRF` hop, not at
`adv.advantage`: the halves of `HashSig.SLHDSA.Security.SchemeGames` are defined at the real
experiment, and no dispatch split of the key-idealized experiment exists in this repository.

*Open-preimage bound.* -/
structure OpenPreCertificate (adv : unforgeableAdv (generalAlg prims)) where
  /-- The `SKG_PRF` distinguisher against the secret-value `PRF` at `pkSeed`. -/
  skgAdv : PRFScheme.PRFAdversary Adrs prims.Y
  /-- The public seed the secret-value `PRF` hop is taken at. -/
  pkSeed : prims.PkSeed
  /-- The `MCO_ITSR` adversary against `H_msg`. -/
  itsrAdv : KeyedHash.ITSRAdversary (hmsgItsrProblem prims)
  /-- The open-preimage adversary against the FORS leaf hash `F`.  Its advantage is the bound's
  FORS-`F` summand outright; no reduction is applied to it. -/
  openPreAdv : SM_DT_OpenPRE_SourceFinalValidity.Adversary (forsFOpenPreProblem prims)
  /-- The target-collision adversary against the FORS internal-node hash `H`. -/
  forsHAdv : SM_DT_TCR_SourceFinalValidity.Adversary (forsHTcrCProblem prims)
  /-- The target-collision adversary against the FORS root compression `T_k`. -/
  forsTlAdv : SM_DT_TCR_SourceFinalValidity.Adversary (forsTlTcrCProblem prims)
  /-- The undetectability adversary against the WOTS+ chain hash `F`. -/
  wotsFUdAdv : SM_DT_UD_SourceFinalValidity.Adversary (wotsFUdCProblem prims)
  /-- The target-collision adversary against the WOTS+ chain hash `F`. -/
  wotsFTcrAdv : SM_DT_TCR_SourceFinalValidity.Adversary (wotsFTcrCProblem prims)
  /-- The preimage adversary against the WOTS+ chain hash `F`. -/
  wotsFPreAdv : SM_DT_PRE_SourceFinalValidity.Adversary (wotsFPreCProblem prims)
  /-- The target-collision adversary against the WOTS+ compression `T_len`. -/
  wotsTlAdv : SM_DT_TCR_SourceFinalValidity.Adversary (wotsTlTcrCProblem prims)
  /-- The target-collision adversary against the XMSS internal-node hash `H`. -/
  xmssHAdv : SM_DT_TCR_SourceFinalValidity.Adversary (xmssHTcrCProblem prims)
  /-- The FORS branch's share of the advantage surviving the `MKG_PRF` hop. -/
  forsBranch : ℝ≥0∞
  /-- The hypertree branch's share of the advantage surviving the `MKG_PRF` hop. -/
  hypertreeBranch : ℝ≥0∞
  /-- The dispatch split, at the advantage that survives the `MKG_PRF` hop. -/
  split : msgPrfIdealAdvantage prims adv ≤ forsBranch + hypertreeBranch
  /-- **The FORS branch bound**, carrying the open-preimage advantage directly. -/
  forsBranch_le : forsBranch ≤ KeyedHash.ITSRAdvantage itsrAdv
    + SM_DT_OpenPRE_SourceFinalValidity.Advantage openPreAdv
    + SM_DT_TCR_SourceFinalValidity.Advantage forsHAdv
    + SM_DT_TCR_SourceFinalValidity.Advantage forsTlAdv
  /-- **The hypertree branch bound**, carrying the `(w − 2)` coefficient. -/
  hypertreeBranch_le : hypertreeBranch ≤
    (vp.params.w - 2 : ℕ) * SM_DT_UD_SourceFinalValidity.AbsoluteAdvantage wotsFUdAdv
      + SM_DT_TCR_SourceFinalValidity.Advantage wotsFTcrAdv
      + SM_DT_PRE_SourceFinalValidity.Advantage wotsFPreAdv
      + SM_DT_TCR_SourceFinalValidity.Advantage wotsTlAdv
      + SM_DT_TCR_SourceFinalValidity.Advantage xmssHAdv

variable {prims}

/-- The eleven summands a certificate names.  The `MKG_PRF` one is at the reduction the forger
determines; the FORS-`F` one is the certificate's own open-preimage advantage, unreduced.

*Open-preimage bound.* -/
noncomputable def OpenPreCertificate.summands {adv : unforgeableAdv (generalAlg prims)}
    (c : OpenPreCertificate prims adv) : OpenPreSummands where
  skgPrf := prfAbsAdvantage (skPrfScheme prims c.pkSeed) c.skgAdv
  mkgPrf := prfAbsAdvantage (msgPrfScheme prims) (msgPrfReduction prims adv)
  hmsgItsr := KeyedHash.ITSRAdvantage c.itsrAdv
  forsFOpenPre := SM_DT_OpenPRE_SourceFinalValidity.Advantage c.openPreAdv
  forsHTcr := SM_DT_TCR_SourceFinalValidity.Advantage c.forsHAdv
  forsTlTcr := SM_DT_TCR_SourceFinalValidity.Advantage c.forsTlAdv
  wotsFUd := SM_DT_UD_SourceFinalValidity.AbsoluteAdvantage c.wotsFUdAdv
  wotsFTcr := SM_DT_TCR_SourceFinalValidity.Advantage c.wotsFTcrAdv
  wotsFPre := SM_DT_PRE_SourceFinalValidity.Advantage c.wotsFPreAdv
  wotsTlTcr := SM_DT_TCR_SourceFinalValidity.Advantage c.wotsTlAdv
  xmssHTcr := SM_DT_TCR_SourceFinalValidity.Advantage c.xmssHAdv

/-- **The bound a certificate names, written out.**  Neither `OpenPreSummands.bound` nor
`OpenPreCertificate.summands` has an exposed body, so this equation is how a consumer reads the
summand-to-game routing.

*Open-preimage bound.* -/
theorem OpenPreCertificate.bound_eq {adv : unforgeableAdv (generalAlg prims)}
    (c : OpenPreCertificate prims adv) :
    c.summands.bound vp.params =
      prfAbsAdvantage (skPrfScheme prims c.pkSeed) c.skgAdv
        + prfAbsAdvantage (msgPrfScheme prims) (msgPrfReduction prims adv)
        + KeyedHash.ITSRAdvantage c.itsrAdv
        + SM_DT_OpenPRE_SourceFinalValidity.Advantage c.openPreAdv
        + SM_DT_TCR_SourceFinalValidity.Advantage c.forsHAdv
        + SM_DT_TCR_SourceFinalValidity.Advantage c.forsTlAdv
        + (vp.params.w - 2 : ℕ) *
            SM_DT_UD_SourceFinalValidity.AbsoluteAdvantage c.wotsFUdAdv
        + SM_DT_TCR_SourceFinalValidity.Advantage c.wotsFTcrAdv
        + SM_DT_PRE_SourceFinalValidity.Advantage c.wotsFPreAdv
        + SM_DT_TCR_SourceFinalValidity.Advantage c.wotsTlAdv
        + SM_DT_TCR_SourceFinalValidity.Advantage c.xmssHAdv := by
  rw [OpenPreSummands.bound_eq]
  rfl

/-- **The EUF-CMA bound at the open-preimage advantage.**  The advantage of any adversary against
the external SLH-DSA algebra is at most the eleven-summand expression its certificate names.

Neither `sm-dspr` of the FORS leaf hash nor VCVio's fiber-counting interface occurs anywhere in
the statement or its proof.

*Open-preimage bound.* -/
theorem advantage_le_openPreBound {adv : unforgeableAdv (generalAlg prims)}
    (c : OpenPreCertificate prims adv) :
    adv.advantage ProbCompRuntime.probComp ≤ c.summands.bound vp.params := by
  rw [c.bound_eq]
  calc adv.advantage ProbCompRuntime.probComp
      ≤ prfAbsAdvantage (msgPrfScheme prims) (msgPrfReduction prims adv)
          + msgPrfIdealAdvantage prims adv := advantage_le_msgPrf_add_ideal prims adv
    _ ≤ prfAbsAdvantage (skPrfScheme prims c.pkSeed) c.skgAdv
          + prfAbsAdvantage (msgPrfScheme prims) (msgPrfReduction prims adv)
          + (c.forsBranch + c.hypertreeBranch) := by
        gcongr
        · exact le_add_self
        · exact c.split
    _ ≤ prfAbsAdvantage (skPrfScheme prims c.pkSeed) c.skgAdv
          + prfAbsAdvantage (msgPrfScheme prims) (msgPrfReduction prims adv)
          + ((KeyedHash.ITSRAdvantage c.itsrAdv
              + SM_DT_OpenPRE_SourceFinalValidity.Advantage c.openPreAdv
              + SM_DT_TCR_SourceFinalValidity.Advantage c.forsHAdv
              + SM_DT_TCR_SourceFinalValidity.Advantage c.forsTlAdv)
            + ((vp.params.w - 2 : ℕ) *
                SM_DT_UD_SourceFinalValidity.AbsoluteAdvantage c.wotsFUdAdv
              + SM_DT_TCR_SourceFinalValidity.Advantage c.wotsFTcrAdv
              + SM_DT_PRE_SourceFinalValidity.Advantage c.wotsFPreAdv
              + SM_DT_TCR_SourceFinalValidity.Advantage c.wotsTlAdv
              + SM_DT_TCR_SourceFinalValidity.Advantage c.xmssHAdv)) := by
        gcongr
        · exact c.forsBranch_le
        · exact c.hypertreeBranch_le
    _ = _ := by ring

/-! ## Recovering the twelve-summand shape -/

section Recover

variable [Fintype prims.Y]

/-- **The certificate of `HashSig.SLHDSA.Security.Composition` this one yields**, given the
fiber-counting interface it otherwise does without.  Nothing else has to be supplied: the ten
adversary fields, the two branch quantities and the three inequalities transfer unchanged, and
`mkgAdv` and `idealAdvantage` are the constructions of `HashSig.SLHDSA.Security.PrfHops` and
`prfHops` is `advantage_le_msgPrf_add_ideal`.

*Open-preimage bound.* -/
noncomputable def OpenPreCertificate.toCertificate {adv : unforgeableAdv (generalAlg prims)}
    (c : OpenPreCertificate prims adv)
    (counting : SM_DT_OpenPRE_SourceFinalValidity.CountingInterface c.openPreAdv) :
    Certificate prims adv where
  skgAdv := c.skgAdv
  mkgAdv := msgPrfReduction prims adv
  pkSeed := c.pkSeed
  itsrAdv := c.itsrAdv
  openPreAdv := c.openPreAdv
  counting := counting
  forsHAdv := c.forsHAdv
  forsTlAdv := c.forsTlAdv
  wotsFUdAdv := c.wotsFUdAdv
  wotsFTcrAdv := c.wotsFTcrAdv
  wotsFPreAdv := c.wotsFPreAdv
  wotsTlAdv := c.wotsTlAdv
  xmssHAdv := c.xmssHAdv
  idealAdvantage := msgPrfIdealAdvantage prims adv
  forsBranch := c.forsBranch
  hypertreeBranch := c.hypertreeBranch
  prfHops := le_trans (advantage_le_msgPrf_add_ideal prims adv) (by gcongr; exact le_add_self)
  split := c.split
  forsBranch_le := c.forsBranch_le
  hypertreeBranch_le := c.hypertreeBranch_le

/-- **The open-preimage bound is never the weaker of the two.**  Wherever the twelve-summand
bound of `HashSig.SLHDSA.Security.Composition` is available — that is, wherever a
`CountingInterface` has been supplied — this one is at most as large.

This is the statement that the FORS-`F` block's `DSPR + 3 · TCR` form is an upper bound applied
on top of the open-preimage advantage, not an alternative route to it.  The two expressions
agree summand for summand except at that block, where `openPre_le_dspr_add_three_tcr`
orders them.

*Open-preimage bound.* -/
theorem openPreBound_le_bound {adv : unforgeableAdv (generalAlg prims)}
    (c : OpenPreCertificate prims adv)
    (counting : SM_DT_OpenPRE_SourceFinalValidity.CountingInterface c.openPreAdv) :
    c.summands.bound vp.params ≤ (c.toCertificate counting).summands.bound vp.params := by
  have h : SM_DT_OpenPRE_SourceFinalValidity.Advantage c.openPreAdv ≤
      SM_DT_DSPR_SourceFinalValidity.Advantage
          (SM_DT_OpenPRE_SourceFinalValidity.toDSPR c.openPreAdv)
        + 3 * SM_DT_TCR_SourceFinalValidity.Advantage
          (SM_DT_OpenPRE_SourceFinalValidity.toTCR c.openPreAdv) :=
    openPre_le_dspr_add_three_tcr (c.toCertificate counting)
  rw [c.bound_eq, Certificate.bound_eq]
  simp only [OpenPreCertificate.toCertificate]
  calc prfAbsAdvantage (skPrfScheme prims c.pkSeed) c.skgAdv
          + prfAbsAdvantage (msgPrfScheme prims) (msgPrfReduction prims adv)
          + KeyedHash.ITSRAdvantage c.itsrAdv
          + SM_DT_OpenPRE_SourceFinalValidity.Advantage c.openPreAdv
          + SM_DT_TCR_SourceFinalValidity.Advantage c.forsHAdv
          + SM_DT_TCR_SourceFinalValidity.Advantage c.forsTlAdv
          + (vp.params.w - 2 : ℕ) *
              SM_DT_UD_SourceFinalValidity.AbsoluteAdvantage c.wotsFUdAdv
          + SM_DT_TCR_SourceFinalValidity.Advantage c.wotsFTcrAdv
          + SM_DT_PRE_SourceFinalValidity.Advantage c.wotsFPreAdv
          + SM_DT_TCR_SourceFinalValidity.Advantage c.wotsTlAdv
          + SM_DT_TCR_SourceFinalValidity.Advantage c.xmssHAdv
      ≤ prfAbsAdvantage (skPrfScheme prims c.pkSeed) c.skgAdv
          + prfAbsAdvantage (msgPrfScheme prims) (msgPrfReduction prims adv)
          + KeyedHash.ITSRAdvantage c.itsrAdv
          + (SM_DT_DSPR_SourceFinalValidity.Advantage
                (SM_DT_OpenPRE_SourceFinalValidity.toDSPR c.openPreAdv)
              + 3 * SM_DT_TCR_SourceFinalValidity.Advantage
                (SM_DT_OpenPRE_SourceFinalValidity.toTCR c.openPreAdv))
          + SM_DT_TCR_SourceFinalValidity.Advantage c.forsHAdv
          + SM_DT_TCR_SourceFinalValidity.Advantage c.forsTlAdv
          + (vp.params.w - 2 : ℕ) *
              SM_DT_UD_SourceFinalValidity.AbsoluteAdvantage c.wotsFUdAdv
          + SM_DT_TCR_SourceFinalValidity.Advantage c.wotsFTcrAdv
          + SM_DT_PRE_SourceFinalValidity.Advantage c.wotsFPreAdv
          + SM_DT_TCR_SourceFinalValidity.Advantage c.wotsTlAdv
          + SM_DT_TCR_SourceFinalValidity.Advantage c.xmssHAdv := by gcongr
    _ = _ := by ring

end Recover

end SLHDSA.Security
