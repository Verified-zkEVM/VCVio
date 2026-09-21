/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.Security.OpenPreBound
public import HashSigTest.SLHDSA.Composition

/-!
# SLH-DSA open-preimage bound canaries

Elaboration pins for every declaration `HashSig.SLHDSA.Security.OpenPreBound` exports, restated at
the toy bundle of `HashSigTest.SLHDSA.Composition`, and the vacuity canary for its certificate: two
closed `OpenPreCertificate`s built from an address key and a public seed, each naming a bound that
is at least one.

## Nothing here is runnable, and that is a property of the subject

Every declaration the library module exports is about an `ℝ≥0∞`-valued advantage, and every such
advantage is `noncomputable`.  The module carries no `Params`-level data of its own — the
coefficient `w − 2` and the target caps are `Composition`'s and are run there — so this file has no
`main` and is built by the `HashSigTest` library glob alone.

## The vacuity canary

`OpenPreCertificate` asks for less than `Certificate`: no `Fintype` on the node type, no
`CountingInterface`, and neither an `mkgAdv` nor an `idealAdvantage` field.  What it does ask for
is inhabited from an address key `t` and a public seed alone, at every validated parameter set,
every primitive bundle carrying the instances the structure names, and every adversary:

* `freeOpenPreCertificate t pkSeed` puts the whole of `msgPrfIdealAdvantage adv` on the hypertree
  branch, where `freePreAdv t` has advantage one, and sets `forsBranch := 0`;
* `winningOpenPreCertificate t pkSeed` puts it on the FORS branch instead, where
  `winningOpenPre t` has advantage one, and sets `hypertreeBranch := 0`.

The second is the one `Certificate` does not admit from the same two inputs: its `counting` field
is asked at the open-preimage adversary, and `nonempty_counting_winningOpenPre_iff` says what
supplying it at `winningOpenPre` amounts to.  `OpenPreCertificate` has no such field, so nothing
obstructs it.  Both bounds are at least one, so `advantage_le_openPreBound` at either certificate
reads `adv.advantage ≤ (something ≥ 1)`, which `MeasureTheory.measure_le_one` already gives.

This is not a soundness bug: `advantage_le_openPreBound` is true and its proof is correct.  It says
the antecedent costs nothing, so the implication carries no information about SLH-DSA until the
summands it names are bounded in a model where hash evaluation is a counted query.

## What the checks cannot catch

* **Anything about a probability.**  See above.
* **What the two branch quantities mean.**  `forsBranch` and `hypertreeBranch` are `ℝ≥0∞` fields
  tied to no experiment; `split` bounds their sum below by `msgPrfIdealAdvantage adv` and nothing
  bounds either above.
* **Whether the eleven summands are the source's.**  That is a reading of `SPHINCS_PLUS.ec`,
  recorded in `HashSig.SLHDSA.Security.Composition`'s module docstring.

## What is here

Twenty-six `example`s in `Pins`, at least one for each of the nine declarations the library module
exports.  Then the vacuity canary — six declarations and four `example`s: the two certificates at
an arbitrary bundle, each with its `1 ≤ bound` theorem and its headline conjunction, and the same
four facts restated at the toy bundle.

## References

- NIST FIPS 205, §9, Algorithms 18--20
-/

public section

namespace SLHDSA.OpenPreBoundTest

open Security Security.CanonicalGames CompositionTest KeyedHash OracleComp OracleSpec ENNReal
  SignatureAlg TweakableHash

/-! ## The pins

Every one of the nine declarations `HashSig.SLHDSA.Security.OpenPreBound` exports, restated at the
toy bundle's types.  A library-side edit of the summand record, of a certificate field's type, of
the summand-to-game routing or of either bound's shape moves the library statement and fails the
pin here. -/

section Pins

variable (s : OpenPreSummands) (p : Params)
  (adv : unforgeableAdv (generalAlg (vp := toy) toyPrimitives))

/-! ### The summand record and its bound -/

example : ℝ≥0∞ := s.skgPrf
example : ℝ≥0∞ := s.forsFOpenPre
example : ℝ≥0∞ := s.xmssHTcr

noncomputable example : ℝ≥0∞ := s.bound p

example : s.bound p = s.skgPrf + s.mkgPrf + s.hmsgItsr
    + s.forsFOpenPre + s.forsHTcr + s.forsTlTcr
    + (p.w - 2 : ℕ) * s.wotsFUd + s.wotsFTcr + s.wotsFPre + s.wotsTlTcr + s.xmssHTcr :=
  s.bound_eq p

/-! ### The certificate, field by field -/

variable (c : OpenPreCertificate (vp := toy) toyPrimitives adv)

example : PRFScheme.PRFAdversary Adrs toyPrimitives.Y := c.skgAdv
example : toyPrimitives.PkSeed := c.pkSeed
example : ITSRAdversary (hmsgItsrProblem toyPrimitives) := c.itsrAdv
example : SM_DT_OpenPRE_SourceFinalValidity.Adversary (forsFOpenPreProblem toyPrimitives) :=
  c.openPreAdv
example : SM_DT_TCR_SourceFinalValidity.Adversary (forsHTcrCProblem toyPrimitives) := c.forsHAdv
example : SM_DT_TCR_SourceFinalValidity.Adversary (forsTlTcrCProblem toyPrimitives) := c.forsTlAdv
example : SM_DT_UD_SourceFinalValidity.Adversary (wotsFUdCProblem toyPrimitives) := c.wotsFUdAdv
example : SM_DT_TCR_SourceFinalValidity.Adversary (wotsFTcrCProblem toyPrimitives) := c.wotsFTcrAdv
example : SM_DT_PRE_SourceFinalValidity.Adversary (wotsFPreCProblem toyPrimitives) := c.wotsFPreAdv
example : SM_DT_TCR_SourceFinalValidity.Adversary (wotsTlTcrCProblem toyPrimitives) := c.wotsTlAdv
example : SM_DT_TCR_SourceFinalValidity.Adversary (xmssHTcrCProblem toyPrimitives) := c.xmssHAdv

example : ℝ≥0∞ := c.forsBranch
example : ℝ≥0∞ := c.hypertreeBranch

example : msgPrfIdealAdvantage (vp := toy) toyPrimitives adv ≤ c.forsBranch + c.hypertreeBranch :=
  c.split

example : c.forsBranch ≤ ITSRAdvantage c.itsrAdv
    + SM_DT_OpenPRE_SourceFinalValidity.Advantage c.openPreAdv
    + SM_DT_TCR_SourceFinalValidity.Advantage c.forsHAdv
    + SM_DT_TCR_SourceFinalValidity.Advantage c.forsTlAdv := c.forsBranch_le

example : c.hypertreeBranch ≤
    (toy.params.w - 2 : ℕ) * SM_DT_UD_SourceFinalValidity.AbsoluteAdvantage c.wotsFUdAdv
      + SM_DT_TCR_SourceFinalValidity.Advantage c.wotsFTcrAdv
      + SM_DT_PRE_SourceFinalValidity.Advantage c.wotsFPreAdv
      + SM_DT_TCR_SourceFinalValidity.Advantage c.wotsTlAdv
      + SM_DT_TCR_SourceFinalValidity.Advantage c.xmssHAdv := c.hypertreeBranch_le

/-! ### The eleven summands, and the headline -/

noncomputable example : OpenPreSummands := c.summands

example : c.summands.bound toy.params =
    prfAbsAdvantage (skPrfScheme toyPrimitives c.pkSeed) c.skgAdv
      + prfAbsAdvantage (msgPrfScheme toyPrimitives) (msgPrfReduction (vp := toy) toyPrimitives adv)
      + ITSRAdvantage c.itsrAdv
      + SM_DT_OpenPRE_SourceFinalValidity.Advantage c.openPreAdv
      + SM_DT_TCR_SourceFinalValidity.Advantage c.forsHAdv
      + SM_DT_TCR_SourceFinalValidity.Advantage c.forsTlAdv
      + (toy.params.w - 2 : ℕ) *
          SM_DT_UD_SourceFinalValidity.AbsoluteAdvantage c.wotsFUdAdv
      + SM_DT_TCR_SourceFinalValidity.Advantage c.wotsFTcrAdv
      + SM_DT_PRE_SourceFinalValidity.Advantage c.wotsFPreAdv
      + SM_DT_TCR_SourceFinalValidity.Advantage c.wotsTlAdv
      + SM_DT_TCR_SourceFinalValidity.Advantage c.xmssHAdv := c.bound_eq

example : adv.advantage ProbCompRuntime.probComp ≤ c.summands.bound toy.params :=
  advantage_le_openPreBound c

/-! ### Recovering the twelve-summand shape -/

noncomputable example
    (counting : SM_DT_OpenPRE_SourceFinalValidity.CountingInterface c.openPreAdv) :
    Certificate (vp := toy) toyPrimitives adv :=
  c.toCertificate counting

example (counting : SM_DT_OpenPRE_SourceFinalValidity.CountingInterface c.openPreAdv) :
    c.summands.bound toy.params ≤ (c.toCertificate counting).summands.bound toy.params :=
  openPreBound_le_bound c counting

end Pins

/-! ## The vacuity canary -/

section Vacuity

variable {vp : ValidatedParams} {prims : Primitives vp.params}
  [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.PkSeed]
  [SampleableType prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey]
  [DecidableEq prims.Y] [Inhabited prims.Y]

/-- **An `OpenPreCertificate` from nothing**, with the load on the hypertree branch.  The two
arguments are an address key and a public seed, which are data the scheme itself has and not
assumptions; `forsBranch := 0` puts the whole of `msgPrfIdealAdvantage adv` on
`hypertreeBranch_le`, and `freePreAdv_advantage` discharges it. -/
noncomputable def freeOpenPreCertificate {adv : unforgeableAdv (generalAlg prims)}
    (t : prims.AdrsKey) (pkSeed : prims.PkSeed) : OpenPreCertificate prims adv where
  skgAdv := (pure true : OracleComp (PRFScheme.PRFOracleSpec Adrs prims.Y) Bool)
  pkSeed := pkSeed
  itsrAdv := ⟨(pure (default, ⟨pkSeed, default, []⟩) :
    OracleComp (unifSpec + ITSRTargetSpec (HmsgITSRInput prims.PkSeed prims.Y) prims.Y)
      (prims.Y × HmsgITSRInput prims.PkSeed prims.Y))⟩
  openPreAdv := idleOpenPre (forsFOpenPreProblem prims)
  forsHAdv := idleTcr _
  forsTlAdv := idleTcr _
  wotsFUdAdv := idleUd _
  wotsFTcrAdv := idleTcr _
  wotsFPreAdv := freePreAdv prims t
  wotsTlAdv := idleTcr _
  xmssHAdv := idleTcr _
  forsBranch := 0
  hypertreeBranch := msgPrfIdealAdvantage prims adv
  split := by simp
  forsBranch_le := by simp
  hypertreeBranch_le := by
    calc msgPrfIdealAdvantage prims adv ≤ 1 := msgPrfIdealAdvantage_le_one prims adv
      _ = SM_DT_PRE_SourceFinalValidity.Advantage (freePreAdv prims t) :=
          (freePreAdv_advantage prims t).symm
      _ ≤ _ := le_add_right (le_add_right le_add_self)

/-- **The bound that certificate names is at least one**: its preimage summand is one. -/
theorem one_le_freeOpenPreCertificate_bound {adv : unforgeableAdv (generalAlg prims)}
    (t : prims.AdrsKey) (pkSeed : prims.PkSeed) :
    1 ≤ (freeOpenPreCertificate (adv := adv) t pkSeed).summands.bound vp.params := by
  rw [OpenPreCertificate.bound_eq]
  calc (1 : ℝ≥0∞) = SM_DT_PRE_SourceFinalValidity.Advantage (freePreAdv prims t) :=
        (freePreAdv_advantage prims t).symm
    _ ≤ _ := le_add_right (le_add_right le_add_self)

/-- **The headline at that certificate.**  The bound holds, and what it bounds the advantage by
is at least one. -/
theorem freeOpenPreCertificate_headline {adv : unforgeableAdv (generalAlg prims)}
    (t : prims.AdrsKey) (pkSeed : prims.PkSeed) :
    adv.advantage ProbCompRuntime.probComp ≤
        (freeOpenPreCertificate (adv := adv) t pkSeed).summands.bound vp.params ∧
      1 ≤ (freeOpenPreCertificate (adv := adv) t pkSeed).summands.bound vp.params :=
  ⟨advantage_le_openPreBound _, one_le_freeOpenPreCertificate_bound t pkSeed⟩

/-- **An `OpenPreCertificate` from nothing**, with the load on the FORS branch.  The same two
arguments; `hypertreeBranch := 0` puts the whole of `msgPrfIdealAdvantage adv` on
`forsBranch_le`, and `winningOpenPre_advantage` discharges it.  No counting interface is asked
for, at this or any other open-preimage adversary. -/
noncomputable def winningOpenPreCertificate {adv : unforgeableAdv (generalAlg prims)}
    (t : prims.AdrsKey) (pkSeed : prims.PkSeed) : OpenPreCertificate prims adv where
  skgAdv := (pure true : OracleComp (PRFScheme.PRFOracleSpec Adrs prims.Y) Bool)
  pkSeed := pkSeed
  itsrAdv := ⟨(pure (default, ⟨pkSeed, default, []⟩) :
    OracleComp (unifSpec + ITSRTargetSpec (HmsgITSRInput prims.PkSeed prims.Y) prims.Y)
      (prims.Y × HmsgITSRInput prims.PkSeed prims.Y))⟩
  openPreAdv := winningOpenPre (forsFOpenPreProblem prims) t
  forsHAdv := idleTcr _
  forsTlAdv := idleTcr _
  wotsFUdAdv := idleUd _
  wotsFTcrAdv := idleTcr _
  wotsFPreAdv := freePreAdv prims t
  wotsTlAdv := idleTcr _
  xmssHAdv := idleTcr _
  forsBranch := msgPrfIdealAdvantage prims adv
  hypertreeBranch := 0
  split := by simp
  forsBranch_le := by
    calc msgPrfIdealAdvantage prims adv ≤ 1 := msgPrfIdealAdvantage_le_one prims adv
      _ = SM_DT_OpenPRE_SourceFinalValidity.Advantage
            (winningOpenPre (forsFOpenPreProblem prims) t) :=
          (winningOpenPre_advantage _ t (by
            rw [forsFOpenPreProblem_numTargets]
            exact targetCount_pos vp.params vp.valid TargetRole.forsF)).symm
      _ ≤ _ := le_add_right (le_add_right le_add_self)
  hypertreeBranch_le := by simp

/-- **The bound that certificate names is at least one too**: its preimage summand is one, as in
`freeOpenPreCertificate`, and so is its open-preimage summand. -/
theorem one_le_winningOpenPreCertificate_bound {adv : unforgeableAdv (generalAlg prims)}
    (t : prims.AdrsKey) (pkSeed : prims.PkSeed) :
    1 ≤ (winningOpenPreCertificate (adv := adv) t pkSeed).summands.bound vp.params := by
  rw [OpenPreCertificate.bound_eq]
  calc (1 : ℝ≥0∞) = SM_DT_PRE_SourceFinalValidity.Advantage (freePreAdv prims t) :=
        (freePreAdv_advantage prims t).symm
    _ ≤ _ := le_add_right (le_add_right le_add_self)

/-- **The headline at the FORS-loaded certificate.** -/
theorem winningOpenPreCertificate_headline {adv : unforgeableAdv (generalAlg prims)}
    (t : prims.AdrsKey) (pkSeed : prims.PkSeed) :
    adv.advantage ProbCompRuntime.probComp ≤
        (winningOpenPreCertificate (adv := adv) t pkSeed).summands.bound vp.params ∧
      1 ≤ (winningOpenPreCertificate (adv := adv) t pkSeed).summands.bound vp.params :=
  ⟨advantage_le_openPreBound _, one_le_winningOpenPreCertificate_bound t pkSeed⟩

end Vacuity

/-! ### The same four facts at the toy bundle

The section above is at an arbitrary `ValidatedParams` and an arbitrary bundle; these restate it at
the profile the pins use, so a change that breaks only the concrete case is caught too. -/

noncomputable example (t : Adrs) (pkSeed : toyPrimitives.PkSeed)
    (adv : unforgeableAdv (generalAlg (vp := toy) toyPrimitives)) :
    OpenPreCertificate (vp := toy) toyPrimitives adv :=
  freeOpenPreCertificate (vp := toy) (prims := toyPrimitives) (adv := adv) t pkSeed

example (t : Adrs) (pkSeed : toyPrimitives.PkSeed)
    (adv : unforgeableAdv (generalAlg (vp := toy) toyPrimitives)) :
    adv.advantage ProbCompRuntime.probComp ≤
        (freeOpenPreCertificate (vp := toy) (prims := toyPrimitives) (adv := adv) t
          pkSeed).summands.bound toy.params ∧
      1 ≤ (freeOpenPreCertificate (vp := toy) (prims := toyPrimitives) (adv := adv) t
          pkSeed).summands.bound toy.params :=
  freeOpenPreCertificate_headline (vp := toy) (prims := toyPrimitives) (adv := adv) t pkSeed

noncomputable example (t : Adrs) (pkSeed : toyPrimitives.PkSeed)
    (adv : unforgeableAdv (generalAlg (vp := toy) toyPrimitives)) :
    OpenPreCertificate (vp := toy) toyPrimitives adv :=
  winningOpenPreCertificate (vp := toy) (prims := toyPrimitives) (adv := adv) t pkSeed

example (t : Adrs) (pkSeed : toyPrimitives.PkSeed)
    (adv : unforgeableAdv (generalAlg (vp := toy) toyPrimitives)) :
    adv.advantage ProbCompRuntime.probComp ≤
        (winningOpenPreCertificate (vp := toy) (prims := toyPrimitives) (adv := adv) t
          pkSeed).summands.bound toy.params ∧
      1 ≤ (winningOpenPreCertificate (vp := toy) (prims := toyPrimitives) (adv := adv) t
          pkSeed).summands.bound toy.params :=
  winningOpenPreCertificate_headline (vp := toy) (prims := toyPrimitives) (adv := adv) t pkSeed

end SLHDSA.OpenPreBoundTest
