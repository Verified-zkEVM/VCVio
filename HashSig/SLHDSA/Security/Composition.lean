/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.Security.SchemeGames

/-!
# The composition certificate and the conditional EUF-CMA bound

This is the module that finally writes the SLH-DSA security result as an inequality.  It is
*conditional*, and everything worth checking about it is which hypotheses it carries.

## The statement

`SLHDSA.Security.advantage_le_bound` says: for any adversary `adv` against the external SLH-DSA
algebra `generalAlg`, and any `Certificate` for that adversary,

`adv.advantage ProbCompRuntime.probComp ≤ (c.summands prims).bound vp.params`

where `Summands.bound` is the twelve-summand expression of `EUFCMA_SPHINCS_PLUS`, at the source's
coefficients, and `Certificate.summands` routes each summand to the advantage of a named game of
`HashSig.SLHDSA.Security.CanonicalGames`.  `Certificate.bound_eq` writes the right-hand side out.

## What a `Certificate` is, and what it is not

A `Certificate` bundles twelve adversary fields, the OpenPRE counting interface, three real numbers
and four inequalities.  It is the honest content of this module and a reader should attack it
first.  Three things are true of it and worth stating separately.

* **No field is the conclusion.**  No field mentions `Summands.bound` or `Certificate.summands`; a
  certificate cannot say "the bound holds".  The four inequalities decompose as
  `advantage ≤ prf + prf + ideal`, `ideal ≤ forsBranch + hypertreeBranch`, and one bound per
  branch, and the step from there to the conclusion is arithmetic this module does — including one
  step that is not arithmetic at all (below).
* **How much it needs is measured, not asserted.**  `Certificate.ofBranchBounds` builds one from
  the twelve adversaries, the counting interface and *two* inequalities — one per branch of
  `SchemeGames`' dispatch split, stated at `forsHalf adv` and `hypertreeHalf adv` — discharging
  `split` from `advantage_le_forsHalf_add_hypertreeHalf` and `prfHops` from `le_add_self`.  So
  `split` is provably instantiable and is not a disguised assumption, and what remains unproven is
  the two branch bounds, which is the bulk of the EasyCrypt development.  What is *not* claimed is
  that the structure is uninhabited: no proof of that is given or attempted, and the honest
  statement is the weaker one, that no route to a certificate is known here which does not pass
  through an inequality nothing in this repository proves.
* **`ofBranchBounds` takes no PRF hop.**  It sets `idealAdvantage := adv.advantage`, so in the
  certificate it returns the two PRF summands are pure slack: they appear in the bound and do no
  work.  A certificate that takes a real PRF hop has to choose a smaller `idealAdvantage`, and
  nothing in this repository can.  `advantage_le_bound_of_halves` is that reading as one statement.

## Where the arithmetic is not arithmetic

`Certificate.forsBranch_le` carries the **OpenPRE** advantage of `forsFOpenPreProblem`, not the
pair `DSPR + 3·TCR` that the source's expression has.  `advantage_le_bound` replaces one by the
other by applying `TweakableHash.SM_DT_OpenPRE_SourceFinalValidity.advantage_le_tcrDsprBound` to
the certificate's `counting` field.  That is the only step of the proof that is not `gcongr` and
`ring`, and it is why the `3` in `Summands.bound` is not a transcription: the library derives it
from `openPRE_multipleMass_add_reciprocal_le_three_collision`, and a `Summands.bound` that said
`2 *` fails to elaborate against the library's own `TCRDSPRBound`.

The other coefficient, `(p.w - 2 : ℕ)`, is **not** derived anywhere in Lean.  VCVio has no
hybrid-argument machinery for SM-DT-UD; the coefficient is carried from
`MEUFGCMA_WOTSTWESNPRF` and `EUFNAGCMA_FLSLXMSSMTTWESNPRF`, and a paired edit of it in
`Summands.bound` and in `Certificate.hypertreeBranch_le` is refused by nothing inside this
repository.  `two_le_w` is the one thing that is pinned about it: at a validated parameter set
`2 ≤ p.w`, so the `ℕ`-truncation never fires and the coefficient is never silently zero.

## What is not established, and cannot be read into the inequality

The bound is conditional on every field of the certificate, and **no field is populated anywhere
in this repository**.  There is no `Certificate` in `HashSig`, in `HashSigTest` or anywhere else;
`ofBranchBounds` is a constructor, not an instance.  In particular:

* no reduction adversary is constructed, so the twelve adversary fields are hypotheses about
  objects that do not exist here;
* nothing says any honest value was recorded as a valid challenge target before a forgery, that
  any execution produced any target transcript, or that a game's final-validity bit survived;
* the two PRF hops are assumed, not taken: there is no key-idealized variant of
  `GeneralScheme.signInternalM` anywhere in the repository;
* the OpenPRE counting interface is assumed.  Its `uniformInputs` field alone is dischargeable,
  from `CanonicalGames.forsFOpenPreProblem_hasUniformInputs`; its two equations and its inequality
  are, in VCVio's own words, "the substantive probabilistic coupling still to be constructed";
* the `(w − 2)` undetectability hybrid is not performed;
* nothing here is a statement about SUF-CMA.  `SchemeGames.strongAdvantage_le_halves` names the
  same-message residual, and the same-randomizer term inside it has no bound at all.

And one caveat that is easy to lose.  **The Lean branch assignment is not the source's.**
`HashSig.SLHDSA.Security.SchemeWitnesses` records that this lane reorders the source's four-way
FORS split into three branches and that "a transcription of its `mu_split` coefficients would be
unsound here".  `Summands.bound` is the source's *expression* at the source's coefficients; nothing
about the tightness of a Lean reduction follows from it, and the two branch bounds are stated at
this lane's own dispatch split rather than at the source's.

## Labels

Twenty-one declarations.

*Composition arithmetic* — a statement about the bound expression or about a certificate:

* `prfAbsAdvantage`, `prfAbsAdvantage_toReal`;
* `two_le_w`;
* `Summands`, `Summands.bound`, `Summands.bound_eq`, `bound_eq_zero_of_summands_zero`,
  `bound_wotsFUd_coefficient`, `bound_wotsFUd_coefficient_add_two`,
  `bound_forsFTcr_coefficient`;
* `Certificate`, `Certificate.summands`, `Certificate.bound_eq`, `advantage_le_bound`;
* `Certificate.ofBranchBounds`, `Certificate.ofBranchBounds_summands`,
  `advantage_le_bound_of_halves`.

*Game transport* — a statement that moves a bound between two of slice 6's named games:

* `dspr_bound_transfer`, `tcr_bound_transfer`, `summands_forsF_le`, `openPre_le_summands_forsF`.

None is `private` and none carries `@[expose]`; `Summands.bound_eq` and `Certificate.bound_eq` are
what a consumer that needs the expression's shape rewrites with, exactly as
`SchemeGames.internalLog_eq` is for `internalLog`.

## Correspondence with the EasyCrypt development

`Summands.bound` is the right-hand side of `EUFCMA_SPHINCS_PLUS`, in the source's order: the two
`PRF` hops of `SKG_PRF` and `MKG_PRF`; the `MCO_ITSR` term; the FORS block
`DSPR − SPprob`, `3 · TCR`, `TRHC_TCR`, `TRCOC_TCR` of `EUFCMA_MFORSTWESNPRF`; and the hypertree
block `(w − 2) · FC_UD`, `FC_TCR`, `FC_PRE`, `PKCOC_TCR`, `TRHC_TCR` of
`EUFNAGCMA_FLSLXMSSMTTWESNPRF`, whose first three are `MEUFGCMA_WOTSTWESNPRF`'s.  The three `hoare`
address-discipline side conditions that the hypertree lemma carries in its own statement are not
summands; they are the obligations the `SourceFinalValidity` monitor replaces with its sticky
`valid` bit, and this module assumes that bit rather than establishing it.

## References

- NIST FIPS 205, §9, Algorithms 18--20
- Barbosa, Dupressoir, Hülsing, Meijers, and Strub, "A Tight Security Proof for SPHINCS+,
  Formally Verified" (`SPHINCS_PLUS.ec`, `FORS_ES.ec`, `FL_SL_XMSS_MT_ES.ec`, `WOTS_TW_ES.ec`)
-/

public section

namespace SLHDSA.Security

open OracleComp OracleSpec ENNReal SignatureAlg TweakableHash Security.CanonicalGames

/-! ## The `ℝ≥0∞`-valued PRF distinguishing advantage

`PRFScheme.prfAdvantage` is `ℝ`-valued and every other summand of the bound is `ℝ≥0∞`-valued.  The
precedent for carrying both is `SM_DT_UD_SourceFinalValidity`, which has a signed
`DirectedAdvantage : ℝ` and an `AbsoluteAdvantage : ℝ≥0∞` with a `toReal` bridge between them.

TODO: promote `prfAbsAdvantage` and its bridge to `VCVio/CryptoFoundations/PRF.lean`, beside
`PRFScheme.prfAdvantage`.  They are kept here because this slice should not add to a shared
module's public surface, and the bridge makes the relationship checkable from either side. -/

/-- The PRF distinguishing advantage as an `ℝ≥0∞`, the absolute gap between the real and ideal
experiments' success probabilities.

*Composition arithmetic.* -/
noncomputable def prfAbsAdvantage {K D R : Type} [DecidableEq D] [SampleableType R]
    (prf : PRFScheme K D R) (adv : PRFScheme.PRFAdversary D R) : ℝ≥0∞ :=
  ENNReal.absDiff (Pr[= true | prf.prfRealExp adv]) (Pr[= true | PRFScheme.prfIdealExp adv])

/-- The `ℝ≥0∞` advantage is the library's `ℝ`-valued one.  Without this a reader cannot check that
the two PRF summands of the bound are the source's two absolute differences of `main(false)` and
`main(true)` probabilities rather than something else with the same name.

*Composition arithmetic.* -/
theorem prfAbsAdvantage_toReal {K D R : Type} [DecidableEq D] [SampleableType R]
    (prf : PRFScheme K D R) (adv : PRFScheme.PRFAdversary D R) :
    (prfAbsAdvantage prf adv).toReal = PRFScheme.prfAdvantage prf adv := by
  rw [prfAbsAdvantage, PRFScheme.prfAdvantage,
    ENNReal.absDiff_toReal probOutput_ne_top probOutput_ne_top]

/-! ## The twelve summands -/

/-- At a validated parameter set the Winternitz width is at least two, so the `ℕ`-subtraction in
the `(p.w - 2)` coefficient of `Summands.bound` never truncates and the coefficient is never
silently zero.  `Params.w_pos` gives only `0 < p.w`, which is not enough.

*Composition arithmetic.* -/
theorem two_le_w {p : Params} (h : p.Valid) : 2 ≤ p.w := by
  rw [Params.w]
  exact Nat.one_lt_two_pow (Nat.ne_of_gt h.lgw_pos)

/-- **The twelve named summands of `EUFCMA_SPHINCS_PLUS`**, in the source's order.  A bare record of
twelve extended non-negative reals: it carries no claim about where they come from, which is what
`Certificate.summands` supplies.

*Composition arithmetic.* -/
structure Summands where
  /-- `SKG_PRF` — the secret-value `PRF` hop. -/
  skgPrf : ℝ≥0∞
  /-- `MKG_PRF` — the message-randomizer `PRF_msg` hop. -/
  mkgPrf : ℝ≥0∞
  /-- `MCO_ITSR` — interleaved-target subset resilience of `H_msg`. -/
  hmsgItsr : ℝ≥0∞
  /-- `FP_DSPR` — decisional second-preimage resistance of the FORS leaf hash `F`, already
  carrying the source's truncated `DSPR success − SPprob` subtraction. -/
  forsFDspr : ℝ≥0∞
  /-- `FP_TCR` — target-collision resistance of the FORS leaf hash `F`, at coefficient three. -/
  forsFTcr : ℝ≥0∞
  /-- `FTWES.TRHC_TCR` — target-collision resistance of the FORS internal-node hash `H`. -/
  forsHTcr : ℝ≥0∞
  /-- `TRCOC_TCR` — target-collision resistance of the FORS root compression `T_k`. -/
  forsTlTcr : ℝ≥0∞
  /-- `FC_UD` — undetectability of the WOTS+ chain hash `F`, at coefficient `w − 2`. -/
  wotsFUd : ℝ≥0∞
  /-- `FC_TCR` — target-collision resistance of the WOTS+ chain hash `F`. -/
  wotsFTcr : ℝ≥0∞
  /-- `FC_PRE` — preimage resistance of the WOTS+ chain hash `F`. -/
  wotsFPre : ℝ≥0∞
  /-- `PKCOC_TCR` — target-collision resistance of the WOTS+ compression `T_len`. -/
  wotsTlTcr : ℝ≥0∞
  /-- `FSSLXMTWES.TRHC_TCR` — target-collision resistance of the XMSS internal-node hash `H`. -/
  xmssHTcr : ℝ≥0∞

/-- **The conditional EUF-CMA bound expression**, with the source's two coefficients: `3` on the
FORS-`F` target-collision term and `w − 2` on the WOTS+-`F` undetectability term.  Every other
summand has coefficient one.

*Composition arithmetic.* -/
noncomputable def Summands.bound (s : Summands) (p : Params) : ℝ≥0∞ :=
  s.skgPrf + s.mkgPrf + s.hmsgItsr
    + s.forsFDspr + 3 * s.forsFTcr + s.forsHTcr + s.forsTlTcr
    + (p.w - 2 : ℕ) * s.wotsFUd + s.wotsFTcr + s.wotsFPre + s.wotsTlTcr + s.xmssHTcr

/-- Unfolding equation for `Summands.bound`.  The body is not exposed, so this is what a consumer
that needs the twelve-summand shape — the coefficients included — rewrites with.

*Composition arithmetic.* -/
theorem Summands.bound_eq (s : Summands) (p : Params) :
    s.bound p = s.skgPrf + s.mkgPrf + s.hmsgItsr
      + s.forsFDspr + 3 * s.forsFTcr + s.forsHTcr + s.forsTlTcr
      + (p.w - 2 : ℕ) * s.wotsFUd + s.wotsFTcr + s.wotsFPre + s.wotsTlTcr + s.xmssHTcr := by
  rfl

/-- The bound of the all-zero summands is zero: the expression is a sum of the twelve terms and
nothing else.  A stray additive constant, or a `max` against anything non-zero, fails it.

*Composition arithmetic.* -/
theorem bound_eq_zero_of_summands_zero (p : Params) :
    (Summands.mk 0 0 0 0 0 0 0 0 0 0 0 0).bound p = 0 := by
  rw [Summands.bound_eq]
  simp

/-- The coefficient on the undetectability summand, isolated: it is `w − 2` and it multiplies
`wotsFUd` alone.

This is the one coefficient nothing in this repository derives.  It is pinned here against the
expression and in `HashSigTest.SLHDSA.Composition` against a numeral at two profiles, and against
nothing else: a paired edit of it here and in `Certificate.hypertreeBranch_le` produces a
consistent, compiling, differently-scaled theorem.

*Composition arithmetic.* -/
theorem bound_wotsFUd_coefficient (p : Params) (x : ℝ≥0∞) :
    (Summands.mk 0 0 0 0 0 0 0 x 0 0 0 0).bound p = (p.w - 2 : ℕ) * x := by
  rw [Summands.bound_eq]
  simp

/-- **The `ℕ` subtraction in the undetectability coefficient is exact.**  At a validated parameter
set the coefficient plus two is the Winternitz width, so `(p.w - 2 : ℕ)` is a difference and not a
truncation.  This is what `two_le_w` is for.

It does *not* say the coefficient is non-zero.  `Params.Valid` requires only `0 < p.lgw`, so it
admits `lgw = 1`, where `p.w = 2`, the coefficient is `0`, and the WOTS+-`F` undetectability
summand leaves the bound entirely — correctly, because the source's hybrid over chain positions
has `w - 2` steps and at `w = 2` it has none.  What `two_le_w` rules out is `p.w = 1`, where the
subtraction would truncate a negative difference to zero and the summand would vanish for a
reason that is an artefact of `ℕ`.  `HashSigTest.SLHDSA.Composition` carries both parameter sets
and asserts which of the two is `Valid`.

*Composition arithmetic.* -/
theorem bound_wotsFUd_coefficient_add_two {p : Params} (h : p.Valid) (x : ℝ≥0∞) :
    (Summands.mk 0 0 0 0 0 0 0 x 0 0 0 0).bound p + 2 * x = (p.w : ℝ≥0∞) * x := by
  rw [bound_wotsFUd_coefficient, ← add_mul]
  congr 1
  rw [show ((2 : ℝ≥0∞)) = ((2 : ℕ) : ℝ≥0∞) by norm_num, ← Nat.cast_add,
    Nat.sub_add_cancel (two_le_w h)]

/-- The coefficient on the FORS-`F` target-collision summand, isolated: it is three.

Unlike `bound_wotsFUd_coefficient` this one is pinned from below by the library:
`advantage_le_bound` applies `SM_DT_OpenPRE_SourceFinalValidity.advantage_le_tcrDsprBound`, whose
`TCRDSPRBound` has the literal `3`, so a coefficient smaller than three does not elaborate there.

*Composition arithmetic.* -/
theorem bound_forsFTcr_coefficient (p : Params) (x : ℝ≥0∞) :
    (Summands.mk 0 0 0 0 x 0 0 0 0 0 0 0).bound p = 3 * x := by
  rw [Summands.bound_eq]
  simp

/-! ## The certificate -/

variable {vp : ValidatedParams} (prims : Primitives vp.params)

section Certificate

variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.PkSeed]
  [SampleableType prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey]
  [DecidableEq prims.Y] [Fintype prims.Y] [Inhabited prims.Y]

/-- **A composition certificate for one EUF-CMA adversary against `generalAlg`.**

Twelve adversary fields against the games of `HashSig.SLHDSA.Security.CanonicalGames`, the public
seed the secret-value `PRF` is keyed at, VCVio's OpenPRE counting interface, three named quantities
and four inequalities.  Every one of them is a hypothesis; none is discharged in this repository,
and the module docstring says per field why.

The four inequalities are a chain, not a restatement of the conclusion.  `prfHops` moves from the
real experiment to a key-idealized quantity this module only names; `split` moves from that to two
branches; the two `_le` fields bound each branch by its own games.  Nothing here mentions
`Summands.bound`, and the step from `forsBranch_le`'s OpenPRE advantage to the bound's
`DSPR + 3·TCR` pair is `advantage_le_bound`'s work and consumes `counting`.

`Certificate.ofBranchBounds` builds one from the twelve adversaries, `counting`, and two branch
bounds stated at `SchemeGames`' own dispatch halves, which is the measurement of how much a
certificate needs: `split` and `prfHops` are discharged there, the two branch bounds are not.

*Composition arithmetic.* -/
structure Certificate (adv : unforgeableAdv (generalAlg prims)) where
  /-- The `SKG_PRF` distinguisher against the secret-value `PRF` at `pkSeed`. -/
  skgAdv : PRFScheme.PRFAdversary Adrs prims.Y
  /-- The `MKG_PRF` distinguisher against the message randomizer `PRF_msg`. -/
  mkgAdv : PRFScheme.PRFAdversary (prims.Y × List Byte) prims.Y
  /-- The public seed the secret-value `PRF` hop is taken at; `skPrfScheme` is indexed by it. -/
  pkSeed : prims.PkSeed
  /-- The `MCO_ITSR` adversary against `H_msg`. -/
  itsrAdv : KeyedHash.ITSRAdversary (hmsgItsrProblem prims)
  /-- The open-preimage adversary against the FORS leaf hash `F`.  The bound's `DSPR` and `3·TCR`
  summands are both derived from this one adversary, through `Problem.toDSPR` and
  `Problem.toTCR`. -/
  openPreAdv : SM_DT_OpenPRE_SourceFinalValidity.Adversary (forsFOpenPreProblem prims)
  /-- VCVio's fiber-counting interface for `openPreAdv`, which its own docstring calls "deliberately
  a proof obligation, not a theorem supplied by this file". -/
  counting : SM_DT_OpenPRE_SourceFinalValidity.CountingInterface openPreAdv
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
  /-- The advantage that survives the two PRF hops.  Named, not defined: there is no key-idealized
  variant of `GeneralScheme.signInternalM` in this repository for it to be the advantage of. -/
  idealAdvantage : ℝ≥0∞
  /-- The FORS branch's share of `idealAdvantage`. -/
  forsBranch : ℝ≥0∞
  /-- The hypertree branch's share of `idealAdvantage`. -/
  hypertreeBranch : ℝ≥0∞
  /-- **H1 — the two PRF hops.**  Assumed: discharging it needs a key-idealized signer, two
  distinguisher constructions and two program equivalences, none of which exists here. -/
  prfHops : adv.advantage ProbCompRuntime.probComp ≤
    prfAbsAdvantage (skPrfScheme prims pkSeed) skgAdv
      + prfAbsAdvantage (msgPrfScheme prims) mkgAdv + idealAdvantage
  /-- The dispatch split, at the idealized advantage.  `Certificate.ofBranchBounds` discharges this
  field from `SchemeGames.advantage_le_forsHalf_add_hypertreeHalf`, so it is provably instantiable
  and not a disguised assumption. -/
  split : idealAdvantage ≤ forsBranch + hypertreeBranch
  /-- **H2, first half — the FORS branch bound.**  Assumed: it is an adversary construction plus
  challenge recording plus final validity.  Note that it carries the *OpenPRE* advantage; the
  source's `DSPR + 3·TCR` pair is produced by `advantage_le_bound` from `counting`. -/
  forsBranch_le : forsBranch ≤ KeyedHash.ITSRAdvantage itsrAdv
    + SM_DT_OpenPRE_SourceFinalValidity.Advantage openPreAdv
    + SM_DT_TCR_SourceFinalValidity.Advantage forsHAdv
    + SM_DT_TCR_SourceFinalValidity.Advantage forsTlAdv
  /-- **H2, second half — the hypertree branch bound.**  Assumed, for the same reason, and
  carrying the `(w − 2)` coefficient that nothing in this repository derives. -/
  hypertreeBranch_le : hypertreeBranch ≤
    (vp.params.w - 2 : ℕ) * SM_DT_UD_SourceFinalValidity.AbsoluteAdvantage wotsFUdAdv
      + SM_DT_TCR_SourceFinalValidity.Advantage wotsFTcrAdv
      + SM_DT_PRE_SourceFinalValidity.Advantage wotsFPreAdv
      + SM_DT_TCR_SourceFinalValidity.Advantage wotsTlAdv
      + SM_DT_TCR_SourceFinalValidity.Advantage xmssHAdv

variable {prims}

/-- The twelve summands a certificate names, each the advantage of one named game.

The FORS-`F` pair is where a reader should look: both `forsFDspr` and `forsFTcr` are read off the
*one* open-preimage adversary, through VCVio's two reductions, and neither is a separate field.

*Composition arithmetic.* -/
noncomputable def Certificate.summands {adv : unforgeableAdv (generalAlg prims)}
    (c : Certificate prims adv) : Summands where
  skgPrf := prfAbsAdvantage (skPrfScheme prims c.pkSeed) c.skgAdv
  mkgPrf := prfAbsAdvantage (msgPrfScheme prims) c.mkgAdv
  hmsgItsr := KeyedHash.ITSRAdvantage c.itsrAdv
  forsFDspr := SM_DT_DSPR_SourceFinalValidity.Advantage
    (SM_DT_OpenPRE_SourceFinalValidity.toDSPR c.openPreAdv)
  forsFTcr := SM_DT_TCR_SourceFinalValidity.Advantage
    (SM_DT_OpenPRE_SourceFinalValidity.toTCR c.openPreAdv)
  forsHTcr := SM_DT_TCR_SourceFinalValidity.Advantage c.forsHAdv
  forsTlTcr := SM_DT_TCR_SourceFinalValidity.Advantage c.forsTlAdv
  wotsFUd := SM_DT_UD_SourceFinalValidity.AbsoluteAdvantage c.wotsFUdAdv
  wotsFTcr := SM_DT_TCR_SourceFinalValidity.Advantage c.wotsFTcrAdv
  wotsFPre := SM_DT_PRE_SourceFinalValidity.Advantage c.wotsFPreAdv
  wotsTlTcr := SM_DT_TCR_SourceFinalValidity.Advantage c.wotsTlAdv
  xmssHTcr := SM_DT_TCR_SourceFinalValidity.Advantage c.xmssHAdv

/-- **The bound a certificate names, written out.**  This is the twelve-summand expression of
`EUFCMA_SPHINCS_PLUS` at the certificate's own adversaries, and it is what `advantage_le_bound`'s
right-hand side means.  The body of neither `Summands.bound` nor `Certificate.summands` is exposed,
so this equation is how a consumer reads the summand-to-game routing and the two coefficients.

*Composition arithmetic.* -/
theorem Certificate.bound_eq {adv : unforgeableAdv (generalAlg prims)}
    (c : Certificate prims adv) :
    c.summands.bound vp.params =
      prfAbsAdvantage (skPrfScheme prims c.pkSeed) c.skgAdv
        + prfAbsAdvantage (msgPrfScheme prims) c.mkgAdv
        + KeyedHash.ITSRAdvantage c.itsrAdv
        + SM_DT_DSPR_SourceFinalValidity.Advantage
            (SM_DT_OpenPRE_SourceFinalValidity.toDSPR c.openPreAdv)
        + 3 * SM_DT_TCR_SourceFinalValidity.Advantage
            (SM_DT_OpenPRE_SourceFinalValidity.toTCR c.openPreAdv)
        + SM_DT_TCR_SourceFinalValidity.Advantage c.forsHAdv
        + SM_DT_TCR_SourceFinalValidity.Advantage c.forsTlAdv
        + (vp.params.w - 2 : ℕ) *
            SM_DT_UD_SourceFinalValidity.AbsoluteAdvantage c.wotsFUdAdv
        + SM_DT_TCR_SourceFinalValidity.Advantage c.wotsFTcrAdv
        + SM_DT_PRE_SourceFinalValidity.Advantage c.wotsFPreAdv
        + SM_DT_TCR_SourceFinalValidity.Advantage c.wotsTlAdv
        + SM_DT_TCR_SourceFinalValidity.Advantage c.xmssHAdv := by
  rw [Summands.bound_eq]
  rfl

/-- **The conditional quantitative theorem.**  The EUF-CMA advantage of any adversary against the
external SLH-DSA algebra is at most the twelve-summand expression its certificate names.

Read what this does and does not say.  It is an implication whose antecedent is a `Certificate`,
and no `Certificate` exists anywhere in this repository; nothing here bounds any of the twelve
summands, constructs any of the twelve adversaries, records any challenge, or establishes any
game's final validity.  What it does is compose: the certificate's four inequalities plus VCVio's
OpenPRE-to-`DSPR + 3·TCR` coupling give the source's expression, and the coupling is where the
`3` comes from.

*Composition arithmetic.* -/
theorem advantage_le_bound {adv : unforgeableAdv (generalAlg prims)}
    (c : Certificate prims adv) :
    adv.advantage ProbCompRuntime.probComp ≤ c.summands.bound vp.params := by
  have hopen := SM_DT_OpenPRE_SourceFinalValidity.advantage_le_tcrDsprBound c.openPreAdv c.counting
  rw [SM_DT_OpenPRE_SourceFinalValidity.TCRDSPRBound] at hopen
  rw [c.bound_eq]
  calc adv.advantage ProbCompRuntime.probComp
      ≤ prfAbsAdvantage (skPrfScheme prims c.pkSeed) c.skgAdv
          + prfAbsAdvantage (msgPrfScheme prims) c.mkgAdv + c.idealAdvantage := c.prfHops
    _ ≤ prfAbsAdvantage (skPrfScheme prims c.pkSeed) c.skgAdv
          + prfAbsAdvantage (msgPrfScheme prims) c.mkgAdv
          + (c.forsBranch + c.hypertreeBranch) := by gcongr; exact c.split
    _ ≤ prfAbsAdvantage (skPrfScheme prims c.pkSeed) c.skgAdv
          + prfAbsAdvantage (msgPrfScheme prims) c.mkgAdv
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
    _ ≤ prfAbsAdvantage (skPrfScheme prims c.pkSeed) c.skgAdv
          + prfAbsAdvantage (msgPrfScheme prims) c.mkgAdv
          + ((KeyedHash.ITSRAdvantage c.itsrAdv
              + (SM_DT_DSPR_SourceFinalValidity.Advantage
                    (SM_DT_OpenPRE_SourceFinalValidity.toDSPR c.openPreAdv)
                  + 3 * SM_DT_TCR_SourceFinalValidity.Advantage
                    (SM_DT_OpenPRE_SourceFinalValidity.toTCR c.openPreAdv))
              + SM_DT_TCR_SourceFinalValidity.Advantage c.forsHAdv
              + SM_DT_TCR_SourceFinalValidity.Advantage c.forsTlAdv)
            + ((vp.params.w - 2 : ℕ) *
                SM_DT_UD_SourceFinalValidity.AbsoluteAdvantage c.wotsFUdAdv
              + SM_DT_TCR_SourceFinalValidity.Advantage c.wotsFTcrAdv
              + SM_DT_PRE_SourceFinalValidity.Advantage c.wotsFPreAdv
              + SM_DT_TCR_SourceFinalValidity.Advantage c.wotsTlAdv
              + SM_DT_TCR_SourceFinalValidity.Advantage c.xmssHAdv)) := by
        gcongr
    _ = _ := by ring

end Certificate

/-! ## The certificate is not constructible from nothing -/

section AntiVacuity

variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.PkSeed]
  [SampleableType prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey]
  [DecidableEq prims.Y] [Fintype prims.Y] [Inhabited prims.Y]

variable {prims}

/-- **A certificate from the two branch bounds.**  Given the twelve adversaries, the counting
interface, and one inequality per branch of `SchemeGames`' dispatch split — stated at `forsHalf adv`
and `hypertreeHalf adv`, the two probabilities of the instrumented experiment — this builds a
certificate.

What it measures is how much a certificate actually needs.  `split` is discharged from
`advantage_le_forsHalf_add_hypertreeHalf`, a theorem of the previous module, so that field is
provably instantiable and cannot be the place where the conclusion is smuggled in.  `prfHops` is
discharged from `le_add_self` by taking `idealAdvantage := adv.advantage`, which is free in `ℝ≥0∞`
— and that is the honest reading of it: **this constructor takes no PRF hop**, and in the
certificate it returns the two PRF summands are slack that does no work.  What is left unproven is
exactly the two arguments `hfors` and `hhyper`, which are the two branch bounds of the slice plan's
H2 and the bulk of the EasyCrypt development.

*Composition arithmetic.* -/
noncomputable def Certificate.ofBranchBounds {adv : unforgeableAdv (generalAlg prims)}
    (skgAdv : PRFScheme.PRFAdversary Adrs prims.Y)
    (mkgAdv : PRFScheme.PRFAdversary (prims.Y × List Byte) prims.Y)
    (pkSeed : prims.PkSeed)
    (itsrAdv : KeyedHash.ITSRAdversary (hmsgItsrProblem prims))
    (openPreAdv : SM_DT_OpenPRE_SourceFinalValidity.Adversary (forsFOpenPreProblem prims))
    (counting : SM_DT_OpenPRE_SourceFinalValidity.CountingInterface openPreAdv)
    (forsHAdv : SM_DT_TCR_SourceFinalValidity.Adversary (forsHTcrCProblem prims))
    (forsTlAdv : SM_DT_TCR_SourceFinalValidity.Adversary (forsTlTcrCProblem prims))
    (wotsFUdAdv : SM_DT_UD_SourceFinalValidity.Adversary (wotsFUdCProblem prims))
    (wotsFTcrAdv : SM_DT_TCR_SourceFinalValidity.Adversary (wotsFTcrCProblem prims))
    (wotsFPreAdv : SM_DT_PRE_SourceFinalValidity.Adversary (wotsFPreCProblem prims))
    (wotsTlAdv : SM_DT_TCR_SourceFinalValidity.Adversary (wotsTlTcrCProblem prims))
    (xmssHAdv : SM_DT_TCR_SourceFinalValidity.Adversary (xmssHTcrCProblem prims))
    (hfors : forsHalf adv ≤ KeyedHash.ITSRAdvantage itsrAdv
      + SM_DT_OpenPRE_SourceFinalValidity.Advantage openPreAdv
      + SM_DT_TCR_SourceFinalValidity.Advantage forsHAdv
      + SM_DT_TCR_SourceFinalValidity.Advantage forsTlAdv)
    (hhyper : hypertreeHalf adv ≤
      (vp.params.w - 2 : ℕ) * SM_DT_UD_SourceFinalValidity.AbsoluteAdvantage wotsFUdAdv
        + SM_DT_TCR_SourceFinalValidity.Advantage wotsFTcrAdv
        + SM_DT_PRE_SourceFinalValidity.Advantage wotsFPreAdv
        + SM_DT_TCR_SourceFinalValidity.Advantage wotsTlAdv
        + SM_DT_TCR_SourceFinalValidity.Advantage xmssHAdv) :
    Certificate prims adv where
  skgAdv := skgAdv
  mkgAdv := mkgAdv
  pkSeed := pkSeed
  itsrAdv := itsrAdv
  openPreAdv := openPreAdv
  counting := counting
  forsHAdv := forsHAdv
  forsTlAdv := forsTlAdv
  wotsFUdAdv := wotsFUdAdv
  wotsFTcrAdv := wotsFTcrAdv
  wotsFPreAdv := wotsFPreAdv
  wotsTlAdv := wotsTlAdv
  xmssHAdv := xmssHAdv
  idealAdvantage := adv.advantage ProbCompRuntime.probComp
  forsBranch := forsHalf adv
  hypertreeBranch := hypertreeHalf adv
  prfHops := le_add_self
  split := advantage_le_forsHalf_add_hypertreeHalf adv
  forsBranch_le := hfors
  hypertreeBranch_le := hhyper

/-- `ofBranchBounds` smuggles nothing into the summands: the certificate it returns names the same
twelve advantages of the same twelve adversaries it was handed.

*Composition arithmetic.* -/
theorem Certificate.ofBranchBounds_summands {adv : unforgeableAdv (generalAlg prims)}
    (skgAdv : PRFScheme.PRFAdversary Adrs prims.Y)
    (mkgAdv : PRFScheme.PRFAdversary (prims.Y × List Byte) prims.Y)
    (pkSeed : prims.PkSeed)
    (itsrAdv : KeyedHash.ITSRAdversary (hmsgItsrProblem prims))
    (openPreAdv : SM_DT_OpenPRE_SourceFinalValidity.Adversary (forsFOpenPreProblem prims))
    (counting : SM_DT_OpenPRE_SourceFinalValidity.CountingInterface openPreAdv)
    (forsHAdv : SM_DT_TCR_SourceFinalValidity.Adversary (forsHTcrCProblem prims))
    (forsTlAdv : SM_DT_TCR_SourceFinalValidity.Adversary (forsTlTcrCProblem prims))
    (wotsFUdAdv : SM_DT_UD_SourceFinalValidity.Adversary (wotsFUdCProblem prims))
    (wotsFTcrAdv : SM_DT_TCR_SourceFinalValidity.Adversary (wotsFTcrCProblem prims))
    (wotsFPreAdv : SM_DT_PRE_SourceFinalValidity.Adversary (wotsFPreCProblem prims))
    (wotsTlAdv : SM_DT_TCR_SourceFinalValidity.Adversary (wotsTlTcrCProblem prims))
    (xmssHAdv : SM_DT_TCR_SourceFinalValidity.Adversary (xmssHTcrCProblem prims))
    (hfors : forsHalf adv ≤ KeyedHash.ITSRAdvantage itsrAdv
      + SM_DT_OpenPRE_SourceFinalValidity.Advantage openPreAdv
      + SM_DT_TCR_SourceFinalValidity.Advantage forsHAdv
      + SM_DT_TCR_SourceFinalValidity.Advantage forsTlAdv)
    (hhyper : hypertreeHalf adv ≤
      (vp.params.w - 2 : ℕ) * SM_DT_UD_SourceFinalValidity.AbsoluteAdvantage wotsFUdAdv
        + SM_DT_TCR_SourceFinalValidity.Advantage wotsFTcrAdv
        + SM_DT_PRE_SourceFinalValidity.Advantage wotsFPreAdv
        + SM_DT_TCR_SourceFinalValidity.Advantage wotsTlAdv
        + SM_DT_TCR_SourceFinalValidity.Advantage xmssHAdv) :
    (Certificate.ofBranchBounds skgAdv mkgAdv pkSeed itsrAdv openPreAdv counting forsHAdv
        forsTlAdv wotsFUdAdv wotsFTcrAdv wotsFPreAdv wotsTlAdv xmssHAdv hfors hhyper).summands =
      { skgPrf := prfAbsAdvantage (skPrfScheme prims pkSeed) skgAdv
        mkgPrf := prfAbsAdvantage (msgPrfScheme prims) mkgAdv
        hmsgItsr := KeyedHash.ITSRAdvantage itsrAdv
        forsFDspr := SM_DT_DSPR_SourceFinalValidity.Advantage
          (SM_DT_OpenPRE_SourceFinalValidity.toDSPR openPreAdv)
        forsFTcr := SM_DT_TCR_SourceFinalValidity.Advantage
          (SM_DT_OpenPRE_SourceFinalValidity.toTCR openPreAdv)
        forsHTcr := SM_DT_TCR_SourceFinalValidity.Advantage forsHAdv
        forsTlTcr := SM_DT_TCR_SourceFinalValidity.Advantage forsTlAdv
        wotsFUd := SM_DT_UD_SourceFinalValidity.AbsoluteAdvantage wotsFUdAdv
        wotsFTcr := SM_DT_TCR_SourceFinalValidity.Advantage wotsFTcrAdv
        wotsFPre := SM_DT_PRE_SourceFinalValidity.Advantage wotsFPreAdv
        wotsTlTcr := SM_DT_TCR_SourceFinalValidity.Advantage wotsTlAdv
        xmssHTcr := SM_DT_TCR_SourceFinalValidity.Advantage xmssHAdv } := by
  rfl

/-- **What is actually left to prove**, as one statement: bound the two dispatch halves by their
games and the twelve-summand bound follows.

This is `advantage_le_bound` composed with `ofBranchBounds`, and it is the form in which the
remaining obligation is smallest to state.  The two PRF summands on the right are slack — no PRF
hop is taken — which is why the right-hand side is written out here rather than hidden behind
`Summands.bound`.

*Composition arithmetic.* -/
theorem advantage_le_bound_of_halves {adv : unforgeableAdv (generalAlg prims)}
    (skgAdv : PRFScheme.PRFAdversary Adrs prims.Y)
    (mkgAdv : PRFScheme.PRFAdversary (prims.Y × List Byte) prims.Y)
    (pkSeed : prims.PkSeed)
    (itsrAdv : KeyedHash.ITSRAdversary (hmsgItsrProblem prims))
    (openPreAdv : SM_DT_OpenPRE_SourceFinalValidity.Adversary (forsFOpenPreProblem prims))
    (counting : SM_DT_OpenPRE_SourceFinalValidity.CountingInterface openPreAdv)
    (forsHAdv : SM_DT_TCR_SourceFinalValidity.Adversary (forsHTcrCProblem prims))
    (forsTlAdv : SM_DT_TCR_SourceFinalValidity.Adversary (forsTlTcrCProblem prims))
    (wotsFUdAdv : SM_DT_UD_SourceFinalValidity.Adversary (wotsFUdCProblem prims))
    (wotsFTcrAdv : SM_DT_TCR_SourceFinalValidity.Adversary (wotsFTcrCProblem prims))
    (wotsFPreAdv : SM_DT_PRE_SourceFinalValidity.Adversary (wotsFPreCProblem prims))
    (wotsTlAdv : SM_DT_TCR_SourceFinalValidity.Adversary (wotsTlTcrCProblem prims))
    (xmssHAdv : SM_DT_TCR_SourceFinalValidity.Adversary (xmssHTcrCProblem prims))
    (hfors : forsHalf adv ≤ KeyedHash.ITSRAdvantage itsrAdv
      + SM_DT_OpenPRE_SourceFinalValidity.Advantage openPreAdv
      + SM_DT_TCR_SourceFinalValidity.Advantage forsHAdv
      + SM_DT_TCR_SourceFinalValidity.Advantage forsTlAdv)
    (hhyper : hypertreeHalf adv ≤
      (vp.params.w - 2 : ℕ) * SM_DT_UD_SourceFinalValidity.AbsoluteAdvantage wotsFUdAdv
        + SM_DT_TCR_SourceFinalValidity.Advantage wotsFTcrAdv
        + SM_DT_PRE_SourceFinalValidity.Advantage wotsFPreAdv
        + SM_DT_TCR_SourceFinalValidity.Advantage wotsTlAdv
        + SM_DT_TCR_SourceFinalValidity.Advantage xmssHAdv) :
    adv.advantage ProbCompRuntime.probComp ≤
      prfAbsAdvantage (skPrfScheme prims pkSeed) skgAdv
        + prfAbsAdvantage (msgPrfScheme prims) mkgAdv
        + KeyedHash.ITSRAdvantage itsrAdv
        + SM_DT_DSPR_SourceFinalValidity.Advantage
            (SM_DT_OpenPRE_SourceFinalValidity.toDSPR openPreAdv)
        + 3 * SM_DT_TCR_SourceFinalValidity.Advantage
            (SM_DT_OpenPRE_SourceFinalValidity.toTCR openPreAdv)
        + SM_DT_TCR_SourceFinalValidity.Advantage forsHAdv
        + SM_DT_TCR_SourceFinalValidity.Advantage forsTlAdv
        + (vp.params.w - 2 : ℕ) *
            SM_DT_UD_SourceFinalValidity.AbsoluteAdvantage wotsFUdAdv
        + SM_DT_TCR_SourceFinalValidity.Advantage wotsFTcrAdv
        + SM_DT_PRE_SourceFinalValidity.Advantage wotsFPreAdv
        + SM_DT_TCR_SourceFinalValidity.Advantage wotsTlAdv
        + SM_DT_TCR_SourceFinalValidity.Advantage xmssHAdv := by
  have h := advantage_le_bound (Certificate.ofBranchBounds skgAdv mkgAdv pkSeed itsrAdv
    openPreAdv counting forsHAdv forsTlAdv wotsFUdAdv wotsFTcrAdv wotsFPreAdv wotsTlAdv
    xmssHAdv hfors hhyper)
  rwa [Certificate.bound_eq] at h

end AntiVacuity

/-! ## Transporting a bound onto the two induced FORS-`F` games

Slice 6's `forsFDsprProblem` and `forsFTcrProblem` are the games the OpenPRE reductions attack, and
`CanonicalGames.forsFDsprProblem_eq_toDSPR` and `forsFTcrProblem_eq_toTCR` say so.  The obvious way
to use those equations — cast an adversary along one of them and apply the hypothesis — does not
work: the three standalone problems are deliberately not `@[expose]`d, so each equation is
propositional but not definitional across the module boundary, and the cast survives as a `▸` that
blocks unification.  Lean says so explicitly, naming `forsFOpenPreProblem` and `forsFDsprProblem` as
"not unfolded because their definition is not exposed".  What does work is to rewrite the
*hypothesis's own statement* before applying it, which is what these two do. -/

section Transfer

variable [SampleableType prims.PkSeed] [SampleableType prims.Y] [DecidableEq prims.AdrsKey]
  [DecidableEq prims.Y] [Fintype prims.Y] [Inhabited prims.Y]

/-- A DSPR bound quantified over adversaries against slice 6's `forsFDsprProblem` applies to the
adversary VCVio's OpenPRE-to-DSPR reduction produces.

*Game transport.* -/
theorem dspr_bound_transfer (εD : ℝ≥0∞)
    (h : ∀ a : SM_DT_DSPR_SourceFinalValidity.Adversary (forsFDsprProblem prims),
      SM_DT_DSPR_SourceFinalValidity.Advantage a ≤ εD)
    (a : SM_DT_OpenPRE_SourceFinalValidity.Adversary (forsFOpenPreProblem prims)) :
    SM_DT_DSPR_SourceFinalValidity.Advantage
      (SM_DT_OpenPRE_SourceFinalValidity.toDSPR a) ≤ εD :=
  (by rw [← forsFDsprProblem_eq_toDSPR]; exact h :
    ∀ b : SM_DT_DSPR_SourceFinalValidity.Adversary ((forsFOpenPreProblem prims).toDSPR),
      SM_DT_DSPR_SourceFinalValidity.Advantage b ≤ εD)
    (SM_DT_OpenPRE_SourceFinalValidity.toDSPR a)

-- `Fintype prims.Y` is in scope for the DSPR twin above, which needs it, and is unused here:
-- `SM_DT_TCR_SourceFinalValidity.Advantage` asks only for the three `DecidableEq` instances.
omit [Fintype prims.Y] in
/-- A TCR bound quantified over adversaries against slice 6's `forsFTcrProblem` applies to the
adversary VCVio's OpenPRE-to-TCR reduction produces.

*Game transport.* -/
theorem tcr_bound_transfer (εT : ℝ≥0∞)
    (h : ∀ a : SM_DT_TCR_SourceFinalValidity.Adversary (forsFTcrProblem prims),
      SM_DT_TCR_SourceFinalValidity.Advantage a ≤ εT)
    (a : SM_DT_OpenPRE_SourceFinalValidity.Adversary (forsFOpenPreProblem prims)) :
    SM_DT_TCR_SourceFinalValidity.Advantage
      (SM_DT_OpenPRE_SourceFinalValidity.toTCR a) ≤ εT :=
  (by rw [← forsFTcrProblem_eq_toTCR]; exact h :
    ∀ b : SM_DT_TCR_SourceFinalValidity.Adversary ((forsFOpenPreProblem prims).toTCR),
      SM_DT_TCR_SourceFinalValidity.Advantage b ≤ εT)
    (SM_DT_OpenPRE_SourceFinalValidity.toTCR a)

variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [DecidableEq prims.PkSeed]

variable {prims}

/-- The FORS-`F` block of the bound — `DSPR + 3·TCR` — under hypotheses stated at slice 6's two
standalone games rather than at the induced ones.  This is where the two transports do work: the
hypotheses a reader would write are about `forsFDsprProblem` and `forsFTcrProblem`, and the
certificate's summands are about `Problem.toDSPR` and `Problem.toTCR`.

*Game transport.* -/
theorem summands_forsF_le {adv : unforgeableAdv (generalAlg prims)} (c : Certificate prims adv)
    (εD εT : ℝ≥0∞)
    (hD : ∀ a : SM_DT_DSPR_SourceFinalValidity.Adversary (forsFDsprProblem prims),
      SM_DT_DSPR_SourceFinalValidity.Advantage a ≤ εD)
    (hT : ∀ a : SM_DT_TCR_SourceFinalValidity.Adversary (forsFTcrProblem prims),
      SM_DT_TCR_SourceFinalValidity.Advantage a ≤ εT) :
    c.summands.forsFDspr + 3 * c.summands.forsFTcr ≤ εD + 3 * εT := by
  have hd : c.summands.forsFDspr = SM_DT_DSPR_SourceFinalValidity.Advantage
      (SM_DT_OpenPRE_SourceFinalValidity.toDSPR c.openPreAdv) := rfl
  have ht : c.summands.forsFTcr = SM_DT_TCR_SourceFinalValidity.Advantage
      (SM_DT_OpenPRE_SourceFinalValidity.toTCR c.openPreAdv) := rfl
  rw [hd, ht]
  gcongr
  · exact dspr_bound_transfer prims εD hD c.openPreAdv
  · exact tcr_bound_transfer prims εT hT c.openPreAdv

/-- The certificate's own open-preimage advantage is below the FORS-`F` block of its bound, which
is the OpenPRE coupling read off the summands.  Without the `counting` field this is false in
general: VCVio's inequality is conditional on it.

*Game transport.* -/
theorem openPre_le_summands_forsF {adv : unforgeableAdv (generalAlg prims)}
    (c : Certificate prims adv) :
    SM_DT_OpenPRE_SourceFinalValidity.Advantage c.openPreAdv ≤
      c.summands.forsFDspr + 3 * c.summands.forsFTcr := by
  have h := SM_DT_OpenPRE_SourceFinalValidity.advantage_le_tcrDsprBound c.openPreAdv c.counting
  rwa [SM_DT_OpenPRE_SourceFinalValidity.TCRDSPRBound] at h

end Transfer

end SLHDSA.Security
