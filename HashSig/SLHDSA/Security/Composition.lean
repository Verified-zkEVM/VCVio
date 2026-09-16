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

`adv.advantage ProbCompRuntime.probComp ≤ c.summands.bound vp.params`

where `Summands.bound` is the twelve-summand expression of `EUFCMA_SPHINCS_PLUS`, at the source's
coefficients, and `Certificate.summands` routes each summand to the advantage of a named game of
`HashSig.SLHDSA.Security.CanonicalGames`.  `Certificate.bound_eq` writes the right-hand side out.

## What a `Certificate` is, and what it is not

A `Certificate` has twenty fields: eleven adversaries, the public seed the secret-value `PRF` is
keyed at, the OpenPRE counting interface, three named quantities in `ℝ≥0∞` and four inequalities.
Eleven adversaries and twelve summands, because the FORS-`F` `DSPR` and `3 · TCR` summands are read
off one open-preimage adversary.  It is the honest content of this module and a reader should
attack it first.  Three things are true of it and worth stating separately.

* **No field is the conclusion.**  No field's *type* names `Summands.bound`,
  `Certificate.summands` or `advantage_le_bound`, so a certificate cannot say "the bound holds".
  The four inequalities decompose as
  `advantage ≤ prf + prf + ideal`, `ideal ≤ forsBranch + hypertreeBranch`, and one bound per
  branch, and the step from there to the conclusion is arithmetic this module does — including one
  step that is not arithmetic at all (below).
* **How much it needs is exhibited, not asserted.**  `Certificate.ofBranchBounds` builds one from
  the eleven adversaries, the counting interface and *two* inequalities — one per branch of
  `SchemeGames`' dispatch split, stated at `forsHalf adv` and `hypertreeHalf adv` — discharging
  `split` from `advantage_le_forsHalf_add_hypertreeHalf` and `prfHops` from `le_add_self`.  So
  `split` is provably instantiable and is not a disguised assumption, and what remains unproven
  *along that route* is the two branch bounds, which is the bulk of the EasyCrypt development.  It
  is not the only route, and the other one costs nothing: see "A certificate costs nothing" below.
* **`ofBranchBounds` takes no PRF hop.**  It sets `idealAdvantage := adv.advantage`, so in the
  certificate it returns the two PRF summands are pure slack: they appear in the bound and do no
  work.  A certificate that takes a real PRF hop has to choose a smaller `idealAdvantage`, and
  nothing in this repository can.  `advantage_le_bound_of_halves` is that reading as one statement.

And two things about it that nothing here refuses.

* **The three named quantities mean only what the four inequalities say.**  `idealAdvantage`,
  `forsBranch` and `hypertreeBranch` are `ℝ≥0∞` fields with no tie to any experiment.  Their names
  describe the intended reading — an advantage surviving two PRF hops, split into the two branches
  of `SchemeGames`' dispatch — and `ofBranchBounds` exhibits a certificate that honours it, but no
  certificate is obliged to.  One with `forsBranch := 0` and
  `hypertreeBranch := idealAdvantage := adv.advantage` satisfies `prfHops`, `split` and
  `forsBranch_le` for free and puts the whole obligation on `hypertreeBranch_le`; nothing in this
  module sees the difference, and `HashSigTest.SLHDSA.Composition` builds exactly that certificate
  and discharges the one goal it leaves.  Refusing *that* certificate needs the fields tied to the
  experiment, by the inequalities of "What would make it one" below or by fixing them to
  `forsHalf adv` and `hypertreeHalf adv` outright — which would also fix the split this module
  takes, and belongs with whatever bounds a branch.  Neither refuses every certificate: the same
  fixture builds the one that takes those values.
* **`pkSeed` is not tied to the key generation the adversary plays against.**  It is the seed
  `skPrfScheme` is indexed at, chosen by whoever supplies the certificate; a reader who assumes it
  is the seed the experiment sampled is reading something the structure does not say.  The
  obligation that makes it the right one is inside `prfHops`, which is a hypothesis.

## A certificate costs nothing, so this is a theorem about an expression

`HashSigTest.SLHDSA.Composition` builds a closed `Certificate prims adv` — every one of the twenty
fields supplied, all four inequalities proved — at an *arbitrary* `vp : ValidatedParams`, an
arbitrary bundle carrying the instance hypotheses this section asks for, and an arbitrary
adversary, from an address key and a public seed and no security assumption at all; and it proves
that the bound that certificate names is at least one.  `advantage_le_bound` at that certificate
says `adv.advantage ≤ (something ≥ 1)`, which `probOutput_le_one` already gives.  Three facts
compose, each a theorem of that fixture.

* **The preimage game is winnable outright.**  `SM_DT_PRE_SourceFinalValidity` accepts on
  `th.eval pk t (emb m) = th.eval pk t (emb x)` with no `m ≠ x` clause — correctly, because it is
  preimage and not second-preimage resistance — and its challenge oracle answers with an image it
  has just computed, so the fibre the adversary must hit is non-empty.  An adversary whose second
  phase is `Function.invFun` of that map wins with probability one after a single challenge query,
  which `targetCount_pos` keeps inside the cap.  So `Summands.wotsFPre` is `1` at that adversary,
  for every tweakable hash whatsoever.
* **The OpenPRE counting interface is inhabited from nothing.**  An adversary that commits to no
  target records no challenge, so the selected index misses in both the OpenPRE experiment and the
  DSPR experiment of `Problem.toDSPR`, both advantages are zero, and `singleMass := 0` with
  `multipleMass := 0` satisfies the interface's two equations and its inequality.  Its one real
  input is `Problem.HasUniformInputs`, which `CanonicalGames.forsFOpenPreProblem_hasUniformInputs`
  proves.
* **The three `ℝ≥0∞` fields absorb the rest.**  With `forsBranch := 0` and
  `hypertreeBranch := idealAdvantage := adv.advantage`, `prfHops` is `le_add_self`, `split` and
  `forsBranch_le` are `simp`, and `hypertreeBranch_le` is `adv.advantage ≤ 1 = wotsFPre ≤ …`.

The reason is the difference between a reduction and an existential.  `EUFCMA_SPHINCS_PLUS` is a
reduction: every probability on its right-hand side is the advantage of a module *built from* the
forger `A`, and none of those adversaries can be re-chosen.  `Certificate` quantifies
existentially over eleven adversaries with nothing tying any of them to `adv`, and in a model
where an adversary carries no resource bound several of the twelve games are satisfiable at
advantage one.  So `advantage_le_bound` is a true and correctly proved statement about the
**shape** of the source's expression — twelve named quantities, the source's order, the source's
coefficients, and the arithmetic that composes four inequalities into them.  It is not yet a
statement about SLH-DSA's security, and a `Certificate` is not evidence of anything.

### What would make it one, and what that costs

* **Reduction functions.**  Replace the eleven adversary fields by functions
  `unforgeableAdv (generalAlg prims) → Adversary (game prims)`, fixed at the structure or at the
  theorem, so each summand is stated at `R adv` and cannot be re-chosen.  Those are the source's
  twelve `R_…(A)` modules, roughly twenty-four thousand lines of EasyCrypt, and none of them
  exists here, so none of the twelve can be written yet.  This is the
  only change that makes the statement a security statement.  Turning a *field* into one of
  function type is not enough — it is still freely chosen, a certificate being able to supply a
  constant function; the function has to be fixed at the structure or at the theorem, which
  deletes the field.
* **Anchoring the three `ℝ≥0∞` fields** to the experiment — `idealAdvantage ≤ adv.advantage`,
  `forsHalf adv ≤ forsBranch`, `hypertreeHalf adv ≤ hypertreeBranch` — is much smaller, and it
  removes one route rather than the hole.  It does refuse the certificate above, which sets
  `forsBranch := 0`: of the three inequalities it adds that one certificate fails exactly the
  second, which asks there for `forsHalf adv ≤ 0`, and what is left of an attempt to discharge that
  is `forsHalf adv = 0` at an arbitrary adversary.  What it does not do is make a certificate hard
  to come by.  Each half has a game whose winning condition carries no distinctness clause — the
  preimage game on the hypertree side, `SM_DT_OpenPRE_SourceFinalValidity` on the FORS side — so
  each branch bound holds at the anchored value itself, by the chain `half ≤ adv.advantage ≤ 1 =
  that game's advantage ≤ that branch's right-hand side`.  `HashSigTest.SLHDSA.Composition` builds
  the certificate that takes them: `idealAdvantage := adv.advantage`, `forsBranch := forsHalf adv`,
  `hypertreeBranch := hypertreeHalf adv`, from an address key, a public seed and one
  `CountingInterface` at the winning open-preimage adversary, with all three anchoring
  inequalities holding at it by `le_refl`.  So what anchoring buys is that one field, asked for at
  an adversary of advantage one rather than at one of advantage zero, and nothing else.

  What it buys is settled down to an inequality.  At any open-preimage adversary of advantage one
  over a finite input type with at least two elements and with uniformly sampled inputs, a
  `CountingInterface` exists **exactly when** `1 ≤ TCRDSPRBound` at it — that is, when its two
  induced reductions satisfy `DSPR + 3 · TCR ≥ 1`.  The fixture proves both directions; the reverse
  one puts every unit of mass on the stratum of fibre size two, which is where the `3` binds twice
  over: the pointwise inequality `1 + 1/n ≤ 3 · (n − 1)/n` that
  `openPRE_multipleMass_add_reciprocal_le_three_collision` sums is an equality at `n = 2` and
  strict above it, and the reverse construction's own requirement,
  `(n − 1)(1 − DSPR) / (n + 1) ≤ TCR` at fibre size `n`, is weakest there too.  Whether the
  fixture's own winning adversary satisfies the inequality turns on which preimage
  `Function.invFun` returns, and
  is settled neither here nor there.  An adversary drawing its preimage uniformly from the fibre
  would satisfy it, because the conditional law of a uniform target given its image is uniform on
  the fibre — but that is an argument on paper, and what it would take to make it a checked one is
  exactly the coupling VCVio leaves open.  So anchoring very probably closes nothing, and what
  would settle that is the coupling rather than the anchoring.
* **A resource bound** on the quantified adversaries would rule out both fixture adversaries at
  once: `Function.invFun` is not a computation, and an unbounded commitment phase is not a
  bounded one.  `OracleComp` carries no such bound; adding one is a change to VCVio, not to this
  module.

## Where the arithmetic is not arithmetic

`Certificate.forsBranch_le` carries the **OpenPRE** advantage of `forsFOpenPreProblem`, not the
pair `DSPR + 3·TCR` that the source's expression has.  `advantage_le_bound` replaces one by the
other by applying `TweakableHash.SM_DT_OpenPRE_SourceFinalValidity.advantage_le_tcrDsprBound` to
the certificate's `counting` field.  That is the only step of the proof that is not `gcongr` and
`ring`, and it is why the `3` in `Summands.bound` is not a transcription: the library derives it
from `openPRE_multipleMass_add_reciprocal_le_three_collision`, so a `Summands.bound` that said
`2 *` does not typecheck against the library's own `TCRDSPRBound`.  The coefficient is therefore
bounded below by the library and not bounded above inside this module; raised to `4 *` it is
refused only by `HashSigTest.SLHDSA.Composition`.

The other coefficient, `(p.w - 2 : ℕ)`, is **not** derived anywhere in Lean.  VCVio has no
hybrid-argument machinery for SM-DT-UD; the coefficient is carried from
`MEUFGCMA_WOTSTWESNPRF` and `EUFNAGCMA_FLSLXMSSMTTWESNPRF`.  Nothing inside *this module* refuses
a paired edit of it — changed throughout, with `bound_wotsFUd_coefficient_add_two`'s own constant
moved with it, this module is still well-formed.  What refuses such a value is
`HashSigTest.SLHDSA.Composition`, which restates the coefficient in its pins and in the hypertree
branch bound of the certificate that survives anchoring; a coefficient changed in both places is
refused by nothing beyond the source citation above.

## What is not established, and cannot be read into the inequality

The bound is conditional on every field of the certificate, and inside `HashSig` no closed term of
type `Certificate` occurs: `ofBranchBounds` is a constructor taking two unproved inequalities, and
the only certificate this library names is a variable.  That is not an anti-vacuity result —
`HashSigTest.SLHDSA.Composition` builds a closed one from nothing, and the section above says what
follows.  In particular:

* no reduction adversary is constructed, so no adversary field is a function of `adv`; the eleven
  are satisfied by any adversaries at all, including the eleven the fixture supplies;
* nothing says any honest value was recorded as a valid challenge target before a forgery, that
  any execution produced any target transcript, or that a game's final-validity bit survived;
* the two PRF hops are assumed, not taken: there is no key-idealized variant of
  `GeneralScheme.signInternalM` anywhere in the repository;
* the OpenPRE counting interface is assumed.  Its `uniformInputs` field is dischargeable from
  `CanonicalGames.forsFOpenPreProblem_hasUniformInputs`; its two equations and its inequality are,
  in VCVio's own words, "the substantive probabilistic coupling still to be constructed", and they
  are also dischargeable at an adversary that records no target, where every mass is zero.  At an
  adversary that wins outright, over an input type with at least two elements and sampled
  uniformly as this one's is, they are equivalent to `1 ≤ TCRDSPRBound` at it, which is neither
  proved nor refuted here;
* the `MCO_ITSR` summand carries no query bound.  `KeyedHash.ITSRProblem` has two fields and
  neither is a target cap: `ITSRTargetOracle` answers and records every query, so the Lean
  advantage is the supplied adversary's success probability, with no bound on its target
  transcript.  The source's term is bounded through its reduction, by the forger's signing
  queries, and that reduction is not here;
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

*Game transport* — a statement that moves a bound between two of `CanonicalGames`' named games:

* `dspr_bound_transfer`, `tcr_bound_transfer`, `summands_forsF_le`, `openPre_le_summands_forsF`.

None is `private` and none carries `@[expose]`; `Summands.bound_eq` and `Certificate.bound_eq` are
what a consumer that needs the expression's shape rewrites with, exactly as
`SchemeGames.internalLog_eq` is for `internalLog`.

## Correspondence with the EasyCrypt development

`Summands.bound` is the right-hand side of `EUFCMA_SPHINCS_PLUS`, in the source's order: the two
`PRF` hops of `SKG_PRF` and `MKG_PRF`; then the five summands of `EUFCMA_MFORSTWESNPRF`, which are
`MCO_ITSR`, `DSPR − SPprob`, `3 · TCR`, `TRHC_TCR` and `TRCOC_TCR`; and then the hypertree block
`(w − 2) · FC_UD`, `FC_TCR`, `FC_PRE`, `PKCOC_TCR`, `TRHC_TCR` of
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
`PRFScheme.prfAdvantage`.  They are kept here so as not to widen a shared module's public surface,
and the bridge makes the relationship checkable from either side. -/

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
the `(p.w - 2)` coefficient of `Summands.bound` never truncates a negative difference.
The coefficient is zero when `p.w = 2`.  `Params.w_pos` gives only `0 < p.w`, which is not enough.

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

This is the one coefficient nothing in this repository derives.  Inside this module it is pinned
only relative to the constant in `bound_wotsFUd_coefficient_add_two`, so an edit that moves both
leaves this module well-formed; what refuses it is `HashSigTest.SLHDSA.Composition`, which
restates this equation, that one, the two branch expressions and the coefficient as a numeral at
two profiles, in a file no edit of this module reaches.

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
summand leaves the bound entirely.  Whether that is right is not settled by the source, which
fixes `w ∈ {4, 16, 256}` (`WOTS_TW_ES.ec`, `val_w`) and states neither
`MEUFGCMA_WOTSTWESNPRF` nor `EUFNAGCMA_FLSLXMSSMTTWESNPRF` outside it; `Params.Valid` is strictly
more permissive here than the parameter space of the theorem this expression mirrors.  What
`two_le_w` rules out is `p.w = 1`, where the
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
`TCRDSPRBound` has the literal `3`, so a coefficient smaller than three does not typecheck there.
A larger one is not bounded above inside this module and is refused by the fixture alone.

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

Eleven adversary fields against the games of `HashSig.SLHDSA.Security.CanonicalGames`, the public
seed the secret-value `PRF` is keyed at, VCVio's OpenPRE counting interface, three named quantities
and four inequalities: twenty fields for twelve summands, because one open-preimage adversary
supplies two of them.  Every one of the twenty is a hypothesis, and none is discharged in
`HashSig`; the module docstring says per field why.

The four inequalities are a chain, not a restatement of the conclusion.  `prfHops` moves from the
real experiment to a key-idealized quantity this module only names; `split` moves from that to two
branches; the two `_le` fields bound each branch by its own games.  Nothing here mentions
`Summands.bound`, and the step from `forsBranch_le`'s OpenPRE advantage to the bound's
`DSPR + 3·TCR` pair is `advantage_le_bound`'s work and consumes `counting`.

**That the chain is not the conclusion does not make it expensive.**  Because the eleven
adversaries are quantified with nothing tying them to `adv`, the whole structure is inhabited from
an address key and a public seed: `HashSigTest.SLHDSA.Composition` builds such a term at an
arbitrary validated parameter set and an arbitrary bundle, and the bound it names is at least one.
The module docstring's "A certificate costs nothing" says how, and says what is therefore left of
`advantage_le_bound`.

`Certificate.ofBranchBounds` builds one from the eleven adversaries, `counting`, and two branch
bounds stated at `SchemeGames`' own dispatch halves.  That measures what the *intended* route
costs: `split` and `prfHops` are discharged there, the two branch bounds are not.  It does not
measure what a certificate costs, which is nothing.

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

Read what this does and does not say.  What it does is compose: the certificate's four
inequalities plus VCVio's OpenPRE-to-`DSPR + 3·TCR` coupling give the source's expression, and the
coupling is where the `3` comes from.  What it does not do is say anything about SLH-DSA.  Its
antecedent is free — `HashSigTest.SLHDSA.Composition` builds a `Certificate` for every adversary
from an address key and a public seed, and proves that the bound that one names is at least one,
so at that certificate this theorem is `probOutput_le_one` with extra steps.  Nothing here bounds
any of the twelve summands, ties any of the eleven adversaries to `adv`, records any challenge, or
establishes any game's final validity.  The module docstring's "A certificate costs nothing" says
what would have to change.

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

/-! ## Building a certificate from the two branch bounds

The section name is what this constructor measures: how much the *intended* route to a certificate
costs, namely the two dispatch-half bounds and nothing else.  It is not a claim that the route is
forced; the module docstring records the route that costs nothing. -/

section BranchBounds

variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.PkSeed]
  [SampleableType prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey]
  [DecidableEq prims.Y] [Fintype prims.Y] [Inhabited prims.Y]

variable {prims}

/-- **A certificate from the two branch bounds.**  Given the eleven adversaries, the counting
interface, and one inequality per branch of `SchemeGames`' dispatch split — stated at `forsHalf adv`
and `hypertreeHalf adv`, the two probabilities of the instrumented experiment — this builds a
certificate.

What it measures is how much the intended route needs — not how much a certificate needs, which
is nothing.  `split` is discharged from `advantage_le_forsHalf_add_hypertreeHalf`, a theorem of
the previous module, so that field is provably instantiable and cannot be the place where the
conclusion is smuggled in.  `prfHops` is
discharged from `le_add_self` by taking `idealAdvantage := adv.advantage`, which is free in `ℝ≥0∞`
— and that is the honest reading of it: **this constructor takes no PRF hop**, and in the
certificate it returns the two PRF summands are slack that does no work.  What is left unproven is
exactly the two arguments `hfors` and `hhyper`, the two branch bounds, which are the bulk of the
EasyCrypt development.

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
twelve advantages of the same eleven adversaries it was handed.

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

/-- **What the intended route leaves to prove**, as one statement: bound the two dispatch halves
by their games and the twelve-summand bound follows.

This is `advantage_le_bound` composed with `ofBranchBounds`, and it is the form in which that
obligation is smallest to state.  It is not the only way to reach the conclusion — the two
hypotheses here are stated at `forsHalf adv` and `hypertreeHalf adv`, which `Certificate` itself
does not require of any certificate, and the module docstring records what follows.

The two PRF summands on the right are slack — no PRF hop is taken — which is why the right-hand
side is written out here rather than hidden behind `Summands.bound`.

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

end BranchBounds

/-! ## Transporting a bound onto the two induced FORS-`F` games

`CanonicalGames`' `forsFDsprProblem` and `forsFTcrProblem` are the games the OpenPRE reductions
attack, and
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

/-- A DSPR bound quantified over adversaries against `CanonicalGames`' `forsFDsprProblem` applies
to the
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
/-- A TCR bound quantified over adversaries against `CanonicalGames`' `forsFTcrProblem` applies to
the
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

/-- The FORS-`F` block of the bound — `DSPR + 3·TCR` — under hypotheses stated at `CanonicalGames`'
two
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
