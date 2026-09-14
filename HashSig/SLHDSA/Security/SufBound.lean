/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.Security.Composition

/-!
# The strong-unforgeability residual bound

`HashSig.SLHDSA.Security.Composition` bounds the *existential* advantage against `generalAlg` by
the twelve-summand expression of `EUFCMA_SPHINCS_PLUS`.  This module carries that bound across
VCVio's SUF-to-EUF partition and names what the crossing costs.

## The statement

`SLHDSA.Security.strongAdvantage_le_bound_add_sameMessage`: for any strong-unforgeability adversary
`sadv` against `generalAlg`, and any `Certificate` for the existential adversary underneath it,

`sadv.advantage ProbCompRuntime.probComp ≤ c.summands.bound vp.params +`
`  sadv.sameMessageAdvantage ProbCompRuntime.probComp`

and `strongAdvantage_le_sufBound` refines the residual into the two named halves of
`HashSig.SLHDSA.Security.SchemeGames`, the fresh-randomizer one and the same-randomizer one.

## This adds nothing to the previous module's inequality, and that is a theorem here

Read `strongAdvantage_le_add_sameMessage_iff` before anything else.  For every `ε : ℝ≥0∞`,

`sadv.advantage ≤ ε + sadv.sameMessageAdvantage  ↔  sadv.toUnforgeableAdv.advantage ≤ ε`

— an equivalence, not an implication.  VCVio's partition is an *equality*,
`advantage = euf + sameMessage`, and the same-message term is a probability and so never `⊤`, so
it cancels: the residual written on the right is the same quantity as the one sitting inside the
left-hand side.  The headline is therefore the previous module's `advantage_le_bound`, restated at
a strong-unforgeability adversary, and it is exactly as strong and exactly as weak.  What this
module contributes is the naming and the argument, not the inequality.

Nor does splitting the residual recover anything.  `sameMessageAdvantage_eq_arms` proves that at
*any* selector the same-message advantage is the **sum** of the instrumented experiment's two arms —
an equality, which the module that owns the split states holds and does not prove, since the
`≤` direction is all a bound consumes — so
`strongAdvantage_le_add_arms_iff` is the same equivalence again, for every selector.  No
instrumentation of the residual makes the bound say more.

So the vacuity of this statement is the vacuity of the previous one, neither more nor less.  That
one is measured there and shipped as a canary: a closed `Certificate` is constructible at an
arbitrary validated parameter set, an arbitrary bundle and an arbitrary adversary from an address
key and a public seed, and the bound it names is at least one.  At that certificate this module's
headline reads `sadv.advantage ≤ (something ≥ 1) + residual`, which `probOutput_le_one` gives with
extra steps, and `HashSigTest.SLHDSA.SufBound` ships that reading too.

**What is not free is the residual itself.**  Every summand of `Summands.bound` is the advantage of
an adversary a certificate supplies, chosen with nothing tying it to `sadv`; the residual is a
probability of `sadv`'s own experiment, so it cannot be re-chosen, and the four bounds below —
each half by the advantage it splits and by its own branch — pin it from above at both ends.  What
is missing is a bound, not an anchor: nothing in this repository bounds either half, and the
same-randomizer one has nothing to route into.  The distinction matters because the two kinds of
looseness have different repairs, and only one of them is the EasyCrypt development.

## The same-randomizer term has no counterpart in the source, and here is the argument

`HashSig.SLHDSA.Security.SufResidual` establishes the negative fact; what follows is why it is a
fact about the two models rather than an omission, derived from the source rather than asserted.

**The source's signer is deterministic in the message.**  Its message key is
`op mkg : mseed -> msg -> mkey` (`SPHINCS_PLUS.ec:409`), a function of the master seed and the
message with no per-signature argument, and the signing oracle before the `MKG` hop computes
`mk <- mkg ms m` (`SPHINCS_PLUS.ec:2020`).  After the hop the oracle memoizes on the message —
`if (m \notin mmap) { mk <$ dmkey; mmap.[m] <- mk } mk <- oget mmap.[m]`
(`SPHINCS_PLUS.ec:2082-2086`) — and the hop's equivalence identifies that table with the generic
`PRF` oracle's own memo table, `O_CMA_SPHINCSPLUSTWFS_NPRF.mmap{1} = O_PRF_Default.m{2}`
(`SPHINCS_PLUS.ec:3112`).  On both sides of the hop, re-signing a message returns the identical
signature, so a transcript there carries **one randomizer per message** and the case this term
names is empty.

**The Lean signer is not.**  FIPS 205 Algorithm 19 sets `opt_rand ← addrnd` and then
`R ← PRF_msg(SK.prf, opt_rand, M)`; §9.2 makes that hedged variant the default and offers
`opt_rand ← PK.seed` as the deterministic alternative, under which signing the same message twice
gives the same signature.  `GeneralScheme.signInternalM` takes `addrnd` as an argument and
`SchemeGames.generalAlg`'s signer samples it per signature, so `SufResidual.loggedRandomizers` at
one message can hold as many distinct values as that message had queries, and the case is
reachable.

**And the source would not reach it in any case.**  Over the eleven `.ec`/`.eca` files the
case-insensitive tokens `strong` and `unforge` occur zero times and every occurrence matching `suf`
is the word `suff`; all twenty assignments to `is_fresh` test the *message* — `! m' \in qs`, a call
to a `fresh` procedure taking a `msg`, or a message disequality in the no-adaptivity games — and no
signature is compared anywhere.  So the source's ITSR pair-freshness conjunct is discharged by its
own game's message freshness, which is the step a strong-unforgeability freshness condition cannot
take.

Two independent reasons, then, and neither is an omission: the term is this lane's alone, the
source neither bounds it nor needs to, and no coefficient of `EUFCMA_SPHINCS_PLUS` may be
transcribed onto it.

**It is not zero either.**  On this branch the two signatures split to one digest against one
public key (`SufResidual.schemeParts_eq_of_randomizer_eq`) and differ in the FORS half or in the
hypertree half (`SufResidual.components_ne_of_ne_of_randomizer_eq`); `generalAlg.verify` accepts
whatever recomputes the honest root, which a second signature can do wherever the component hashes
collide.  That is the same event the games `Summands.bound` sums are about — so what is missing on
this branch is an extractor, not a hardness assumption.

**And it routes nowhere, which the lane's own theorems measure rather than assert.**  The `H_msg`
bridge is not merely unproved there, it is unavailable: the forged pair *is* one of the embedded
targets (`SufResidual.mem_embedTargets_of_mem_loggedRandomizers`), so the winning condition fails
on its freshness conjunct (`not_wins_of_mem_loggedRandomizers`), and the first-uncovered-index
extractor returns nothing (`findUncoveredIndex_eq_none_of_mem_loggedRandomizers`).  Three of the
four witness families cannot be handed the pair at all, because they compute their second object
from `sk`; the fourth, `findWotsWitness`, concludes validity against the *supplied* partner, so a
witness there is a collision between two adversarial objects rather than an attack on honest
committed material.  A same-digest extractor is a further witness module.

The fresh half is the one with somewhere to go: `SchemeGames.freshRandomizer_notMem_embedTargets`
and `freshRandomizer_wins_or_uncovered` carry it into the `H_msg` bridge.  Neither is consumed
here — bounding it is an adversary construction, which is the same deferral the previous module's
two branch bounds carry.

## What is not established

* **No bound on either half.**  `freshRandomizerHalf` and `sameRandomizerHalf` are named and
  bounded above by the advantage they split and by their own branches, and by nothing else.
  `strongAdvantage_le_bound_add_sameRandomizer_of_fresh_le` is the shape a bound on the fresh half
  would plug into; its hypothesis is not discharged anywhere.
* **The named halves are not identified with the arms.**  `sameMessageAdvantage_eq_arms` is an
  equality at an arbitrary selector, and at `SchemeGames.randomizerLogged` its two arms are the two
  named halves *in the module that defines them*.  That identification is not available here: the
  halves' bodies are not exposed, so a consumer gets `Type mismatch` with the note naming
  `freshRandomizerHalf` as not unfolded, and `unfold` fails outright.  The named refinement
  `strongAdvantage_le_sufBound` therefore goes through the exported `≤` and is, as far as anything
  stated here can tell, possibly strict.  An unfolding equation in the module that owns the halves
  would close it; adding one there is a change to that module's exported surface and is not made
  here.
* **Nothing about `SameMessageBinding`.**  VCVio's own docstring says no `ε < 1` can hold for a
  hash-based scheme, and issue #629 item 2b records that the per-adversary partition is what a
  quantitative result must consume.  This module consumes the partition.
* **Everything the previous module does not establish.**  No reduction adversary, no challenge
  recording, no final validity, no PRF hop, no undetectability hybrid, no query cap on the
  `MCO_ITSR` summand, and the Lean branch assignment is not the source's.  The `Certificate` this
  module takes is that module's, unchanged.

## Labels

Thirteen declarations, one definition and twelve theorems.

*Experiment split* — a statement about the same-message experiment or about the partition.  Six:

* `sameMessageAdvantage_eq_arms`, `sameMessageAdvantage_le_one`;
* `strongAdvantage_le_add_sameMessage_iff`, `strongAdvantage_le_add_arms_iff`;
* `freshRandomizerHalf_le_strongAdvantage`, `sameRandomizerHalf_le_strongAdvantage`.

*Residual arithmetic* — a statement about the bound expression this module writes.  Seven:

* `Summands.sufBound`, `Summands.sufBound_eq`, `sufBound_eq_bound_of_residuals_zero`;
* `strongAdvantage_le_bound_add_sameMessage`, `strongAdvantage_le_bound_add_arms`,
  `strongAdvantage_le_sufBound`,
  `strongAdvantage_le_bound_add_sameRandomizer_of_fresh_le`.

None is `private` and none carries `@[expose]`; `Summands.sufBound_eq` is what a consumer that
needs the expression's shape rewrites with, exactly as `Composition.Summands.bound_eq` is for the
twelve summands.

## References

- NIST FIPS 205, §9.2 and Algorithm 19 (the hedged and deterministic variants)
- Barbosa, Dupressoir, Hülsing, Meijers, and Strub, "A Tight Security Proof for SPHINCS+,
  Formally Verified" (`SPHINCS_PLUS.ec`, `FORS_ES.ec`)
-/

public section

namespace SLHDSA.Security

open OracleComp OracleSpec ENNReal SignatureAlg TweakableHash Security.CanonicalGames

universe u

/-! ## The same-message advantage is exactly the sum of the two arms -/

section Generic

variable {ι : Type u} {spec : OracleSpec ι} {M PK SK S : Type}
  [DecidableEq M] [DecidableEq S]

omit [DecidableEq M] [DecidableEq S] in
/-- **The same-message split is an equality.**  `SchemeGames.sameMessageAdvantage_le_arms` bounds
the same-message advantage by the sum of the instrumented experiment's two arms; the two arms are
disjoint and exhaust the success event, so the two are equal.

The module that owns the split records that equality holds and proves only the `≤` direction, on
the ground that `VCVio.EvalDist` offers `probEvent_or_le` and `probEvent_compl` and no
disjoint-union equality.  The missing step is one `tsum` congruence over `Bool × Bool` at
`probEvent_eq_tsum_ite`, and it is taken here because this module's subject is what the residual
costs: with only the `≤` direction a reader cannot tell whether instrumenting the residual weakens
the bound, and with the equality `strongAdvantage_le_add_arms_iff` says it does not.

The hypothesis is the runtime's pure-return factoring law, the same one the projection equation
takes; `ProbCompRuntime.probComp` satisfies it by `ProbCompRuntime.probComp_evalSPMF_bind_pure`.
The fresh arm is written first, matching
`SchemeGames.sameMessageAdvantage_le_freshRandomizer_add_sameRandomizer`.

*Experiment split.* -/
theorem sameMessageAdvantage_eq_arms {sigAlg : SignatureAlg (OracleComp spec) M PK SK S}
    (runtime : ProbCompRuntime (OracleComp spec))
    (h_pull : ∀ {α β : Type} (f : α → β) (mx : OracleComp spec α),
      runtime.evalSPMF (mx >>= fun x => pure (f x)) = f <$> runtime.evalSPMF mx)
    (adv : strongUnforgeableAdv sigAlg) (sel : QueryLog (M →ₒ S) → M → S → Bool) :
    adv.sameMessageAdvantage runtime =
      Pr[fun x => x.1 = true ∧ x.2 = false | instrumentedSameMessageExp runtime adv sel] +
      Pr[fun x => x.1 = true ∧ x.2 = true | instrumentedSameMessageExp runtime adv sel] := by
  rw [strongUnforgeableAdv.sameMessageAdvantage, sameMessageStrongUnforgeableExp_apply_singleton,
    instrumentedSameMessageExp_fst runtime h_pull adv sel, ← probEvent_eq_eq_probOutput,
    probEvent_map]
  classical
  simp only [probEvent_eq_tsum_ite, ← ENNReal.tsum_add]
  refine tsum_congr fun x => ?_
  obtain ⟨b, s⟩ := x
  cases b <;> cases s <;> simp

omit [DecidableEq M] [DecidableEq S] in
/-- The same-message advantage is a probability, so it is finite.  This is what makes the residual
cancel in `strongAdvantage_le_add_sameMessage_iff`: in `ℝ≥0∞` a summand may be added to both sides
of a `≤` and removed again only when it is not `⊤`.

*Experiment split.* -/
theorem sameMessageAdvantage_le_one {sigAlg : SignatureAlg (OracleComp spec) M PK SK S}
    (runtime : ProbCompRuntime (OracleComp spec)) (adv : strongUnforgeableAdv sigAlg) :
    adv.sameMessageAdvantage runtime ≤ 1 := by
  rw [strongUnforgeableAdv.sameMessageAdvantage, sameMessageStrongUnforgeableExp_apply_singleton]
  exact probOutput_le_one

end Generic

/-! ## The residual cancels

The two equivalences below are the module's honest core.  Each says that an inequality with the
residual added on the right is the *same statement* as the existential inequality without it, so
nothing that bounds the strong advantage this way can be stronger than what bounds the existential
one.  A reader who takes the headline for a strong-unforgeability result should read these
instead. -/

section Cancel

variable {vp : ValidatedParams} {prims : Primitives vp.params}
  [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.PkSeed]
  [SampleableType prims.Y] [DecidableEq prims.Y]

/-- **The residual carries no information.**  Bounding the strong advantage by anything *plus the
same-message advantage* is equivalent to bounding the existential advantage by that thing alone.

Forward and backward, so there is no reading on which the left-hand side is the weaker claim.  The
mechanism is VCVio's partition, which is an equality, together with the residual's finiteness: the
term added on the right is the term already inside the left.

*Experiment split.* -/
theorem strongAdvantage_le_add_sameMessage_iff (sadv : strongUnforgeableAdv (generalAlg prims))
    (ε : ℝ≥0∞) :
    sadv.advantage ProbCompRuntime.probComp ≤
        ε + sadv.sameMessageAdvantage ProbCompRuntime.probComp ↔
      sadv.toUnforgeableAdv.advantage ProbCompRuntime.probComp ≤ ε := by
  rw [strongAdvantage_eq_advantage_add_sameMessage sadv]
  exact ENNReal.add_le_add_iff_right
    (ne_top_of_le_ne_top one_ne_top (sameMessageAdvantage_le_one _ sadv))

/-- **Instrumenting the residual recovers nothing either.**  At every selector the two arms sum to
the same-message advantage, so the equivalence above holds verbatim with the residual split in two.

This is what rules out the reading that a cleverer split of the residual would make the bound say
more.  It does not rule out a *bound* on one arm making it say more —
`strongAdvantage_le_bound_add_sameRandomizer_of_fresh_le` is that statement, and its hypothesis is
not discharged anywhere.

*Experiment split.* -/
theorem strongAdvantage_le_add_arms_iff (sadv : strongUnforgeableAdv (generalAlg prims))
    (ε : ℝ≥0∞) (sel : QueryLog (List Byte →ₒ GeneralScheme.SignatureCore vp prims.core) →
      List Byte → GeneralScheme.SignatureCore vp prims.core → Bool) :
    sadv.advantage ProbCompRuntime.probComp ≤ ε +
        (Pr[fun x => x.1 = true ∧ x.2 = false |
            instrumentedSameMessageExp ProbCompRuntime.probComp sadv sel] +
          Pr[fun x => x.1 = true ∧ x.2 = true |
            instrumentedSameMessageExp ProbCompRuntime.probComp sadv sel]) ↔
      sadv.toUnforgeableAdv.advantage ProbCompRuntime.probComp ≤ ε := by
  rw [← sameMessageAdvantage_eq_arms ProbCompRuntime.probComp
    (fun f mx => ProbCompRuntime.probComp_evalSPMF_bind_pure f mx) sadv sel]
  exact strongAdvantage_le_add_sameMessage_iff sadv ε

/-- The fresh-randomizer half is at most the strong advantage it is a piece of.  Together with
`SchemeGames.freshRandomizerHalf_le_sameMessageAdvantage` and `freshRandomizerHalf_le_branch` this
pins it from above at every level between it and the headline.

*Experiment split.* -/
theorem freshRandomizerHalf_le_strongAdvantage (sadv : strongUnforgeableAdv (generalAlg prims)) :
    freshRandomizerHalf sadv ≤ sadv.advantage ProbCompRuntime.probComp := by
  rw [strongAdvantage_eq_advantage_add_sameMessage sadv]
  exact le_add_left (freshRandomizerHalf_le_sameMessageAdvantage sadv)

/-- The same-randomizer half is at most the strong advantage it is a piece of.  This is the only
thing this module proves *about* the term it holds out of scope, and it is an upper bound by a
quantity nothing bounds either.

*Experiment split.* -/
theorem sameRandomizerHalf_le_strongAdvantage (sadv : strongUnforgeableAdv (generalAlg prims)) :
    sameRandomizerHalf sadv ≤ sadv.advantage ProbCompRuntime.probComp := by
  rw [strongAdvantage_eq_advantage_add_sameMessage sadv]
  exact le_add_left (sameRandomizerHalf_le_sameMessageAdvantage sadv)

end Cancel

/-! ## The bound expression -/

/-- **The strong-unforgeability bound expression**: the twelve-summand existential bound of
`Composition.Summands.bound`, plus a fresh-randomizer residual, plus a same-randomizer residual.

The two residuals carry coefficient one and are added as a group, which is the association
`SchemeGames.strongAdvantage_le_halves` produces and the one
`sufBound_eq_bound_of_residuals_zero` pins.  Calling it a *bound* is a statement about the shape of
the expression and not about its size: its third argument is the term this lane holds out of scope,
and nothing here or anywhere in this repository bounds it.

*Residual arithmetic.* -/
noncomputable def Summands.sufBound (s : Summands) (p : Params) (fresh same : ℝ≥0∞) : ℝ≥0∞ :=
  s.bound p + (fresh + same)

/-- Unfolding equation for `Summands.sufBound`.  The body is not exposed, so this is what a
consumer that needs the three-part shape — the two unit coefficients included — rewrites with.

*Residual arithmetic.* -/
theorem Summands.sufBound_eq (s : Summands) (p : Params) (fresh same : ℝ≥0∞) :
    s.sufBound p fresh same = s.bound p + (fresh + same) := by
  rfl

/-- At zero residuals the expression is the existential bound: the two residuals are added and
nothing else is.  A coefficient other than one on either of them, or a stray additive constant,
fails it.

*Residual arithmetic.* -/
theorem sufBound_eq_bound_of_residuals_zero (s : Summands) (p : Params) :
    s.sufBound p 0 0 = s.bound p := by
  rw [Summands.sufBound_eq]
  simp

/-! ## The headline -/

section Headline

variable {vp : ValidatedParams} {prims : Primitives vp.params}
  [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.PkSeed]
  [SampleableType prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey]
  [DecidableEq prims.Y] [Fintype prims.Y] [Inhabited prims.Y]

/-- **The strong-unforgeability bound.**  The SUF-CMA advantage of any adversary against the
external SLH-DSA algebra is at most the twelve-summand expression its existential certificate
names, plus the same-message residual.

By `strongAdvantage_le_add_sameMessage_iff` this is `Composition.advantage_le_bound` and nothing
more: the residual on the right is the residual inside the left, and the two cancel.  So everything
that theorem does not say, this one does not say either — in particular its antecedent is free, and
`HashSigTest.SLHDSA.SufBound` exhibits the certificate at which this statement is
`probOutput_le_one` with extra steps.

What the statement *does* do is put the residual where a reader has to see it.  The previous
module's headline is about an existential adversary and is silent about strong unforgeability; this
one is about a strong-unforgeability adversary and carries, by name, the term that separates the
two.

*Residual arithmetic.* -/
theorem strongAdvantage_le_bound_add_sameMessage
    {sadv : strongUnforgeableAdv (generalAlg prims)}
    (c : Certificate prims sadv.toUnforgeableAdv) :
    sadv.advantage ProbCompRuntime.probComp ≤
      c.summands.bound vp.params + sadv.sameMessageAdvantage ProbCompRuntime.probComp :=
  (strongAdvantage_le_add_sameMessage_iff sadv _).mpr (advantage_le_bound c)

/-- **The headline with the residual instrumented**, at an arbitrary selector.  Its right-hand side
is equal to the headline's, by `sameMessageAdvantage_eq_arms`, so this is the same statement;
`strongAdvantage_le_add_arms_iff` is that reading as an equivalence.

It is stated because the named refinement below cannot be obtained from it: the two named halves
are this pair of arms at `SchemeGames.randomizerLogged`, but their defining equations are not
exported, so this module can bound the halves and cannot identify them.

*Residual arithmetic.* -/
theorem strongAdvantage_le_bound_add_arms {sadv : strongUnforgeableAdv (generalAlg prims)}
    (c : Certificate prims sadv.toUnforgeableAdv)
    (sel : QueryLog (List Byte →ₒ GeneralScheme.SignatureCore vp prims.core) →
      List Byte → GeneralScheme.SignatureCore vp prims.core → Bool) :
    sadv.advantage ProbCompRuntime.probComp ≤ c.summands.bound vp.params +
      (Pr[fun x => x.1 = true ∧ x.2 = false |
          instrumentedSameMessageExp ProbCompRuntime.probComp sadv sel] +
        Pr[fun x => x.1 = true ∧ x.2 = true |
          instrumentedSameMessageExp ProbCompRuntime.probComp sadv sel]) :=
  (strongAdvantage_le_add_arms_iff sadv _ sel).mpr (advantage_le_bound c)

/-- **The headline refined through the two named halves.**  The residual is replaced by the
fresh-randomizer half plus the same-randomizer half of
`HashSig.SLHDSA.Security.SchemeGames`, which is where the same-randomizer term acquires a name.

This one is a `≤` and not an equivalence, and the direction that is missing is measured rather than
assumed: the step it takes is
`SchemeGames.sameMessageAdvantage_le_freshRandomizer_add_sameRandomizer`, whose reverse is
`sameMessageAdvantage_eq_arms` at `SchemeGames.randomizerLogged` — true, proved above at every
selector, and not transportable to the named halves from here, because their bodies are not
exposed.  So this statement is possibly strict and this module cannot tell.

*Residual arithmetic.* -/
theorem strongAdvantage_le_sufBound {sadv : strongUnforgeableAdv (generalAlg prims)}
    (c : Certificate prims sadv.toUnforgeableAdv) :
    sadv.advantage ProbCompRuntime.probComp ≤
      c.summands.sufBound vp.params (freshRandomizerHalf sadv) (sameRandomizerHalf sadv) := by
  rw [Summands.sufBound_eq]
  refine le_trans (strongAdvantage_le_bound_add_sameMessage c) ?_
  gcongr
  exact sameMessageAdvantage_le_freshRandomizer_add_sameRandomizer sadv

/-- **What a bound on the fresh half would buy**, as one statement: with the fresh-randomizer half
bounded by `εfresh`, the strong advantage is at most the twelve summands plus `εfresh` plus the
same-randomizer half, and the same-randomizer half is then the only unbounded term left.

This is the shape the next slice's `H_msg` reduction plugs into, and it is the form in which the
residual's remaining cost is smallest to state.  Its hypothesis is not discharged here or anywhere
in this repository: bounding the fresh half is an adversary construction, the same deferral the
previous module's two branch bounds carry.

*Residual arithmetic.* -/
theorem strongAdvantage_le_bound_add_sameRandomizer_of_fresh_le
    {sadv : strongUnforgeableAdv (generalAlg prims)}
    (c : Certificate prims sadv.toUnforgeableAdv) (εfresh : ℝ≥0∞)
    (hfresh : freshRandomizerHalf sadv ≤ εfresh) :
    sadv.advantage ProbCompRuntime.probComp ≤
      c.summands.bound vp.params + εfresh + sameRandomizerHalf sadv := by
  refine le_trans (strongAdvantage_le_sufBound c) ?_
  rw [Summands.sufBound_eq, ← add_assoc]
  gcongr

end Headline

end SLHDSA.Security
