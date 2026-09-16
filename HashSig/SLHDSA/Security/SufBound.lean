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
`HashSig.SLHDSA.Security.SchemeGames`, the fresh-randomizer one and the same-randomizer one.  That
refinement is a `≤` because the halves' bodies are not exposed, and
`sufBound_eq_bound_add_sameMessage_of_unfoldings` says what that costs: take the two defining
equations that module proves and does not name as hypotheses, and the two right-hand sides are
equal, so the refinement is the headline and not a weakening of it.

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
an equality, where the module that owns the split proves only `≤`, since that direction is all a
bound consumes — so `strongAdvantage_le_add_arms_iff` is the same equivalence again, for every
selector.  No instrumentation of the residual makes the bound say more.

So the vacuity of this statement is the vacuity of the previous one, neither more nor less. That one
is exhibited there as a canary: a closed `Certificate` is constructible at an arbitrary validated
parameter set, an arbitrary bundle and an arbitrary adversary from an address key and a public seed,
and the bound it names is at least one. At that certificate this module's headline reads
`sadv.advantage ≤ (something ≥ 1) + residual`, which `probOutput_le_one` gives with extra steps, and
`HashSigTest.SLHDSA.SufBound` ships that reading too.

**What is not free is the residual itself.**  Every summand of `Summands.bound` is the advantage of
an adversary a certificate supplies, chosen with nothing tying it to `sadv`; the residual is a
probability of `sadv`'s own experiment, so it cannot be re-chosen at all.  Between the headline and
the two halves it is pinned above and below by named statements: `sameMessageAdvantage_eq_arms`
identifies it exactly with the two arms, `freshRandomizerHalf_le_strongAdvantage` and
`sameRandomizerHalf_le_strongAdvantage` put each half under the advantage this module bounds, and
`SchemeGames`' four half-bounds put each half under the advantage it splits and under its own
branch.  What is missing is a bound, not an anchor: nothing in this repository bounds either half,
and the same-randomizer one has nothing to route into.  The distinction matters because the two
kinds of looseness have different repairs, and only one of them is the EasyCrypt development.

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
signature, so a transcript there carries **one randomizer per message**.

That is the whole of the formulation difference, and it is narrower than it looks.  It does *not*
make the same-randomizer case empty: a second signature reusing a message's one randomizer is still
in it, and reusing the randomizer costs an adversary nothing, because the randomizer is a field of
the signature it was handed.  `HashSigTest.SLHDSA.SufBound` runs that at the deterministic
variant's own log, where the case is inhabited.  What the hedged default changes is the *size* of
the logged-randomizer list at a message, and so how hard the **fresh** branch is to reach.
`HashSig.SLHDSA.Security.SufResidual` states the same boundary: deterministic signing narrows
the logged-randomizer list without emptying the second branch.

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

Two independent reasons, then, and neither is an omission: the source's game never reaches the case
because its freshness test is on the message alone, and its signer could not have populated the
logged-randomizer list as widely if it had.  So the term is this lane's alone, the source neither
bounds it nor needs to, and no coefficient of `EUFCMA_SPHINCS_PLUS` may be transcribed onto it.

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

## What fixes this module's claims, and where nothing does

Four things about this module are held in place by the fixture alone or by nothing at all.

* **The two equivalences, weakened to implications.** `strongAdvantage_le_add_sameMessage_iff` and
  `strongAdvantage_le_add_arms_iff` restated as `euf ≤ ε → advantage ≤ ε + residual`, with both
  consumers repaired, leave this module well-formed; only the two fixture pins that restate them
  refuse it. An edit that moves the fixture too is silent.
* **Which half the consumption form bounds.**
  `strongAdvantage_le_bound_add_sameRandomizer_of_fresh_le` takes a bound on the fresh half. The
  mirror statement, taking one on the same-randomizer half, is equally true and equally provable,
  and is refused by one fixture pin only; move that pin and **nothing** refuses it. What decides
  which is right is the argument above — the fresh branch has the `H_msg` bridge and the other has
  nothing — and not a check.
* **The order of the two residuals in `Summands.sufBound`, and their association.** Swapping them or
  reassociating the sum leaves this module provable once its four proofs are repaired, and is
  refused by three fixture entries either way; an edit that moves those entries too changes the
  claim rather than being caught. Two neighbouring edits are *not* in this class. A coefficient
  other than one on a residual makes `sufBound_eq_bound_add_sameMessage_of_unfoldings` false, and is
  refused there and nowhere else here. A stray additive constant makes both it and
  `sufBound_eq_bound_of_residuals_zero` false, and the zero law refuses such a constant
  independently of the statement beside it.
* **The strength of the certificate.** Inherited unchanged from
  `HashSig.SLHDSA.Security.Composition`: nothing refuses a certificate, and the fixture there builds
  one from an address key and a public seed. Adding the residual does not touch that question, which
  is why this module's vacuity is exactly that module's.

## What is not established

* **No bound on either half.**  `freshRandomizerHalf` and `sameRandomizerHalf` are named and
  bounded above by the advantage they split and by their own branches, and by nothing else.
  `strongAdvantage_le_bound_add_sameRandomizer_of_fresh_le` is the shape a bound on the fresh half
  would plug into; its hypothesis is not discharged anywhere.
* **The named halves are not identified with the arms, and what is missing is written down.**
  `sameMessageAdvantage_eq_arms` is an equality at an arbitrary selector, and at
  `SchemeGames.randomizerLogged` its two arms are the two named halves *in the module that defines
  them*. That identification is not available here: the halves' bodies are not exposed, so a
  consumer's `rfl` is refused and `unfold` fails outright. The named refinement
  `strongAdvantage_le_sufBound` therefore goes through the exported `≤` and is, as far as anything
  proved here can tell, possibly strict. What closes it is the halves' two defining equations — not
  one, and not an `@[expose]`: the module that owns them already proves both by `rfl`, as two
  unnamed `example`s, so naming them there is a pure addition to it. Naming their *consequence*
  there is not: that module's own same-message split is a `≤`, and the equality the consequence
  needs is `sameMessageAdvantage_eq_arms` above, which would have to move down beside it.
  `sameMessageAdvantage_eq_halves_of_unfoldings` and
  `sufBound_eq_bound_add_sameMessage_of_unfoldings` take the two equations as hypotheses and draw
  the consequence, so the gap is one named theorem wide — the two equations, or, with the arms
  equality moved down beside them, the single joint equality they give — and that theorem belongs
  one module down, where it is not stated.
* **Nothing about `SameMessageBinding`.** No `ε < 1` holds of it for a hash-based scheme, as VCVio's
  own docstring records, so a quantitative result must consume the per-adversary partition instead.
  This module consumes the partition.
* **Everything the previous module does not establish.**  No reduction adversary, no challenge
  recording, no final validity, no PRF hop, no undetectability hybrid, no query cap on the
  `MCO_ITSR` summand, and the Lean branch assignment is not the source's.  The `Certificate` this
  module takes is that module's, unchanged.

## Labels

Fifteen declarations, one definition and fourteen theorems.

*Experiment split* — a statement about the same-message experiment or about the partition.  Seven:

* `sameMessageAdvantage_eq_arms`, `sameMessageAdvantage_le_one`;
* `strongAdvantage_le_add_sameMessage_iff`, `strongAdvantage_le_add_arms_iff`;
* `freshRandomizerHalf_le_strongAdvantage`, `sameRandomizerHalf_le_strongAdvantage`;
* `sameMessageAdvantage_eq_halves_of_unfoldings`.

*Residual arithmetic* — a statement about the bound expression this module writes.  Eight:

* `Summands.sufBound`, `Summands.sufBound_eq`, `sufBound_eq_bound_of_residuals_zero`;
* `strongAdvantage_le_bound_add_sameMessage`, `strongAdvantage_le_bound_add_arms`,
  `strongAdvantage_le_sufBound`,
  `strongAdvantage_le_bound_add_sameRandomizer_of_fresh_le`;
* `sufBound_eq_bound_add_sameMessage_of_unfoldings`.

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

/-- **The same-message split is an equality.**  `SchemeGames.sameMessageAdvantage_le_arms` bounds
the same-message advantage by the sum of the instrumented experiment's two arms; the two arms are
disjoint and exhaust the success event, so the two are equal.

Where the module that owns the split records that equality holds is its *dispatch* split,
`SchemeGames.advantage_le_arms`, on the ground that `VCVio.EvalDist` offers `probEvent_or_le`,
`probEvent_le_add_of_imp_or` and `probEvent_compl` and no disjoint-union equality; there it proves
only the `≤` direction, and `SchemeGames.sameMessageAdvantage_le_arms` claims no equality either.
The same `tsum` congruence over `Bool × Bool` at `probEvent_eq_tsum_ite` gives both, and this module
takes it for the same-message one because this module's subject is what the residual costs: with
only the `≤` direction a reader cannot tell whether instrumenting the residual weakens the bound,
and with the equality `strongAdvantage_le_add_arms_iff` says it does not.  The dispatch one is left
alone here, and the same argument would sharpen it.

The hypothesis is the runtime's pure-return factoring law, the same one the projection equation
takes; `ProbCompRuntime.probComp` satisfies it by `ProbCompRuntime.probComp_evalSPMF_bind_pure`.
The fresh arm is written first, matching
`SchemeGames.sameMessageAdvantage_le_freshRandomizer_add_sameRandomizer` rather than
`sameMessageAdvantage_le_arms`, whose two summands are in the other order; so this is that lemma's
missing direction up to `add_comm` and not literally.

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
more.  It does not rule out a *bound* on one half making it say more —
`strongAdvantage_le_bound_add_sameRandomizer_of_fresh_le` is that statement, at the fresh half, and
its hypothesis is not discharged anywhere.

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

The two residuals are added as a group, which is the association
`SchemeGames.strongAdvantage_le_halves` produces and the one `HashSigTest.SLHDSA.SufBound`'s
`sufBound` examples pin; `sufBound_eq_bound_of_residuals_zero` fixes the value at zero residuals and
says nothing about the residuals themselves.  That they carry coefficient one is pinned here, by
`sufBound_eq_bound_add_sameMessage_of_unfoldings`, whose equation a coefficient makes false.

Calling it a *bound* is a statement about the shape of the expression and not about its size.  The
same-randomizer residual is the term this lane holds out of scope, and nothing here or anywhere in
this repository bounds it; `s.bound p` is not bounded either, since the vacuity canary that
`HashSigTest.SLHDSA.SufBound` rebuilds constructs a certificate at which it is freely at least one.

*Residual arithmetic.* -/
noncomputable def Summands.sufBound (s : Summands) (p : Params) (fresh same : ℝ≥0∞) : ℝ≥0∞ :=
  s.bound p + (fresh + same)

/-- Unfolding equation for `Summands.sufBound`.  The body is not exposed, so this is what a
consumer that needs the three-part shape — the two unit coefficients included — rewrites with.

*Residual arithmetic.* -/
theorem Summands.sufBound_eq (s : Summands) (p : Params) (fresh same : ℝ≥0∞) :
    s.sufBound p fresh same = s.bound p + (fresh + same) := by
  rfl

/-- At zero residuals the expression is the existential bound.  It fixes the value at zero
residuals only: it constrains neither the residuals' coefficients, nor their order, nor the
association of the sum, nor whether either residual appears in the body at all. What refuses an edit
that moves the value is this statement — a stray additive constant, or a second copy of `s.bound p`.
What fixes the order and the association is `HashSigTest.SLHDSA.SufBound`'s `sufBound` examples;
what fixes the coefficients is those and `sufBound_eq_bound_add_sameMessage_of_unfoldings`.

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

This one is a `≤` and not an equivalence, and the direction that is missing is named rather than
assumed away: the step it takes is
`SchemeGames.sameMessageAdvantage_le_freshRandomizer_add_sameRandomizer`, whose reverse is
`sameMessageAdvantage_eq_arms` at `SchemeGames.randomizerLogged` — true, proved above at every
selector, and not transportable to the named halves from here, because their bodies are not exposed.
So this statement is possibly strict and this module cannot tell; what would settle it, and nothing
more, is the pair of hypotheses `sufBound_eq_bound_add_sameMessage_of_unfoldings` takes.

Like the headline, it says nothing about the size of what it bounds by:
`HashSigTest.SLHDSA.SufBound.freeCertificate_sufBound_headline` exhibits a certificate at which
this right-hand side is at least one.

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
same-randomizer half, and the same-randomizer half is then the only term not fixed by a hypothesis
of this statement.  It is not the only unbounded one: `c.summands.bound vp.params` is free too, as
the vacuity canary shows.

This is the shape an `H_msg` reduction plugs into, and it is the form in which the residual's
remaining cost is smallest to state. Its hypothesis is not discharged here or anywhere in this
repository: bounding the fresh half is an adversary construction, the same deferral the previous
module's two branch bounds carry.

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

/-! ## How far the refinement is from exact

`strongAdvantage_le_sufBound` reaches the two named halves through
`SchemeGames.sameMessageAdvantage_le_freshRandomizer_add_sameRandomizer`, a `≤`, so nothing above
says whether it is strict.  The two statements here say exactly what is missing: the halves'
defining equations, which the module that defines them proves by `rfl` and does not name.  Supply
them and the refinement's right-hand side *is* the headline's, so the two statements are one. -/

section Exactness

variable {vp : ValidatedParams} {prims : Primitives vp.params}
  [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.PkSeed]
  [SampleableType prims.Y] [DecidableEq prims.Y]

/-- **The same-message advantage is the sum of the two named halves**, given their defining
equations.  This is `sameMessageAdvantage_eq_arms` at `SchemeGames.randomizerLogged`, transported
along the two hypotheses.

Neither hypothesis is discharged here and neither can be: `freshRandomizerHalf` and
`sameRandomizerHalf` are `noncomputable def`s in `HashSig.SLHDSA.Security.SchemeGames` whose bodies
that module does not expose, so a consumer's `rfl` reports that the two sides are not definitionally
equal and names the half as a definition it could not unfold. Inside that module both are `rfl`, and
it already proves both, as two unnamed `example`s beside its four half-bounds. Naming them there is
a pure addition to that module and would discharge these two hypotheses at every call site. Naming
this conclusion there instead, where it would need no hypotheses, is not a pure addition: that
module's own same-message split is a `≤`, so the conclusion would carry
`sameMessageAdvantage_eq_arms` down with it. That is where this statement belongs, and it is not
stated there; here it can only take the two equations as hypotheses, which is what it does.

*Experiment split.* -/
theorem sameMessageAdvantage_eq_halves_of_unfoldings
    (sadv : strongUnforgeableAdv (generalAlg prims))
    (hfresh : freshRandomizerHalf sadv =
      Pr[ fun x => x.1 = true ∧ x.2 = false |
        instrumentedSameMessageExp ProbCompRuntime.probComp sadv
          (randomizerLogged (prims := prims))])
    (hsame : sameRandomizerHalf sadv =
      Pr[ fun x => x.1 = true ∧ x.2 = true |
        instrumentedSameMessageExp ProbCompRuntime.probComp sadv
          (randomizerLogged (prims := prims))]) :
    sadv.sameMessageAdvantage ProbCompRuntime.probComp =
      freshRandomizerHalf sadv + sameRandomizerHalf sadv := by
  rw [hfresh, hsame]
  exact sameMessageAdvantage_eq_arms ProbCompRuntime.probComp
    (fun f mx => ProbCompRuntime.probComp_evalSPMF_bind_pure f mx) sadv
    (randomizerLogged (prims := prims))

/-- **The refinement is exact**, given the same two equations: at the two named halves the bound
expression is the headline's right-hand side, so `strongAdvantage_le_sufBound` and
`strongAdvantage_le_bound_add_sameMessage` are the same inequality and the first is not strict.

Without the two equations this module can only say `≤`, which is what
`strongAdvantage_le_sufBound`'s docstring records.  With them the gap closes for any `s` and `p`,
the certificate's included.

*Residual arithmetic.* -/
theorem sufBound_eq_bound_add_sameMessage_of_unfoldings (s : Summands) (p : Params)
    (sadv : strongUnforgeableAdv (generalAlg prims))
    (hfresh : freshRandomizerHalf sadv =
      Pr[ fun x => x.1 = true ∧ x.2 = false |
        instrumentedSameMessageExp ProbCompRuntime.probComp sadv
          (randomizerLogged (prims := prims))])
    (hsame : sameRandomizerHalf sadv =
      Pr[ fun x => x.1 = true ∧ x.2 = true |
        instrumentedSameMessageExp ProbCompRuntime.probComp sadv
          (randomizerLogged (prims := prims))]) :
    s.sufBound p (freshRandomizerHalf sadv) (sameRandomizerHalf sadv) =
      s.bound p + sadv.sameMessageAdvantage ProbCompRuntime.probComp := by
  rw [Summands.sufBound_eq, sameMessageAdvantage_eq_halves_of_unfoldings sadv hfresh hsame]

end Exactness

end SLHDSA.Security
