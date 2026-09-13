/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.Security.SufResidual

/-!
# The SLH-DSA scheme games, and the two experiment splits

This is the first module in the security lane with probabilistic content.  Everything before it is
deterministic: a witness family, a ledger membership, a log reading.  What this module adds is the
external `SignatureAlg` the arbitrary-`d` construction packages to, and two *splits* of its
experiments — an upper bound of one advantage by the two probabilities of one instrumented
experiment that returns the success bit paired with a decidable bit read off the same run.

## The two splits, and what a split is worth

A split is a union bound, not an identity, and neither of its two terms is bounded here.  What the
instrumentation buys is that each term is a probability of a *named event of one experiment*, so a
later slice can bound each separately without re-deriving the experiment, and so the term that
cannot be bounded at all is one named summand rather than an unquantified caveat.

* **The dispatch split.**  `advantage_le_forsHalf_add_hypertreeHalf` bounds the EUF-CMA advantage of
  an adversary against `generalAlg` by `forsHalf + hypertreeHalf`, the two probabilities of the
  instrumented experiment at the selector `forsArm`.  `forsArm` recomputes, from the key pair the
  experiment sampled and the message and signature the adversary returned, the FORS public-key
  comparison `HashSig.SLHDSA.Security.SchemeWitnesses`' dispatch splits on.  The deterministic
  content is that module's; what is new is that the two branches are events of a probability space.
* **The same-message split.**  `sameMessageAdvantage_le_freshRandomizer_add_sameRandomizer` does the
  same to `SignatureAlg.sameMessageStrongUnforgeableGame`, at the selector `randomizerLogged`, which
  is the `by_cases` of `HashSig.SLHDSA.Security.SufResidual`'s `itsrFresh_or_sameRandomizer`.  With
  the library's own exact partition `strongUnforgeableAdv.advantage_eq_euf_add_sameMessage` this
  gives `strongAdvantage_le_halves`: the SUF-CMA advantage is bounded by four named terms, of which
  `sameRandomizerHalf` is the one this lane holds out of scope and now holds out of scope *by name*.

## What the two selectors read, and what they cannot read

`forsArm` reads the key pair, the message and the signature, and no log.  It reads the signature
through its FORS half and through the digest only; two signatures that share a randomizer, a message
and a FORS half take the same arm however their hypertree halves differ, and
`HashSigTest.SLHDSA.SchemeGames` exhibits such a pair.  It reads the *secret* key, so neither half
is a quantity a reduction can compute — they are events of the experiment, which is all a union
bound needs and less than a reduction needs.

`randomizerLogged` reads the signing log, at one message, and nothing else.  Membership in a list is
invariant under permutation and under de-duplication, so no fixture can make a reordering or a
collapsing of the log visible through this predicate; the test module records that as a property of
the predicate rather than a gap in its own data.

## The external message, which is where a silent error lives

`generalAlg` is the *external* API: it signs and verifies `emptyContextMessage msg`, the FIPS 205
§10 empty-context encoding `0x00 || 0x00 || M`, while the adversary's forged message and the signing
log's keys are the raw `msg`.  Two consequences, both of which a statement can get wrong without a
type error.

* `forsArm` must split the digest of the *internal* message.  A selector applied to the raw `msg`
  is a different, silently wrong predicate: it still has type `Bool`, and every statement below
  still elaborates.  What separates the two is a fixture at a bundle whose `H_msg` can see two
  prefixed zero bytes — which is a real condition and not an automatic one: the fixture this lane
  inherited folds a message by exclusive-or, which cannot, and `HashSigTest.SLHDSA.SchemeGames`
  asserts that blindness before replacing the fold.
* The `H_msg` transcript a reduction records is the transcript of the *internal* messages, so the
  log has to be internalised before `HashSig.SLHDSA.Security.SufResidual`'s transport lemmas apply
  to it.  `internalLog` is that map and `loggedSignatures_internalLog` is what makes it harmless:
  `emptyContextMessage` is injective, so internalising the log moves the transcript without moving
  any per-message reading of it.  Stating the `H_msg` consequences at the raw log instead would be
  a claim about a transcript the honest signer never produced.

## What is not established

The union bound is over the experiment's own runs.  Nothing here constructs a reduction adversary,
records a challenge, exhibits a target transcript that an actual execution produced, or bounds
either half of either split by a hardness advantage.  In particular:

* `forsHalf` is not the FORS half's advantage in any game.  It is the probability that the forgery
  succeeds *and* recovers the honest FORS public key; turning that into a bound on a FORS game is
  the adversary construction the eight review records of this stack all name as outstanding.
* `sameRandomizerHalf` has no source counterpart and no bound.  What it *has* is
  `sameRandomizer_of_randomizerLogged`: on that branch the adversary's signature comes with a
  logged signature at the same message carrying the same randomizer, splitting to the same digest
  and differing in one of the two component halves — the four facts of the right disjunct of
  `itsrFresh_or_sameRandomizer`, which is a statement about two adversarial signatures and not
  about honest committed material.
* The secret key the *dispatch* selector reads is the experiment's, so that split says nothing about
  what a reduction which does not hold the secret key can observe.  The same-message selector reads
  only the signing log, which such a reduction does hold — and bounds nothing either.
* No PRF hop is taken: `generalAlg` derives its FORS secret values and its message randomizer from
  the seeds through `prims.PRF` and `prims.PRFmsg`, exactly as `GeneralScheme` does.

What *is* established about the algebra itself is `generalAlg_perfectlyComplete`: honest signatures
verify with probability one, so neither bound is a statement about a scheme that accepts nothing.

## Correspondence with the EasyCrypt development

The dispatch selector is the case `valid_MFORSTWESNPRF <- pkFORS' = pkFORS` of `SPHINCS_PLUS.ec`,
and the split of a probability on it is that file's `mu_split` inside `EUFCMA_SPHINCS_PLUS_FX`.  The
qualifier `HashSig.SLHDSA.Security.SchemeWitnesses` records applies here unchanged and is the reason
no coefficient is transcribed: the source takes that split *after* both PRF hops, at a game whose
FORS secret values are sampled rather than derived, and this split is taken before either hop.  The
same-message split has no source counterpart at all — `SufResidual` establishes that strong
unforgeability does not occur in the development.

## Labels

Forty-eight declarations, twenty-two of them about a probability.

*Experiment split* — a statement about a probability of an experiment, or about what one run of
one produced:

* `instrumentedEufExp`, `instrumentedEufExp_fst`, `advantage_le_arms`;
* `instrumentedSameMessageExp`, `instrumentedSameMessageExp_fst`, `sameMessageAdvantage_le_arms`;
* `forsHalf`, `hypertreeHalf`, `advantage_le_forsHalf_add_hypertreeHalf`;
* `freshRandomizerHalf`, `sameRandomizerHalf`,
  `sameMessageAdvantage_le_freshRandomizer_add_sameRandomizer`;
* `forsHalf_le_advantage`, `hypertreeHalf_le_advantage`,
  `sameRandomizerHalf_le_sameMessageAdvantage`, `freshRandomizerHalf_le_sameMessageAdvantage`,
  the four that bound each half by the advantage it splits;
* `strongAdvantage_eq_advantage_add_sameMessage`, `strongAdvantage_le_halves`;
* `honestKey_of_mem_support`, `findWitness_isSome_of_mem_support`, `exists_witness_of_mem_support`,
  the three that read the key pair off the support of key generation;
* `generalAlg_perfectlyComplete`, which is what keeps both bounds from being about a signature
  algebra that verifies nothing.

*Deterministic inclusion* — a statement whose free objects are a primitive bundle, seeds, a public
key, a message, a signature and witness data:

* `generalAlg`, `generalAlg_keygen`, `generalAlg_sign`, `generalAlg_verify`,
  `generalAlg_keygen_eq`;
* `emptyContextMessage_injective`;
* `forsArm`, `forsArm_eq_true_iff`, `forsArm_eq_false_iff`;
* `findWitness_eq_fors_of_forsArm`, `findWitness_eq_hypertree_of_forsArm`,
  `witness_eq_fors_of_forsArm`, `exists_hypertree_witness_of_forsArm_eq_false`.

*Transcript transport* — a statement about a signing log or a role ledger:

* `internalLog`, `internalLog_eq`, `loggedSignatures_internalLog`,
  `loggedRandomizers_internalLog`, `logQueries_internalLog`, `signingLogContains_internalLog`;
* `randomizerLogged`, `randomizerLogged_eq_true_iff`, `randomizerLogged_eq_false_iff`;
* `freshRandomizer_notMem_embedTargets`, `freshRandomizer_wins_or_uncovered`,
  `sameRandomizer_of_randomizerLogged`, `itsrFresh_or_sameRandomizer_external`.

Those forty-eight are the module's whole interface; none is `private`, and `generalAlg` is the one
that carries `@[expose]`.

The six generic declarations of the first section are stated over an arbitrary `SignatureAlg` and
are not SLH-DSA-specific.  They are here rather than in `VCVio.CryptoFoundations.SignatureAlg`
because this slice already edits one merged module; promoting them is a six-declaration move that
would leave the two selectors behind as the only SLH-DSA content, and it is left to the maintainer.
None of the six mentions an SLH-DSA type; the target file, if they move, is
`VCVio/CryptoFoundations/SignatureAlg.lean`, beside the two experiments whose bodies they duplicate.

## References

- NIST FIPS 205, §9, Algorithms 18--20, and §10 for the external-message encoding
- Barbosa, Dupressoir, Hülsing, Meijers, and Strub, "A Tight Security Proof for SPHINCS+,
  Formally Verified" (`SPHINCS_PLUS.ec`)
-/

public section

namespace SLHDSA.Security

open OracleComp OracleSpec ENNReal SignatureAlg Security.CanonicalGames KeyedHash

universe u

/-! ## The instrumented experiments

Stated over an arbitrary signature algebra, because nothing about them is SLH-DSA-specific: a
selector is any decidable function of what one run of the experiment already computed. -/

section Generic

variable {ι : Type u} {spec : OracleSpec ι} {M PK SK S : Type}
  [DecidableEq M] [DecidableEq S]

/-- The EUF-CMA experiment of `VCVio.CryptoFoundations.SignatureAlg`, returning the success bit
paired with a selector bit read off the same run.

The body is `SignatureAlg.unforgeableExp`'s with one component added to the final `return`.  It
opens with the same two `letI : DecidableEq _ := Classical.decEq _` lines that experiment opens
with, and it has to — though not by the mechanism the shape suggests.  Dropping them puts
`[DecidableEq M]` and `[DecidableEq S]` back into this definition's signature, which makes the
`omit`s below illegal — `cannot omit referenced section variable`, at the first two of them — and
then leaves the two dispatch halves and their two `example`s unable to synthesize
`DecidableEq (GeneralScheme.SignatureCore vp prims.core)`, and the two `_le_advantage` theorems
with unsolved goals.  Measured: eight errors, and no `congr` step is ever reached.

The selector is a function of the sampled key pair and the returned pair.  It may read the *secret*
key, so a selector is not in general something a reduction can evaluate; what a union bound needs is
only that the two events partition the success event, which any `Bool`-valued function of the run
gives.

The result type is the runtime's subdistribution reading of a pair of bits and is left to
inference, as `SignatureAlg.unforgeableExp` leaves its own: writing it out is the direct
finite-distribution coupling that `scripts/check-pmf-boundary.sh` ratchets, and the annotation
would put this module over a ceiling of zero for no gain in what the definition says.

*Experiment split.* -/
noncomputable def instrumentedEufExp {sigAlg : SignatureAlg (OracleComp spec) M PK SK S}
    (runtime : ProbCompRuntime (OracleComp spec)) (adv : unforgeableAdv sigAlg)
    (sel : PK → SK → M → S → Bool) :=
  letI : DecidableEq M := Classical.decEq M
  letI : DecidableEq S := Classical.decEq S
  runtime.evalSPMF do
    let (pk, sk) ← sigAlg.keygen
    let impl : QueryImpl (spec + (M →ₒ S))
        (WriterT (QueryLog (M →ₒ S)) (OracleComp spec)) :=
      (HasQuery.toQueryImpl (spec := spec) (m := OracleComp spec)).liftTarget
        (WriterT (QueryLog (M →ₒ S)) (OracleComp spec)) +
        sigAlg.signingOracle pk sk
    let simAdv : WriterT (QueryLog (M →ₒ S)) (OracleComp spec) (M × S) :=
      simulateQ impl (adv.main pk)
    let ((msg, σ), log) ← simAdv.run
    let verified ← sigAlg.verify pk msg σ
    return (!log.wasQueried msg && verified, sel pk sk msg σ)

omit [DecidableEq M] [DecidableEq S] in
/-- **The projection equation.**  Forgetting the selector bit recovers the experiment.

The hypothesis is the runtime's pure-return factoring law, the same one
`strongUnforgeableAdv.advantage_eq_euf_add_sameMessage` takes; `ProbCompRuntime.probComp` satisfies
it by `ProbCompRuntime.probComp_evalSPMF_bind_pure`.  It is what lets the two `return`s be compared
without evaluating either computation: both are one joint execution followed by a pure function of
its result, and the law pulls that function out of the evaluator.

Neither `[DecidableEq M]` nor `[DecidableEq S]` is used, because both computations supply their own
classical instances; the `omit` records that rather than leaving the binders to be inferred as
load-bearing.

*Experiment split.* -/
theorem instrumentedEufExp_fst {sigAlg : SignatureAlg (OracleComp spec) M PK SK S}
    (runtime : ProbCompRuntime (OracleComp spec))
    (h_pull : ∀ {α β : Type} (f : α → β) (mx : OracleComp spec α),
      runtime.evalSPMF (mx >>= fun x => pure (f x)) = f <$> runtime.evalSPMF mx)
    (adv : unforgeableAdv sigAlg) (sel : PK → SK → M → S → Bool) :
    unforgeableExp runtime adv = Prod.fst <$> instrumentedEufExp runtime adv sel := by
  rw [unforgeableExp, instrumentedEufExp, ← h_pull Prod.fst]
  congr 1
  simp

omit [DecidableEq M] [DecidableEq S] in
/-- **The dispatch split, generically.**  The advantage is at most the sum of the two selector
branches of the success event.

This is an inequality and not an equality, and the inequality is the only direction a union bound
gives.  The two events are in fact disjoint and their union is the success event, so equality holds.
What `VCVio.EvalDist` offers on that surface is `probEvent_or_le`, `probEvent_le_add_of_imp_or` and
`probEvent_compl`, all inequalities or complements, and no disjoint-union equality; the `≤`
direction is what a bound consumes, so no equality is claimed and none is proved.

*Experiment split.* -/
theorem advantage_le_arms {sigAlg : SignatureAlg (OracleComp spec) M PK SK S}
    (runtime : ProbCompRuntime (OracleComp spec))
    (h_pull : ∀ {α β : Type} (f : α → β) (mx : OracleComp spec α),
      runtime.evalSPMF (mx >>= fun x => pure (f x)) = f <$> runtime.evalSPMF mx)
    (adv : unforgeableAdv sigAlg) (sel : PK → SK → M → S → Bool) :
    adv.advantage runtime ≤
      Pr[fun x => x.1 = true ∧ x.2 = true | instrumentedEufExp runtime adv sel] +
      Pr[fun x => x.1 = true ∧ x.2 = false | instrumentedEufExp runtime adv sel] := by
  rw [unforgeableAdv.advantage, instrumentedEufExp_fst runtime h_pull adv sel,
    ← probEvent_eq_eq_probOutput, probEvent_map]
  refine le_trans (probEvent_mono ?_) (probEvent_or_le _ _ _)
  rintro ⟨b, s⟩ _ hx
  cases s
  · exact Or.inr ⟨hx, rfl⟩
  · exact Or.inl ⟨hx, rfl⟩

/-- The same-message, new-signature event of `SignatureAlg.sameMessageStrongUnforgeableGame`,
returning its own bit paired with a selector bit.

The selector takes the signing log rather than the key pair, because the residual this
instrumentation exists to split is a statement about what the log returned.  It could take both;
it takes what the SLH-DSA selector reads, and a wider argument list would be three unused binders.

*Experiment split.* -/
noncomputable def instrumentedSameMessageExp
    {sigAlg : SignatureAlg (OracleComp spec) M PK SK S}
    (runtime : ProbCompRuntime (OracleComp spec)) (adv : strongUnforgeableAdv sigAlg)
    (sel : QueryLog (M →ₒ S) → M → S → Bool) :=
  letI : DecidableEq M := Classical.decEq M
  letI : DecidableEq S := Classical.decEq S
  runtime.evalSPMF do
    let (pk, sk) ← sigAlg.keygen
    let impl : QueryImpl (spec + (M →ₒ S))
        (WriterT (QueryLog (M →ₒ S)) (OracleComp spec)) :=
      (HasQuery.toQueryImpl (spec := spec) (m := OracleComp spec)).liftTarget
        (WriterT (QueryLog (M →ₒ S)) (OracleComp spec)) +
        sigAlg.signingOracle pk sk
    let simAdv : WriterT (QueryLog (M →ₒ S)) (OracleComp spec) (M × S) :=
      simulateQ impl (adv.main pk)
    let ((msg, σ), log) ← simAdv.run
    let verified ← sigAlg.verify pk msg σ
    return (log.wasQueried msg && !signingLogContains log msg σ && verified, sel log msg σ)

omit [DecidableEq M] [DecidableEq S] in
/-- The projection equation for the same-message experiment.

*Experiment split.* -/
theorem instrumentedSameMessageExp_fst {sigAlg : SignatureAlg (OracleComp spec) M PK SK S}
    (runtime : ProbCompRuntime (OracleComp spec))
    (h_pull : ∀ {α β : Type} (f : α → β) (mx : OracleComp spec α),
      runtime.evalSPMF (mx >>= fun x => pure (f x)) = f <$> runtime.evalSPMF mx)
    (adv : strongUnforgeableAdv sigAlg) (sel : QueryLog (M →ₒ S) → M → S → Bool) :
    runtime.evalSPMF (sameMessageStrongUnforgeableGame adv) =
      Prod.fst <$> instrumentedSameMessageExp runtime adv sel := by
  rw [instrumentedSameMessageExp, ← h_pull Prod.fst]
  congr 1
  rw [sameMessageStrongUnforgeableGame]
  simp

omit [DecidableEq M] [DecidableEq S] in
/-- **The same-message split, generically.**  The same-message advantage is at most the sum of the
two selector branches of its own success event.

The passage from the measure-valued `sameMessageStrongUnforgeableExp` to the point-probability
reading is `sameMessageStrongUnforgeableExp_apply_singleton`, the library's own compatibility
equation; no measure-theoretic step is taken here beyond it.

*Experiment split.* -/
theorem sameMessageAdvantage_le_arms {sigAlg : SignatureAlg (OracleComp spec) M PK SK S}
    (runtime : ProbCompRuntime (OracleComp spec))
    (h_pull : ∀ {α β : Type} (f : α → β) (mx : OracleComp spec α),
      runtime.evalSPMF (mx >>= fun x => pure (f x)) = f <$> runtime.evalSPMF mx)
    (adv : strongUnforgeableAdv sigAlg) (sel : QueryLog (M →ₒ S) → M → S → Bool) :
    adv.sameMessageAdvantage runtime ≤
      Pr[fun x => x.1 = true ∧ x.2 = true | instrumentedSameMessageExp runtime adv sel] +
      Pr[fun x => x.1 = true ∧ x.2 = false | instrumentedSameMessageExp runtime adv sel] := by
  rw [strongUnforgeableAdv.sameMessageAdvantage, sameMessageStrongUnforgeableExp_apply_singleton,
    instrumentedSameMessageExp_fst runtime h_pull adv sel, ← probEvent_eq_eq_probOutput,
    probEvent_map]
  refine le_trans (probEvent_mono ?_) (probEvent_or_le _ _ _)
  rintro ⟨b, s⟩ _ hx
  cases s
  · exact Or.inr ⟨hx, rfl⟩
  · exact Or.inl ⟨hx, rfl⟩

end Generic

/-! ## The external SLH-DSA signature algebra -/

variable {vp : ValidatedParams} {prims : Primitives vp.params}

/-- **The arbitrary-`d` external SLH-DSA signature algebra**, in the standard model: key generation
samples the three seeds, signing samples the per-signature `addrnd`, and both signing and
verification apply the FIPS 205 §10 empty-context encoding to the caller's message.

`SLHDSA.slhdsaAlg` and `SLHDSA.slhdsaConcreteAlg` of `HashSig.SLHDSA.RandomOracle` are the only
other `SignatureAlg`s in `HashSig` — the repository has others, in `LatticeCrypto`, `Examples` and
`VCVio`, none of them hash-based — and both take `hd : p.d = 1` and run the depth-one
*compatibility* programs.  Every witness family of this lane is stated over `GeneralScheme`, so
routing a scheme game through the compatibility programs would put the depth-one bridge — whose
point is that the two signers agree on outputs and differ in oracle traces — inside a probability
argument.  This packaging avoids that and needs no `d = 1` hypothesis.

Exposed, and what that attribute is for was read off the errors its removal produces: without it
the three component equations below report `Not a definitional equality`, each with the note "This
theorem is exported from the current module.  This requires that all definitions that need to be
unfolded to prove this theorem must be exposed."  Three errors, one per equation, and no other
error in the module; the per-declaration form is what the expose-boundary ratchet does not count.

*Deterministic inclusion.* -/
@[expose] def generalAlg (prims : Primitives vp.params) [SampleableType prims.SkSeed]
    [SampleableType prims.SkPrf] [SampleableType prims.PkSeed] [SampleableType prims.Y]
    [DecidableEq prims.Y] :
    SignatureAlg ProbComp (List Byte) (PublicKeyCore prims.core) (SecretKeyCore prims.core)
      (GeneralScheme.SignatureCore vp prims.core) where
  keygen := do
    let skSeed ← $ᵗ prims.SkSeed
    let skPrf ← $ᵗ prims.SkPrf
    let pkSeed ← $ᵗ prims.PkSeed
    pure (GeneralScheme.keygenInternal vp prims skSeed skPrf pkSeed)
  sign _pk sk msg := do
    let addrnd ← $ᵗ prims.Y
    pure (GeneralScheme.signInternal vp prims (emptyContextMessage msg) sk addrnd)
  verify pk msg sig :=
    pure (GeneralScheme.verifyInternal vp prims (emptyContextMessage msg) sig pk)

section Alg

variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.PkSeed]
  [SampleableType prims.Y] [DecidableEq prims.Y]

/-- Key generation samples the three seeds and returns FIPS 205 Algorithm 18's pair.

*Deterministic inclusion.* -/
@[simp] theorem generalAlg_keygen :
    (generalAlg prims).keygen = (do
      let skSeed ← $ᵗ prims.SkSeed
      let skPrf ← $ᵗ prims.SkPrf
      let pkSeed ← $ᵗ prims.PkSeed
      pure (GeneralScheme.keygenInternal vp prims skSeed skPrf pkSeed)) := rfl

/-- Signing samples `addrnd` and signs the *internal* message.  The public key argument is ignored,
as FIPS 205 Algorithm 19 ignores it: everything the signer needs is in the secret key.

*Deterministic inclusion.* -/
@[simp] theorem generalAlg_sign (pk : PublicKeyCore prims.core)
    (sk : SecretKeyCore prims.core) (msg : List Byte) :
    (generalAlg prims).sign pk sk msg = (do
      let addrnd ← $ᵗ prims.Y
      pure (GeneralScheme.signInternal vp prims (emptyContextMessage msg) sk addrnd)) := rfl

/-- Verification is deterministic and reads the *internal* message.  This is the equation that says
what the experiment's `verified` bit is; every statement below about a forgery that verifies is
about the right-hand side.

*Deterministic inclusion.* -/
@[simp] theorem generalAlg_verify (pk : PublicKeyCore prims.core) (msg : List Byte)
    (sig : GeneralScheme.SignatureCore vp prims.core) :
    (generalAlg prims).verify pk msg sig =
      pure (GeneralScheme.verifyInternal vp prims (emptyContextMessage msg) sig pk) := rfl

/-- **Key generation, with both components named.**  The published root and the root the secret key
retains are one `GeneralHypertree.root` application, not two computations that agree.

This is where `GeneralScheme.keygenInternal_fst` and `GeneralScheme.keygenInternal_snd` are
consumed, and it is why the second was needed: the pair equation is not available by `rfl` to an
ordinary importer, and neither projection is.

*Deterministic inclusion.* -/
theorem generalAlg_keygen_eq :
    (generalAlg prims).keygen = (do
      let skSeed ← $ᵗ prims.SkSeed
      let skPrf ← $ᵗ prims.SkPrf
      let pkSeed ← $ᵗ prims.PkSeed
      pure ((⟨pkSeed, GeneralHypertree.root vp prims skSeed pkSeed⟩ :
          PublicKeyCore prims.core),
        (⟨skSeed, skPrf, pkSeed, GeneralHypertree.root vp prims skSeed pkSeed⟩ :
          SecretKeyCore prims.core))) := by
  rw [generalAlg_keygen]
  refine bind_congr fun skSeed => bind_congr fun skPrf => bind_congr fun pkSeed => ?_
  rw [← GeneralScheme.keygenInternal_fst vp prims skSeed skPrf pkSeed,
    ← GeneralScheme.keygenInternal_snd vp prims skSeed skPrf pkSeed]

/-- **The algebra is not vacuous.**  Every honest key pair, message and per-signature randomness
produces a signature that verifies, with probability one.

Both splits are upper bounds, so a signature algebra that verified nothing would satisfy them
trivially; this is the statement that says it does not, and it is the reason `generalAlg` is a
packaging of the real algorithms rather than three plausible-looking `do` blocks.

The whole computation reduces to four uniform samples followed by `pure true`, because
`GeneralScheme.verifyInternal_signInternal` holds at every choice of seeds, randomizer and message
— there is no failure event to bound, and no `δ`.

*Experiment split.* -/
theorem generalAlg_perfectlyComplete :
    (generalAlg prims).PerfectlyComplete ProbCompRuntime.probComp := by
  intro msg
  have hbody : (do
      let (pk, sk) ← (generalAlg prims).keygen
      let sig ← (generalAlg prims).sign pk sk msg
      (generalAlg prims).verify pk msg sig) = (do
      let _skSeed ← $ᵗ prims.SkSeed
      let _skPrf ← $ᵗ prims.SkPrf
      let _pkSeed ← $ᵗ prims.PkSeed
      let _addrnd ← $ᵗ prims.Y
      pure true) := by
    rw [generalAlg_keygen]
    simp only [generalAlg_sign, generalAlg_verify, bind_assoc, pure_bind]
    refine bind_congr fun skSeed => bind_congr fun skPrf => bind_congr fun pkSeed => ?_
    refine bind_congr fun addrnd => ?_
    rw [GeneralScheme.verifyInternal_signInternal]
  rw [hbody]
  simp [ProbCompRuntime.evalSPMF, ProbCompRuntime.probComp]

/-- **The honest key pair, read off the support.**  On every run of key generation the published key
is the honest one for the secret key that run produced: its seed is the secret key's public seed and
its root is the hypertree root of the secret key's secret seed under that seed.

This is the hypothesis `HashSig.SLHDSA.Security.SchemeWitnesses`' completeness theorem takes,
supplied by the experiment rather than assumed; it is the only place in this module where the shape
of `keygen` is used for anything other than rewriting.

*Experiment split.* -/
theorem honestKey_of_mem_support {pk : PublicKeyCore prims.core}
    {sk : SecretKeyCore prims.core} (h : (pk, sk) ∈ support ((generalAlg prims).keygen)) :
    pk = ⟨sk.pkSeed, GeneralHypertree.root vp prims sk.skSeed sk.pkSeed⟩ := by
  rw [generalAlg_keygen_eq] at h
  simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff,
    Prod.mk.injEq] at h
  obtain ⟨s1, -, s2, -, s3, -, hpk, hsk⟩ := h
  subst hpk
  subst hsk
  rfl

end Alg

/-! ## The dispatch selector -/

/-- **The dispatch bit.**  Whether the FORS public key the signature recovers, at the FORS address
its own digest names, is the honest FORS public key there.

This is the equality `SchemeWitnesses.verifyInternal_cases` splits on and `findWitness` tests,
recomputed from the key pair the experiment holds.  Three arguments are load-bearing in a way no
type catches.

* The message is `emptyContextMessage msg`, because that is what the external algorithm hashes.
  A selector at the raw `msg` type-checks and is a different predicate.
* The secret seed is `sk.skSeed`, read off the *secret key*, so this is not an adversary-computable
  bit.
* The public seed is `pk.pkSeed`, read off the *public key* rather than off `sk`.  At a key pair the
  experiment produced those agree, by `honestKey_of_mem_support`; at an arbitrary pair they need
  not, and no statement below assumes they do.

*Deterministic inclusion.* -/
def forsArm (prims : Primitives vp.params) [DecidableEq prims.Y]
    (pk : PublicKeyCore prims.core) (sk : SecretKeyCore prims.core) (msg : List Byte)
    (sig : GeneralScheme.SignatureCore vp prims.core) : Bool :=
  decide (forsPkFromSig prims sig.fors
      (schemeParts vp prims (emptyContextMessage msg) sig pk).md.toList pk.pkSeed
      (schemeParts vp prims (emptyContextMessage msg) sig pk).forsAdrs =
    forsPkGen prims sk.skSeed pk.pkSeed
      (schemeParts vp prims (emptyContextMessage msg) sig pk).forsAdrs)

section Arm

variable [DecidableEq prims.Y]

/-- The bit is `true` exactly at the public-key match.  The body is not exposed, so this is what a
consumer rewrites with.

*Deterministic inclusion.* -/
theorem forsArm_eq_true_iff (pk : PublicKeyCore prims.core) (sk : SecretKeyCore prims.core)
    (msg : List Byte) (sig : GeneralScheme.SignatureCore vp prims.core) :
    forsArm prims pk sk msg sig = true ↔
      forsPkFromSig prims sig.fors
          (schemeParts vp prims (emptyContextMessage msg) sig pk).md.toList pk.pkSeed
          (schemeParts vp prims (emptyContextMessage msg) sig pk).forsAdrs =
        forsPkGen prims sk.skSeed pk.pkSeed
          (schemeParts vp prims (emptyContextMessage msg) sig pk).forsAdrs := by
  rw [forsArm, decide_eq_true_eq]

/-- And `false` exactly at the mismatch.  Stated separately rather than left to `Bool` reasoning
because both branches of both splits are used, and each is used at the shape its own consumer takes.

*Deterministic inclusion.* -/
theorem forsArm_eq_false_iff (pk : PublicKeyCore prims.core) (sk : SecretKeyCore prims.core)
    (msg : List Byte) (sig : GeneralScheme.SignatureCore vp prims.core) :
    forsArm prims pk sk msg sig = false ↔
      forsPkFromSig prims sig.fors
          (schemeParts vp prims (emptyContextMessage msg) sig pk).md.toList pk.pkSeed
          (schemeParts vp prims (emptyContextMessage msg) sig pk).forsAdrs ≠
        forsPkGen prims sk.skSeed pk.pkSeed
          (schemeParts vp prims (emptyContextMessage msg) sig pk).forsAdrs := by
  rw [forsArm, decide_eq_false_iff_not]

/-- **The bit names the arm, on the `true` side.**  This is `findWitness_eq_fors_of_pk` at the
internal message and the experiment's secret seed.

*Deterministic inclusion.* -/
theorem findWitness_eq_fors_of_forsArm (pk : PublicKeyCore prims.core)
    (sk : SecretKeyCore prims.core) (msg : List Byte)
    (sig : GeneralScheme.SignatureCore vp prims.core) (target : Fin vp.params.k)
    (h : forsArm prims pk sk msg sig = true) :
    findWitness sk.skSeed pk (emptyContextMessage msg) sig target =
      some (.fors (findForsWitness prims sig.fors
        (schemeParts vp prims (emptyContextMessage msg) sig pk).md.toList sk.skSeed pk.pkSeed
        (schemeParts vp prims (emptyContextMessage msg) sig pk).forsAdrs target)) :=
  findWitness_eq_fors_of_pk sk.skSeed pk (emptyContextMessage msg) sig target
    ((forsArm_eq_true_iff pk sk msg sig).mp h)

/-- And on the `false` side, where the extractor is the layer walk and may return nothing.

*Deterministic inclusion.* -/
theorem findWitness_eq_hypertree_of_forsArm (pk : PublicKeyCore prims.core)
    (sk : SecretKeyCore prims.core) (msg : List Byte)
    (sig : GeneralScheme.SignatureCore vp prims.core) (target : Fin vp.params.k)
    (h : forsArm prims pk sk msg sig = false) :
    findWitness sk.skSeed pk (emptyContextMessage msg) sig target =
      (findHypertreeWitness vp prims sk.skSeed pk.pkSeed
        (LayerPosition.initial vp (schemeParts vp prims (emptyContextMessage msg) sig pk))
        vp.params.d (by simp)
        (forsPkFromSig prims sig.fors
          (schemeParts vp prims (emptyContextMessage msg) sig pk).md.toList pk.pkSeed
          (schemeParts vp prims (emptyContextMessage msg) sig pk).forsAdrs)
        (forsPkGen prims sk.skSeed pk.pkSeed
          (schemeParts vp prims (emptyContextMessage msg) sig pk).forsAdrs)
        sig.hypertree).map .hypertree :=
  findWitness_eq_hypertree_of_ne sk.skSeed pk (emptyContextMessage msg) sig target
    ((forsArm_eq_false_iff pk sk msg sig).mp h)

/-- Whatever the extractor returns on the `true` side is a FORS witness.

*Deterministic inclusion.* -/
theorem witness_eq_fors_of_forsArm (pk : PublicKeyCore prims.core)
    (sk : SecretKeyCore prims.core) (msg : List Byte)
    (sig : GeneralScheme.SignatureCore vp prims.core) (target : Fin vp.params.k)
    {w : Witness vp prims} (h : forsArm prims pk sk msg sig = true)
    (hw : findWitness sk.skSeed pk (emptyContextMessage msg) sig target = some w) :
    w = .fors (findForsWitness prims sig.fors
      (schemeParts vp prims (emptyContextMessage msg) sig pk).md.toList sk.skSeed pk.pkSeed
      (schemeParts vp prims (emptyContextMessage msg) sig pk).forsAdrs target) := by
  rw [findWitness_eq_fors_of_forsArm pk sk msg sig target h, Option.some.injEq] at hw
  exact hw.symm

/-- And on the `false` side it is a hypertree witness.  The walk's own result is not named, because
which layer it stops at is not determined by this bit.

*Deterministic inclusion.* -/
theorem exists_hypertree_witness_of_forsArm_eq_false (pk : PublicKeyCore prims.core)
    (sk : SecretKeyCore prims.core) (msg : List Byte)
    (sig : GeneralScheme.SignatureCore vp prims.core) (target : Fin vp.params.k)
    {w : Witness vp prims} (h : forsArm prims pk sk msg sig = false)
    (hw : findWitness sk.skSeed pk (emptyContextMessage msg) sig target = some w) :
    ∃ u : HypertreeWitness vp prims vp.params.d, w = .hypertree u := by
  rw [findWitness_eq_hypertree_of_forsArm pk sk msg sig target h,
    Option.map_eq_some_iff] at hw
  obtain ⟨u, -, hu⟩ := hw
  exact ⟨u, hu.symm⟩

end Arm

section Extract

variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.PkSeed]
  [SampleableType prims.Y] [DecidableEq prims.Y]

/-- **Completeness at a sampled key pair.**  A signature that verifies against a public key the
experiment produced yields a witness.

The honest identification the deterministic theorem takes as a hypothesis is supplied here by
`honestKey_of_mem_support`, which is the whole reason the support statement exists.  The byte laws
stay a hypothesis: they are a property of the primitive bundle, discharged at any concrete bundle
and not by anything the experiment does.

*Experiment split.* -/
theorem findWitness_isSome_of_mem_support (laws : prims.core.ByteLaws)
    {pk : PublicKeyCore prims.core} {sk : SecretKeyCore prims.core}
    (hkey : (pk, sk) ∈ support ((generalAlg prims).keygen)) (msg : List Byte)
    (sig : GeneralScheme.SignatureCore vp prims.core)
    (hverify : GeneralScheme.verifyInternal vp prims (emptyContextMessage msg) sig pk = true)
    (target : Fin vp.params.k) :
    (findWitness sk.skSeed pk (emptyContextMessage msg) sig target).isSome := by
  have hpk := honestKey_of_mem_support hkey
  subst hpk
  exact findWitness_isSome laws sk.skSeed sk.pkSeed (emptyContextMessage msg) sig target hverify

/-- The same, with the witness named and its validity carried.  This is the statement a bound on
either half has to start from: on the success event there *is* a witness, and the dispatch bit says
which family it is in.

*Experiment split.* -/
theorem exists_witness_of_mem_support (laws : prims.core.ByteLaws)
    {pk : PublicKeyCore prims.core} {sk : SecretKeyCore prims.core}
    (hkey : (pk, sk) ∈ support ((generalAlg prims).keygen)) (msg : List Byte)
    (sig : GeneralScheme.SignatureCore vp prims.core)
    (hverify : GeneralScheme.verifyInternal vp prims (emptyContextMessage msg) sig pk = true)
    (target : Fin vp.params.k) :
    ∃ w : Witness vp prims,
      findWitness sk.skSeed pk (emptyContextMessage msg) sig target = some w ∧
        w.Valid sk.skSeed pk (emptyContextMessage msg) sig := by
  obtain ⟨w, hw⟩ :=
    Option.isSome_iff_exists.mp (findWitness_isSome_of_mem_support laws hkey msg sig hverify target)
  exact ⟨w, hw, findWitness_sound sk.skSeed pk (emptyContextMessage msg) sig target hw⟩

end Extract

/-! ## The dispatch split at the SLH-DSA experiment -/

section Halves

variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.PkSeed]
  [SampleableType prims.Y] [DecidableEq prims.Y]

/-- The probability that the adversary forges *and* its forgery recovers the honest FORS public key
at its own digest's address.

Not the FORS half's advantage in any game: no reduction is applied, no challenge is recorded, and
the event reads the secret key.

*Experiment split.* -/
noncomputable def forsHalf (adv : unforgeableAdv (generalAlg prims)) : ℝ≥0∞ :=
  Pr[fun x => x.1 = true ∧ x.2 = true |
    instrumentedEufExp ProbCompRuntime.probComp adv (forsArm prims)]

/-- The probability that the adversary forges and its forgery does *not* recover that key, so its
hypertree half carries the value it did recover to the published root.

*Experiment split.* -/
noncomputable def hypertreeHalf (adv : unforgeableAdv (generalAlg prims)) : ℝ≥0∞ :=
  Pr[fun x => x.1 = true ∧ x.2 = false |
    instrumentedEufExp ProbCompRuntime.probComp adv (forsArm prims)]

/-- **The dispatch split.**  The EUF-CMA advantage against the external SLH-DSA algebra is at most
the sum of its two dispatch branches.

The runtime is fixed to `ProbCompRuntime.probComp`, whose factoring law is
`ProbCompRuntime.probComp_evalSPMF_bind_pure`, so the statement carries no hypothesis a reader has
to discharge.  `advantage_le_arms` is the general-runtime form for anyone who needs another one.

*Experiment split.* -/
theorem advantage_le_forsHalf_add_hypertreeHalf (adv : unforgeableAdv (generalAlg prims)) :
    adv.advantage ProbCompRuntime.probComp ≤ forsHalf adv + hypertreeHalf adv :=
  advantage_le_arms ProbCompRuntime.probComp
    (fun f mx => ProbCompRuntime.probComp_evalSPMF_bind_pure f mx) adv (forsArm prims)

/-! ### What pins the two halves, in two kinds

The halves admit two silent weakenings of different shapes, and they need canaries of different
kinds.  The first is a *naming* error and the second is a *vacuity* one.

**Which branch each name is attached to.**  `advantage_le_forsHalf_add_hypertreeHalf` is symmetric
in its two summands, so it holds just as well of a module in which the two names are attached to
the wrong branches, and no fixture can catch that: both are `noncomputable`.  The two `example`s
below are that canary.  They are `example`s rather than theorems, and they are here rather than in
the test module, because both reasons are the same one: the bodies are not exposed, so a
`theorem … := rfl` exported from this module is refused ("Not a definitional equality", with the
note that every definition that has to be unfolded must be exposed) and the same statement in an
importing module is refused for the same reason.  An `example` is not exported and sees the body.
Swapping the two definitions' bodies — with or without a matching flip of `forsArm`'s polarity —
fails these two at build time.

**Whether a half is an event of the success bit at all.**  This the `example`s cannot reach, and
the reason is structural: they are `rfl` against the body, so a paired edit of the body moves them
with it.  Drop the conjunct `x.1 = true` from all four halves and re-prove both splits by
monotonicity: with the two theorems below absent, that module elaborates with zero errors, needs no
edit to the test module, and passes all seventy-seven runtime checks — and both headline theorems
are then information-free, since `Pr[sel = true] + Pr[sel = false]` is the experiment's total mass
and dominates every event.  All three were measured.  The
two theorems below are that canary.  They are *semantic* rather than syntactic — each half is at
most the advantage it splits, which is false of the weakened halves — so no paired edit of the body
carries them along; against that weakening each fails at the success conjunct it no longer has.
They are also the splits' other direction, so each pair is pinned from both sides. -/

/-- The FORS half is at most the advantage it splits.

Not a weaker `advantage_le_forsHalf_add_hypertreeHalf`: that bounds the advantage by the two halves
and this bounds one half by the advantage, and neither follows from the other.  What it pins is that
`forsHalf` is an event of the *success bit*, the conjunct a paired weakening of both halves can drop
without breaking either split.

*Experiment split.* -/
theorem forsHalf_le_advantage (adv : unforgeableAdv (generalAlg prims)) :
    forsHalf adv ≤ adv.advantage ProbCompRuntime.probComp := by
  rw [forsHalf, unforgeableAdv.advantage,
    instrumentedEufExp_fst ProbCompRuntime.probComp
      (fun f mx => ProbCompRuntime.probComp_evalSPMF_bind_pure f mx) adv (forsArm prims),
    ← probEvent_eq_eq_probOutput, probEvent_map]
  exact probEvent_mono fun x _ hx => hx.1

/-- The hypertree half is at most the advantage it splits.

*Experiment split.* -/
theorem hypertreeHalf_le_advantage (adv : unforgeableAdv (generalAlg prims)) :
    hypertreeHalf adv ≤ adv.advantage ProbCompRuntime.probComp := by
  rw [hypertreeHalf, unforgeableAdv.advantage,
    instrumentedEufExp_fst ProbCompRuntime.probComp
      (fun f mx => ProbCompRuntime.probComp_evalSPMF_bind_pure f mx) adv (forsArm prims),
    ← probEvent_eq_eq_probOutput, probEvent_map]
  exact probEvent_mono fun x _ hx => hx.1

example (adv : unforgeableAdv (generalAlg prims)) :
    forsHalf adv = Pr[fun x => x.1 = true ∧ x.2 = true |
      instrumentedEufExp ProbCompRuntime.probComp adv (forsArm prims)] := rfl

example (adv : unforgeableAdv (generalAlg prims)) :
    hypertreeHalf adv = Pr[fun x => x.1 = true ∧ x.2 = false |
      instrumentedEufExp ProbCompRuntime.probComp adv (forsArm prims)] := rfl

end Halves

/-! ## The signing log at the internal message -/

/-- `emptyContextMessage` prefixes two zero bytes, so it is injective.

Named because every transport below is this fact and `List.filterMap_congr`; without it a reading of
the internalised log at one message could collect entries from another.

*Deterministic inclusion.* -/
theorem emptyContextMessage_injective : Function.Injective emptyContextMessage := by
  intro a b h
  simpa [emptyContextMessage] using h

/-- **The signing log, at the messages the honest signer actually hashed.**  The signing oracle logs
the *external* messages the adversary sent; `H_msg` was applied to their empty-context encodings.
This is the log with each entry's message internalised, and it is the log a reduction's `H_msg`
target transcript is read off.

*Transcript transport.* -/
def internalLog (log : QueryLog (List Byte →ₒ GeneralScheme.SignatureCore vp prims.core)) :
    QueryLog (List Byte →ₒ GeneralScheme.SignatureCore vp prims.core) :=
  log.map fun e => ⟨emptyContextMessage e.1, e.2⟩

/-- Unfolding equation for `internalLog`.  The body is not exposed, so this is what a consumer that
needs the `List.map` shape rewrites with.

*Transcript transport.* -/
theorem internalLog_eq (log : QueryLog (List Byte →ₒ GeneralScheme.SignatureCore vp prims.core)) :
    internalLog log = log.map fun e => ⟨emptyContextMessage e.1, e.2⟩ := by rfl

/-- **Internalising the log does not move any per-message reading of it.**  The signatures listed at
the internal message are exactly the signatures listed at the external one.

This is what makes the internalisation harmless, and it is an equality of lists rather than of sets:
the order and the repetitions are preserved too, which matters because `loggedSignatures` is as long
as the number of times the message was signed.

*Transcript transport.* -/
theorem loggedSignatures_internalLog
    (log : QueryLog (List Byte →ₒ GeneralScheme.SignatureCore vp prims.core)) (msg : List Byte) :
    loggedSignatures (internalLog log) (emptyContextMessage msg) = loggedSignatures log msg := by
  rw [loggedSignatures_eq, loggedSignatures_eq, internalLog_eq, List.filterMap_map]
  refine List.filterMap_congr fun e _ => ?_
  simp only [Function.comp_apply]
  rcases eq_or_ne e.1 msg with h | h
  · rw [if_pos h, if_pos (congrArg emptyContextMessage h)]
  · rw [if_neg h, if_neg fun hc => h (emptyContextMessage_injective hc)]

/-- And therefore neither does the randomizer reading.

*Transcript transport.* -/
theorem loggedRandomizers_internalLog
    (log : QueryLog (List Byte →ₒ GeneralScheme.SignatureCore vp prims.core)) (msg : List Byte) :
    loggedRandomizers (internalLog log) (emptyContextMessage msg) = loggedRandomizers log msg := by
  rw [loggedRandomizers_eq, loggedRandomizers_eq, loggedSignatures_internalLog]

/-- The pair transcript of the internalised log, written out: each entry contributes the randomizer
the signer returned and the internal message it hashed.  This is the transcript, and the one at the
external messages is not.

*Transcript transport.* -/
theorem logQueries_internalLog
    (log : QueryLog (List Byte →ₒ GeneralScheme.SignatureCore vp prims.core)) :
    logQueries (internalLog log) = log.map fun e => (e.2.randomness, emptyContextMessage e.1) := by
  rw [logQueries_eq, internalLog_eq, List.map_map]
  rfl

/-- The library's exact-pair predicate is unmoved as well, so the strong-unforgeability freshness
condition can be read at either log.

*Transcript transport.* -/
theorem signingLogContains_internalLog
    [DecidableEq (GeneralScheme.SignatureCore vp prims.core)]
    (log : QueryLog (List Byte →ₒ GeneralScheme.SignatureCore vp prims.core)) (msg : List Byte)
    (sig : GeneralScheme.SignatureCore vp prims.core) :
    SignatureAlg.signingLogContains (internalLog log) (emptyContextMessage msg) sig =
      SignatureAlg.signingLogContains log msg sig := by
  refine Bool.eq_iff_iff.mpr ?_
  rw [signingLogContains_eq_true_iff, signingLogContains_eq_true_iff,
    loggedSignatures_internalLog]

/-! ## The same-message selector, and what each of its branches yields -/

/-- **The same-message selector.**  Whether the forged signature's randomizer is one the log
returned *at this message*.

This is the `by_cases` of `SufResidual.itsrFresh_or_sameRandomizer`, as a `Bool`.  It reads the log
at the external message, which is the key the signing oracle logged; the transport lemmas above
move the `H_msg` consequences to the internal one.

*Transcript transport.* -/
def randomizerLogged [DecidableEq prims.Y]
    (log : QueryLog (List Byte →ₒ GeneralScheme.SignatureCore vp prims.core)) (msg : List Byte)
    (sig : GeneralScheme.SignatureCore vp prims.core) : Bool :=
  decide (sig.randomness ∈ loggedRandomizers log msg)

section Selector

variable [DecidableEq prims.Y]

/-- The bit is `true` exactly at a repeated randomizer.  The body is not exposed, so this is what a
consumer rewrites with.

*Transcript transport.* -/
theorem randomizerLogged_eq_true_iff
    (log : QueryLog (List Byte →ₒ GeneralScheme.SignatureCore vp prims.core)) (msg : List Byte)
    (sig : GeneralScheme.SignatureCore vp prims.core) :
    randomizerLogged log msg sig = true ↔ sig.randomness ∈ loggedRandomizers log msg := by
  rw [randomizerLogged, decide_eq_true_eq]

/-- And `false` exactly at a fresh one.

*Transcript transport.* -/
theorem randomizerLogged_eq_false_iff
    (log : QueryLog (List Byte →ₒ GeneralScheme.SignatureCore vp prims.core)) (msg : List Byte)
    (sig : GeneralScheme.SignatureCore vp prims.core) :
    randomizerLogged log msg sig = false ↔ sig.randomness ∉ loggedRandomizers log msg := by
  rw [randomizerLogged, decide_eq_false_iff_not]

/-- **The fresh branch, at the transcript.**  A fresh randomizer leaves the forged `H_msg` input
absent from the transcript of the internalised log.

*Transcript transport.* -/
theorem freshRandomizer_notMem_embedTargets (pk : PublicKeyCore prims.core)
    {log : QueryLog (List Byte →ₒ GeneralScheme.SignatureCore vp prims.core)} {msg : List Byte}
    {sig : GeneralScheme.SignatureCore vp prims.core}
    (h : randomizerLogged log msg sig = false) :
    (sig.randomness, (⟨pk.pkSeed, pk.pkRoot, emptyContextMessage msg⟩ :
        HmsgITSRInput prims.PkSeed prims.Y)) ∉
      embedTargets prims pk.pkSeed pk.pkRoot (logQueries (internalLog log)) :=
  notMem_embedTargets_of_notMem_loggedRandomizers pk
    (by rw [loggedRandomizers_internalLog]; exact (randomizerLogged_eq_false_iff log msg sig).mp h)

end Selector

/-- **The fresh branch, at the `H_msg` bridge.**  On that branch the dichotomy of
`HashSig.SLHDSA.Security.HmsgWitnesses` applies unchanged: either the forged pair wins the
interleaved-target-subset-resilience game against the recorded transcript, or it names a FORS
coordinate no recorded target covers.

This is the whole of what the fresh branch buys, and it is exactly what
`SufResidual.wins_or_uncovered_of_notMem_loggedRandomizers` gives, transported to the internal
message.

*Transcript transport.* -/
theorem freshRandomizer_wins_or_uncovered [SampleableType prims.Y] [DecidableEq prims.PkSeed]
    [DecidableEq prims.Y] (pk : PublicKeyCore prims.core)
    {log : QueryLog (List Byte →ₒ GeneralScheme.SignatureCore vp prims.core)} {msg : List Byte}
    {sig : GeneralScheme.SignatureCore vp prims.core}
    (h : randomizerLogged log msg sig = false) :
    (hmsgItsrProblem prims).Wins
        (embedTargets prims pk.pkSeed pk.pkRoot (logQueries (internalLog log)))
        (sig.randomness, ⟨pk.pkSeed, pk.pkRoot, emptyContextMessage msg⟩) ∨
      ∃ idx, findUncoveredIndex prims
          (embedTargets prims pk.pkSeed pk.pkRoot (logQueries (internalLog log)))
          (sig.randomness, ⟨pk.pkSeed, pk.pkRoot, emptyContextMessage msg⟩) = some idx ∧
        idx ∈ (hmsgItsrProblem prims).indexSet
          (sig.randomness, ⟨pk.pkSeed, pk.pkRoot, emptyContextMessage msg⟩) ∧
        idx ∉ (hmsgItsrProblem prims).targetIndexSet
          (embedTargets prims pk.pkSeed pk.pkRoot (logQueries (internalLog log))) :=
  wins_or_uncovered_of_notMem_loggedRandomizers pk
    (by rw [loggedRandomizers_internalLog]; exact (randomizerLogged_eq_false_iff log msg sig).mp h)

/-- **The logged branch, with its four facts besides the membership.**  On that branch the forged
signature comes with a
signature the log returned at the same message which carries the same randomizer, differs from it,
splits to the same internal digest against the same public key, and differs from it in its FORS half
or in its hypertree half.  The existential's body has those four conjuncts and the membership makes
five, which is the base `HashSigTest.SLHDSA.SchemeGames` counts on.

The freshness hypothesis is the same-message experiment's own `!signingLogContains` conjunct, so on
the success event of the instrumented experiment it holds.  Nothing beyond these four facts is
claimed: `SufResidual` establishes that on this branch both alternatives of the `H_msg` dichotomy
are closed off, and that the witness families this lane has built cannot be pointed at a pair of two
adversarial signatures.

*Transcript transport.* -/
theorem sameRandomizer_of_randomizerLogged
    [DecidableEq (GeneralScheme.SignatureCore vp prims.core)] [DecidableEq prims.Y]
    (pk : PublicKeyCore prims.core)
    {log : QueryLog (List Byte →ₒ GeneralScheme.SignatureCore vp prims.core)} {msg : List Byte}
    {sig : GeneralScheme.SignatureCore vp prims.core}
    (hfresh : SignatureAlg.signingLogContains log msg sig = false)
    (h : randomizerLogged log msg sig = true) :
    ∃ sig' ∈ loggedSignatures log msg, sig'.randomness = sig.randomness ∧ sig' ≠ sig ∧
      schemeParts vp prims (emptyContextMessage msg) sig pk =
        schemeParts vp prims (emptyContextMessage msg) sig' pk ∧
      (sig.fors ≠ sig'.fors ∨ sig.hypertree ≠ sig'.hypertree) := by
  obtain ⟨sig', hmem, hr⟩ :=
    mem_loggedRandomizers.mp ((randomizerLogged_eq_true_iff log msg sig).mp h)
  have hnot : sig ∉ loggedSignatures log msg := fun hc =>
    Bool.noConfusion (hfresh ▸ (signingLogContains_eq_true_iff log msg sig).mpr hc)
  have hne : sig' ≠ sig := fun he => hnot (he ▸ hmem)
  exact ⟨sig', hmem, hr, hne,
    schemeParts_eq_of_randomizer_eq (emptyContextMessage msg) sig sig' pk hr.symm,
    components_ne_of_ne_of_randomizer_eq (Ne.symm hne) hr.symm⟩

/-- **The residual at the external interface.**  `SufResidual.itsrFresh_or_sameRandomizer` with the
log read at the message the signing oracle logged and the `H_msg` consequences at the message the
signer hashed.

The two branches are the two branches of `randomizerLogged`, which is what makes that selector the
right one to instrument the same-message experiment with.

*Transcript transport.* -/
theorem itsrFresh_or_sameRandomizer_external
    [DecidableEq (GeneralScheme.SignatureCore vp prims.core)]
    (log : QueryLog (List Byte →ₒ GeneralScheme.SignatureCore vp prims.core)) (msg : List Byte)
    (sig : GeneralScheme.SignatureCore vp prims.core) (pk : PublicKeyCore prims.core)
    (hfresh : SignatureAlg.signingLogContains log msg sig = false) :
    (sig.randomness, (⟨pk.pkSeed, pk.pkRoot, emptyContextMessage msg⟩ :
          HmsgITSRInput prims.PkSeed prims.Y)) ∉
        embedTargets prims pk.pkSeed pk.pkRoot (logQueries (internalLog log)) ∨
      ∃ sig' ∈ loggedSignatures log msg, sig'.randomness = sig.randomness ∧ sig' ≠ sig ∧
        schemeParts vp prims (emptyContextMessage msg) sig pk =
          schemeParts vp prims (emptyContextMessage msg) sig' pk ∧
        (sig.fors ≠ sig'.fors ∨ sig.hypertree ≠ sig'.hypertree) := by
  classical
  -- `Bool.eq_false_or_eq_true : ∀ (b : Bool), b = true ∨ b = false` yields the `true` disjunct
  -- *first*, against what its name suggests, so the first branch here is the logged one and the
  -- second the fresh one.  The pairing looks inverted and is not.
  rcases Bool.eq_false_or_eq_true (randomizerLogged log msg sig) with h | h
  · exact Or.inr (sameRandomizer_of_randomizerLogged pk hfresh h)
  · exact Or.inl (freshRandomizer_notMem_embedTargets pk h)

/-! ## The same-message split at the SLH-DSA experiment -/

section SufHalves

variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.PkSeed]
  [SampleableType prims.Y] [DecidableEq prims.Y]

/-- The probability that the adversary returns a new valid signature on a queried message *and* its
randomizer is one the log already returned at that message.

This is the term this lane holds out of scope, now held out of scope by name.  What is known about
it is `sameRandomizer_of_randomizerLogged`; no bound on it is claimed anywhere.

*Experiment split.* -/
noncomputable def sameRandomizerHalf (adv : strongUnforgeableAdv (generalAlg prims)) : ℝ≥0∞ :=
  Pr[fun x => x.1 = true ∧ x.2 = true |
    instrumentedSameMessageExp ProbCompRuntime.probComp adv (randomizerLogged (prims := prims))]

/-- The probability that it does so with a randomizer fresh at that message, where the `H_msg`
bridge applies.

*Experiment split.* -/
noncomputable def freshRandomizerHalf (adv : strongUnforgeableAdv (generalAlg prims)) : ℝ≥0∞ :=
  Pr[fun x => x.1 = true ∧ x.2 = false |
    instrumentedSameMessageExp ProbCompRuntime.probComp adv (randomizerLogged (prims := prims))]

/-- **The same-message split.**  The same-message advantage is at most the fresh-randomizer term
plus the same-randomizer term.

The summands are written in the reverse of the order `sameMessageAdvantage_le_arms` produces them,
because the fresh branch is the one a reduction can use; `add_comm` is the whole difference.

*Experiment split.* -/
theorem sameMessageAdvantage_le_freshRandomizer_add_sameRandomizer
    (adv : strongUnforgeableAdv (generalAlg prims)) :
    adv.sameMessageAdvantage ProbCompRuntime.probComp ≤
      freshRandomizerHalf adv + sameRandomizerHalf adv := by
  rw [freshRandomizerHalf, sameRandomizerHalf, add_comm]
  exact sameMessageAdvantage_le_arms ProbCompRuntime.probComp
    (fun f mx => ProbCompRuntime.probComp_evalSPMF_bind_pure f mx) adv
    (randomizerLogged (prims := prims))

/-- The library's exact SUF-to-EUF partition, at the canonical runtime.

*Experiment split.* -/
theorem strongAdvantage_eq_advantage_add_sameMessage
    (adv : strongUnforgeableAdv (generalAlg prims)) :
    adv.advantage ProbCompRuntime.probComp =
      adv.toUnforgeableAdv.advantage ProbCompRuntime.probComp +
        adv.sameMessageAdvantage ProbCompRuntime.probComp :=
  strongUnforgeableAdv.advantage_eq_euf_add_sameMessage _
    (fun f mx => ProbCompRuntime.probComp_evalSPMF_bind_pure f mx) adv

/-- **Both splits together.**  The SUF-CMA advantage against the external SLH-DSA algebra is at most
the sum of four named terms: the two dispatch branches of the EUF-CMA experiment and the two
randomizer branches of the same-message one.

None of the four is bounded here.  Three of them route into machinery this lane has built — the FORS
and hypertree witness families for the first two, the `H_msg` bridge for the third — and the fourth
routes nowhere.

*Experiment split.* -/
theorem strongAdvantage_le_halves (adv : strongUnforgeableAdv (generalAlg prims)) :
    adv.advantage ProbCompRuntime.probComp ≤
      (forsHalf adv.toUnforgeableAdv + hypertreeHalf adv.toUnforgeableAdv) +
        (freshRandomizerHalf adv + sameRandomizerHalf adv) := by
  rw [strongAdvantage_eq_advantage_add_sameMessage adv]
  exact add_le_add (advantage_le_forsHalf_add_hypertreeHalf adv.toUnforgeableAdv)
    (sameMessageAdvantage_le_freshRandomizer_add_sameRandomizer adv)

/-! ### What pins the two same-message halves

Both canaries again, for the same two weakenings and for the same reasons.  Here the `true` branch
is the *same-randomizer* one, because `randomizerLogged` reports membership; getting that round the
wrong way is the likeliest single-character error in the module and the reason the two `example`s
are stated at all. -/

/-- The same-randomizer half is at most the same-message advantage it splits.

*Experiment split.* -/
theorem sameRandomizerHalf_le_sameMessageAdvantage
    (adv : strongUnforgeableAdv (generalAlg prims)) :
    sameRandomizerHalf adv ≤ adv.sameMessageAdvantage ProbCompRuntime.probComp := by
  rw [sameRandomizerHalf, strongUnforgeableAdv.sameMessageAdvantage,
    sameMessageStrongUnforgeableExp_apply_singleton,
    instrumentedSameMessageExp_fst ProbCompRuntime.probComp
      (fun f mx => ProbCompRuntime.probComp_evalSPMF_bind_pure f mx) adv
      (randomizerLogged (prims := prims)),
    ← probEvent_eq_eq_probOutput, probEvent_map]
  exact probEvent_mono fun x _ hx => hx.1

/-- The fresh-randomizer half is at most the same-message advantage it splits.

*Experiment split.* -/
theorem freshRandomizerHalf_le_sameMessageAdvantage
    (adv : strongUnforgeableAdv (generalAlg prims)) :
    freshRandomizerHalf adv ≤ adv.sameMessageAdvantage ProbCompRuntime.probComp := by
  rw [freshRandomizerHalf, strongUnforgeableAdv.sameMessageAdvantage,
    sameMessageStrongUnforgeableExp_apply_singleton,
    instrumentedSameMessageExp_fst ProbCompRuntime.probComp
      (fun f mx => ProbCompRuntime.probComp_evalSPMF_bind_pure f mx) adv
      (randomizerLogged (prims := prims)),
    ← probEvent_eq_eq_probOutput, probEvent_map]
  exact probEvent_mono fun x _ hx => hx.1

example (adv : strongUnforgeableAdv (generalAlg prims)) :
    sameRandomizerHalf adv = Pr[fun x => x.1 = true ∧ x.2 = true |
      instrumentedSameMessageExp ProbCompRuntime.probComp adv
        (randomizerLogged (prims := prims))] := rfl

example (adv : strongUnforgeableAdv (generalAlg prims)) :
    freshRandomizerHalf adv = Pr[fun x => x.1 = true ∧ x.2 = false |
      instrumentedSameMessageExp ProbCompRuntime.probComp adv
        (randomizerLogged (prims := prims))] := rfl

end SufHalves

end SLHDSA.Security
