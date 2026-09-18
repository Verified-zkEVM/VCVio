/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.Security.Composition

/-!
# The message-randomizer PRF hop, taken by a constructed reduction

This module replaces the first of the SLH-DSA bound's two `PRF` summands by the advantage of a
distinguisher *built from the forger*, and proves the hop that summand stands for.

## The statement

`SLHDSA.Security.advantage_le_msgPrf_add_ideal` says: for every adversary `adv` against the
external SLH-DSA algebra `generalAlg`,

`adv.advantage ProbCompRuntime.probComp ≤
  prfAbsAdvantage (msgPrfScheme prims) (msgPrfReduction adv) + msgPrfIdealAdvantage adv`

Both terms on the right are functions of `adv` alone.  `msgPrfReduction adv` is a closed term
of `PRFScheme.PRFAdversary`, and `msgPrfIdealAdvantage adv` is the success probability of that
same reduction in the ideal `PRF` experiment — the SLH-DSA CMA game with `PRF_msg` replaced by a
lazily sampled random function, which is what "the advantage that survives the `MKG_PRF` hop"
means.  Nothing is quantified: no certificate, and no field to supply.

## How the reduction is built

`msgPrfReduction adv` holds the whole secret key except `SK.prf`.  It samples `SK.seed` and
`PK.seed` itself, computes the hypertree root honestly, hands the forger the resulting public
key, and answers each signing query by sampling `addrnd`, asking its own oracle for
`R` at `(addrnd, internal message)`, and signing with
`GeneralScheme.signInternalWithRandomizer`.  It then re-runs verification and the freshness test
and returns their conjunction.  The construction is exactly `R_MKGPRF_EUFCMA`
(`SPHINCS_PLUS.ec:1214-1359`): the challenge lives at one line inside the signing oracle, and
the number of oracle queries is one per signing query.

`GeneralScheme.signInternalM_eq_signInternalWithRandomizerM` is what makes this possible:
`SK.prf` enters a signature only through `R`, so replacing `PRF_msg` by an oracle changes one
value and leaves the rest of Algorithm 19 untouched.

## What the real experiment is

`prfRealExp_msgPrfReduction` is the content: in the real `PRF` experiment the reduction *is* the
CMA game, so `Pr[real] = adv.advantage`.  The seed sampling order differs — `prfRealExp` samples
the key first, `generalAlg.keygen` samples `SK.seed` first — and `evalDist_bind_bind_swap`
reconciles them.  The hop then follows from `a ≤ ENNReal.absDiff a b + b`.

## What this does not do

* It does not bound `msgPrfIdealAdvantage`.  That is the next hop's job, and the term is the
  honest carrier of everything not yet reduced; it is *not* claimed small.
* It does not touch the secret-value `PRF` hop, whose reduction needs a signer parameterised by
  a secret-value provider.  `HashSig.SLHDSA.Security.Composition`'s `skgAdv` field is unaffected.
* It builds no certificate.  `HashSig.SLHDSA.Security.OpenPreBound` is where the hop is consumed,
  and where the fields it removes are actually removed.
* The ideal experiment's random function is keyed at `(addrnd, internal message)` pairs and is
  memoised by `PRFScheme.prfIdealExp`'s lazy oracle, so a repeated signing query on the same
  message answers with the same `R` only when `addrnd` repeats.  That is the behaviour of
  `generalAlg`, which samples a fresh `addrnd` per query, and not the behaviour of a scheme that
  derandomizes; nothing here claims otherwise.

## Labels

Eleven declarations.

*Message-`PRF` reduction* — the construction and what it satisfies:

* `msgPrfSpec`, `msgPrfSigningOracle`, `msgPrfQueryImpl`, `msgPrfReduction`,
  `msgPrfIdealAdvantage`;
* `cmaImpl`, `simulateQ_prfReal_msgPrfQueryImpl_run`;
* `prfRealExp_msgPrfReduction`, `unforgeableExp_generalAlg`,
  `prfRealExp_msgPrfReduction_apply`, `advantage_le_msgPrf_add_ideal`.

`advantage_le_msgPrf_add_ideal` is the result; `prfRealExp_msgPrfReduction_apply` is the equality
it rests on, and the two experiment-shape theorems above it are what a reader checks to see that
neither side was bent to fit.

## References

- NIST FIPS 205, §9, Algorithm 19
- Barbosa, Dupressoir, Hülsing, Meijers, and Strub, "A Tight Security Proof for SPHINCS+,
  Formally Verified" (`SPHINCS_PLUS.ec`, `R_MKGPRF_EUFCMA`)
-/

public section

namespace SLHDSA.Security

open OracleComp OracleSpec ENNReal SignatureAlg TweakableHash Security.CanonicalGames

variable {vp : ValidatedParams} (prims : Primitives vp.params)
  [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.PkSeed]
  [SampleableType prims.Y] [DecidableEq prims.Y]

/-- The oracle family the message-randomizer distinguisher runs in: uniform sampling together
with `PRF_msg` at an `(addrnd, internal message)` pair.

*Message-`PRF` reduction.* -/
abbrev msgPrfSpec := PRFScheme.PRFOracleSpec (prims.Y × List Byte) prims.Y

/-- **The signing oracle the reduction serves.**  It samples `addrnd`, takes the randomizer from
its own challenge oracle, and signs with the rest of the secret key, which it holds.

*Message-`PRF` reduction.* -/
def msgPrfSigningOracle (skSeed : prims.SkSeed) (pkSeed : prims.PkSeed)
    (pkRoot : prims.Y) :
    QueryImpl (List Byte →ₒ GeneralScheme.SignatureCore vp prims.core)
      (OracleComp (msgPrfSpec prims)) := fun msg => do
  let addrnd ← OracleComp.liftComp ($ᵗ prims.Y) (msgPrfSpec prims)
  let r ← PRFScheme.functionQuery (D := prims.Y × List Byte) (R := prims.Y)
      (addrnd, emptyContextMessage msg)
  pure (GeneralScheme.signInternalWithRandomizer vp prims (emptyContextMessage msg)
    skSeed pkSeed pkRoot r)

/-- The forger's two oracles as the reduction implements them: ambient uniform sampling is
forwarded unchanged, and signing queries are answered by `msgPrfSigningOracle` and logged, in
the same `WriterT` layer `unforgeableExp` uses.

*Message-`PRF` reduction.* -/
def msgPrfQueryImpl (skSeed : prims.SkSeed) (pkSeed : prims.PkSeed) (pkRoot : prims.Y) :
    QueryImpl (unifSpec + (List Byte →ₒ GeneralScheme.SignatureCore vp prims.core))
      (WriterT (QueryLog (List Byte →ₒ GeneralScheme.SignatureCore vp prims.core))
        (OracleComp (msgPrfSpec prims))) :=
  (HasQuery.toQueryImpl (spec := unifSpec)
      (m := OracleComp (msgPrfSpec prims))).liftTarget
    (WriterT (QueryLog (List Byte →ₒ GeneralScheme.SignatureCore vp prims.core))
      (OracleComp (msgPrfSpec prims))) +
    (msgPrfSigningOracle prims skSeed pkSeed pkRoot).withLogging

/-- **The `MKG_PRF` distinguisher constructed from a forger.**  A function of `adv`: no
certificate supplies it and no other adversary can be substituted for it.

*Message-`PRF` reduction.* -/
noncomputable def msgPrfReduction (adv : unforgeableAdv (generalAlg prims)) :
    PRFScheme.PRFAdversary (prims.Y × List Byte) prims.Y :=
  letI : DecidableEq (List Byte) := Classical.decEq _
  letI : DecidableEq (GeneralScheme.SignatureCore vp prims.core) := Classical.decEq _
  (do
    let skSeed ← OracleComp.liftComp ($ᵗ prims.SkSeed) (msgPrfSpec prims)
    let pkSeed ← OracleComp.liftComp ($ᵗ prims.PkSeed) (msgPrfSpec prims)
    let pkRoot := GeneralHypertree.root vp prims skSeed pkSeed
    let pk : PublicKeyCore prims.core := ⟨pkSeed, pkRoot⟩
    let ((msg, sig), log) ←
      (simulateQ (msgPrfQueryImpl prims skSeed pkSeed pkRoot) (adv.main pk)).run
    pure (!log.wasQueried msg &&
      GeneralScheme.verifyInternal vp prims (emptyContextMessage msg) sig pk) :
    OracleComp (msgPrfSpec prims) Bool)

/-- **The advantage that survives the `MKG_PRF` hop**, at the reduction the forger determines:
the reduction's success probability in the ideal `PRF` experiment, which is the SLH-DSA CMA game
with `PRF_msg` replaced by a lazily sampled random function.

Unlike `Certificate.idealAdvantage`, which is a field, this is a function of `adv`.

*Message-`PRF` reduction.* -/
noncomputable def msgPrfIdealAdvantage (adv : unforgeableAdv (generalAlg prims)) : ℝ≥0∞ :=
  𝒟[PRFScheme.prfIdealExp (msgPrfReduction prims adv)] {true}

/-! ## The real experiment is the CMA game -/

/-- The forger's two oracles as `unforgeableExp` implements them at a named key pair.  Factored
out so that the composition of the reduction's handler with the real `PRF` handler can be
identified with it.

*Message-`PRF` reduction.* -/
def cmaImpl (pk : PublicKeyCore prims.core) (sk : SecretKeyCore prims.core) :
    QueryImpl (unifSpec + (List Byte →ₒ GeneralScheme.SignatureCore vp prims.core))
      (WriterT (QueryLog (List Byte →ₒ GeneralScheme.SignatureCore vp prims.core)) ProbComp) :=
  (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
      (WriterT (QueryLog (List Byte →ₒ GeneralScheme.SignatureCore vp prims.core)) ProbComp) +
    (generalAlg prims).signingOracle pk sk

/-- **Under the real `PRF` handler the reduction's oracles are the CMA game's oracles.**  This is
the whole content of the hop: `SK.prf` reaches a signature only through `R`, so answering the
reduction's challenge query with `PRF_msg` restores Algorithm 19 exactly.

*Message-`PRF` reduction.* -/
theorem simulateQ_prfReal_msgPrfQueryImpl_run {α : Type} (skPrf : prims.SkPrf)
    (skSeed : prims.SkSeed) (pkSeed : prims.PkSeed) (pkRoot : prims.Y)
    (oa : OracleComp (unifSpec + (List Byte →ₒ GeneralScheme.SignatureCore vp prims.core)) α) :
    simulateQ (PRFScheme.prfRealQueryImpl (msgPrfScheme prims) skPrf)
        ((simulateQ (msgPrfQueryImpl prims skSeed pkSeed pkRoot) oa).run) =
      (simulateQ (cmaImpl prims ⟨pkSeed, pkRoot⟩ ⟨skSeed, skPrf, pkSeed, pkRoot⟩)
        oa).run := by
  rw [QueryImpl.simulateQ_writerTMapBase_run]
  congr 2
  funext t
  cases t with
  | inl n =>
      ext
      change (fun a => (a, ([] :
            QueryLog (List Byte →ₒ GeneralScheme.SignatureCore vp prims.core)))) <$>
          simulateQ (PRFScheme.prfRealQueryImpl (msgPrfScheme prims) skPrf)
            (OracleComp.liftComp
              (liftM (unifSpec.query n) : OracleComp unifSpec _) (msgPrfSpec prims)) =
        (fun a => (a, ([] :
            QueryLog (List Byte →ₒ GeneralScheme.SignatureCore vp prims.core)))) <$>
          (liftM (unifSpec.query n) : ProbComp _)
      rw [PRFScheme.simulateQ_prfRealQueryImpl_liftComp]
  | inr m =>
      ext
      have heval : ∀ k rm, (msgPrfScheme prims).eval k rm = prims.PRFmsg k rm.1 rm.2 :=
        fun _ _ => rfl
      have hlift : simulateQ (PRFScheme.prfRealQueryImpl (msgPrfScheme prims) skPrf)
          (liftM ($ᵗ prims.Y) : OracleComp (msgPrfSpec prims) prims.Y) = $ᵗ prims.Y :=
        PRFScheme.simulateQ_prfRealQueryImpl_liftComp _ _ _
      simp [hlift, heval, QueryImpl.writerTMapBase, msgPrfQueryImpl, msgPrfSigningOracle, cmaImpl,
        SignatureAlg.signingOracle, PRFScheme.functionQuery, generalAlg_sign,
        GeneralScheme.signInternal_eq_signInternalWithRandomizer, map_eq_bind_pure_comp]

/-- **The real `PRF` experiment at the reduction, written out.**  Its only difference from
`unforgeableExp` at `generalAlg` is the order in which the three seeds are sampled.

*Message-`PRF` reduction.* -/
theorem prfRealExp_msgPrfReduction (adv : unforgeableAdv (generalAlg prims)) :
    PRFScheme.prfRealExp (msgPrfScheme prims) (msgPrfReduction prims adv) =
      letI : DecidableEq (List Byte) := Classical.decEq _
      letI : DecidableEq (GeneralScheme.SignatureCore vp prims.core) := Classical.decEq _
      (do
        let skPrf ← $ᵗ prims.SkPrf
        let skSeed ← $ᵗ prims.SkSeed
        let pkSeed ← $ᵗ prims.PkSeed
        let pkRoot := GeneralHypertree.root vp prims skSeed pkSeed
        let pk : PublicKeyCore prims.core := ⟨pkSeed, pkRoot⟩
        let ((msg, sig), log) ←
          (simulateQ (cmaImpl prims pk ⟨skSeed, skPrf, pkSeed, pkRoot⟩) (adv.main pk)).run
        pure (!log.wasQueried msg &&
          GeneralScheme.verifyInternal vp prims (emptyContextMessage msg) sig pk) :
      ProbComp Bool) := by
  unfold PRFScheme.prfRealExp msgPrfReduction
  refine bind_congr fun skPrf => ?_
  rw [simulateQ_bind]
  rw [PRFScheme.simulateQ_prfRealQueryImpl_liftComp]
  refine bind_congr fun skSeed => ?_
  rw [simulateQ_bind]
  rw [PRFScheme.simulateQ_prfRealQueryImpl_liftComp]
  refine bind_congr fun pkSeed => ?_
  rw [simulateQ_bind, simulateQ_prfReal_msgPrfQueryImpl_run]
  refine bind_congr fun x => ?_
  rw [simulateQ_pure]

/-- **The CMA experiment at `generalAlg`, written out** with both key components named and the
deterministic verifier inlined.  This is `prfRealExp_msgPrfReduction`'s right-hand side with
`SK.seed` sampled before `SK.prf`.

*Message-`PRF` reduction.* -/
theorem unforgeableExp_generalAlg (adv : unforgeableAdv (generalAlg prims)) :
    unforgeableExp ProbCompRuntime.probComp adv =
      letI : DecidableEq (List Byte) := Classical.decEq _
      letI : DecidableEq (GeneralScheme.SignatureCore vp prims.core) := Classical.decEq _
      𝒟[(do
        let skSeed ← $ᵗ prims.SkSeed
        let skPrf ← $ᵗ prims.SkPrf
        let pkSeed ← $ᵗ prims.PkSeed
        let pkRoot := GeneralHypertree.root vp prims skSeed pkSeed
        let pk : PublicKeyCore prims.core := ⟨pkSeed, pkRoot⟩
        let ((msg, sig), log) ←
          (simulateQ (cmaImpl prims pk ⟨skSeed, skPrf, pkSeed, pkRoot⟩) (adv.main pk)).run
        pure (!log.wasQueried msg &&
          GeneralScheme.verifyInternal vp prims (emptyContextMessage msg) sig pk) :
      ProbComp Bool)] := by
  unfold unforgeableExp
  rw [ProbCompRuntime.probComp_evalDist]
  congr 1
  rw [generalAlg_keygen_eq]
  simp only [bind_assoc, pure_bind]
  refine bind_congr fun skSeed => bind_congr fun skPrf => bind_congr fun pkSeed => ?_
  refine bind_congr fun x => ?_
  rw [generalAlg_verify, pure_bind]

/-! ## The hop -/

/-- **In the real `PRF` experiment the reduction is the CMA game.**  Its success probability is
the forger's EUF-CMA advantage exactly, not up to a bound.

*Message-`PRF` reduction.* -/
theorem prfRealExp_msgPrfReduction_apply (adv : unforgeableAdv (generalAlg prims)) :
    𝒟[PRFScheme.prfRealExp (msgPrfScheme prims) (msgPrfReduction prims adv)] {true}
      = adv.advantage ProbCompRuntime.probComp := by
  rw [unforgeableAdv.advantage, unforgeableExp_generalAlg, prfRealExp_msgPrfReduction]
  congr 1
  exact evalDist_bind_bind_swap_of_countable _ _ _

/-- **The `MKG_PRF` hop, taken.**  The forger's EUF-CMA advantage is at most the `PRF_msg`
distinguishing advantage of a distinguisher *constructed from that forger*, plus the advantage
that survives the hop.

Both right-hand terms are functions of `adv`.  This is the field-free replacement for the
`mkgAdv`, `idealAdvantage` and `prfHops` parts of
`HashSig.SLHDSA.Security.Composition`'s `Certificate`: there the `MKG_PRF` summand is an
advantage at an adversary a caller supplies, and here it is an advantage at a named
construction, which no caller can re-choose.

*Message-`PRF` reduction.* -/
theorem advantage_le_msgPrf_add_ideal (adv : unforgeableAdv (generalAlg prims)) :
    adv.advantage ProbCompRuntime.probComp ≤
      prfAbsAdvantage (msgPrfScheme prims) (msgPrfReduction prims adv)
        + msgPrfIdealAdvantage prims adv := by
  rw [← prfRealExp_msgPrfReduction_apply, msgPrfIdealAdvantage]
  exact prfRealExp_le_prfAbsAdvantage_add_prfIdealExp _ _

end SLHDSA.Security
