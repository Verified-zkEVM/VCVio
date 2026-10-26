/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.SHAKE128s.Bridge.Wire.KeyLog
public import HashSig.SLHDSA.SHAKE128s.Statement.Game.CompleteBudget

/-!
# Fixed-context wire and counted-game equality

Forgetting the actual phase counters preserves the result and complete context-attached
signing log, including arbitrary related initial prefixes. At consistent keys, the external
verifier and returned-pair freshness identify the after-keygen winning program. Common key
generation and one shared random-oracle execution preserve the complete winning distribution
and strong-unforgeability advantage.
-/

public section

open OracleComp OracleSpec SignatureAlg

namespace SLHDSA.SHAKE128s.Bridge

/-- Private sampling, the shared SHAKE-128s oracle and raw-byte signing requests. -/
abbrev WireAdversarySpec :=
  (unifSpec + SLHDSA.Security.shakeSpec FIPS205.params) + (Bytes →ₒ Bytes)

/-- Canonical public-key bytes presented to a SHAKE-128s wire adversary. -/
abbrev encodeWirePublicKey (pk : PublicKeyCore FIPS205.core) : Bytes :=
  (publicKeyCodec (Concrete.shakeWireCodec FIPS205.params.params)).encode pk

/-- A single returned wire pair becomes the same pair with its fixed context and `some`. -/
theorem fixedContextLog_singleton (ctx : SLHDSA.Security.PureContext) (message signature : Bytes) :
    fixedContextLog ctx [⟨message, signature⟩] =
      [⟨⟨message, ctx.bytes⟩, some signature⟩] := rfl

/-- Agreement of signing programs identifies the actual phase result and complete
context-attached log after forgetting only the phase counters. -/
theorem runPhase_fixedContextHandler_of_sign_eq {PK SK α : Type}
    (scheme : Game.ExternalScheme FIPS205.Answer PK SK)
    (alg : SignatureAlg (OracleComp (Game.World FIPS205.Answer)) Bytes Bytes SK Bytes)
    (ctx : SLHDSA.Security.PureContext) (sk : SK) (pk : Bytes)
    (sign_eq : ∀ message, scheme.sign sk { message := message, context := ctx.bytes } =
      (fun signature => some signature) <$> alg.sign pk sk message)
    (program : OracleComp WireAdversarySpec α) (signedPrefix : QueryLog (Bytes →ₒ Bytes)) :
    (fun z : (α × Game.Counts) × Game.SigningLog => (z.1.1, z.2)) <$>
        Game.runPhase scheme sk
          (simulateQ (fixedContextHandler ctx) program) (fixedContextLog ctx signedPrefix) =
      (fun z => (z.1, fixedContextLog ctx (signedPrefix ++ z.2))) <$>
        alg.runWithSigningOracle pk sk program := by
  induction program using OracleComp.inductionOn generalizing signedPrefix with
  | pure value =>
      simp [SignatureAlg.runWithSigningOracle]
  | query_bind input next ih =>
      rcases input with input | message
      · simp only [simulateQ_bind, simulateQ_spec_query, fixedContextHandler_world]
        rw [Game.runPhase_bind, Game.runPhase_query_world]
        simp only [bind_map_left, map_bind, map_pure]
        simp [SignatureAlg.runWithSigningOracle, SignatureAlg.signingOracle,
          QueryImpl.passthrough_add, ih]
      · simp only [simulateQ_bind, simulateQ_spec_query, fixedContextHandler_sign,
          bind_map_left]
        rw [Game.runPhase_bind, Game.runPhase_query_sign]
        rw [sign_eq]
        simp only [bind_map_left, map_bind, map_pure]
        suffices
            (do
              let signature ← alg.sign pk sk message
              (fun z : (α × Game.Counts) × Game.SigningLog => (z.1.1, z.2)) <$>
                Game.runPhase scheme sk (simulateQ (fixedContextHandler ctx) (next signature))
                  (fixedContextLog ctx
                    (signedPrefix ++ [(⟨message, signature⟩ : (_ : Bytes) × Bytes)]))) =
            (do
              let signature ← alg.sign pk sk message
              (fun z : α × QueryLog (Bytes →ₒ Bytes) => (z.1,
                fixedContextLog ctx
                  ((signedPrefix ++ [(⟨message, signature⟩ : (_ : Bytes) × Bytes)]) ++ z.2))) <$>
                alg.runWithSigningOracle pk sk (next signature)) by
          simpa [SignatureAlg.runWithSigningOracle, SignatureAlg.signingOracle,
            QueryImpl.passthrough_add, fixedContextLog_append, fixedContextLog_singleton,
            List.append_assoc] using this
        exact bind_congr fun signature => ih signature (signedPrefix ++ [⟨message, signature⟩])

/-- At consistent keys, the actual phase retains every context-attached wire log entry. -/
theorem runPhase_fixedContextHandler (ctx : SLHDSA.Security.PureContext)
    (sk : SecretKeyCore FIPS205.core) (pk : PublicKeyCore FIPS205.core)
    (consistent : pk = FIPS205.SecretKeyCore.publicKey sk)
    {α : Type} (program : OracleComp WireAdversarySpec α)
    (signedPrefix : QueryLog (Bytes →ₒ Bytes)) :
    (fun z : (α × Game.Counts) × Game.SigningLog => (z.1.1, z.2)) <$>
        Game.runPhase FIPS205.scheme sk
          (simulateQ (fixedContextHandler ctx) program) (fixedContextLog ctx signedPrefix) =
      (fun z => (z.1, fixedContextLog ctx (signedPrefix ++ z.2))) <$>
        (wireAlgorithm ctx).runWithSigningOracle (encodeWirePublicKey pk) sk program :=
  runPhase_fixedContextHandler_of_sign_eq FIPS205.scheme (wireAlgorithm ctx) ctx sk
    (encodeWirePublicKey pk)
    (fixedContext_sign_eq_wire_sign ctx sk pk consistent) program signedPrefix

/-- Mapping a phase result leaves its actual counts and complete signing log unchanged. -/
theorem runPhase_map {Output PK SK α β : Type}
    (scheme : Game.ExternalScheme Output PK SK) (sk : SK)
    (program : OracleComp (Game.World Output + Game.SigningSpec) α) (f : α → β)
    (signed : Game.SigningLog) :
    Game.runPhase scheme sk (f <$> program) signed =
      (fun z => ((f z.1.1, z.1.2), z.2)) <$> Game.runPhase scheme sk program signed := by
  simp [Game.runPhase, Prod.map]

/-- Forgetting the query-cost vector recovers the original world program. -/
theorem fst_map_countQueries {Output α : Type}
    (cost : (Game.World Output).Domain → Game.Counts)
    (program : OracleComp (Game.World Output) α) :
    Prod.fst <$> Game.countQueries cost program = program := by
  simpa only [Game.countQueries, Functor.map_map, Function.comp_def] using
    fst_map_run_simulateQ_addCostOracle cost program

/-- The actual named adversary retains its complete forgery and context-attached signing log. -/
theorem runPhase_fixedContextAdversary (ctx : SLHDSA.Security.PureContext)
    (sk : SecretKeyCore FIPS205.core) (pk : PublicKeyCore FIPS205.core)
    (consistent : pk = FIPS205.SecretKeyCore.publicKey sk)
    (adv : StrongUnforgeableAdversary (wireAlgorithm ctx))
    (signedPrefix : QueryLog (Bytes →ₒ Bytes)) :
    (fun z : (Game.Forgery × Game.Counts) × Game.SigningLog => (z.1.1, z.2)) <$>
        Game.runPhase FIPS205.scheme sk ((fixedContextAdversary ctx adv).main pk)
          (fixedContextLog ctx signedPrefix) =
      (fun z => (Game.Forgery.mk ⟨z.1.1, ctx.bytes⟩ z.1.2,
        fixedContextLog ctx (signedPrefix ++ z.2))) <$>
        (wireAlgorithm ctx).runWithSigningOracle (encodeWirePublicKey pk) sk
          (adv.main (encodeWirePublicKey pk)) := by
  change _ <$> Game.runPhase _ _ (_ <$> simulateQ _ _) _ = _
  rw [runPhase_map]
  have h := runPhase_fixedContextHandler ctx sk pk consistent
    (adv.main (encodeWirePublicKey pk)) signedPrefix
  have h' := congrArg (fun computation =>
    (fun z : (Bytes × Bytes) × Game.SigningLog =>
      (Game.Forgery.mk ⟨z.1.1, ctx.bytes⟩ z.1.2, z.2)) <$> computation) h
  simpa only [Functor.map_map, Function.comp_def] using h'

/-- A continuation that ignores the query-cost vector executes the original world program. -/
theorem countQueries_bind {Output α β : Type}
    (cost : (Game.World Output).Domain → Game.Counts)
    (program : OracleComp (Game.World Output) α)
    (next : α → OracleComp (Game.World Output) β) :
    (Game.countQueries cost program >>= fun result => next result.1) = program >>= next := by
  rw [← bind_map_left, fst_map_countQueries]

/-- The computed winning bit is verification conjoined with returned-pair freshness. -/
theorem decide_Wins_mk (forgery : Game.Forgery) (signed : Game.SigningLog)
    (verified : Bool) (counts : Game.Counts) :
    decide (Game.Wins ⟨forgery, signed, verified, counts⟩) =
      (verified && decide (Game.Fresh signed forgery)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, Bool.and_eq_true]
  rfl

/-- At consistent keys, the actual after-keygen winning program is the canonical wire program. -/
theorem afterKeygen_fixedContext (ctx : SLHDSA.Security.PureContext)
    (sk : SecretKeyCore FIPS205.core) (pk : PublicKeyCore FIPS205.core)
    (consistent : pk = FIPS205.SecretKeyCore.publicKey sk)
    (adv : StrongUnforgeableAdversary (wireAlgorithm ctx)) :
    (fun outcome => decide (Game.Wins outcome)) <$>
        Game.afterKeygen FIPS205.scheme (fixedContextAdversary ctx adv) (sk, pk) = do
      let ((msg, signature), signed) ← (wireAlgorithm ctx).runWithSigningOracle
        (encodeWirePublicKey pk) sk (adv.main (encodeWirePublicKey pk))
      let verified ← (wireAlgorithm ctx).verify (encodeWirePublicKey pk) msg signature
      return !signingLogContains signed msg signature && verified := by
  rw [Game.afterKeygen_eq_runPhase]
  simp only [map_bind, map_pure, decide_Wins_mk]
  trans (do
    let result ← (fun z : (Game.Forgery × Game.Counts) × Game.SigningLog =>
      (z.1.1, z.2)) <$> Game.runPhase FIPS205.scheme sk
        ((fixedContextAdversary ctx adv).main pk) (fixedContextLog ctx [])
    let verified ← FIPS205.scheme.verify pk result.1.message result.1.signature
    pure (verified && decide (Game.Fresh result.2 result.1)))
  · simp only [bind_map_left]
    apply bind_congr
    intro a
    exact countQueries_bind _ _ (fun verified =>
      pure (verified && decide (Game.Fresh a.2 a.1.1)))
  · rw [runPhase_fixedContextAdversary ctx sk pk consistent adv []]
    simp only [bind_map_left, List.nil_append]
    simp_rw [fixedContext_verify_eq_wire_verify, decide_fresh_fixedContextLog]
    simp [encodeWirePublicKey, Bool.and_comm]

/-- A continuation that ignores total hash counts retains the complete original world program. -/
theorem countAllHashes_bind {Output α β : Type}
    (program : OracleComp (Game.World Output) α)
    (next : α → OracleComp (Game.World Output) β) :
    (Game.countAllHashes program >>= fun result => next result.1) = program >>= next := by
  rw [← bind_map_left, Game.fst_map_countAllHashes]

/-- Winning ignores the experiment's outer key-generation and later-hash counters. -/
theorem experimentBySource_win {Output PK SK : Type}
    (scheme : Game.ExternalScheme Output PK SK) (adversary : Game.Adversary Output PK) :
    (fun result => decide (Game.Wins result.1)) <$> Game.experimentBySource scheme adversary =
      (scheme.keygen >>= fun keys =>
        (fun outcome => decide (Game.Wins outcome)) <$>
          Game.afterKeygen scheme adversary keys) := by
  simp only [Game.experimentBySource, map_bind, map_pure]
  trans (Game.countAllHashes scheme.keygen >>= fun result =>
    (fun outcome => decide (Game.Wins outcome)) <$> Game.afterKeygen scheme adversary result.1)
  · apply bind_congr
    intro keys
    simpa only [map_eq_bind_pure_comp, Function.comp_def] using
      countAllHashes_bind (Game.afterKeygen scheme adversary keys.1)
        (fun outcome => pure (decide (Game.Wins outcome)))
  · exact countAllHashes_bind scheme.keygen
      (fun keys : SK × PK =>
        (fun outcome => decide (Game.Wins outcome)) <$> Game.afterKeygen scheme adversary keys)

/-- Byte-wire key generation maps only the public-key component of the underlying keys. -/
theorem wireScheme_keygen {ι : Type} {spec : OracleSpec ι} {M E PK WPK SK S WS : Type}
    (alg : SignatureAlg (OracleComp spec) M PK SK S) (message : E → M)
    (pk : CanonicalEncoding PK WPK) (sig : CanonicalEncoding S WS) :
    (SignatureAlg.Wire.scheme alg message pk sig).keygen =
      (fun keys => (pk.encode keys.1, keys.2)) <$> alg.keygen := rfl

/-- The fixed-context wire scheme and typed FIPS game use the same generated keys. -/
theorem wireAlgorithm_keygen (ctx : SLHDSA.Security.PureContext) :
    (wireAlgorithm ctx).keygen =
      (fun keys => (encodeWirePublicKey keys.1, keys.2)) <$> FIPS205.internal.keygen := by
  simpa only [wireAlgorithm, SLHDSA.Security.wireShakeScheme, encodeWirePublicKey,
    WireCodec.canonicalEncoding] using wireScheme_keygen FIPS205.internal ctx.encode
      (publicKeyCodec (Concrete.shakeWireCodec FIPS205.params.params)).canonicalEncoding
      (signatureCodec FIPS205.params
        (Concrete.shakeWireCodec FIPS205.params.params)).canonicalEncoding

/-- Common key generation and pointwise winning programs determine the complete experiment. -/
theorem experimentBySource_eq_of_common_keygen {Output PK SK : Type}
    (scheme : Game.ExternalScheme Output PK SK)
    (alg : SignatureAlg (OracleComp (Game.World Output)) Bytes Bytes SK Bytes)
    (adversary : Game.Adversary Output PK) (adv : StrongUnforgeableAdversary alg)
    (common : OracleComp (Game.World Output) (PK × SK)) (encodePK : PK → Bytes)
    (targetKeygen : scheme.keygen = (fun keys => (keys.2, keys.1)) <$> common)
    (wireKeygen : alg.keygen = (fun keys => (encodePK keys.1, keys.2)) <$> common)
    (afterEq : ∀ keys ∈ support common,
      (fun outcome => decide (Game.Wins outcome)) <$>
        Game.afterKeygen scheme adversary (keys.2, keys.1) = do
          let ((msg, signature), signed) ← alg.runWithSigningOracle (encodePK keys.1) keys.2
            (adv.main (encodePK keys.1))
          let verified ← alg.verify (encodePK keys.1) msg signature
          return !signingLogContains signed msg signature && verified) :
    (fun result => decide (Game.Wins result.1)) <$> Game.experimentBySource scheme adversary =
      strongUnforgeableExperiment adv := by
  rw [experimentBySource_win, strongUnforgeableExperiment, wireKeygen, targetKeygen]
  simp only [bind_map_left]
  apply OracleComp.bind_congr_of_forall_mem_support
  intro keys member
  refine (afterEq keys member).trans ?_
  apply bind_congr
  rintro ⟨⟨message, signature⟩, signed⟩
  apply bind_congr
  intro verified
  congr 1
  congr 2
  exact decide_eq_decide.mpr Iff.rfl

/-- The complete adapted winning program is the canonical wire strong-unforgeability program. -/
theorem experimentBySource_fixedContext (ctx : SLHDSA.Security.PureContext)
    (adv : StrongUnforgeableAdversary (wireAlgorithm ctx)) :
    (fun result => decide (Game.Wins result.1)) <$>
        Game.experimentBySource FIPS205.scheme (fixedContextAdversary ctx adv) =
      strongUnforgeableExperiment adv := by
  have targetKeygen : FIPS205.scheme.keygen =
      (fun keys => (keys.2, keys.1)) <$> FIPS205.internal.keygen := rfl
  exact experimentBySource_eq_of_common_keygen
    FIPS205.scheme (wireAlgorithm ctx) (fixedContextAdversary ctx adv) adv
    FIPS205.internal.keygen encodeWirePublicKey targetKeygen (wireAlgorithm_keygen ctx)
    (fun keys member => afterKeygen_fixedContext ctx keys.2 keys.1
      (internal_keygen_consistent keys member) adv)

/-- The fixed 30-byte SHAKE game and wire runtime share their entire oracle handler. -/
theorem sharedRO_impl :
    RandomOracleModel.impl Bytes FIPS205.Answer =
      (SLHDSA.Security.shakeSpec FIPS205.params).romImpl := rfl

/-- Mapping an output leaves the single threaded random-oracle execution unchanged. -/
theorem randomOracleModel_run_map {Output α β : Type} [SampleableType Output]
    (program : OracleComp (Game.World Output) α) (f : α → β) :
    RandomOracleModel.run (f <$> program) = f <$> RandomOracleModel.run program := by
  simp [RandomOracleModel.run]

/-- Exact winning-program equality identifies success probabilities under one shared oracle. -/
theorem advantage_eq_of_winProgram_eq
    {Output PK SK M WPK WSK S : Type} [SampleableType Output]
    (scheme : Game.ExternalScheme Output PK SK) (targetAdv : Game.Adversary Output PK)
    (alg : SignatureAlg (OracleComp (Game.World Output)) M WPK WSK S)
    (adv : StrongUnforgeableAdversary alg)
    (winProgram : (fun result => decide (Game.Wins result.1)) <$>
      Game.experimentBySource scheme targetAdv = strongUnforgeableExperiment adv) :
    strongUnforgeableAdvantage (ProbCompRuntime.rom (RandomOracleModel.HashSpec Bytes Output)) adv =
      (Game.securityGame scheme).advantage () targetAdv := by
  have runEq := congrArg (fun program => RandomOracleModel.run program) winProgram
  rw [randomOracleModel_run_map] at runEq
  rw [SignatureAlg.strongUnforgeableAdvantage]
  change 𝒟[RandomOracleModel.run (strongUnforgeableExperiment adv)] {true} = _
  rw [← prEvent_eq_evalDist_singleton, ← runEq]
  change Pr{let result ← (fun result => decide (Game.Wins result.1)) <$>
    RandomOracleModel.run (Game.experimentBySource scheme targetAdv)}[result = true] =
    Pr{let result ← (fun result => (decide (Game.Wins result.1), result.2)) <$>
      RandomOracleModel.run (Game.experimentBySource scheme targetAdv)}[result.1 = true]
  simp only [prEvent_map]

/-- A fixed-context wire adversary and its actual FIPS game adaptation have equal advantages. -/
theorem strongUnforgeableAdvantage_eq_fixedContext (ctx : SLHDSA.Security.PureContext)
    (adv : StrongUnforgeableAdversary (wireAlgorithm ctx)) :
    strongUnforgeableAdvantage (SLHDSA.Security.shakeRuntime FIPS205.params) adv =
      (Game.securityGame FIPS205.scheme).advantage () (fixedContextAdversary ctx adv) :=
  advantage_eq_of_winProgram_eq FIPS205.scheme (fixedContextAdversary ctx adv)
    (wireAlgorithm ctx) adv (experimentBySource_fixedContext ctx adv)

end SLHDSA.SHAKE128s.Bridge
