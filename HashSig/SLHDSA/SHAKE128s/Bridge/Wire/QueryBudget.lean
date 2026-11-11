/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.SHAKE128s.Bridge.Wire.Defs
public import HashSig.SLHDSA.SHAKE128s.Statement.Game.CompleteBudget

/-!
# Actual SHAKE-128s wire-game query budgets

The canonical intrinsic verifier certificate gives the actual external verifier its universal
3929-call cap. The fixed-context handler preserves the wire adversary's syntactic budgets, so
the real source-counted game has almost-sure work at most `qh + qs + verifierCap`. Only signing
requests, direct adversary hashes and final verification hashes are selected; private sampling,
key generation and signer-internal hashing remain excluded.
-/

public section

open OracleComp OracleSpec SignatureAlg

namespace SLHDSA.SHAKE128s.Bridge

open SLHDSA.Security

/-- The actual SHAKE-128s internal verifier makes at most `verifierCap` total oracle calls.
Canonical public-hash naturality and the one-query SHAKE encoding transport the intrinsic bound. -/
theorem isTotalQueryBound_FIPS205_internal_verify (pk : PublicKeyCore FIPS205.core) (msg : Bytes)
    (signature : GeneralScheme.SignatureCore FIPS205.params FIPS205.core) :
    IsTotalQueryBound (FIPS205.internal.verify pk msg signature) verifierCap := by
  let ambient : QueryImpl (publicHashSpec FIPS205.core)
      (OracleComp (unifSpec + hashSpec FIPS205.core)) :=
    QueryImpl.ofLift (publicHashSpec FIPS205.core) _
  let F : HasQuery.QueryHom (publicHashSpec FIPS205.core)
      (OracleComp (publicHashSpec FIPS205.core))
      (OracleComp (unifSpec + hashSpec FIPS205.core)) :=
    { toMonadHom := simulateQ' ambient
      map_query' _ := rfl }
  change IsTotalQueryBound
    (simulateQ (encImpl FIPS205.params)
      (GeneralScheme.verifyInternalM FIPS205.params FIPS205.core msg signature pk)) _
  rw [← GeneralScheme.verifyInternalM_natural FIPS205.params FIPS205.core F]
  change IsTotalQueryBound
    (simulateQ (encImpl FIPS205.params) (simulateQ ambient
      (GeneralScheme.verifyInternalM FIPS205.params FIPS205.core msg signature pk))) _
  rw [← QueryImpl.simulateQ_compose]
  simpa only [Nat.mul_one, verifierCap] using IsTotalQueryBound.simulateQ_of_step_le
    (GeneralScheme.verifyInternalM_isTotalQueryBound FIPS205.params FIPS205.core msg signature pk)
    (step := 1) (impl := encImpl FIPS205.params ∘ₛ ambient) (by
      intro t
      rcases t with (t | t)
      all_goals
        simp only [QueryImpl.apply_compose]
        exact ⟨Nat.one_pos, fun _ => trivial⟩)

/-- The actual external SHAKE-128s verifier has the universal cap 3929 (`verifierCap_eq`).
Invalid contexts and malformed encodings return before hashing. Acceptance is not assumed. -/
theorem isTotalQueryBound_FIPS205_verify (pk : PublicKeyCore FIPS205.core) (request : Message)
    (signature : Bytes) :
    IsTotalQueryBound (FIPS205.scheme.verify pk request signature) verifierCap := by
  simp only [FIPS205.scheme]
  split
  · trivial
  · split
    · trivial
    · exact isTotalQueryBound_FIPS205_internal_verify _ _ _

/-- The actual fixed-context transformation preserves syntactic hash and signing budgets.
One source signing query becomes one target signing request; ambient sampling remains free. -/
theorem fixedContextAdversary_romQueryBound (ctx : SLHDSA.Security.PureContext)
    (adv : StrongUnforgeableAdversary (wireAlgorithm ctx)) {qh qs : Nat}
    (hadv : adv.RomQueryBound qh qs) (pk : PublicKeyCore FIPS205.core) :
    IsQueryBoundP ((fixedContextAdversary ctx adv).main pk)
      (IsHashQuery (hs := RandomOracleModel.HashSpec Bytes FIPS205.Answer)
        (M := Message) (S := Option Bytes)) qh ∧
    IsQueryBoundP ((fixedContextAdversary ctx adv).main pk)
      (IsSignQuery (hs := RandomOracleModel.HashSpec Bytes FIPS205.Answer)
        (M := Message) (S := Option Bytes)) qs := by
  change IsQueryBoundP (_ <$> simulateQ _ _) _ _ ∧ IsQueryBoundP (_ <$> simulateQ _ _) _ _
  simp only [isQueryBoundP_map_iff]
  constructor
  · apply (hadv ((publicKeyCodec (Concrete.shakeWireCodec FIPS205.params.params)).encode
      pk)).1.simulateQ_of_step
    · rintro ((sample | hash) | msg) ht <;>
        simp_all [fixedContextHandler, IsHashQuery, isQueryBoundP_query_iff]
    · rintro ((sample | hash) | msg) ht <;>
        simp_all [fixedContextHandler, IsHashQuery, isQueryBoundP_map_iff, isQueryBoundP_query_iff]
  · apply (hadv ((publicKeyCodec (Concrete.shakeWireCodec FIPS205.params.params)).encode
      pk)).2.simulateQ_of_step
    · rintro ((sample | hash) | msg) ht <;>
        simp_all [fixedContextHandler, IsSignQuery, isQueryBoundP_map_iff, isQueryBoundP_query_iff]
    · rintro ((sample | hash) | msg) ht <;>
        simp_all [fixedContextHandler, IsSignQuery, isQueryBoundP_query_iff]

/-- A wire adversary within the syntactic lifetime signing budget obeys the actual game limit. -/
theorem withinSigningLimit_fixedContext (ctx : SLHDSA.Security.PureContext)
    (adv : StrongUnforgeableAdversary (wireAlgorithm ctx)) {qh qs : Nat}
    (hadv : adv.RomQueryBound qh qs) (hqs : qs ≤ signingLimit) :
    Game.WithinSigningLimit FIPS205.scheme (fixedContextAdversary ctx adv) :=
  (Game.almostSure_bounds FIPS205.scheme (fixedContextAdversary ctx adv)
    (fixedContextAdversary_romQueryBound ctx adv hadv)
    (fun pk forgery => isTotalQueryBound_FIPS205_verify pk forgery.message forgery.signature)).1 hqs

/-- A wire adversary with syntactic hash and signing budgets has almost-sure selected work
at most `qh + qs + verifierCap`, including final verification and every losing outcome. -/
theorem hasQueryBound_fixedContext (ctx : SLHDSA.Security.PureContext)
    (adv : StrongUnforgeableAdversary (wireAlgorithm ctx)) {qh qs : Nat}
    (hadv : adv.RomQueryBound qh qs) :
    (Game.securityGame FIPS205.scheme).HasQueryBound () Game.adversaryWork
      (fixedContextAdversary ctx adv) (qh + qs + verifierCap) :=
  (Game.almostSure_bounds FIPS205.scheme (fixedContextAdversary ctx adv)
    (fixedContextAdversary_romQueryBound ctx adv hadv)
    (fun pk forgery => isTotalQueryBound_FIPS205_verify pk forgery.message forgery.signature)).2

end SLHDSA.SHAKE128s.Bridge
