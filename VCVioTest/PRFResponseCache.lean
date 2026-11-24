/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import VCVio.CryptoFoundations.PRF.ResponseQueries
public import VCVio.CryptoFoundations.SyncSignatureAlg.PRFSimulation

/-!
# Full-response PRF cache controls

The first tests query one input twice and read a different field of the response each time. The
ideal handler draws one pair, caches it whole, and answers the second query from the cache, so the
second field comes from the same draw as the first. The query count still charges both calls.

The last tests run a small signer that queries the PRF at its epoch, through `idealHandler`. A
repeated epoch returns `none` without running the signer, so it makes no PRF query and leaves the
cache unchanged. A failed signature still uses up its epoch: a later request there returns `none`
even when it would have succeeded.
-/

public section
namespace VCVioTest.PRFResponseCache
open OracleComp OracleSpec PRFScheme.ResponseQueries SyncSignatureAlg SyncSignatureAlg.PRFSimulation

private theorem one {D S R : Type} (project : S → R) (input : Fin 1 → D) :
    responseQueries project 1 input =
      (fun r => [project r]) <$> PRFScheme.functionQuery (input 0) := by
  simp [responseQueries, Fin.mOfFn, List.ofFn_succ, List.ofFn_zero,
    map_eq_bind_pure_comp]

/-- Read the first field of the response at `()`, then the second field at the same input. -/
@[expose] def program :
    OracleComp (PRFScheme.PRFOracleSpec Unit (Bool × Bool)) (List Bool × List Bool) := do
  let left ← responseQueries Prod.fst 1 (fun _ => ())
  let right ← responseQueries Prod.snd 1 (fun _ => ())
  pure (left, right)

/-- The ideal handler draws one pair. The second query reads the second field of that cached pair,
which the first query did not return. -/
theorem full_cache :
    (simulateQ (PRFScheme.prfIdealQueryImpl (D := Unit) (R := Bool × Bool)) program).run ∅ =
      (fun r : Bool × Bool =>
        (([r.1], [r.2]), (∅ : (Unit →ₒ (Bool × Bool)).QueryCache).cacheQuery () r)) <$>
          ($ᵗ (Bool × Bool)) := by
  simp [program, one, PRFScheme.simulateQ_prfIdealQueryImpl_functionQuery,
    StateT.run_bind, map_eq_bind_pure_comp, bind_assoc]

/-- The query count charges both calls, although the second is answered from the cache: the program
makes at most two queries and is not bounded by one. -/
theorem two_calls : IsTotalQueryBound program 2 ∧ ¬ IsTotalQueryBound program 1 := by
  refine ⟨?_, fun h => ?_⟩
  · unfold program
    apply isTotalQueryBound_bind (n₂ := 1) (responseQueries_bound Prod.fst 1 (fun _ => ()))
    intro left
    apply isTotalQueryBound_bind (n₂ := 0) (responseQueries_bound Prod.snd 1 (fun _ => ()))
    intro right
    trivial
  · simp only [program, one, PRFScheme.functionQuery, map_eq_bind_pure_comp, bind_assoc] at h
    rw [isTotalQueryBound_query_bind_iff] at h
    have h' := h.2 (false, false)
    simp only [Function.comp_apply, pure_bind] at h'
    rw [isTotalQueryBound_query_bind_iff] at h'
    exact absurd h'.1 (by decide)

/-- Messages `true` fail. Message `false` signs at epoch `ep` with the first field of the PRF
response at `ep`. -/
@[expose] def scheme :
    SyncSignatureAlg (OracleComp (PRFScheme.PRFOracleSpec Bool (Bool × Bool)))
      Bool Unit Unit Bool Bool where
  keygen := pure ((), ())
  sign _ ep msg :=
    if msg then pure none else (fun r : Bool × Bool => some r.1) <$> PRFScheme.functionQuery ep
  verify _ _ _ _ := true

private theorem scheme_sign (sk : Unit) (ep msg : Bool) :
    scheme.sign sk ep msg =
      if msg then pure none else (fun r : Bool × Bool => some r.1) <$> PRFScheme.functionQuery ep :=
  rfl

/-- Send two signing requests and return both answers. -/
@[expose] def twoRequests (first second : Bool × Bool) :
    OracleComp (unifSpec + signingSpec Bool Bool Bool) (Option Bool × Option Bool) := do
  let a ← (unifSpec + signingSpec Bool Bool Bool).query (Sum.inr first)
  let b ← (unifSpec + signingSpec Bool Bool Bool).query (Sum.inr second)
  pure (a, b)

/-- Two successful-looking requests at epoch `true`. The signer runs only for the first. The second
returns `none`, so it makes no PRF query: the cache holds only the response drawn for the first
request, and the history keeps the first request. -/
theorem repeated_epoch :
    (simulateQ (idealHandler scheme ()) (twoRequests (true, false) (true, false))).run
      (emptyHistory, ∅) =
      (fun r : Bool × Bool => ((some r.1, none),
        (Function.update (emptyHistory : History Bool Bool Bool) true (some (false, some r.1)),
          (∅ : (Bool →ₒ (Bool × Bool)).QueryCache).cacheQuery true r))) <$>
        ($ᵗ (Bool × Bool)) := by
  have hsecond (r : Bool × Bool) (cache : (Bool →ₒ (Bool × Bool)).QueryCache) :=
    idealHandler_used scheme () true false
      (Function.update (emptyHistory : History Bool Bool Bool) true (some (false, some r.1)))
      cache false (some r.1) rfl
  simp [twoRequests, scheme_sign, idealHandler_unused _ _ _ _ emptyHistory _ rfl, StateT.run_bind,
    PRFScheme.simulateQ_prfIdealQueryImpl_functionQuery, hsecond]
  rfl

/-- The first request at epoch `false` fails. The second request there would succeed, but the
failed request has used up the epoch, so it returns `none`. The history records the failed first
request, and neither request queries the PRF. -/
theorem failure_uses_epoch :
    (simulateQ (idealHandler scheme ()) (twoRequests (false, true) (false, false))).run
      (emptyHistory, ∅) =
      pure ((none, none),
        (Function.update (emptyHistory : History Bool Bool Bool) false (some (true, none)),
          ∅)) := by
  have hsecond := idealHandler_used scheme () false false
    (Function.update (emptyHistory : History Bool Bool Bool) false (some (true, none)))
    ∅ true none rfl
  simp [twoRequests, scheme_sign, idealHandler_unused _ _ _ _ emptyHistory _ rfl, StateT.run_bind,
    hsecond]
  rfl

end VCVioTest.PRFResponseCache
