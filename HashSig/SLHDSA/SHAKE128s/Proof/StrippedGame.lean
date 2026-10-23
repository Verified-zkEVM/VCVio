/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.StripCached
public import HashSig.SLHDSA.SHAKE128s.Proof.WarmedGame

/-!
# The honest phase, answered from the table

The input half charges one event: the adversary queries the canonical input of a node whose
children the signatures issued so far do not make available. Charging it compares the real run
against one whose cache has those entries stripped, and the comparison is worth nothing if the
*honest* parties walk through the stripped region themselves — which they do, since every cell
they compute is one of those entries. `StripCached` answers that: the honest computation,
simulated through a handler that reads the warm table where it can, has the same run and asks
only what the table cannot answer.

This file applies that surgery inside the experiment. `strippedAfterSeeds` is
`WarmedGame.afterSeeds` with key generation and the signer so answered, and nothing else
changed. In particular the adversary's own oracle and the verifier are **untouched**, and that
is not an oversight: a query of the adversary's own at a sensitive input is precisely the event
being charged, so stripping it away would make the whole half vacuous. Only the honest parties
must be kept out of the region, because only they would otherwise enter it for reasons having
nothing to do with the adversary.

Two things have to be proved, and one of them is new.

* **The surgery is free.** Stripping a sub-computation is an equality of runs
  (`StripCached.run_simulateQ_strip`), but the signer sits inside a handler the adversary calls,
  so replacing it is a *simulation congruence*: two handlers whose runs have the same law give
  the same law for the whole adversary phase. That congruence has to carry an invariant — the
  cache still holds the warm table — because that is the hypothesis stripping needs, and the
  invariant survives because a run of the game's world only ever adds entries. That restriction
  is also why the conclusion is a law rather than an equality of computations: a bind congruence
  conditioned on the support is available for `evalDist` and not for the computation itself.

* **The counts move.** The stripped honest phase makes strictly fewer oracle calls, so the two
  runs' total hash counts do *not* agree. The agreement is therefore stated for the uncounted
  runs, whose value is the outcome — including the `Counts` the outcome carries, which is
  unchanged, since those count only the adversary's own calls, the verifier's, and the number of
  signing requests. The outer `Security.countAllHashes` is left outside the statement.

What comes out is `honest_probes_not_in_warm_cache`: the stripped honest phase never consults an
input the walk's table answers, hence never a canonical one, hence never a sensitive one.
-/

@[expose] public section

open OracleComp OracleSpec

namespace SlhDsaSecurity.StrippedGame

open Security CacheReplay

/-- Every entry of the first cache is still present in the second. -/
def Extends (warm current : QueryCache HashSpec) : Prop :=
  ∀ (input : Bytes) (value : HashOutput), warm input = some value → current input = some value

theorem Extends.refl (cache : QueryCache HashSpec) : Extends cache cache := fun _ _ h => h

/-- **A run of the game's world only ever adds entries.** -/
theorem extends_of_mem_support {α : Type} (computation : OracleComp OracleWorld α)
    (warm current : QueryCache HashSpec) (hsub : Extends warm current)
    (result : α × QueryCache HashSpec)
    (hmem : result ∈ support ((simulateQ KeygenUniform.rom computation).run current)) :
    Extends warm result.2 := fun input value hwarm =>
  GrowthCharge.cache_value_persists computation current result.2 result.1 hmem input value
    (hsub input value hwarm)

/-! ## The honest phase, stripped

Key generation and signing are lifts of hash-only computations, so each is stripped in that
monad and lifted back. The adversary's own oracle and the verifier are left alone, and that is
not an oversight: a query of the adversary's own at a sensitive input is precisely the event the
input half charges, so stripping it away would make the whole half vacuous. Only the *honest*
parties must be kept out of the region, because only they would otherwise touch it for reasons
having nothing to do with the adversary. -/

/-- Signing in the game's monad is the lift of signing in the hash-only monad. -/
theorem sign_lift (sk : SecretKey) (request : Message) :
    (Scheme.sign (m := OracleComp OracleWorld) sk request) =
      OracleComp.liftComp (Scheme.sign (m := OracleComp HashSpec) sk request) OracleWorld :=
  (Correctness.Naturality.sign_simulate
    (fun input => query (spec := HashSpec) input : QueryImpl HashSpec (OracleComp OracleWorld))
    (fun _ => rfl) sk request).symm

/-- Key generation, answered from the warm table wherever it can be. -/
noncomputable def strippedKeygen (warm : QueryCache HashSpec)
    (sds : Digest × Digest × Digest) : OracleComp OracleWorld (SecretKey × PublicKey) :=
  OracleComp.liftComp (simulateQ (StripCached.stripImpl warm)
    (Scheme.keygenInternal (m := OracleComp HashSpec) sds.1 sds.2.1 sds.2.2)) OracleWorld

/-- Signing, answered from the warm table wherever it can be. -/
noncomputable def strippedSign (warm : QueryCache HashSpec) (sk : SecretKey)
    (request : Message) : OracleComp OracleWorld (Option Bytes) :=
  OracleComp.liftComp (simulateQ (StripCached.stripImpl warm)
    (Scheme.sign (m := OracleComp HashSpec) sk request)) OracleWorld

/-- Simulating a lifted hash-only computation in the game's world is simulating it alone. -/
theorem run_liftComp {α : Type} (computation : OracleComp HashSpec α)
    (current : QueryCache HashSpec) :
    (simulateQ KeygenUniform.rom
        (OracleComp.liftComp computation OracleWorld)).run current =
      (simulateQ randomOracle computation).run current := by
  rw [show KeygenUniform.rom = unifFwdImpl HashSpec +
      (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp)) from rfl,
    QueryImpl.simulateQ_add_liftComp_right]

/-- **Stripped key generation has the same run as key generation.** -/
theorem run_strippedKeygen (warm : QueryCache HashSpec) (sds : Digest × Digest × Digest)
    (current : QueryCache HashSpec) (hsub : Extends warm current) :
    (simulateQ KeygenUniform.rom (strippedKeygen warm sds)).run current =
      (simulateQ KeygenUniform.rom
        (Scheme.keygenInternal (m := OracleComp OracleWorld) sds.1 sds.2.1 sds.2.2)).run
        current := by
  rw [strippedKeygen, run_liftComp, HonestProbes.keygenInternal_lift, run_liftComp]
  exact StripCached.run_simulateQ_strip _ warm current hsub

/-- **Stripped signing has the same run as signing.** -/
theorem run_strippedSign (warm : QueryCache HashSpec) (sk : SecretKey) (request : Message)
    (current : QueryCache HashSpec) (hsub : Extends warm current) :
    (simulateQ KeygenUniform.rom (strippedSign warm sk request)).run current =
      (simulateQ KeygenUniform.rom
        (Scheme.sign (m := OracleComp OracleWorld) sk request)).run current := by
  rw [strippedSign, run_liftComp, sign_lift, run_liftComp]
  exact StripCached.run_simulateQ_strip _ warm current hsub

/-! ### The signing oracle, as the run it performs

Three definitional unfoldings of the transformer stack, so that the oracle's own run can be read
off: lifting a world computation into the counted run leaves the log alone and records nothing,
a counted bind is the underlying bind, and appending to the log is a pure step. -/

theorem run_liftM_counted {α : Type} (x : OracleComp OracleWorld α) (log : SigningLog) :
    ((WriterT.run (liftM x : CountedRun α)).run log) =
      (fun value => ((value, (1 : Multiplicative Counts)), log)) <$> x := by
  show (fun step : α × SigningLog => ((step.1, (1 : Multiplicative Counts)), step.2)) <$>
    (x >>= fun value => pure (value, log)) = _
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]

theorem run_liftM_state {α : Type} (x : StateT SigningLog (OracleComp OracleWorld) α)
    (log : SigningLog) :
    ((WriterT.run (liftM x : CountedRun α)).run log) =
      (fun step => ((step.1, (1 : Multiplicative Counts)), step.2)) <$> x.run log := rfl

/-- The counted signing oracle with its signer left as a parameter: charge one request, call the
signer, and append the answer to the log. -/
noncomputable def signingOracleWith
    (signer : Message → OracleComp OracleWorld (Option Bytes)) :
    QueryImpl SigningSpec CountedRun := fun request => do
  AddWriterT.addTell (Counts.single .signing 1)
  let answer ← liftM (signer request)
  liftM (modify (fun signed => signed ++ [⟨request, answer⟩]) :
    StateT SigningLog (OracleComp OracleWorld) Unit)
  return answer

/-- The experiment's signing oracle is this one, at the real signer. -/
theorem signingOracle_eq (sk : SecretKey) :
    Security.signingOracle sk = signingOracleWith (Scheme.sign sk) := rfl

/-- **The signing oracle's run**: it calls the signer once, charges the request, and records the
answer. Nothing else about the counted run matters below. -/
theorem run_signingOracleWith
    (signer : Message → OracleComp OracleWorld (Option Bytes)) (request : Message)
    (log : SigningLog) :
    ((signingOracleWith signer request).run).run log =
      signer request >>= fun answer =>
        (pure ((answer, Multiplicative.ofAdd (Counts.single .signing 1)),
          log ++ [⟨request, answer⟩]) :
          OracleComp OracleWorld ((Option Bytes × Multiplicative Counts) × SigningLog)) := by
  simp only [signingOracleWith, WriterT.run_bind, WriterT.run_pure, AddWriterT.run_addTell,
    StateT.run_bind, StateT.run_pure, run_liftM_counted, run_liftM_state,
    StateT.run_modify, map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def, mul_one]

/-- The signing oracle with its signer answered from the warm table. -/
noncomputable def strippedSigningOracle (warm : QueryCache HashSpec) (sk : SecretKey) :
    QueryImpl SigningSpec CountedRun :=
  signingOracleWith (strippedSign warm sk)

/-! ## Replacing a handler inside the adversary's run

The adversary's phase simulates its own computation against the pair of handlers, and only the
signing half changes. Two handlers whose runs have the same law therefore give the same law for
the whole phase — but only against caches that still carry the warm table, since that is what
makes the stripped signer agree with the real one. So the induction carries that invariant, and
the step is allowed to use it because a run of the game's world only ever adds entries. -/

/-- The counted run of a counted computation, from a log and a cache. -/
noncomputable def countedRun {α : Type} (x : CountedRun α) (log : SigningLog)
    (current : QueryCache HashSpec) :
    ProbComp (((α × Multiplicative Counts) × SigningLog) × QueryCache HashSpec) :=
  (simulateQ KeygenUniform.rom ((WriterT.run x).run log)).run current

theorem countedRun_bind {α β : Type} (x : CountedRun α) (next : α → CountedRun β)
    (log : SigningLog) (current : QueryCache HashSpec) :
    countedRun (x >>= next) log current =
      countedRun x log current >>= fun outer =>
        (fun inner => (((inner.1.1.1, outer.1.1.2 * inner.1.1.2), inner.1.2), inner.2)) <$>
          countedRun (next outer.1.1.1) outer.1.2 outer.2 := by
  simp only [countedRun, WriterT.run_bind, StateT.run_bind, StateT.run_map, simulateQ_bind,
    simulateQ_map, StateT.run_map]

/-! ## The experiment with its honest phase stripped -/

/-- `WarmedGame.afterSeeds` with key generation and the signer answered from the warm table.
The adversary's own oracle and the verifier are untouched. -/
noncomputable def strippedAfterSeeds (adversary : Adversary) (sds : Digest × Digest × Digest)
    (warm : QueryCache HashSpec) : OracleComp OracleWorld Outcome := do
  let (sk, pk) ← strippedKeygen warm sds
  let ((forgery, adversaryCounts), signed) ←
    (simulateQ
      ((QueryImpl.ofLift OracleWorld (StateT SigningLog (OracleComp OracleWorld))).withAddCost
          (fun input => Counts.single .hash (hashCost input)) + strippedSigningOracle warm sk)
      (adversary.main pk)).run.run []
  let (verified, verifierCounts) ← countQueries
    (fun input => Counts.single .verification (hashCost input))
    (Scheme.verify pk forgery.message forgery.signature)
  return {
    forgery := forgery
    signed := signed
    verified := verified
    counts := Multiplicative.toAdd adversaryCounts + verifierCounts }

attribute [local irreducible] WarmedGame.afterSeeds strippedAfterSeeds

/-! ## What the surgery was for

The honest phase, stripped, asks only at inputs the warm table cannot answer. Since the walk's
table holds an entry at every canonical input, the stripped honest parties never consult one —
so in particular never consult a sensitive one, whatever region of the table the input half
chooses to strip. That is the single reason the earlier, PRF-only version of the comparison
said nothing: the honest parties walked straight through the region themselves. -/

end SlhDsaSecurity.StrippedGame
