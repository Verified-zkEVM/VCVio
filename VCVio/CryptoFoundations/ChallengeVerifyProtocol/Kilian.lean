/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

module

public import VCVio.CryptoFoundations.VectorCommitment
public import VCVio.CryptoFoundations.ChallengeVerifyProtocol.Basic
public import VCVio.OracleComp.ProbComp
public import VCVio.OracleComp.QueryTracking.LoggingOracle.Core

/-!
# The Kilian Transformation

This file describes the Kilian transformation ([Kilian '92], [SNARGs book Chapter 20]).
This transformation converts a Probabilistically Checkable Proof (PCP)
into a succinct interactive argument using a vector commitment such as a Merkle tree.
This can then be made non-interactive using the Fiat-Shamir transformation
(these two transformations together are referred to by the SNARGs book as
the "Micali transformation" [Micali '00]).

The majority of the Kilian paper is a way to make the classic GMW graph-coloring
zero-knowledge proof more efficient while keeping zero knowledge by implementing a
"notarized envelope" primitive. This file focuses on the succinctness part.

## The commitment

The transformation is built on a `DetVectorCommitment` relative to one oracle `X →ₒ Y`
(`VCVio.CryptoFoundations.VectorCommitment`), for instance the salted Merkle tree of
`VCVio.CryptoFoundations.MerkleTree.Salted.Defs`. Its opening is batched: the prover opens the
whole set of positions the PCP verifier reads with a single proof, and the claimed values travel as
one partial vector `PartialVec pcp.length pcp.Symbol`.

`KilianTransformation` evaluates the commitment's oracle at a fixed function `H : X → Y`
(`VectorCommitment.fixedOracleImpl`), so the resulting protocol lives in `ProbComp` and its verifier
is a deterministic `Bool`, as `ChallengeVerifyProtocol` requires. Completeness holds for every `H`.

## Main results

- `PCP`: probabilistically checkable proofs with adaptive deterministic verifier queries, and their
  correctness/soundness notions.
- `KilianTransformation`: the succinct interactive argument built from a `PCP` and a
  `DetVectorCommitment`, with the oracle answered by `H`.
- `KilianTransformation_perfectlyComplete`: perfect completeness, from PCP completeness for a coin
  sampler with full support and perfect completeness of the commitment.
- `runVerifier_of_KilianTransformation_verify`: the deterministic core of soundness. If the values
  of an accepted response agree with some proof string, the PCP verifier accepts that string on
  the challenge coins.

Soundness proper is stated in the random-oracle model, where a cheating prover queries the oracle
and an extractor reads a proof string off its queries; the binding condition of the salted Merkle
extractor (ePrint 2025/2166, Thm 8.4 condition 2) supplies the agreement hypothesis of
`runVerifier_of_KilianTransformation_verify`. That statement, and knowledge soundness, are future
work.
-/

public section

open OracleComp OracleSpec

/-- A **Probabilistically Checkable Proof (PCP)** system for a relation `rel : Stmt → Wit → Bool`.

  The honest prover turns a statement and witness into a proof string of `length` symbols over the
  alphabet `Symbol`.

  The verifier draws random coins of type `Coins` (sampled by `sampleCoins`); *given* its coins it
  is the deterministic oracle computation `Verifier stmt coins`, which adaptively queries positions
  of the proof string (modeled by `Fin length →ₒ Symbol`) and outputs a single accept/reject bit.

  Separating the coins from the proof queries — rather than folding both into a single
  `OracleComp (unifSpec + (Fin length →ₒ Symbol))` — matches the public-coin structure used by the
  Kilian transformation: the verifier *sends* its coins, and the prover then simulates `Verifier
  stmt coins` to learn exactly which positions to open. -/
structure PCP (Stmt Wit : Type) where
  /-- The alphabet of the proof string. -/
  Symbol : Type
  /-- The alphabet is finite. -/
  [finSymbol : Fintype Symbol]
  /-- The number of symbols in a proof string. -/
  length : ℕ
  /-- The verifier's random coins. -/
  Coins : Type
  /-- The verifier's coin sampler. -/
  sampleCoins : ProbComp Coins
  /-- The honest prover, producing a proof string from a statement and a witness. -/
  Prover : Stmt → Wit → ProbComp (List.Vector Symbol length)
  /-- The verifier on given coins: it queries positions of the proof string and accepts or
  rejects. -/
  Verifier : Stmt → Coins → OracleComp (Fin length →ₒ Symbol) Bool

namespace PCP

open scoped NNReal

variable {Stmt Wit : Type}

/-- Run the PCP verifier on statement `stmt` with fixed coins `coins` against a concrete proof
  string `proof`, answering each oracle query for position `i` with `proof.get i`. Since the coins
  are fixed and the proof is concrete, the result is a deterministic accept/reject bit. -/
@[expose]
def runVerifier (pcp : PCP Stmt Wit) (stmt : Stmt) (coins : pcp.Coins)
    (proof : List.Vector pcp.Symbol pcp.length) : Bool :=
  Id.run <| simulateQ (QueryImpl.ofListVector proof) (pcp.Verifier stmt coins)

/-- A PCP system satisfies **correctness** with error `correctnessError` if for every
  statement/witness pair `(stmt, wit)` in the relation, the honest verifier accepts a proof
  produced by the honest prover with probability at least `1 - correctnessError`. -/
@[expose]
noncomputable def correctness (pcp : PCP Stmt Wit) (rel : Stmt → Wit → Bool)
    (correctnessError : ℝ≥0) : Prop :=
  ∀ stmt : Stmt,
  ∀ wit : Wit,
    rel stmt wit →
      Pr{let accept ← (do
          let proof ← pcp.Prover stmt wit
          let coins ← pcp.sampleCoins
          return pcp.runVerifier stmt coins proof)}[accept] ≥ 1 - correctnessError

/-- A PCP system satisfies **perfect correctness** if it satisfies correctness with no error. -/
@[expose]
noncomputable def perfectCorrectness (pcp : PCP Stmt Wit) (rel : Stmt → Wit → Bool) : Prop :=
  pcp.correctness rel 0

/-- A PCP system satisfies **soundness** with error `soundnessError` if for every statement `stmt`
  outside the language (i.e. with no valid witness), and every adversarially chosen proof string,
  the verifier accepts with probability at most `soundnessError`.

  Since the verifier's only source of randomness is its own coin tosses, it suffices to quantify
  over fixed proof strings: a randomized malicious prover is a convex combination of these, so it
  can do no better than the best fixed proof. -/
@[expose]
noncomputable def soundness (pcp : PCP Stmt Wit) (rel : Stmt → Wit → Bool)
    (soundnessError : ℝ≥0) : Prop :=
  ∀ stmt : Stmt,
    (¬ ∃ wit : Wit, rel stmt wit) →
  ∀ proof : List.Vector pcp.Symbol pcp.length,
    Pr{let accept ← (do
        let coins ← pcp.sampleCoins
        return pcp.runVerifier stmt coins proof)}[accept] ≤ soundnessError

/-- A PCP system satisfies **perfect soundness** if it satisfies soundness with no error, i.e. the
  verifier never accepts a proof for a statement outside the language. -/
@[expose]
noncomputable def perfectSoundness (pcp : PCP Stmt Wit) (rel : Stmt → Wit → Bool) : Prop :=
  pcp.soundness rel 0

-- TODO: Definition 19.1.3. straightline knowledge soundness error with extraction time

end PCP

section ReadLog

/-! ## Read-log of a deterministic oracle computation

`pathLog so comp` is the list of inputs that `comp` queries, in the order it reads them, when its
oracles are answered by the handler `so`. It is the input-only projection of the generic query log
produced by `QueryImpl.withLogging`: each query/response pair `⟨t, u⟩` is recorded, and `pathLog`
keeps only the inputs `t`. The Kilian prover uses it to discover exactly which proof positions the
verifier reads. -/

universe u

variable {ι : Type u} {spec : OracleSpec ι}

/-- The inputs a deterministic computation queries when its oracles are answered by `so`, in the
order they are read: the `QueryImpl.withLogging` query log with each entry's response discarded. -/
@[expose]
def pathLog (so : QueryImpl spec Id) {α : Type u} (comp : OracleComp spec α) : List ι :=
  ((simulateQ so.withLogging comp).run.2).map Sigma.fst

/-- A query records its input at the head of the read-log and then continues: `withLogging` appends
`⟨t, so t⟩` for the query, so projecting to inputs prepends `t`. -/
theorem pathLog_query (so : QueryImpl spec Id) {α : Type u} (t : spec.Domain)
    (oa : spec.Range t → OracleComp spec α) :
    pathLog so (liftM (spec.query t) >>= oa) = t :: pathLog so (oa (so t)) := by
  unfold pathLog
  simp only [simulateQ_bind, simulateQ_spec_query, QueryImpl.withLogging_apply,
    WriterT.run_bind', WriterT.run_tell]
  rfl

end ReadLog

section AnswerFunctions

/-! ## The verifier's claim-lookup handler

The honest parties answer the deterministic PCP verifier with reusable pieces of the generic
`QueryImpl` library: purely with `QueryImpl.ofFn f` (answer query `i` with `f i`), and — when the
prover needs the positions read — with `pathLog`. `claimAnswer` below is the verifier's own
per-query handler: a failing lookup in the prover's claimed partial vector. -/

variable {ι Sym : Type*}

/-- Answer each query by looking it up in the claimed values `ans`, failing where `ans` has no
entry. This is the verifier's per-query handler in `KilianTransformation`. It is `QueryImpl.ofFn?`
over `ans`, using that `QueryImpl spec Option` is `QueryImpl spec (OptionT Id)`. -/
@[expose]
def claimAnswer (ans : ι → Option Sym) : QueryImpl (ι →ₒ Sym) (OptionT Id) :=
  QueryImpl.ofFn? ans

end AnswerFunctions

section KilianTransformation

variable {Stmt Wit : Type} {X : Type} {Y Cm Td Pf : Type}

/-- **The Kilian transformation.**

Turn a `PCP` into a (public-coin) succinct `ChallengeVerifyProtocol`, the interactive argument at
the heart of Kilian's protocol, from a deterministic vector commitment `vc` over the PCP's symbol
alphabet whose oracle is answered by the fixed function `H`:

1. the prover commits to its PCP proof string with `vc.commit`, retaining the proof string
   alongside the trapdoor as its private state (`commit`);
2. the verifier sends random coins (the protocol record carries no challenge sampler: completeness
   holds on every challenge);
3. the prover simulates `pcp.Verifier stmt coins` against its retained proof to learn exactly which
   positions the verifier reads, and opens *exactly* that set in one shot with `vc.opening`,
   returning the claimed values as a partial vector alongside the opening proof (`respond`);
4. the verifier checks the opening against the commitment with `vc.check`, then replays
   `pcp.Verifier stmt coins`, answering each position query from the claimed values, and accepts
   iff the opening verifies, every queried position was claimed, and the PCP verifier accepts
   (`verify`).

Succinctness is what makes Kilian interesting: only the positions the verifier actually queries
are opened, and `verify` rejects (through the failing branch of `claimAnswer`) if it ever reads an
unclaimed position. -/
@[expose]
noncomputable def KilianTransformation
    (pcp : PCP Stmt Wit)
    (vc : DetVectorCommitment X Y pcp.Symbol Cm Td Pf pcp.length) (H : X → Y)
    (rel : Stmt → Wit → Bool) :
    ChallengeVerifyProtocol Stmt Wit
      Cm                                                      -- Commit: the vector commitment
      (Td × (Fin pcp.length → pcp.Symbol))                    -- PrvState: trapdoor + proof
      pcp.Coins                                               -- Chal: the verifier's coins
      (PartialVec pcp.length pcp.Symbol × Pf)                 -- Resp: claims + opening proof
      rel ProbComp where
  commit stmt wit := do
    let proof ← pcp.Prover stmt wit
    let z ← simulateQ (VectorCommitment.fixedOracleImpl H) (vc.commit proof.get)
    return (z.1, (z.2, proof.get))
  respond stmt _wit st coins :=
    -- Simulate the verifier against the retained proof, logging the positions it reads, and open
    -- exactly those positions as a single batch.
    let queried : Finset (Fin pcp.length) := (pathLog st.2 (pcp.Verifier stmt coins)).toFinset
    return (PartialVec.restrict st.2 queried, vc.opening queried st.1)
  verify stmt c coins resp :=
    -- Check the opening, then replay the verifier answering each position from its claimed value;
    -- an unclaimed position fails the run, as does an opening that does not verify.
    evalWithAnswerFn (QueryImpl.ofFn H) (vc.check c resp.1 resp.2) &&
      (Id.run (simulateQ (claimAnswer resp.1) (pcp.Verifier stmt coins)).run == some true)

end KilianTransformation

section ReplayInfrastructure

/-! ## Deterministic replay infrastructure

The completeness of the Kilian transformation rests on a deterministic fact about the verifier:
the prover's logging simulation (which records the inputs the verifier reads), the verifier's own
replay against the prover's claims, and the bare run on the answer function are all the *same*
deterministic computation answered consistently. These lemmas package that fact for a fixed answer
function `f : ι → Sym` on a single-oracle spec `ι →ₒ Sym`. -/

universe u

variable {ι Sym : Type u}

/-- **Replay lemma.** If the claims answer every input the verifier reads (under `f`) with `f`'s
value, the verifier's `OptionT` replay never fails and reproduces the pure run. -/
theorem claimAnswer_run (f : ι → Sym) (ans : ι → Option Sym) {β : Type u}
    (comp : OracleComp (ι →ₒ Sym) β) :
    (∀ t ∈ pathLog f comp, ans t = some (f t)) →
      (simulateQ (claimAnswer ans) comp).run
        = some (evalWithAnswerFn (QueryImpl.ofFn f) comp) := by
  induction comp using OracleComp.inductionOn with
  | pure x => intro _; rfl
  | query_bind t oa ih =>
    intro h
    have ht : claimAnswer ans t = (pure (f t) : OptionT Id Sym) := by
      simp only [claimAnswer, QueryImpl.ofFn?,
        h t (by rw [pathLog_query]; exact List.mem_cons_self ..)]
      rfl
    have hq : evalWithAnswerFn (QueryImpl.ofFn f) (liftM ((ι →ₒ Sym).query t)) = f t := by
      change simulateQ (QueryImpl.ofFn f) (liftM ((ι →ₒ Sym).query t)) = f t
      rw [simulateQ_spec_query]; rfl
    simp only [simulateQ_bind, simulateQ_spec_query, ht, evalWithAnswerFn_bind, hq]
    exact ih (f t) (fun t' ht' => h t' (by rw [pathLog_query]; exact List.mem_cons_of_mem _ ht'))

/-- **Agreement replay lemma.** If every claimed value agrees with the answer function `f`, then a
successful (`some`-valued) replay against the claims coincides with the pure run on `f`: every
query the replay manages to answer is answered with `f`'s value, so the replay path *is* the
`f`-path. This is the soundness-side complement of `claimAnswer_run`: there the claims are known
to cover the `f`-path and the replay is shown to succeed; here the replay is assumed to succeed
and its result is pinned down, with no coverage hypothesis at all. -/
theorem eq_of_claimAnswer_run_eq_some (f : ι → Sym) (ans : ι → Option Sym)
    (hagree : ∀ i v, ans i = some v → v = f i) {β : Type u}
    (comp : OracleComp (ι →ₒ Sym) β) (b : β) :
    (simulateQ (claimAnswer ans) comp).run = some b →
      evalWithAnswerFn (QueryImpl.ofFn f) comp = b := by
  induction comp using OracleComp.inductionOn with
  | pure x => exact fun h => Option.some.inj h
  | query_bind t oa ih =>
    intro h
    rw [simulateQ_bind, simulateQ_spec_query] at h
    cases hlook : ans t with
    | none =>
      rw [show claimAnswer ans t = (failure : OptionT Id Sym) from by
        simp only [claimAnswer, QueryImpl.ofFn?, hlook]; rfl] at h
      -- A failed lookup fails the whole replay, contradicting the `some`-valued run.
      exact absurd h.symm (Option.some_ne_none b)
    | some v =>
      rw [show claimAnswer ans t = (pure v : OptionT Id Sym) from by
        simp only [claimAnswer, QueryImpl.ofFn?, hlook]; rfl, pure_bind] at h
      obtain rfl : v = f t := hagree t v hlook
      have hq : evalWithAnswerFn (QueryImpl.ofFn f) (liftM ((ι →ₒ Sym).query t)) = f t := by
        change simulateQ (QueryImpl.ofFn f) (liftM ((ι →ₒ Sym).query t)) = f t
        rw [simulateQ_spec_query]; rfl
      rw [evalWithAnswerFn_bind, hq]
      exact ih (f t) h

end ReplayInfrastructure

section Completeness

variable {Stmt Wit : Type} {rel : Stmt → Wit → Bool} {X : Type} {Y Cm Td Pf : Type}

/-- **Deterministic completeness core.** For fixed coins and any answer function `data` (for the
honest prover, its PCP proof string), the Kilian verifier accepts the restriction of `data` to an
opened set `Q`, provided:

* `hcov` — `Q` covers every position the PCP verifier reads against `data`
  (it does, since the prover opens exactly the logged positions);
* `hcheck` — the opening proof verifies (vector-commitment completeness); and
* `haccept` — the PCP verifier accepts `data` (PCP completeness).

The novel content is the `claimAnswer_run` replay: the verifier's failing `OptionT` replay against
the claims reproduces the bare PCP run, so it accepts exactly when the PCP run does. -/
theorem KilianTransformation_verify_eq_true
    (pcp : PCP Stmt Wit)
    (vc : DetVectorCommitment X Y pcp.Symbol Cm Td Pf pcp.length) (H : X → Y)
    (boolRel : Stmt → Wit → Bool)
    (x : Stmt) (c : Cm) (data : Fin pcp.length → pcp.Symbol) (coins : pcp.Coins)
    (pf : Pf) (Q : Finset (Fin pcp.length))
    (hcov : ∀ t ∈ pathLog data (pcp.Verifier x coins), t ∈ Q)
    (hcheck : evalWithAnswerFn (QueryImpl.ofFn H) (vc.check c (PartialVec.restrict data Q) pf)
      = true)
    (haccept : evalWithAnswerFn (QueryImpl.ofFn data) (pcp.Verifier x coins) = true) :
    (KilianTransformation pcp vc H boolRel).verify x c coins
      (PartialVec.restrict data Q, pf) = true := by
  have hreplay := claimAnswer_run data (PartialVec.restrict data Q) (pcp.Verifier x coins)
    (fun t ht => by simp [hcov t ht])
  change (evalWithAnswerFn (QueryImpl.ofFn H) (vc.check c (PartialVec.restrict data Q) pf)
      && (Id.run ((simulateQ (claimAnswer (PartialVec.restrict data Q))
        (pcp.Verifier x coins)).run) == some true)) = true
  rw [hcheck, hreplay, haccept]; rfl

/-- Running the PCP verifier on a concrete proof string is the same as evaluating it with the
answer function that reads each position out of that string. This bridges the `runVerifier`
vocabulary of PCP correctness with the `evalWithAnswerFn` form consumed by the deterministic
core. -/
theorem runVerifier_eq_evalWithAnswerFn
    (pcp : PCP Stmt Wit) (stmt : Stmt) (coins : pcp.Coins)
    (proof : List.Vector pcp.Symbol pcp.length) :
    pcp.runVerifier stmt coins proof
      = evalWithAnswerFn (QueryImpl.ofFn proof.get) (pcp.Verifier stmt coins) :=
  rfl

/-- Ordinary PCP completeness (`pcp.perfectCorrectness`): every proof the honest prover can produce
passes the PCP verifier on every coin set the PCP's coin sampler can return. -/
theorem runVerifier_of_perfectCorrectness
    (pcp : PCP Stmt Wit) (rel : Stmt → Wit → Bool) (hpcp : pcp.perfectCorrectness rel) :
    ∀ x w, rel x w →
      ∀ proof ∈ support (pcp.Prover x w),
      ∀ coins ∈ support pcp.sampleCoins,
        pcp.runVerifier x coins proof = true := by
  intro x w hxw proof hproof coins hcoins
  unfold PCP.perfectCorrectness PCP.correctness at hpcp
  have hpr := hpcp x w hxw
  simp only [ENNReal.coe_zero, tsub_zero, ge_iff_le] at hpr
  have h1 := le_antisymm (prEvent_le_one _) hpr
  rw [prEvent_eq_one_iff] at h1
  refine h1 _ ?_
  rw [mem_support_bind_iff]
  refine ⟨proof, hproof, ?_⟩
  rw [mem_support_bind_iff]
  exact ⟨coins, hcoins, by rw [support_pure]; rfl⟩

/-- **Perfect completeness of the Kilian transformation.** If the underlying deterministic vector
commitment is perfectly complete, and the PCP is complete with a coin sampler that can return every
coin set, then the resulting interactive argument is perfectly complete for every choice of the
oracle function `H`: the honest prover convinces the verifier on every challenge.

`hfull` is needed because `PerfectlyComplete` asks for acceptance on every challenge, while PCP
completeness only speaks about the coins the sampler draws, so the two meet only when the sampler
has full support.

The deterministic content lives in `KilianTransformation_verify_eq_true`; here it is lifted across
the probabilistic structure, using that every `ProbComp` is lossless. -/
theorem KilianTransformation_perfectlyComplete
    (pcp : PCP Stmt Wit) (rel : Stmt → Wit → Bool)
    (vc : DetVectorCommitment X Y pcp.Symbol Cm Td Pf pcp.length) (H : X → Y)
    (hvc : vc.PerfectlyComplete)
    (hpcp : pcp.perfectCorrectness rel)
    (hfull : ∀ coins, coins ∈ support pcp.sampleCoins) :
    (KilianTransformation pcp vc H rel).PerfectlyComplete := by
  have hAccept := runVerifier_of_perfectCorrectness pcp rel hpcp
  intro x w hxw coins
  rw [← prEvent_eq_evalDist_singleton]
  refine le_antisymm (prEvent_le_one _) ?_
  simp only [KilianTransformation, bind_assoc, pure_bind]
  -- Each draw of the honest transcript is lossless, and each of its possible outputs leads on.
  refine le_prEvent_bind_of_forall_le_of_support _ (OracleComp.prEvent_true_eq_one _) _ _
    fun proof hproof => ?_
  refine le_prEvent_bind_of_forall_le_of_support _ (OracleComp.prEvent_true_eq_one _) _ _
    fun z hz => ?_
  -- The verifier accepts every honest transcript.
  rw [prEvent_pure, ite_eq_left]
  refine KilianTransformation_verify_eq_true pcp vc H rel x z.1 proof.get coins _ _
    (fun t ht => List.mem_toFinset.mpr ht) ?_ ?_
  · exact hvc H proof.get _ z hz
  · rw [← runVerifier_eq_evalWithAnswerFn]
    exact hAccept x w hxw proof hproof coins (hfull coins)

end Completeness

section Soundness

variable {Stmt Wit : Type} {X : Type} {Y Cm Td Pf : Type}

/-- **Deterministic soundness core.** If the claimed values of a response that the Kilian verifier
accepts agree with a proof string `f`, the successful replay reproduces the PCP verifier's run on
`f`: the PCP verifier accepts `f` on these coins.

A soundness argument supplies `f` and the agreement hypothesis `hagree` from the commitment: in
the random-oracle model, an extractor reads `f` off the prover's oracle queries, and the binding
condition of the extractor (ePrint 2025/2166, Thm 8.4 condition 2) states that every accepted
opening agrees with it. PCP soundness then bounds the probability over the coins that `f` is
accepted. -/
theorem runVerifier_of_KilianTransformation_verify
    (pcp : PCP Stmt Wit) (rel : Stmt → Wit → Bool)
    (vc : DetVectorCommitment X Y pcp.Symbol Cm Td Pf pcp.length) (H : X → Y)
    (x : Stmt) (c : Cm) (coins : pcp.Coins)
    (resp : PartialVec pcp.length pcp.Symbol × Pf) (f : Fin pcp.length → pcp.Symbol)
    (hagree : ∀ i v, resp.1 i = some v → v = f i)
    (hacc : (KilianTransformation pcp vc H rel).verify x c coins resp = true) :
    pcp.runVerifier x coins (List.Vector.ofFn f) = true := by
  change (evalWithAnswerFn (QueryImpl.ofFn H) (vc.check c resp.1 resp.2) &&
    (Id.run (simulateQ (claimAnswer resp.1) (pcp.Verifier x coins)).run == some true)) = true
    at hacc
  rw [Bool.and_eq_true, beq_iff_eq] at hacc
  have hf := eq_of_claimAnswer_run_eq_some f resp.1 hagree (pcp.Verifier x coins) true hacc.2
  rw [runVerifier_eq_evalWithAnswerFn,
    show (List.Vector.ofFn f).get = f from funext fun i => List.Vector.get_ofFn _ i]
  exact hf

end Soundness
