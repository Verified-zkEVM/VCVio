/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

module

public import VCVio.CryptoFoundations.VectorCommitment.Basic
public import VCVio.CryptoFoundations.ChallengeVerifyProtocol.Basic
public import VCVio.OracleComp.ProbComp
public import VCVio.OracleComp.QueryTracking.LoggingOracle.Core
public import ToMathlib.Data.List.Lookup

/-!


# The Kilian Transformation

This file is to describe the Kilian transformation ([Kilian '92], [SNARGs book Chapter 20]).
This transformation converts a Probabilistically Checkable Proof (PCP)
into an succinct interactive argument/Sigma protocol using Merkle trees.
This can then be made non-interactive using the Fiat-Shamir transformation,
(these two transformations together are referred to by the SNARGs book as
the "Micali transformation" [Micali '00]).

The majority of the Kilian paper is actually a beautiful way to make the classic GMW graph-coloring
zero-knowledge proof more efficient while keeping zero knowledge by implementing a
"notarized envelope" primitive. But I think this file should just focus on the succinctness part.

## Main results

- `PCP`: probabilistically checkable proofs with adaptive deterministic verifier queries, and their
  correctness/soundness notions.
- `KilianTransformation`: the succinct interactive argument built from a `PCP` and a
  `BatchOpeningVectorCommitment`.
- `KilianTransformation_perfectlyComplete`: perfect completeness, from PCP completeness for a coin
  sampler with full support and commitment correctness.
- `KilianTransformation_sound`: statistical soundness with the PCP's soundness error, for the
  verifier that draws its challenge with the PCP's coin sampler, from perfect batch position
  binding — a straight-line argument in which the commitment itself pins down the effective proof
  string (`BatchOpeningVectorCommitment.committedValue`), with no extractor.
- `KilianTransformation_perfectlyComplete_probComp`, `KilianTransformation_sound_probComp`: the
  same statements at `m := ProbComp`, where the hypotheses relating the `ProbComp` lift to the
  ambient monad hold by definition and the commitment's operations never fail.

Knowledge soundness (extraction) and the computational refinement of soundness — where binding may
fail on a negligible-probability event, as for hash-based Merkle commitments — are future work.

## Probability assumptions

The transformation is generic in the monad `m` of the vector commitment, following the conventions
of `VCVio.CryptoFoundations.SigmaProtocol`. The probability-bearing statements use the measure
semantics `[EvalDistSemantics m]`, and their proofs add `[LawfulEvalDistSemantics m]`; the
possible outputs of the honest parties are given by `[MonadAttach m]`. The PCP itself lives in
`ProbComp` and is pulled into `m` by `MonadLiftT ProbComp m`; the theorems ask for this lift to
preserve distributions (`hfaithful`) and, for completeness, not to enlarge supports (`hlift`).
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
prover needs the positions read — with `pathLog` (the read-log built on
`QueryImpl.withTraceAppendBefore`). `claimAnswer` below is the verifier's own per-query handler: a
failing lookup against the prover's claimed `(position, value)` pairs. -/

variable {ι Sym : Type*}

/-- Implement oracle by
looking up an input among the claimed `(input, value)` pairs, failing if absent. This is the
verifier's per-query handler in `KilianTransformation.verify`. It is `QueryImpl.ofFn?` over the
association-list lookup `claims.lookup`, using that `QueryImpl spec Option` is `QueryImpl spec
(OptionT Id)`. -/
@[expose]
def claimAnswer [BEq ι] (claims : List (ι × Sym)) : QueryImpl (ι →ₒ Sym) (OptionT Id) :=
  QueryImpl.ofFn? (claims.lookup ·)

end AnswerFunctions

section KilianTransformation

variable {Stmt Wit : Type}

/-- **The Kilian transformation.**

Turn a `PCP` into a (public-coin) succinct `ChallengeVerifyProtocol`, the interactive argument at
the heart of Kilian's protocol, parameterized by an arbitrary batch-opening vector commitment `bovc`
over the PCP's symbol alphabet (e.g. the inductive Merkle tree of
`VCVio.CryptoFoundations.VectorCommitment.MerkleTree`):

1. the prover commits to its PCP proof string with `bovc.commit`, retaining the proof string
   alongside the opener state as its private state (`commit`);
2. the verifier sends random coins, drawn by `pcp.sampleCoins` (the protocol record itself carries
   no challenge sampler: completeness holds on every challenge, and `KilianTransformation_sound`
   measures soundness against the lifted coin sampler `liftM pcp.sampleCoins`);
3. the prover simulates `pcp.Verifier stmt coins` against its retained proof to learn exactly which
   positions the verifier reads, and opens *exactly* that set in one shot with `bovc.openBatch`,
   returning the claimed `(position, value)` pairs alongside the batch opening (`respond`);
4. the verifier checks the batch opening against the commitment with `bovc.verifyBatch`, then
   replays `pcp.Verifier stmt coins`, answering each position query from the claimed values, accepts
   iff
   the batch opening verifies, every queried position was claimed, and the PCP verifier accepts
   (`verify`).

A batch-opening commitment is the natural primitive here: Kilian opens a whole set of positions at
once, so a construction that amortizes work across that set (a shared-path Merkle proof, say) is
exactly what makes the argument succinct.

Modeling choices for this definition:

- Positions of the proof string are the commitment indices `Fin pcp.length`; the value at a position
  is a PCP symbol.
- The whole transformation runs in the commitment's monad `m`; the prover's PCP randomness is pulled
  in via `MonadLiftT ProbComp m`. Taking `m := ProbComp` with a standard-model Merkle commitment
  recovers the usual deterministic-verification formulation.
- `Resp` is the claimed `(position, value)` pairs together with a single batch opening. Succinctness
  is what makes Kilian interesting: only the positions the verifier actually queries are opened, and
  `verify` rejects (via the `none` branch of the lookup) if it ever reads an unclaimed position.

Security: `KilianTransformation_perfectlyComplete` derives perfect completeness from PCP
completeness and commitment correctness, and `KilianTransformation_sound` derives statistical
soundness (with the PCP's soundness error) from perfect batch position binding of the
commitment. -/
@[expose]
noncomputable def KilianTransformation
    (pcp : PCP Stmt Wit)
    {m : Type → Type} [Monad m] [MonadLiftT ProbComp m]
    {Commit State BatchOpening : Type}
    (bovc : BatchOpeningVectorCommitment m (Fin pcp.length) pcp.Symbol Commit State BatchOpening)
    (rel : Stmt → Wit → Bool) :
    ChallengeVerifyProtocol Stmt Wit
      Commit                                                  -- Commit: the vector commitment
      (State × (Fin pcp.length → pcp.Symbol))                 -- PrvState: opener state + proof
      pcp.Coins                                               -- Chal: the verifier's coins
      (List (Fin pcp.length × pcp.Symbol) × BatchOpening)     -- Resp: claims + batch opening
      rel m where
  commit stmt wit := do
    let proof ← pcp.Prover stmt wit
    let cs ← bovc.commit proof.get
    return (cs.1, (cs.2, proof.get))
  respond stmt _wit st coins := do
    -- Simulate the verifier against the retained proof, logging the positions it reads.
    let queried : List (Fin pcp.length) :=
      (pathLog st.2 (pcp.Verifier stmt coins)).dedup
    -- Open exactly the queried positions as a single batch, alongside the claimed values.
    let op ← bovc.openBatch st.1 queried
    return (queried.map (fun i => (i, st.2 i)), op)
  verify stmt c coins resp :=
    -- Check the batch opening, then replay the verifier answering each position from its claimed
    -- value; an unclaimed position fails the run, as does a batch opening that does not verify.
    let (claims, op) := resp
    bovc.verifyBatch c claims op &&
      (Id.run (simulateQ (claimAnswer claims) (pcp.Verifier stmt coins)).run == some true)

end KilianTransformation

section ReplayInfrastructure

/-! ## Deterministic replay infrastructure

The completeness of the Kilian transformation rests on a deterministic fact about the verifier:
the prover's logging simulation (which records the inputs the verifier reads), the verifier's own
replay against the prover's openings, and the bare run on the answer function are all the *same*
deterministic computation answered consistently. These lemmas package that fact for a fixed answer
function `f : ι → Sym` on a single-oracle spec `ι →ₒ Sym`. -/

universe u

variable {ι Sym : Type u} [BEq ι] [LawfulBEq ι]

/-- The verifier's per-query handler answers a claimed input with its value. -/
theorem claimAnswer_map (f : ι → Sym) (L : List ι) (t : ι) (ht : t ∈ L) :
    claimAnswer (L.map (fun i => (i, f i))) t = (pure (f t) : OptionT Id Sym) := by
  simp only [claimAnswer, QueryImpl.ofFn?, List.map_lookup f t L ht]
  rfl

omit [LawfulBEq ι] in
/-- **Replay lemma.** If the claims answer every input the verifier reads (under `f`) with `f`'s
value, the verifier's `OptionT` replay never fails and reproduces the pure run. -/
theorem claimAnswer_run (f : ι → Sym) (claims : List (ι × Sym)) {β : Type u}
    (comp : OracleComp (ι →ₒ Sym) β) :
    (∀ t ∈ pathLog f comp, claimAnswer claims t = (pure (f t) : OptionT Id Sym)) →
      (simulateQ (claimAnswer claims) comp).run
        = some (evalWithAnswerFn (QueryImpl.ofFn f) comp) := by
  induction comp using OracleComp.inductionOn with
  | pure x => intro _; rfl
  | query_bind t oa ih =>
    intro h
    have ht : claimAnswer claims t = (pure (f t) : OptionT Id Sym) :=
      h t (by rw [pathLog_query]; exact List.mem_cons_self ..)
    have hq : evalWithAnswerFn (QueryImpl.ofFn f) (liftM ((ι →ₒ Sym).query t)) = f t := by
      change simulateQ (QueryImpl.ofFn f) (liftM ((ι →ₒ Sym).query t)) = f t
      rw [simulateQ_spec_query]; rfl
    simp only [simulateQ_bind, simulateQ_spec_query, ht, evalWithAnswerFn_bind, hq]
    exact ih (f t) (fun t' ht' => h t' (by rw [pathLog_query]; exact List.mem_cons_of_mem _ ht'))

/-- **Binding replay lemma.** If every claimed value agrees with the answer function `f`, then a
successful (`some`-valued) replay against the claims coincides with the pure run on `f`: every
query the replay manages to answer is answered with `f`'s value, so the replay path *is* the
`f`-path. This is the soundness-side complement of `claimAnswer_run`: there the claims are known
to cover the `f`-path and the replay is shown to succeed; here the replay is assumed to succeed
and its result is pinned down, with no coverage hypothesis at all. -/
theorem eq_of_claimAnswer_run_eq_some (f : ι → Sym) (claims : List (ι × Sym))
    (hbound : ∀ i v, (i, v) ∈ claims → v = f i) {β : Type u}
    (comp : OracleComp (ι →ₒ Sym) β) (b : β) :
    (simulateQ (claimAnswer claims) comp).run = some b →
      evalWithAnswerFn (QueryImpl.ofFn f) comp = b := by
  induction comp using OracleComp.inductionOn with
  | pure x => exact fun h => Option.some.inj h
  | query_bind t oa ih =>
    intro h
    rw [simulateQ_bind, simulateQ_spec_query] at h
    cases hlook : claims.lookup t with
    | none =>
      rw [show claimAnswer claims t = (failure : OptionT Id Sym) from by
        simp only [claimAnswer, QueryImpl.ofFn?, hlook]; rfl] at h
      -- A failed lookup fails the whole replay, contradicting the `some`-valued run.
      exact absurd h.symm (Option.some_ne_none b)
    | some v =>
      rw [show claimAnswer claims t = (pure v : OptionT Id Sym) from by
        simp only [claimAnswer, QueryImpl.ofFn?, hlook]; rfl, pure_bind] at h
      obtain rfl : v = f t := hbound t v (List.mem_of_lookup_eq_some hlook)
      have hq : evalWithAnswerFn (QueryImpl.ofFn f) (liftM ((ι →ₒ Sym).query t)) = f t := by
        change simulateQ (QueryImpl.ofFn f) (liftM ((ι →ₒ Sym).query t)) = f t
        rw [simulateQ_spec_query]; rfl
      rw [evalWithAnswerFn_bind, hq]
      exact ih (f t) h

end ReplayInfrastructure

section Completeness

variable {Stmt Wit : Type} {rel : Stmt → Wit → Bool}

/-- **Deterministic completeness core.** For fixed coins and any answer function `data` (for the
honest prover, its PCP proof string), the Kilian verifier accepts the response built from `data`,
provided:

* `hcov` — the opened set `queried` covers every position the PCP verifier reads against `data`
  (it does, since the prover opens exactly the logged positions);
* `hbatch` — the batch opening verifies (vector-commitment correctness); and
* `haccept` — the PCP verifier accepts `data` (PCP completeness).

The novel content is the `claimAnswer_run` replay: the verifier's failing `OptionT` replay against
the openings reproduces the bare PCP run, so it accepts exactly when the PCP run does. -/
theorem KilianTransformation_verify_eq_true
    (pcp : PCP Stmt Wit)
    {m : Type → Type} [Monad m] [MonadLiftT ProbComp m] {Commit State BatchOpening : Type}
    (bovc : BatchOpeningVectorCommitment m (Fin pcp.length) pcp.Symbol Commit State BatchOpening)
    (boolRel : Stmt → Wit → Bool)
    (x : Stmt) (c : Commit) (data : Fin pcp.length → pcp.Symbol) (coins : pcp.Coins)
    (op : BatchOpening) (queried : List (Fin pcp.length))
    (hcov : pathLog data (pcp.Verifier x coins) ⊆ queried)
    (hbatch : bovc.verifyBatch c (queried.map fun i => (i, data i)) op = true)
    (haccept : evalWithAnswerFn (QueryImpl.ofFn data) (pcp.Verifier x coins) = true) :
    (KilianTransformation pcp bovc boolRel).verify x c coins
      (queried.map (fun i => (i, data i)), op) = true := by
  have hreplay := claimAnswer_run data
    (queried.map fun i => (i, data i)) (pcp.Verifier x coins)
    (fun t ht => claimAnswer_map data queried t (hcov ht))
  change (bovc.verifyBatch c (queried.map fun i => (i, data i)) op
      && (Id.run ((simulateQ (claimAnswer (queried.map fun i => (i, data i)))
        (pcp.Verifier x coins)).run) == some true)) = true
  rw [hbatch, hreplay, haccept]; rfl

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

/-- Ordinary PCP completeness (`pcp.perfectCorrectness`) delivers the acceptance condition consumed
by `KilianTransformation_perfectlyComplete`, namely that every proof the honest prover can produce
in `m` passes the PCP verifier on every coin set the PCP's coin sampler can return.

One side condition bridges the gap between PCP completeness (stated over `ProbComp`) and the
ambient monad `m`: `hlift` — lifting a `ProbComp` into `m` does not enlarge its support. This is
the coherence of the public-randomness lift; it cannot be derived from the bare
`MonadLiftT ProbComp m` (the lift could *a priori* interpret sampling differently from `ProbComp`),
so it is required explicitly. It holds by `rfl` for `m := ProbComp` and for any faithful lift. -/
theorem perfectCorrectness_accepts_liftedProver
    (pcp : PCP Stmt Wit)
    {m : Type → Type} [MonadLiftT ProbComp m] [MonadAttach m]
    (rel : Stmt → Wit → Bool)
    (hlift : ∀ {β : Type} (mx : ProbComp β), support (liftM mx : m β) ⊆ support mx)
    (hpcp : pcp.perfectCorrectness rel) :
    ∀ x w, rel x w →
      ∀ proof ∈ support (liftM (pcp.Prover x w) : m (List.Vector pcp.Symbol pcp.length)),
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
  refine ⟨proof, hlift _ hproof, ?_⟩
  rw [mem_support_bind_iff]
  exact ⟨coins, hcoins, by rw [support_pure]; rfl⟩

/-- **Perfect completeness of the Kilian transformation.** If the underlying batch-opening vector
commitment is complete (perfectly correct), and the PCP is complete with a coin sampler that can
return every coin set, then the resulting interactive argument is perfectly complete: the honest
prover convinces the verifier on every challenge.

The hypotheses isolate the moving parts:

* `hbovc` — the batch-opening vector commitment is complete: an honest commitment opens its
  committed claims to a batch opening that verifies;
* `hpcp` — the PCP is complete (`pcp.perfectCorrectness`); together with `hlift` (lifting
  `ProbComp` into `m` does not enlarge supports) this gives, via
  `perfectCorrectness_accepts_liftedProver`, that the honest proof is accepted on every coin set
  the sampler can return;
* `hfull` — the PCP's coin sampler can return every coin set. `PerfectlyComplete` asks for
  acceptance on every challenge, while PCP completeness only speaks about the coins the sampler
  draws, so the two meet only when the sampler has full support;
* `hfaithful` — lifting `ProbComp` into `m` preserves the distribution, so the lifted honest prover
  never fails, as no `ProbComp` computation does;
* `hCommit` / `hOpen` — the commitment's own operations never fail. These are genuinely independent:
  perfect correctness of `bovc` is vacuous if `openBatch` always fails, so it cannot supply them.

The deterministic content lives in `KilianTransformation_verify_eq_true`; here we lift it across the
probabilistic structure, showing that the honest transcript is lossless and that every output it
can produce is accepted. At `m := ProbComp` the lift hypotheses hold by definition and no
computation fails; see `KilianTransformation_perfectlyComplete_probComp`. -/
theorem KilianTransformation_perfectlyComplete
    (pcp : PCP Stmt Wit) (rel : Stmt → Wit → Bool)
    {m : Type → Type} [Monad m] [LawfulMonad m] [MonadLiftT ProbComp m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m] [MonadAttach m] [WeaklyLawfulMonadAttach m]
    {Commit State BatchOpening : Type}
    (bovc : BatchOpeningVectorCommitment m (Fin pcp.length) pcp.Symbol Commit State BatchOpening)
    (hbovc : bovc.PerfectlyCorrect)
    (hpcp : pcp.perfectCorrectness rel)
    (hfull : ∀ coins, coins ∈ support pcp.sampleCoins)
    (hlift : ∀ {β : Type} (mx : ProbComp β), support (liftM mx : m β) ⊆ support mx)
    (hfaithful : ∀ {β : Type} (mx : ProbComp β), (liftM mx : m β) =ᵈ mx)
    (hCommit : ∀ data, prFail (bovc.commit data) = 0)
    (hOpen : ∀ st is, prFail (bovc.openBatch st is) = 0) :
    (KilianTransformation pcp bovc rel).PerfectlyComplete := by
  have hAccept := perfectCorrectness_accepts_liftedProver pcp rel hlift hpcp
  intro x w hxw coins
  rw [← prEvent_eq_evalDist_singleton]
  refine le_antisymm (prEvent_le_one _) ?_
  simp only [KilianTransformation, bind_assoc, pure_bind]
  -- Each draw of the honest transcript is lossless, and each of its possible outputs leads on.
  refine le_prEvent_bind_of_forall_le_of_support _
    (((hfaithful _).prEvent_eq _).trans (OracleComp.prEvent_true_eq_one _)) _ _
    fun proof hproof => ?_
  refine le_prEvent_bind_of_forall_le_of_support _ ((prFail_eq_zero_iff _).mp (hCommit _)) _ _
    fun cs hcs => ?_
  refine le_prEvent_bind_of_forall_le_of_support _ ((prFail_eq_zero_iff _).mp (hOpen _ _)) _ _
    fun op hop => ?_
  -- The verifier accepts every honest transcript.
  rw [prEvent_pure, ite_eq_left]
  refine KilianTransformation_verify_eq_true pcp bovc rel x cs.1 proof.get coins op _
    (List.subset_dedup _) ?_ ?_
  · exact hbovc proof.get _ cs.1 cs.2 hcs op hop
  · rw [← runVerifier_eq_evalWithAnswerFn]
    exact hAccept x w hxw proof hproof coins (hfull coins)

/-- **Perfect completeness of the Kilian transformation over `ProbComp`.** With the commitment in
`ProbComp`, the lift of the PCP's computations is the identity and no computation fails, so
`KilianTransformation_perfectlyComplete` needs only commitment correctness, PCP completeness, and
a coin sampler with full support. -/
theorem KilianTransformation_perfectlyComplete_probComp
    (pcp : PCP Stmt Wit) (rel : Stmt → Wit → Bool)
    {Commit State BatchOpening : Type}
    (bovc : BatchOpeningVectorCommitment ProbComp (Fin pcp.length) pcp.Symbol Commit State
      BatchOpening)
    (hbovc : bovc.PerfectlyCorrect)
    (hpcp : pcp.perfectCorrectness rel)
    (hfull : ∀ coins, coins ∈ support pcp.sampleCoins) :
    (KilianTransformation pcp bovc rel).PerfectlyComplete :=
  KilianTransformation_perfectlyComplete pcp rel bovc hbovc hpcp hfull (fun _ => subset_rfl)
    (fun _ => EvalDistEq.rfl) (fun _ => prFail_eq_zero _) (fun _ _ => prFail_eq_zero _)

end Completeness

section Soundness

open scoped NNReal ENNReal

variable {Stmt Wit : Type}

/-- **Deterministic soundness core.** Whatever response the Kilian verifier accepts against an
(adversarial) commitment `c`, batch position binding forces every accepted claim to read off the
committed proof string `bovc.committedValue c`, and the successful replay then reproduces the PCP
verifier's run on that string: the PCP verifier accepts `committedValue c` on these coins. No
extractor or rewinding appears — the commitment itself determines the proof string. -/
theorem runVerifier_committedValue_of_KilianTransformation_verify
    (pcp : PCP Stmt Wit) (rel : Stmt → Wit → Bool) [Inhabited pcp.Symbol]
    {m : Type → Type} [Monad m] [MonadLiftT ProbComp m] {Commit State BatchOpening : Type}
    (bovc : BatchOpeningVectorCommitment m (Fin pcp.length) pcp.Symbol Commit State BatchOpening)
    (hbind : bovc.BatchPositionBinding)
    (x : Stmt) (c : Commit) (coins : pcp.Coins)
    (resp : List (Fin pcp.length × pcp.Symbol) × BatchOpening)
    (hacc : (KilianTransformation pcp bovc rel).verify x c coins resp = true) :
    pcp.runVerifier x coins (List.Vector.ofFn (bovc.committedValue c)) = true := by
  obtain ⟨claims, op⟩ := resp
  change (bovc.verifyBatch c claims op &&
    (Id.run (simulateQ (claimAnswer claims) (pcp.Verifier x coins)).run == some true)) = true
    at hacc
  rw [Bool.and_eq_true, beq_iff_eq] at hacc
  obtain ⟨hbatch, hrun⟩ := hacc
  have hbound : ∀ i v, (i, v) ∈ claims → v = bovc.committedValue c i :=
    fun i v hm => (hbind.committedValue_eq hbatch hm).symm
  have hf := eq_of_claimAnswer_run_eq_some (bovc.committedValue c) claims hbound
    (pcp.Verifier x coins) true hrun
  rw [runVerifier_eq_evalWithAnswerFn,
    show (List.Vector.ofFn (bovc.committedValue c)).get = bovc.committedValue c from
      funext fun i => List.Vector.get_ofFn _ i]
  exact hf

/-- **Statistical soundness of the Kilian transformation** under perfect position binding. If the
batch-opening vector commitment is (perfectly, information-theoretically) batch position binding
and the PCP is sound with error `ε`, the resulting interactive argument is sound with the same
error `ε` for the verifier that draws its challenge with the PCP's coin sampler, lifted into `m`,
against arbitrary — even computationally unbounded and adaptive — provers.

The argument is the classical one, made straight-line by perfect binding: a cheating prover's
commitment `pc` pins down a single proof string `bovc.committedValue pc` (no extractor or
rewinding is needed), any response the verifier would accept replays the PCP verifier's run on
that string (`runVerifier_committedValue_of_KilianTransformation_verify`), and PCP soundness
bounds the probability over the verifier's coins that this fixed string is accepted.

For a commitment that is only *computationally* binding (a hash-based Merkle tree, say), this
perfect-binding statement is the information-theoretic core; the computational statement — where
`BatchPositionBinding` may fail on a negligible-probability event — is future work, as is
knowledge soundness. `hfaithful` is the same distribution-faithfulness of the `ProbComp` lift
required by `KilianTransformation_perfectlyComplete`; at `m := ProbComp` it holds by definition
(`KilianTransformation_sound_probComp`). -/
theorem KilianTransformation_sound
    (pcp : PCP Stmt Wit) (rel : Stmt → Wit → Bool) [Inhabited pcp.Symbol]
    {m : Type → Type} [Monad m] [MonadLiftT ProbComp m] [EvalDistSemantics m]
    {Commit State BatchOpening : Type}
    (bovc : BatchOpeningVectorCommitment m (Fin pcp.length) pcp.Symbol Commit State BatchOpening)
    (hbind : bovc.BatchPositionBinding)
    {ε : ℝ≥0} (hpcp : pcp.soundness rel ε)
    (hfaithful : ∀ {β : Type} (mx : ProbComp β), (liftM mx : m β) =ᵈ mx) :
    (KilianTransformation pcp bovc rel).Sound (liftM pcp.sampleCoins) ε := by
  intro x hx pc
  set proofStr := List.Vector.ofFn (bovc.committedValue pc) with hproofStr
  -- Move the probability from the lifted challenge sampler to its `ProbComp` source.
  rw [(hfaithful pcp.sampleCoins).prEvent_eq]
  -- PCP soundness at the committed proof string, in event-over-coins form.
  have hfinal : Pr{let coins ← pcp.sampleCoins}[pcp.runVerifier x coins proofStr = true]
      ≤ (ε : ℝ≥0∞) := by
    have h := hpcp x hx proofStr
    simp only [bind_pure_comp, prEvent_map] at h
    exact h
  refine (prEvent_mono _ _ _ fun coins hcoins => ?_).trans hfinal
  obtain ⟨resp, hresp⟩ := hcoins
  exact runVerifier_committedValue_of_KilianTransformation_verify
    pcp rel bovc hbind x pc coins resp hresp

/-- **Statistical soundness of the Kilian transformation over `ProbComp`.** With the commitment in
`ProbComp`, the verifier draws its challenge with the PCP's coin sampler itself, and
`KilianTransformation_sound` needs only perfect batch position binding and PCP soundness. -/
theorem KilianTransformation_sound_probComp
    (pcp : PCP Stmt Wit) (rel : Stmt → Wit → Bool) [Inhabited pcp.Symbol]
    {Commit State BatchOpening : Type}
    (bovc : BatchOpeningVectorCommitment ProbComp (Fin pcp.length) pcp.Symbol Commit State
      BatchOpening)
    (hbind : bovc.BatchPositionBinding)
    {ε : ℝ≥0} (hpcp : pcp.soundness rel ε) :
    (KilianTransformation pcp bovc rel).Sound pcp.sampleCoins ε :=
  KilianTransformation_sound pcp rel bovc hbind hpcp fun _ => EvalDistEq.rfl

end Soundness
