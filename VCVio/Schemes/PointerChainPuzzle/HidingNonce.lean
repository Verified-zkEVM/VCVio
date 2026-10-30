/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.Schemes.PointerChainPuzzle.HidingPRF
public import VCVio.OracleComp.QueryTracking.QueryBound.Hazard
public import ToMathlib.Data.ENNReal.Gauss

/-!
# Time-lock encryption with the pointer-chain puzzle: the nonce hop

The hybrid `G₁` (`privateExperiment`) derives the subkeys of an encryption from a private random
function of its nonce, so two encryptions under the same nonce share their subkeys. The indexed
hybrid `G₂` (`indexedRun` in the real world of `prf.multiKey`) keys the `j`-th encryption by
instances `(0, j)` and `(1, j)` of `2 qEnc` independently keyed PRF instances, whatever its nonce.
This file bridges the two through a hybrid `G₁½` whose subkeys are indexed by the challenger's
counter of accepted encryptions.

## The counter-indexed hybrid

The challenger of `G₁½` (`counterEncrypt`) keeps the number `j` of accepted requests. For `j < qEnc`
it draws a uniform nonce, which still goes into the envelope, and a fresh uniform pair of subkeys;
beyond the budget it returns the empty byte string, as `indexedEncrypt` does. A request with
messages of different lengths is rejected by the left-or-right oracle and does not advance `j`.

## From `G₁` to `G₁½`

A private random function of the nonce draws fresh subkeys at every nonce not yet seen, so `G₁`
and `G₁½` agree until two accepted encryptions share a nonce (`NonceBad`). The proof is the
until-bad argument (`QueryImpl.DominatedUntilBad`) on the online phases with the log of accepted
encryptions as a ghost state (`counterJointImpl`), read as the private cache of `G₁` by
`logCache`. The nonce of the `j`-th accepted encryption repeats an earlier one with probability at
most `j / |N|`, whatever the adversary did in between, and the hazard lemma
`OracleComp.prEvent_simulateQ_run_le_sum_of_isQueryBoundP` adds these up over the at most `qEnc`
challenge queries to `qEnc (qEnc - 1) / (2 |N|)`. The nonces are drawn adaptively, interleaved with
the adversary's other queries, which is why the bound is per query rather than a birthday bound for
a tape of nonces drawn in advance.

## From `G₁½` to `G₂`

In the random oracle model with the key table `T`, `indexedRun` answers instance `i` by
`prf.eval (T i)` (`keyedRomImpl`). The subkeys that `G₁½` draws for its `j`-th encryption are those
that `G₂` reads at the cells `(0, j)` and `(1, j)` of a uniform key table, which no earlier
encryption reads (`keyTable`, `keyFill`, `intertwinesOn_keyFill`). Under `prf.UniformKey` the key
table of `prf.multiKey` is uniform, and the two hybrids are equal in law. The table is uniform in
`G₁½` only, never in `G₁`, where the subkeys of two encryptions under one nonce coincide.

## Main definitions

* `counterEncrypt`, `counterImpl`, `counterAdversary`, `counterExperiment`: the hybrid `G₁½`.
* `NonceBad`: two accepted encryptions within the budget share their nonce.

## Main statements

* `absDiff_privateExperiment_counterExperiment_le`: `|G₁ - G₁½| ≤ qEnc (qEnc - 1) / (2 |N|)`.
* `counterExperiment_eq_prfReal`: under `prf.UniformKey`, `G₁½` and `G₂` are equal in law.
* `absDiff_privateExperiment_indexed_le`: under `prf.UniformKey`,
  `|G₁ - G₂| ≤ qEnc² / (2 |N|)`.
-/

public section

open OracleSpec OracleComp TimeLockPuzzle PRFScheme
open scoped ENNReal

namespace PointerChainPuzzle

open LeanSeal Envelope

variable {n m : ℕ} {S L Salt Ctx N K : Type}

variable (prf : PRFScheme K ByteArray (Bytes 32)) {w : ℕ} (codec : FixedCodec N w)
  (encodePuzzle : Puzzle n S L Salt → ByteArray) (qEnc : ℕ)

/-! ## The counter-indexed hybrid -/

section Counter

variable [SampleableType N] [SampleableType K]

/-- The counter-indexed challenger's encryption of `msg` under the puzzle bytes `pz`, with the
number `j` of accepted requests as state: it advances the counter and, for `j < qEnc`, draws a
uniform nonce and a fresh uniform pair of subkeys from local coins and returns the envelope under
them. For `j ≥ qEnc` it is the empty byte string, with no coin drawn. The subkeys are those of a
private random function of the counter, which never repeats, so each is a fresh draw. -/
@[expose]
def counterEncrypt (pz : ByteArray) (msg : Plaintext) :
    StateT ℕ (OracleComp (unifSpec + (sealSpec n S L Salt Ctx N K).batch)) ByteArray := do
  let j ← get
  set (j + 1)
  if j < qEnc then
    let nonce ← (liftM (liftM ($ᵗ N : ProbComp N) :
      OracleComp (unifSpec + (sealSpec n S L Salt Ctx N K).batch) N) :
        StateT ℕ (OracleComp (unifSpec + (sealSpec n S L Salt Ctx N K).batch)) N)
    let ks ← (liftM (liftM ($ᵗ (K × K) : ProbComp (K × K)) :
      OracleComp (unifSpec + (sealSpec n S L Salt Ctx N K).batch) (K × K)) :
        StateT ℕ (OracleComp (unifSpec + (sealSpec n S L Salt Ctx N K).batch)) (K × K))
    return sealWith prf codec pz nonce ks msg
  else return ByteArray.empty

/-- The handler of the counter-indexed challenger at hidden bit `b` for the puzzle `puzzle`: local
coins are forwarded, a challenge query is answered by the left-or-right oracle over
`counterEncrypt` under the puzzle's bytes, and rounds are forwarded. -/
@[expose]
def counterImpl (puzzle : Puzzle n S L Salt) (b : Bool) :
    QueryImpl ((unifSpec + LeftOrRight.spec Plaintext ByteArray) +
        (sealSpec n S L Salt Ctx N K).batch)
      (StateT ℕ (OracleComp (unifSpec + (sealSpec n S L Salt Ctx N K).batch))) :=
  (((QueryImpl.ofLift unifSpec
        (OracleComp (unifSpec + (sealSpec n S L Salt Ctx N K).batch))).liftTarget
      (StateT ℕ (OracleComp (unifSpec + (sealSpec n S L Salt Ctx N K).batch)))) +
    LeftOrRight.oracle (counterEncrypt (n := n) (S := S) (L := L) (Salt := Salt) (Ctx := Ctx)
      prf codec qEnc (encodePuzzle puzzle)) plaintextLength b) +
    (fun ts => liftM ((unifSpec + (sealSpec n S L Salt Ctx N K).batch).query (.inr ts)) :
      QueryImpl (sealSpec n S L Salt Ctx N K).batch (StateT ℕ
        (OracleComp (unifSpec + (sealSpec n S L Salt Ctx N K).batch))))

/-- The hiding adversary `adv` with the counter-indexed challenger at hidden bit `b` inlined: a
two-phase adversary against the oracles with subkeys whose output is the guess of the hidden bit.
The counter starts at `0` when the online phase starts. -/
@[expose]
def counterAdversary
    (adv : HidingAdversary (sealSpec n S L Salt Ctx N K) (Puzzle n S L Salt) Plaintext ByteArray)
    (b : Bool) : TwoPhaseAdversary unifSpec (sealSpec n S L Salt Ctx N K) (Puzzle n S L Salt) Bool
    where
  State := adv.State
  preprocess := adv.preprocess
  online σ puzzle := StateT.run'
    (simulateQ (counterImpl prf codec encodePuzzle qEnc puzzle b) (adv.online σ puzzle)) 0

variable (m) in
/-- **The hybrid `G₁½`.** The delay experiment for any output of `sealScheme` against
`counterAdversary adv b`: the hiding experiment at hidden bit `b` with the counter-indexed
challenger, returning the guess together with the puzzle key. -/
@[expose]
def counterExperiment [NeZero n] [AddCommGroup L] [DecidableEq S] [SampleableType Salt]
    [SampleableType L] (mkCtx : Salt → Ctx) (initAcc : Ctx → S)
    (adv : HidingAdversary (sealSpec n S L Salt Ctx N K) (Puzzle n S L Salt) Plaintext ByteArray)
    (b : Bool) : OracleComp (unifSpec + sealSpec n S L Salt Ctx N K) (Bool × S) :=
  (sealScheme n m mkCtx initAcc N K).guessExperiment
    (counterAdversary prf codec encodePuzzle qEnc adv b)

/-! ## The counter-indexed challenger with a log -/

/-- The log of the accepted encryptions of the counter-indexed challenger: the nonce and the pair
of subkeys of each, the latest first. -/
abbrev CounterLog (N K : Type) := List (N × (K × K))

/-- `counterEncrypt` with its nonces and subkeys logged: the state is the counter together with
the log of the accepted encryptions. -/
@[expose]
def counterLogEncrypt (pz : ByteArray) (msg : Plaintext) :
    StateT (ℕ × CounterLog N K)
      (OracleComp (unifSpec + (sealSpec n S L Salt Ctx N K).batch)) ByteArray := do
  let s ← get
  set (s.1 + 1, s.2)
  if s.1 < qEnc then
    let nonce ← (liftM (liftM ($ᵗ N : ProbComp N) :
      OracleComp (unifSpec + (sealSpec n S L Salt Ctx N K).batch) N) :
        StateT (ℕ × CounterLog N K)
          (OracleComp (unifSpec + (sealSpec n S L Salt Ctx N K).batch)) N)
    let ks ← (liftM (liftM ($ᵗ (K × K) : ProbComp (K × K)) :
      OracleComp (unifSpec + (sealSpec n S L Salt Ctx N K).batch) (K × K)) :
        StateT (ℕ × CounterLog N K)
          (OracleComp (unifSpec + (sealSpec n S L Salt Ctx N K).batch)) (K × K))
    set (s.1 + 1, (nonce, ks) :: s.2)
    return sealWith prf codec pz nonce ks msg
  else return ByteArray.empty

/-- `counterImpl` over `counterLogEncrypt`. -/
@[expose]
def counterLogImpl (puzzle : Puzzle n S L Salt) (b : Bool) :
    QueryImpl ((unifSpec + LeftOrRight.spec Plaintext ByteArray) +
        (sealSpec n S L Salt Ctx N K).batch)
      (StateT (ℕ × CounterLog N K)
        (OracleComp (unifSpec + (sealSpec n S L Salt Ctx N K).batch))) :=
  (((QueryImpl.ofLift unifSpec
        (OracleComp (unifSpec + (sealSpec n S L Salt Ctx N K).batch))).liftTarget
      (StateT (ℕ × CounterLog N K)
        (OracleComp (unifSpec + (sealSpec n S L Salt Ctx N K).batch)))) +
    LeftOrRight.oracle (counterLogEncrypt (n := n) (S := S) (L := L) (Salt := Salt) (Ctx := Ctx)
      prf codec qEnc (encodePuzzle puzzle)) plaintextLength b) +
    (fun ts => liftM ((unifSpec + (sealSpec n S L Salt Ctx N K).batch).query (.inr ts)) :
      QueryImpl (sealSpec n S L Salt Ctx N K).batch (StateT (ℕ × CounterLog N K)
        (OracleComp (unifSpec + (sealSpec n S L Salt Ctx N K).batch))))

/-- Forgetting the log, `counterLogEncrypt` is `counterEncrypt`. -/
lemma map_counterLogEncrypt_run (pz : ByteArray) (msg : Plaintext) (s : ℕ × CounterLog N K) :
    Prod.map id Prod.fst <$> (counterLogEncrypt (n := n) (S := S) (L := L) (Salt := Salt)
      (Ctx := Ctx) prf codec qEnc pz msg).run s =
      (counterEncrypt (n := n) (S := S) (L := L) (Salt := Salt) (Ctx := Ctx) prf codec qEnc pz
        msg).run s.1 := by
  by_cases hj : s.1 < qEnc
  · simp [counterLogEncrypt, counterEncrypt, hj]
  · simp [counterLogEncrypt, counterEncrypt, hj]

/-- Forgetting the log, a step of `counterLogImpl` is a step of `counterImpl`. -/
lemma map_counterLogImpl_run (puzzle : Puzzle n S L Salt) (b : Bool)
    (t : ((unifSpec + LeftOrRight.spec Plaintext ByteArray) +
      (sealSpec n S L Salt Ctx N K).batch).Domain) (s : ℕ × CounterLog N K) :
    Prod.map id Prod.fst <$> (counterLogImpl prf codec encodePuzzle qEnc puzzle b t).run s =
      (counterImpl prf codec encodePuzzle qEnc puzzle b t).run s.1 := by
  rcases t with (k | ⟨m₀, m₁⟩) | ts
  · simp [counterLogImpl, counterImpl]
  · simp only [counterLogImpl, counterImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
      LeftOrRight.oracle]
    by_cases h : plaintextLength m₀ = plaintextLength m₁
    · simp only [h, ↓reduceIte, StateT.run_map, ← map_counterLogEncrypt_run, Functor.map_map]
      rfl
    · simp [h]
  · simp [counterLogImpl, counterImpl]

end Counter

/-! ## The online phases as handlers on the cache of the random oracle -/

section Joint

variable [DecidableEq S] [DecidableEq L] [DecidableEq Salt] [DecidableEq Ctx]
  [SampleableType S] [SampleableType L] [DecidableEq N] [SampleableType N] [SampleableType K]

/-- The online phase of the hybrid `G₁` at hidden bit `b` for the puzzle `puzzle`, as one handler
of the adversary's online oracles on the pair of the cache of the random oracle and the private
cache: a step of `privateImpl` on the private cache, with rounds rewritten as single queries
answered by the random oracle on the shared cache. -/
@[expose]
noncomputable def privateJointImpl (puzzle : Puzzle n S L Salt) (b : Bool) :
    QueryImpl ((unifSpec + LeftOrRight.spec Plaintext ByteArray) +
        (sealSpec n S L Salt Ctx N K).batch)
      (StateT ((sealSpec n S L Salt Ctx N K).QueryCache × (privateSpec N K).QueryCache)
        ProbComp) :=
  fun t => StateT.mk fun s => (fun z => (z.1.1, (z.2, z.1.2))) <$>
    (simulateQ (sealSpec n S L Salt Ctx N K).romImpl
      (simulateQ (sealSpec n S L Salt Ctx N K).unbatch
        ((privateImpl prf codec encodePuzzle puzzle b t).run s.2))).run s.1

/-- The online phase of the hybrid `G₁½` with the log of accepted encryptions, at hidden bit `b`
for the puzzle `puzzle`, as one handler on the pair of the cache of the random oracle and the
counter with the log: a step of `counterLogImpl`, with rounds rewritten as single queries answered
by the random oracle on the shared cache. -/
@[expose]
noncomputable def counterJointImpl (puzzle : Puzzle n S L Salt) (b : Bool) :
    QueryImpl ((unifSpec + LeftOrRight.spec Plaintext ByteArray) +
        (sealSpec n S L Salt Ctx N K).batch)
      (StateT ((sealSpec n S L Salt Ctx N K).QueryCache × (ℕ × CounterLog N K)) ProbComp) :=
  fun t => StateT.mk fun s => (fun z => (z.1.1, (z.2, z.1.2))) <$>
    (simulateQ (sealSpec n S L Salt Ctx N K).romImpl
      (simulateQ (sealSpec n S L Salt Ctx N K).unbatch
        ((counterLogImpl prf codec encodePuzzle qEnc puzzle b t).run s.2))).run s.1

lemma privateJointImpl_run_unif (puzzle : Puzzle n S L Salt) (b : Bool) (k : ℕ)
    (s : (sealSpec n S L Salt Ctx N K).QueryCache × (privateSpec N K).QueryCache) :
    (privateJointImpl (Ctx := Ctx) prf codec encodePuzzle puzzle b (.inl (.inl k))).run s =
      (fun z => (z.1, (z.2, s.2))) <$> (unifFwdImpl (sealSpec n S L Salt Ctx N K) k).run s.1 := by
  simp only [add_apply_inl, privateJointImpl, privateImpl, QueryImpl.add_apply_inl,
    PFunctor.Handler.liftTarget_apply, ofPFunctor_toPFunctor, QueryImpl.ofLift_apply,
    StateT.run_monadLift, monadLift_self, bind_pure_comp, simulateQ_map,
    simulateQ_romImpl_simulateQ_unbatch, StateT.run_map, Functor.map_map, StateT.run_mk]
  rw [OracleComp.liftM_eq_liftM_liftM, OracleQuery.liftM_add_left_query, simulateQ_spec_query]
  rfl

lemma counterJointImpl_run_unif (puzzle : Puzzle n S L Salt) (b : Bool) (k : ℕ)
    (s : (sealSpec n S L Salt Ctx N K).QueryCache × (ℕ × CounterLog N K)) :
    (counterJointImpl prf codec encodePuzzle qEnc puzzle b (.inl (.inl k))).run s =
      (fun z => (z.1, (z.2, s.2))) <$> (unifFwdImpl (sealSpec n S L Salt Ctx N K) k).run s.1 := by
  simp only [add_apply_inl, counterJointImpl, counterLogImpl, QueryImpl.add_apply_inl,
    PFunctor.Handler.liftTarget_apply, ofPFunctor_toPFunctor, QueryImpl.ofLift_apply,
    StateT.run_monadLift, monadLift_self, bind_pure_comp, simulateQ_map,
    simulateQ_romImpl_simulateQ_unbatch, StateT.run_map, Functor.map_map, StateT.run_mk]
  rw [OracleComp.liftM_eq_liftM_liftM, OracleQuery.liftM_add_left_query, simulateQ_spec_query]
  rfl

lemma privateJointImpl_run_challenge (puzzle : Puzzle n S L Salt) (b : Bool) (m₀ m₁ : Plaintext)
    (s : (sealSpec n S L Salt Ctx N K).QueryCache × (privateSpec N K).QueryCache) :
    (privateJointImpl (Ctx := Ctx) prf codec encodePuzzle puzzle b (.inl (.inr (m₀, m₁)))).run s =
      if plaintextLength m₀ = plaintextLength m₁ then (do
        let nonce ← $ᵗ N
        let z ← ((privateSpec N K).randomOracle nonce).run s.2
        pure (some (sealWith prf codec (encodePuzzle puzzle) nonce z.1 (if b then m₁ else m₀)),
          (s.1, z.2)))
      else pure (none, s) := by
  by_cases h : plaintextLength m₀ = plaintextLength m₁
  · simp only [privateJointImpl, privateImpl, StateT.run_mk, QueryImpl.add_apply_inl,
      QueryImpl.add_apply_inr, LeftOrRight.oracle, h, ↓reduceIte]
    simp [privateEncrypt, simulateQ_romImpl_simulateQ_unbatch, QueryImpl.simulateQ_add_liftM_left,
      unifFwdImpl.simulateQ_run]
  · simp only [privateJointImpl, privateImpl, StateT.run_mk, QueryImpl.add_apply_inl,
      QueryImpl.add_apply_inr, LeftOrRight.oracle, h, ↓reduceIte]
    simp

lemma counterJointImpl_run_challenge (puzzle : Puzzle n S L Salt) (b : Bool) (m₀ m₁ : Plaintext)
    (s : (sealSpec n S L Salt Ctx N K).QueryCache × (ℕ × CounterLog N K)) :
    (counterJointImpl prf codec encodePuzzle qEnc puzzle b (.inl (.inr (m₀, m₁)))).run s =
      if plaintextLength m₀ = plaintextLength m₁ then
        if s.2.1 < qEnc then (do
          let nonce ← $ᵗ N
          let ks ← $ᵗ (K × K)
          pure (some (sealWith prf codec (encodePuzzle puzzle) nonce ks (if b then m₁ else m₀)),
            (s.1, (s.2.1 + 1, (nonce, ks) :: s.2.2))))
        else pure (some ByteArray.empty, (s.1, (s.2.1 + 1, s.2.2)))
      else pure (none, s) := by
  by_cases h : plaintextLength m₀ = plaintextLength m₁
  · simp only [counterJointImpl, counterLogImpl, StateT.run_mk, QueryImpl.add_apply_inl,
      QueryImpl.add_apply_inr, LeftOrRight.oracle, h, ↓reduceIte]
    by_cases hj : s.2.1 < qEnc
    · simp [counterLogEncrypt, hj, simulateQ_romImpl_simulateQ_unbatch,
        QueryImpl.simulateQ_add_liftM_left, unifFwdImpl.simulateQ_run]
    · simp [counterLogEncrypt, hj]
  · simp only [counterJointImpl, counterLogImpl, StateT.run_mk, QueryImpl.add_apply_inl,
      QueryImpl.add_apply_inr, LeftOrRight.oracle, h, ↓reduceIte]
    simp

lemma privateJointImpl_run_batch (puzzle : Puzzle n S L Salt) (b : Bool)
    (ts : List (sealSpec n S L Salt Ctx N K).Domain)
    (s : (sealSpec n S L Salt Ctx N K).QueryCache × (privateSpec N K).QueryCache) :
    (privateJointImpl (Ctx := Ctx) prf codec encodePuzzle puzzle b (.inr ts)).run s =
      (fun z => (z.1, (z.2, s.2))) <$>
        ((sealSpec n S L Salt Ctx N K).randomOracle.batch ts).run s.1 := by
  simp only [add_apply_inr, privateJointImpl, privateImpl, QueryImpl.add_apply_inr,
    StateT.run_monadLift, bind_pure_comp, simulateQ_map, simulateQ_query, OracleQuery.input_query,
    OracleQuery.cont_query, unbatch_apply_inr, id_map, StateT.run_map, Functor.map_map,
    StateT.run_mk]
  rw [← QueryImpl.apply_compose, QueryImpl.compose_batch]
  congr 3
  funext t
  simp only [QueryImpl.apply_compose, simulateQ_query, OracleQuery.input_query, add_apply_inr,
    OracleQuery.cont_query, QueryImpl.add_apply_inr, QueryImpl.withCaching_apply,
    uniformSampleImpl_apply, map_bind, id_map]

lemma counterJointImpl_run_batch (puzzle : Puzzle n S L Salt) (b : Bool)
    (ts : List (sealSpec n S L Salt Ctx N K).Domain)
    (s : (sealSpec n S L Salt Ctx N K).QueryCache × (ℕ × CounterLog N K)) :
    (counterJointImpl prf codec encodePuzzle qEnc puzzle b (.inr ts)).run s =
      (fun z => (z.1, (z.2, s.2))) <$>
        ((sealSpec n S L Salt Ctx N K).randomOracle.batch ts).run s.1 := by
  simp only [add_apply_inr, counterJointImpl, counterLogImpl, QueryImpl.add_apply_inr,
    StateT.run_monadLift, bind_pure_comp, simulateQ_map, simulateQ_query, OracleQuery.input_query,
    OracleQuery.cont_query, unbatch_apply_inr, id_map, StateT.run_map, Functor.map_map,
    StateT.run_mk]
  rw [← QueryImpl.apply_compose, QueryImpl.compose_batch]
  congr 3
  funext t
  simp only [QueryImpl.apply_compose, simulateQ_query, OracleQuery.input_query, add_apply_inr,
    OracleQuery.cont_query, QueryImpl.add_apply_inr, QueryImpl.withCaching_apply,
    uniformSampleImpl_apply, map_bind, id_map]

end Joint

/-! ## From `G₁` to `G₁½`: identical until a nonce repeats -/

section NonceHop

variable [DecidableEq N]

/-- The private cache of `G₁` read off a log of accepted encryptions: each logged nonce caches its
pair of subkeys, the latest entry taking precedence. -/
@[expose]
def logCache : CounterLog N K → (privateSpec N K).QueryCache
  | [] => ∅
  | e :: l => (logCache l).cacheQuery e.1 e.2

@[simp] lemma logCache_nil : logCache ([] : CounterLog N K) = ∅ := rfl

@[simp] lemma logCache_cons (e : N × (K × K)) (l : CounterLog N K) :
    logCache (e :: l) = (logCache l).cacheQuery e.1 e.2 := rfl

/-- A nonce absent from the log is uncached. -/
lemma logCache_eq_none {l : CounterLog N K} {η : N} (h : η ∉ l.map Prod.fst) :
    logCache l η = none := by
  induction l with
  | nil => rfl
  | cons e l ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at h
    rw [logCache_cons, QueryCache.cacheQuery_of_ne _ _ h.1]
    exact ih h.2

/-- The bad event of the nonce hop on the counter `j` and the log `l` of accepted encryptions: two
accepted encryptions share a nonce, or an encryption beyond the `qEnc`-th was accepted. -/
@[expose]
def NonceBad (s : ℕ × CounterLog N K) : Prop :=
  ¬ (s.2.map Prod.fst).Nodup ∨ qEnc < s.1

variable [DecidableEq S] [DecidableEq L] [DecidableEq Salt] [DecidableEq Ctx]
  [SampleableType S] [SampleableType L] [SampleableType N] [SampleableType K]

/-- A step of the handler of `G₁½` keeps the counter and the log, accepts an encryption within
the budget, logging its nonce and subkeys, or accepts one beyond the budget, logging nothing. -/
lemma counterJointImpl_run_cases (puzzle : Puzzle n S L Salt) (b : Bool)
    (t : ((unifSpec + LeftOrRight.spec Plaintext ByteArray) +
      (sealSpec n S L Salt Ctx N K).batch).Domain)
    (s : (sealSpec n S L Salt Ctx N K).QueryCache × (ℕ × CounterLog N K))
    {z} (hz : z ∈ support ((counterJointImpl prf codec encodePuzzle qEnc puzzle b t).run s)) :
    z.2.2 = s.2 ∨ (s.2.1 < qEnc ∧ ∃ e, z.2.2 = (s.2.1 + 1, e :: s.2.2)) ∨
      (qEnc ≤ s.2.1 ∧ z.2.2 = (s.2.1 + 1, s.2.2)) := by
  rcases t with (k | ⟨m₀, m₁⟩) | ts
  · rw [counterJointImpl_run_unif, support_map] at hz
    obtain ⟨_, -, rfl⟩ := hz
    exact Or.inl rfl
  · rw [counterJointImpl_run_challenge] at hz
    by_cases h : plaintextLength m₀ = plaintextLength m₁
    · by_cases hj : s.2.1 < qEnc
      · simp only [h, hj, ↓reduceIte, mem_support_bind_iff, support_pure,
          Set.mem_singleton_iff] at hz
        obtain ⟨η, -, ks, -, rfl⟩ := hz
        exact Or.inr (Or.inl ⟨hj, (η, ks), rfl⟩)
      · simp only [h, hj, ↓reduceIte, mem_support_pure_iff] at hz
        subst hz
        exact Or.inr (Or.inr ⟨Nat.le_of_not_lt hj, rfl⟩)
    · simp only [h, ↓reduceIte, mem_support_pure_iff] at hz
      subst hz
      exact Or.inl rfl
  · rw [counterJointImpl_run_batch, support_map] at hz
    obtain ⟨_, -, rfl⟩ := hz
    exact Or.inl rfl

/-- A step of the handler of `G₁½` at a query other than a challenge keeps the counter and the
log. -/
lemma counterJointImpl_run_eq_of_not_challenge (puzzle : Puzzle n S L Salt) (b : Bool)
    (t : ((unifSpec + LeftOrRight.spec Plaintext ByteArray) +
      (sealSpec n S L Salt Ctx N K).batch).Domain) (ht : ∀ mm, t ≠ .inl (.inr mm))
    (s : (sealSpec n S L Salt Ctx N K).QueryCache × (ℕ × CounterLog N K))
    {z} (hz : z ∈ support ((counterJointImpl prf codec encodePuzzle qEnc puzzle b t).run s)) :
    z.2.2 = s.2 := by
  rcases t with (k | ⟨m₀, m₁⟩) | ts
  · rw [counterJointImpl_run_unif, support_map] at hz
    obtain ⟨_, -, rfl⟩ := hz
    rfl
  · exact absurd rfl (ht _)
  · rw [counterJointImpl_run_batch, support_map] at hz
    obtain ⟨_, -, rfl⟩ := hz
    rfl

/-- `NonceBad` is sticky in the handler of `G₁½`. -/
lemma preservesInv_counterJointImpl_nonceBad (puzzle : Puzzle n S L Salt) (b : Bool) :
    QueryImpl.PreservesInv (counterJointImpl (Ctx := Ctx) prf codec encodePuzzle qEnc puzzle b)
      (fun s => NonceBad qEnc s.2) := by
  intro t s hs z hz
  rcases counterJointImpl_run_cases prf codec encodePuzzle qEnc puzzle b t s hz with
    h | ⟨-, e, h⟩ | ⟨-, h⟩ <;> rw [NonceBad, h] <;> rw [NonceBad] at hs
  · exact hs
  · rcases hs with hs | hs
    · exact Or.inl fun hd => hs (List.nodup_cons.1 hd).2
    · exact Or.inr (Nat.lt_succ_of_lt hs)
  · rcases hs with hs | hs
    · exact Or.inl hs
    · exact Or.inr (Nat.lt_succ_of_lt hs)

/-- The invariant of the handler of `G₁½`: the log holds one entry per accepted encryption within
the budget. -/
@[expose]
def CounterInv (s : ℕ × CounterLog N K) : Prop := s.2.length = min s.1 qEnc

lemma preservesInv_counterJointImpl_counterInv (puzzle : Puzzle n S L Salt) (b : Bool) :
    QueryImpl.PreservesInv (counterJointImpl (Ctx := Ctx) prf codec encodePuzzle qEnc puzzle b)
      (fun s => CounterInv qEnc s.2) := by
  intro t s hs z hz
  rcases counterJointImpl_run_cases prf codec encodePuzzle qEnc puzzle b t s hz with
    h | ⟨hj, e, h⟩ | ⟨hj, h⟩ <;> rw [CounterInv, h] <;> rw [CounterInv] at hs
  · exact hs
  · simp only [List.length_cons, hs]
    omega
  · simp only [hs]
    omega

/-- **The handlers agree until `NonceBad`.** Read through `logCache`, each step of the handler of
`G₁½` is a step of the handler of `G₁`, unless its post-state is `NonceBad`: local coins and rounds
are answered alike and leave the private states alone; an accepted challenge within the budget
draws the same nonce, and at a nonce absent from the log the private cache of `G₁` draws a fresh
pair of subkeys, as `G₁½` does, and caches it, as logging it does; at a nonce in the log, or beyond
the budget, the post-state is `NonceBad`. -/
theorem dominatedUntilBad_counterJointImpl (puzzle : Puzzle n S L Salt) (b : Bool) :
    QueryImpl.DominatedUntilBad (counterJointImpl (Ctx := Ctx) prf codec encodePuzzle qEnc puzzle b)
      (privateJointImpl (Ctx := Ctx) prf codec encodePuzzle puzzle b)
      (fun s => (s.1, logCache s.2.2)) (fun _ => True) (fun s => NonceBad qEnc s.2) := by
  intro t s _ hb Q
  rcases t with (k | ⟨m₀, m₁⟩) | ts
  · rw [counterJointImpl_run_unif, privateJointImpl_run_unif, prEvent_map, prEvent_map]
    exact prEvent_mono _ _ _ fun z hz => hz.1
  · rw [counterJointImpl_run_challenge, privateJointImpl_run_challenge]
    by_cases h : plaintextLength m₀ = plaintextLength m₁
    · simp only [h, ↓reduceIte]
      by_cases hj : s.2.1 < qEnc
      · simp only [hj, ↓reduceIte]
        refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun η => ?_
        by_cases hη : η ∈ s.2.2.map Prod.fst
        · refine le_trans (le_of_eq (prEvent_eq_zero_of_forall_mem_support _ _ fun z hz hz' => ?_))
            zero_le
          simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
          obtain ⟨ks, -, rfl⟩ := hz
          exact hz'.2 (Or.inl fun hd => (List.nodup_cons.1 hd).1 hη)
        · rw [randomOracle.run_eq, logCache_eq_none hη]
          simp only [bind_assoc, pure_bind]
          refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun ks => ?_
          exact prEvent_pure_le_pure _ _ _ _ fun hq => hq.1
      · simp only [hj, ↓reduceIte]
        refine le_trans (le_of_eq (prEvent_eq_zero_of_forall_mem_support _ _ fun z hz hz' => ?_))
          zero_le
        rw [mem_support_pure_iff] at hz
        subst hz
        refine hz'.2 (Or.inr ?_)
        dsimp only
        omega
    · simp only [h, ↓reduceIte]
      exact prEvent_pure_le_pure _ _ _ _ fun hq => hq.1
  · rw [counterJointImpl_run_batch, privateJointImpl_run_batch, prEvent_map, prEvent_map]
    exact prEvent_mono _ _ _ fun z hz => hz.1

/-- The hazard of a challenge step of the handler of `G₁½` at counter `j`: at most `j / |N|`
within the budget, the probability that the fresh nonce is one of the `j` logged nonces; beyond
the budget the step is bad outright. -/
@[expose]
noncomputable def nonceHazard [Fintype N] (j : ℕ) : ℝ≥0∞ :=
  if j < qEnc then (j : ℝ≥0∞) * (Fintype.card N : ℝ≥0∞)⁻¹ else ⊤

omit [DecidableEq N] [SampleableType N] in
lemma monotone_nonceHazard [Fintype N] : Monotone (nonceHazard (N := N) qEnc) := by
  intro i j hij
  simp only [nonceHazard]
  split_ifs with hi hj hj
  · gcongr
  · exact le_top
  · omega
  · exact le_rfl

/-- **The hazard of a challenge step.** From a good state satisfying `CounterInv`, a challenge step
of the handler of `G₁½` makes the state `NonceBad` with probability at most `nonceHazard` of the
counter: within the budget, only when the fresh uniform nonce is one of the logged nonces, of which
there are as many as accepted encryptions. -/
lemma prEvent_counterJointImpl_run_nonceBad_le [Fintype N] (puzzle : Puzzle n S L Salt) (b : Bool)
    (m₀ m₁ : Plaintext) (s : (sealSpec n S L Salt Ctx N K).QueryCache × (ℕ × CounterLog N K))
    (hs : CounterInv qEnc s.2) (hb : ¬ NonceBad qEnc s.2) :
    Pr{let z ← (counterJointImpl prf codec encodePuzzle qEnc puzzle b
        (.inl (.inr (m₀, m₁)))).run s}[NonceBad qEnc z.2.2] ≤ nonceHazard (N := N) qEnc s.2.1 := by
  rw [counterJointImpl_run_challenge]
  by_cases h : plaintextLength m₀ = plaintextLength m₁
  · by_cases hj : s.2.1 < qEnc
    · simp only [h, hj, ↓reduceIte, nonceHazard]
      refine (prEvent_bind_le_prEvent_of_support _ _ (fun η => η ∈ s.2.2.map Prod.fst) _
        fun η _ hη => prEvent_eq_zero_of_forall_mem_support _ _ fun z hz hz' => ?_).trans ?_
      · simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
        obtain ⟨ks, -, rfl⟩ := hz
        simp only [NonceBad, not_or, not_lt, not_not] at hb
        rcases hz' with hz' | hz'
        · exact hz' (List.nodup_cons.2 ⟨hη, hb.1⟩)
        · dsimp only at hz'
          omega
      · have hlen : (s.2.2.map Prod.fst).length = s.2.1 := by
          rw [List.length_map, hs]
          omega
        refine (le_of_eq (prEvent_congr _ _ _ fun η => ?_)).trans
          ((SampleableType.prEvent_uniformSample_exists_eq_le (s.2.2.map Prod.fst).get).trans ?_)
        · exact List.mem_iff_get.trans (exists_congr fun _ => Iff.rfl)
        · rw [hlen, div_eq_mul_inv]
    · simp only [h, hj, ↓reduceIte, nonceHazard]
      exact le_top
  · simp only [h, ↓reduceIte]
    rw [prEvent_eq_zero_of_forall_mem_support _ _ fun z hz => by
      rw [mem_support_pure_iff] at hz
      exact hz ▸ hb]
    exact zero_le

/-- **The nonce-collision bound.** In the handler of `G₁½`, from the counter `0` and the empty log,
a computation with at most `qEnc` challenge queries ends `NonceBad` with probability at most
`qEnc (qEnc - 1) / (2 |N|)`: the adaptive birthday bound
(`OracleComp.prEvent_simulateQ_run_le_sum_of_isQueryBoundP`) with hazard `j / |N|` at the `j`-th
accepted encryption. Every query satisfying `charged` counts against the budget, and challenge
queries do. -/
theorem prEvent_counterJointImpl_nonceBad_le [Fintype N] (puzzle : Puzzle n S L Salt) (b : Bool)
    {α : Type} (oa : OracleComp ((unifSpec + LeftOrRight.spec Plaintext ByteArray) +
      (sealSpec n S L Salt Ctx N K).batch) α)
    (charged : ((unifSpec + LeftOrRight.spec Plaintext ByteArray) +
      (sealSpec n S L Salt Ctx N K).batch).Domain → Prop) [DecidablePred charged]
    (hcharged : ∀ mm, charged (.inl (.inr mm))) (hq : oa.IsQueryBoundP charged qEnc)
    (c : (sealSpec n S L Salt Ctx N K).QueryCache) :
    Pr{let z ← (simulateQ (counterJointImpl prf codec encodePuzzle qEnc puzzle b) oa).run
        (c, (0, []))}[NonceBad qEnc z.2.2] ≤
      ((qEnc * (qEnc - 1) : ℕ) : ℝ≥0∞) / (2 * Fintype.card N) := by
  refine (prEvent_simulateQ_run_le_sum_of_isQueryBoundP
    (σ := (sealSpec n S L Salt Ctx N K).QueryCache × (ℕ × CounterLog N K)) _ charged
    (fun s => s.2.1) (fun s => CounterInv qEnc s.2) (fun s => NonceBad qEnc s.2)
    (nonceHazard (N := N) qEnc) (monotone_nonceHazard qEnc)
    (preservesInv_counterJointImpl_counterInv prf codec encodePuzzle qEnc puzzle b)
    (fun t s ht _ hb z hz => ?_) (fun t s _ _ _ z hz => ?_) (fun t s _ hs hb => ?_) oa hq _
    (by simp [CounterInv]) (by simp [NonceBad])).trans (le_of_eq ?_)
  · rw [counterJointImpl_run_eq_of_not_challenge prf codec encodePuzzle qEnc puzzle b t
      (by rintro mm rfl; exact ht (hcharged mm)) s hz]
    exact ⟨rfl, hb⟩
  · rcases counterJointImpl_run_cases prf codec encodePuzzle qEnc puzzle b t s hz with
      h | ⟨-, e, h⟩ | ⟨-, h⟩ <;> simp [h]
  · by_cases ht : ∃ mm, t = .inl (.inr mm)
    · obtain ⟨⟨m₀, m₁⟩, rfl⟩ := ht
      exact prEvent_counterJointImpl_run_nonceBad_le prf codec encodePuzzle qEnc puzzle b m₀ m₁ s
        hs hb
    · rw [prEvent_eq_zero_of_forall_mem_support _ _ fun z hz => by
        rw [counterJointImpl_run_eq_of_not_challenge prf codec encodePuzzle qEnc puzzle b t
          (fun mm h => ht ⟨mm, h⟩) s hz]
        exact hb]
      exact zero_le
  · rw [← ENNReal.gauss_sum_inv_eq]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    simp [nonceHazard, hi]

/-- The random-oracle run of the online phase of `G₁`, which runs `privateImpl` on the private
cache inside the run on the shared cache, is equal in distribution to the run of `privateJointImpl`
on the pair of caches. -/
lemma run_romImpl_privateImpl_evalDistEq_privateJointImpl {α : Type} (puzzle : Puzzle n S L Salt)
    (b : Bool) (oa : OracleComp ((unifSpec + LeftOrRight.spec Plaintext ByteArray) +
      (sealSpec n S L Salt Ctx N K).batch) α) (c : (sealSpec n S L Salt Ctx N K).QueryCache) :
    (simulateQ (sealSpec n S L Salt Ctx N K).romImpl
      (simulateQ (sealSpec n S L Salt Ctx N K).unbatch
        ((simulateQ (privateImpl prf codec encodePuzzle puzzle b) oa).run' ∅))).run c =ᵈ
      (fun z => (z.1, z.2.1)) <$>
        (simulateQ (privateJointImpl (Ctx := Ctx) prf codec encodePuzzle puzzle b) oa).run
          (c, ∅) := by
  have h := simulateQ_run_simulateQ_run_evalDistEq
    ((sealSpec n S L Salt Ctx N K).romImpl ∘ₛ (sealSpec n S L Salt Ctx N K).unbatch)
    (privateImpl prf codec encodePuzzle puzzle b)
    (privateJointImpl (Ctx := Ctx) prf codec encodePuzzle puzzle b) (fun t s q => by
      rw [privateJointImpl, StateT.run_mk, Functor.map_map, QueryImpl.simulateQ_compose]
      simp) oa ∅ c
  rw [QueryImpl.simulateQ_compose] at h
  rw [StateT.run'_eq, simulateQ_map, simulateQ_map, StateT.run_map]
  refine (h.map fun z => (z.1.1, z.2)).trans ?_
  rw [Functor.map_map]

/-- The random-oracle run of the online phase of `G₁½`, which runs `counterImpl` on the counter
inside the run on the shared cache, is equal in distribution to the run of `counterJointImpl` on
the cache with the counter `0` and the empty log: forgetting the log, `counterLogImpl` is
`counterImpl`. -/
lemma run_romImpl_counterImpl_evalDistEq_counterJointImpl {α : Type} (puzzle : Puzzle n S L Salt)
    (b : Bool) (oa : OracleComp ((unifSpec + LeftOrRight.spec Plaintext ByteArray) +
      (sealSpec n S L Salt Ctx N K).batch) α) (c : (sealSpec n S L Salt Ctx N K).QueryCache) :
    (simulateQ (sealSpec n S L Salt Ctx N K).romImpl
      (simulateQ (sealSpec n S L Salt Ctx N K).unbatch
        ((simulateQ (counterImpl prf codec encodePuzzle qEnc puzzle b) oa).run' 0))).run c =ᵈ
      (fun z => (z.1, z.2.1)) <$>
        (simulateQ (counterJointImpl (Ctx := Ctx) prf codec encodePuzzle qEnc puzzle b) oa).run
          (c, (0, [])) := by
  rw [← show (simulateQ (counterLogImpl prf codec encodePuzzle qEnc puzzle b) oa).run' (0, []) =
      (simulateQ (counterImpl prf codec encodePuzzle qEnc puzzle b) oa).run' 0 from
    run'_simulateQ_eq_of_query_map_eq _ _ Prod.fst
      (map_counterLogImpl_run prf codec encodePuzzle qEnc puzzle b) oa (0, [])]
  have h := simulateQ_run_simulateQ_run_evalDistEq
    ((sealSpec n S L Salt Ctx N K).romImpl ∘ₛ (sealSpec n S L Salt Ctx N K).unbatch)
    (counterLogImpl prf codec encodePuzzle qEnc puzzle b)
    (counterJointImpl (Ctx := Ctx) prf codec encodePuzzle qEnc puzzle b) (fun t s q => by
      rw [counterJointImpl, StateT.run_mk, Functor.map_map, QueryImpl.simulateQ_compose]
      simp) oa (0, []) c
  rw [QueryImpl.simulateQ_compose] at h
  rw [StateT.run'_eq, simulateQ_map, simulateQ_map, StateT.run_map]
  refine (h.map fun z => (z.1.1, z.2)).trans ?_
  rw [Functor.map_map]

/-- **One online phase, from `G₁` to `G₁½`.** From any cache `c`, an event of the output of the
online handler of `G₁` exceeds the event in the online handler of `G₁½` by at most the probability
of `NonceBad` there. -/
theorem prEvent_privateJointImpl_le {α : Type} (puzzle : Puzzle n S L Salt) (b : Bool)
    (oa : OracleComp ((unifSpec + LeftOrRight.spec Plaintext ByteArray) +
      (sealSpec n S L Salt Ctx N K).batch) α) (c : (sealSpec n S L Salt Ctx N K).QueryCache)
    (P : α → Prop) :
    Pr{let z ← (simulateQ (privateJointImpl (Ctx := Ctx) prf codec encodePuzzle puzzle b) oa).run
        (c, ∅)}[P z.1] ≤
      Pr{let z ← (simulateQ (counterJointImpl (Ctx := Ctx) prf codec encodePuzzle qEnc puzzle b)
          oa).run (c, (0, []))}[P z.1] +
        Pr{let z ← (simulateQ (counterJointImpl (Ctx := Ctx) prf codec encodePuzzle qEnc puzzle b)
          oa).run (c, (0, []))}[NonceBad qEnc z.2.2] :=
  ((dominatedUntilBad_counterJointImpl prf codec encodePuzzle qEnc puzzle b
    ).prEvent_simulateQ_run_le_map_or_bad (fun _ _ _ _ _ => trivial)
    (preservesInv_counterJointImpl_nonceBad prf codec encodePuzzle qEnc puzzle b) oa (c, (0, []))
    trivial fun z => P z.1).trans (prEvent_or_le _ _ _)

/-- **One online phase, from `G₁½` to `G₁`.** From any cache `c`, an event of the output of the
online handler of `G₁½` exceeds the event in the online handler of `G₁` by at most the probability
of `NonceBad`. -/
theorem prEvent_counterJointImpl_le {α : Type} (puzzle : Puzzle n S L Salt) (b : Bool)
    (oa : OracleComp ((unifSpec + LeftOrRight.spec Plaintext ByteArray) +
      (sealSpec n S L Salt Ctx N K).batch) α) (c : (sealSpec n S L Salt Ctx N K).QueryCache)
    (P : α → Prop) :
    Pr{let z ← (simulateQ (counterJointImpl (Ctx := Ctx) prf codec encodePuzzle qEnc puzzle b)
        oa).run (c, (0, []))}[P z.1] ≤
      Pr{let z ← (simulateQ (privateJointImpl (Ctx := Ctx) prf codec encodePuzzle puzzle b) oa).run
          (c, ∅)}[P z.1] +
        Pr{let z ← (simulateQ (counterJointImpl (Ctx := Ctx) prf codec encodePuzzle qEnc puzzle b)
          oa).run (c, (0, []))}[NonceBad qEnc z.2.2] := by
  rw [add_comm]
  exact prEvent_le_prEvent_add_of_prEvent_and_not_le _ _ _ _ _
    ((dominatedUntilBad_counterJointImpl prf codec encodePuzzle qEnc puzzle b
      ).prEvent_simulateQ_run_map_and_not_bad_le (fun _ _ _ _ _ => trivial)
      (preservesInv_counterJointImpl_nonceBad prf codec encodePuzzle qEnc puzzle b) oa
      (c, (0, [])) trivial fun z => P z.1)

/-- **From `G₁` to `G₁½`.** For a hiding adversary `adv` making at most `qEnc` challenge queries,
at either hidden bit, the probabilities that `privateExperiment` and `counterExperiment` return
the guess `true` differ by at most `qEnc (qEnc - 1) / (2 |N|)`.

The two experiments share preprocessing and key generation. From the resulting cache, their
online phases are, up to distribution, the runs of `privateJointImpl` and `counterJointImpl`,
which agree through `logCache` until two accepted encryptions share a nonce
(`dominatedUntilBad_counterJointImpl`); the adaptive birthday bound bounds that event
(`prEvent_counterJointImpl_nonceBad_le`). -/
theorem absDiff_privateExperiment_counterExperiment_le [NeZero n] [AddCommGroup L]
    [SampleableType Salt] [Fintype N] (mkCtx : Salt → Ctx) (initAcc : Ctx → S)
    (adv : HidingAdversary (sealSpec n S L Salt Ctx N K) (Puzzle n S L Salt) Plaintext ByteArray)
    (hadv : adv.MakesAtMostQueries qEnc) (b : Bool) :
    ENNReal.absDiff
      (Pr{let z ← (simulateQ (sealSpec n S L Salt Ctx N K).romImpl
        (privateExperiment m prf codec encodePuzzle mkCtx initAcc adv b)).run' ∅}[z.1 = true])
      (Pr{let z ← (simulateQ (sealSpec n S L Salt Ctx N K).romImpl
        (counterExperiment m prf codec encodePuzzle qEnc mkCtx initAcc adv b)).run' ∅}[
          z.1 = true]) ≤
      ((qEnc * (qEnc - 1) : ℕ) : ℝ≥0∞) / (2 * Fintype.card N) := by
  rw [StateT.run'_eq, StateT.run'_eq, prEvent_map, prEvent_map]
  simp only [privateExperiment, counterExperiment, guessExperiment, simulateQ_bind,
    StateT.run_bind, bind_pure_comp, privateAdversary, counterAdversary]
  have hbad : Pr{let z ← ((simulateQ (sealSpec n S L Salt Ctx N K).romImpl adv.preprocess).run
      ∅ >>= fun p => ((simulateQ (sealSpec n S L Salt Ctx N K).romImpl
        (simulateQ (sealSpec n S L Salt Ctx N K).unbatch
          (sealScheme n m mkCtx initAcc N K).gen)).run
          p.2 >>= fun p₁ => (simulateQ (counterJointImpl (Ctx := Ctx) prf codec encodePuzzle qEnc
            p₁.1.1 b) (adv.online p.1 p₁.1.1)).run (p₁.2, (0, []))))}[NonceBad qEnc z.2.2] ≤
      ((qEnc * (qEnc - 1) : ℕ) : ℝ≥0∞) / (2 * Fintype.card N) :=
    prEvent_bind_le_of_forall_le _ _ _ fun p => prEvent_bind_le_of_forall_le _ _ _ fun p₁ =>
      prEvent_counterJointImpl_nonceBad_le prf codec encodePuzzle qEnc p₁.1.1 b _ _
        (fun _ => rfl) (hadv p.1 p₁.1.1) _
  refine ENNReal.absDiff_le_iff.2 ⟨?_, ?_⟩
  · refine (prEvent_bind_le_add_of_forall_le _ _ _ _ _ _ _ fun p =>
      prEvent_bind_le_add_of_forall_le _ _ _ _ _ _ _ fun p₁ => ?_).trans (add_le_add le_rfl hbad)
    rw [simulateQ_map, simulateQ_map, StateT.run_map, StateT.run_map, prEvent_map, prEvent_map,
      (run_romImpl_privateImpl_evalDistEq_privateJointImpl prf codec encodePuzzle p₁.1.1 b _
        p₁.2).prEvent_eq,
      (run_romImpl_counterImpl_evalDistEq_counterJointImpl prf codec encodePuzzle qEnc p₁.1.1 b _
        p₁.2).prEvent_eq, prEvent_map, prEvent_map]
    exact prEvent_privateJointImpl_le prf codec encodePuzzle qEnc p₁.1.1 b _ p₁.2 (· = true)
  · refine (prEvent_bind_le_add_of_forall_le _ _ _ _ _ _ _ fun p =>
      prEvent_bind_le_add_of_forall_le _ _ _ _ _ _ _ fun p₁ => ?_).trans (add_le_add le_rfl hbad)
    rw [simulateQ_map, simulateQ_map, StateT.run_map, StateT.run_map, prEvent_map, prEvent_map,
      (run_romImpl_privateImpl_evalDistEq_privateJointImpl prf codec encodePuzzle p₁.1.1 b _
        p₁.2).prEvent_eq,
      (run_romImpl_counterImpl_evalDistEq_counterJointImpl prf codec encodePuzzle qEnc p₁.1.1 b _
        p₁.2).prEvent_eq, prEvent_map, prEvent_map]
    exact prEvent_counterJointImpl_le prf codec encodePuzzle qEnc p₁.1.1 b _ p₁.2 (· = true)

end NonceHop

/-! ## From `G₁½` to `G₂`: the counter-indexed subkeys are a uniform key table -/

section KeyTable

/-- The key table read off a log of accepted encryptions over the table `T`: the `j`-th logged
encryption, counted from the oldest, writes its pair of subkeys at the instances `(0, j)` and
`(1, j)`, for `j < qEnc`; every other cell is that of `T`. -/
@[expose]
def keyTable (T : Fin (2 * qEnc) → K) : CounterLog N K → Fin (2 * qEnc) → K
  | [] => T
  | e :: l => if h : l.length < qEnc then
      Function.update (Function.update (keyTable T l) (instanceIndex 0 ⟨l.length, h⟩) e.2.1)
        (instanceIndex 1 ⟨l.length, h⟩) e.2.2
    else keyTable T l

@[simp] lemma keyTable_nil (T : Fin (2 * qEnc) → K) : keyTable qEnc T ([] : CounterLog N K) = T :=
  rfl

lemma keyTable_cons (T : Fin (2 * qEnc) → K) (e : N × (K × K)) (l : CounterLog N K)
    (h : l.length < qEnc) :
    keyTable qEnc T (e :: l) =
      Function.update (Function.update (keyTable qEnc T l) (instanceIndex 0 ⟨l.length, h⟩) e.2.1)
        (instanceIndex 1 ⟨l.length, h⟩) e.2.2 := by
  simp only [keyTable, h, ↓reduceDIte]

lemma instanceIndex_inj {i i' : Fin 2} {j j' : Fin qEnc} :
    instanceIndex i j = instanceIndex i' j' ↔ i = i' ∧ j = j' := by
  rw [instanceIndex, instanceIndex, finProdFinEquiv.apply_eq_iff_eq, Prod.mk.injEq]

lemma instanceIndex_zero_ne_one (j : Fin qEnc) : instanceIndex 0 j ≠ instanceIndex 1 j := by
  simp [instanceIndex_inj]

/-- The cells of the encryptions not yet logged are those of `T`. -/
lemma keyTable_apply_of_le (T : Fin (2 * qEnc) → K) (l : CounterLog N K) (i : Fin 2)
    (j : Fin qEnc) (hj : l.length ≤ j) :
    keyTable qEnc T l (instanceIndex i j) = T (instanceIndex i j) := by
  induction l with
  | nil => rfl
  | cons e l ih =>
    simp only [List.length_cons] at hj
    have hne : ∀ k (h : l.length < qEnc), instanceIndex i j ≠ instanceIndex k ⟨l.length, h⟩ :=
      fun k h he => by
        obtain ⟨-, he⟩ := (instanceIndex_inj qEnc).1 he
        simp only [Fin.ext_iff] at he
        omega
    simp only [keyTable]
    split_ifs with h
    · rw [Function.update_of_ne (hne 1 h), Function.update_of_ne (hne 0 h), ih (by omega)]
    · exact ih (by omega)

/-- Overwriting the cells of an encryption not yet logged commutes with reading off the log. -/
lemma keyTable_update (T : Fin (2 * qEnc) → K) (l : CounterLog N K) (j : Fin qEnc)
    (hj : l.length ≤ j) (u₀ u₁ : K) :
    keyTable qEnc (Function.update (Function.update T (instanceIndex 0 j) u₀)
        (instanceIndex 1 j) u₁) l =
      Function.update (Function.update (keyTable qEnc T l) (instanceIndex 0 j) u₀)
        (instanceIndex 1 j) u₁ := by
  induction l with
  | nil => rfl
  | cons e l ih =>
    simp only [List.length_cons] at hj
    simp only [keyTable]
    split_ifs with h
    · rw [ih (by omega)]
      have hne : ∀ k k', instanceIndex k j ≠ instanceIndex k' ⟨l.length, h⟩ := fun k k' he => by
        obtain ⟨-, he⟩ := (instanceIndex_inj qEnc).1 he
        simp only [Fin.ext_iff] at he
        omega
      rw [Function.update_comm (hne 1 0), Function.update_comm (hne 1 1),
        Function.update_comm (hne 0 0), Function.update_comm (hne 0 1)]
    · exact ih (by omega)

end KeyTable

section PRFHop

variable [DecidableEq S] [DecidableEq L] [DecidableEq Salt] [DecidableEq Ctx] [DecidableEq N]
  [SampleableType S] [SampleableType L] [SampleableType N] [SampleableType K]

/-- The handler of the online phase of `indexedExperiment` at hidden bit `b` for the puzzle
`puzzle`, as it appears there: local coins are forwarded, a challenge query is answered by the
left-or-right oracle over `indexedEncrypt`, and single queries to the oracles with subkeys are
forwarded. -/
@[expose]
def indexedOnlineImpl (puzzle : Puzzle n S L Salt) (b : Bool) :
    QueryImpl ((unifSpec + LeftOrRight.spec Plaintext ByteArray) + sealSpec n S L Salt Ctx N K)
      (StateT ℕ (OracleComp (indexedSpec n S L Salt Ctx N K qEnc))) :=
  ((QueryImpl.ofLift unifSpec (OracleComp (indexedSpec n S L Salt Ctx N K qEnc))).liftTarget
      (StateT ℕ (OracleComp (indexedSpec n S L Salt Ctx N K qEnc))) +
    LeftOrRight.oracle (indexedEncrypt (n := n) (S := S) (L := L) (Salt := Salt) (Ctx := Ctx)
      (K := K) codec qEnc (encodePuzzle puzzle)) plaintextLength b) +
    (fun t => liftM ((indexedSpec n S L Salt Ctx N K qEnc).query (.inr (.inl t))) :
      QueryImpl (sealSpec n S L Salt Ctx N K)
        (StateT ℕ (OracleComp (indexedSpec n S L Salt Ctx N K qEnc))))

/-- The handler of `indexedRun`: local coins are forwarded, the oracles with subkeys are a random
oracle on the cache, and instance queries go to the function oracle. -/
@[expose]
noncomputable def indexedRunImpl :
    QueryImpl (indexedSpec n S L Salt Ctx N K qEnc)
      (StateT (sealSpec n S L Salt Ctx N K).QueryCache
        (OracleComp (PRFOracleSpec (Fin (2 * qEnc) × ByteArray) (Bytes 32)))) :=
  (QueryImpl.ofLift unifSpec
      (OracleComp (PRFOracleSpec (Fin (2 * qEnc) × ByteArray) (Bytes 32)))).liftTarget
    (StateT (sealSpec n S L Salt Ctx N K).QueryCache
      (OracleComp (PRFOracleSpec (Fin (2 * qEnc) × ByteArray) (Bytes 32)))) +
  ((sealSpec n S L Salt Ctx N K).randomOracle.liftTarget
      (StateT (sealSpec n S L Salt Ctx N K).QueryCache
        (OracleComp (PRFOracleSpec (Fin (2 * qEnc) × ByteArray) (Bytes 32)))) +
    (fun x => liftM (functionQuery (R := Bytes 32) x) : QueryImpl (instanceSpec qEnc)
      (StateT (sealSpec n S L Salt Ctx N K).QueryCache
        (OracleComp (PRFOracleSpec (Fin (2 * qEnc) × ByteArray) (Bytes 32))))))

/-- The random oracle model for the oracles of the indexed hybrid with the key table `T`: local
coins are forwarded, the oracles with subkeys are a random oracle on the cache, and instance `i`
evaluates `prf` under `T i`. -/
@[expose]
noncomputable def keyedRomImpl (T : Fin (2 * qEnc) → K) :
    QueryImpl (indexedSpec n S L Salt Ctx N K qEnc)
      (StateT (sealSpec n S L Salt Ctx N K).QueryCache ProbComp) :=
  unifFwdImpl (sealSpec n S L Salt Ctx N K) +
    ((sealSpec n S L Salt Ctx N K).randomOracle +
      (fun x => pure (prf.eval (T x.1) x.2) : QueryImpl (instanceSpec qEnc)
        (StateT (sealSpec n S L Salt Ctx N K).QueryCache ProbComp)))

omit [SampleableType N] in
/-- In the real world of `prf.multiKey` with the key table `T`, the handler of `indexedRun` is
`keyedRomImpl T`. -/
lemma mapStateTBase_indexedRunImpl (T : Fin (2 * qEnc) → K) :
    ((prf.multiKey (Fin (2 * qEnc))).prfRealQueryImpl T).mapStateTBase
        (indexedRunImpl (n := n) (S := S) (L := L) (Salt := Salt) (Ctx := Ctx) (N := N) (K := K)
          qEnc) =
      keyedRomImpl (n := n) (S := S) (L := L) (Salt := Salt) (Ctx := Ctx) prf qEnc T := by
  funext t
  refine StateT.ext fun s => ?_
  rcases t with k | t | x
  · simp only [QueryImpl.mapStateTBase, indexedRunImpl, keyedRomImpl, unifFwdImpl,
      QueryImpl.add_apply_inl, StateT.run_mk, QueryImpl.liftTarget_apply_run,
      QueryImpl.ofLift_apply, simulateQ_map]
    exact congrArg _ (simulateQ_prfRealQueryImpl_liftComp _ _ (liftM (unifSpec.query k)))
  · simp only [QueryImpl.mapStateTBase, indexedRunImpl, keyedRomImpl, QueryImpl.add_apply_inl,
      QueryImpl.add_apply_inr, StateT.run_mk, QueryImpl.liftTarget_apply,
      OracleComp.liftM_StateT_eq]
    exact simulateQ_prfRealQueryImpl_liftComp _ _ _
  · simp [QueryImpl.mapStateTBase, indexedRunImpl, keyedRomImpl, functionQuery]
    rfl

omit [SampleableType N] in
/-- Simulating a computation lifted from the oracles of the hiding game, `keyedRomImpl T` is the
random oracle model. -/
lemma simulateQ_keyedRomImpl_liftComp (T : Fin (2 * qEnc) → K) {α : Type}
    (oa : OracleComp (unifSpec + sealSpec n S L Salt Ctx N K) α) :
    simulateQ (keyedRomImpl prf qEnc T) (liftComp oa (indexedSpec n S L Salt Ctx N K qEnc)) =
      simulateQ (sealSpec n S L Salt Ctx N K).romImpl oa := by
  rw [liftComp_def]
  refine QueryImpl.simulateQ_simulateQ_eq_of_apply (fun t => ?_) oa
  rcases t with k | x
  · exact simulateQ_spec_query (keyedRomImpl (n := n) (S := S) (L := L) (Salt := Salt)
      (Ctx := Ctx) prf qEnc T) (Sum.inl k)
  · rw [OracleComp.liftM_eq_liftM_liftM, simulateQ_query]
    rcases x with p | p | p <;> exact id_map _

/-- The online phase of `G₂` with the key table `T`, at hidden bit `b` for the puzzle `puzzle`, as
one handler on the pair of the cache of the random oracle and the counter: a step of the online
handler of `indexedExperiment`, with rounds answered point by point, followed by `keyedRomImpl T`
on the cache. -/
@[expose]
noncomputable def keyedJointImpl (T : Fin (2 * qEnc) → K) (puzzle : Puzzle n S L Salt) (b : Bool) :
    QueryImpl ((unifSpec + LeftOrRight.spec Plaintext ByteArray) +
        (sealSpec n S L Salt Ctx N K).batch)
      (StateT ((sealSpec n S L Salt Ctx N K).QueryCache × ℕ) ProbComp) :=
  fun t => StateT.mk fun s => (fun z => (z.1.1, (z.2, z.1.2))) <$>
    (simulateQ (keyedRomImpl prf qEnc T)
      (((indexedOnlineImpl (Ctx := Ctx) codec encodePuzzle qEnc puzzle b).batch' t).run
        s.2)).run s.1

lemma keyedJointImpl_run_unif (T : Fin (2 * qEnc) → K) (puzzle : Puzzle n S L Salt) (b : Bool)
    (k : ℕ) (s : (sealSpec n S L Salt Ctx N K).QueryCache × ℕ) :
    (keyedJointImpl prf codec encodePuzzle qEnc T puzzle b (.inl (.inl k))).run s =
      (fun z => (z.1, (z.2, s.2))) <$> (unifFwdImpl (sealSpec n S L Salt Ctx N K) k).run s.1 := by
  simp [keyedJointImpl, indexedOnlineImpl, keyedRomImpl]

lemma keyedJointImpl_run_batch (T : Fin (2 * qEnc) → K) (puzzle : Puzzle n S L Salt) (b : Bool)
    (ts : List (sealSpec n S L Salt Ctx N K).Domain)
    (s : (sealSpec n S L Salt Ctx N K).QueryCache × ℕ) :
    (keyedJointImpl prf codec encodePuzzle qEnc T puzzle b (.inr ts)).run s =
      (fun z => (z.1, (z.2, s.2))) <$>
        ((sealSpec n S L Salt Ctx N K).randomOracle.batch ts).run s.1 := by
  simp only [keyedJointImpl, StateT.run_mk, QueryImpl.batch'_apply_inr, indexedOnlineImpl,
    QueryImpl.add_apply_inr]
  erw [QueryImpl.run_batch_liftTarget (m := OracleComp (indexedSpec n S L Salt Ctx N K qEnc))
    (fun t => liftM ((indexedSpec n S L Salt Ctx N K qEnc).query (.inr (.inl t))))]
  rw [simulateQ_map, StateT.run_map, Functor.map_map, ← QueryImpl.apply_compose,
    QueryImpl.compose_batch]
  have h : (keyedRomImpl (n := n) (S := S) (L := L) (Salt := Salt) (Ctx := Ctx) prf qEnc T ∘ₛ
      fun t => liftM ((indexedSpec n S L Salt Ctx N K qEnc).query (.inr (.inl t)))) =
      (sealSpec n S L Salt Ctx N K).randomOracle := by
    funext t
    rw [QueryImpl.apply_compose, simulateQ_spec_query]
    rfl
  rw [h]
  rfl

lemma keyedJointImpl_run_challenge (T : Fin (2 * qEnc) → K) (puzzle : Puzzle n S L Salt)
    (b : Bool) (m₀ m₁ : Plaintext) (s : (sealSpec n S L Salt Ctx N K).QueryCache × ℕ) :
    (keyedJointImpl prf codec encodePuzzle qEnc T puzzle b (.inl (.inr (m₀, m₁)))).run s =
      if plaintextLength m₀ = plaintextLength m₁ then
        if h : s.2 < qEnc then (do
          let nonce ← $ᵗ N
          pure (some (sealWith prf codec (encodePuzzle puzzle) nonce
            (T (instanceIndex 0 ⟨s.2, h⟩), T (instanceIndex 1 ⟨s.2, h⟩)) (if b then m₁ else m₀)),
            (s.1, s.2 + 1)))
        else pure (some ByteArray.empty, (s.1, s.2 + 1))
      else pure (none, s) := by
  by_cases hl : plaintextLength m₀ = plaintextLength m₁
  · simp only [keyedJointImpl, StateT.run_mk, QueryImpl.batch'_apply_inl, indexedOnlineImpl,
      QueryImpl.add_apply_inl, QueryImpl.add_apply_inr, LeftOrRight.oracle, hl, ↓reduceIte]
    by_cases hj : s.2 < qEnc
    · simp [indexedEncrypt, hj, simulateQ_sealBy, keyedRomImpl, sealBy_pure_eval,
        QueryImpl.simulateQ_add_liftM_left, unifFwdImpl.simulateQ_run]
    · simp [indexedEncrypt, hj]
  · simp only [keyedJointImpl, StateT.run_mk, QueryImpl.batch'_apply_inl, indexedOnlineImpl,
      QueryImpl.add_apply_inl, QueryImpl.add_apply_inr, LeftOrRight.oracle, hl, ↓reduceIte]
    simp

/-- `keyedJointImpl` with its key table as a third component of the state, which no step
changes. -/
@[expose]
noncomputable def keyedTabImpl (puzzle : Puzzle n S L Salt) (b : Bool) :
    QueryImpl ((unifSpec + LeftOrRight.spec Plaintext ByteArray) +
        (sealSpec n S L Salt Ctx N K).batch)
      (StateT (((sealSpec n S L Salt Ctx N K).QueryCache × ℕ) × (Fin (2 * qEnc) → K)) ProbComp) :=
  fun t => StateT.mk fun s => (fun z => (z.1, (z.2, s.2))) <$>
    (keyedJointImpl prf codec encodePuzzle qEnc s.2 puzzle b t).run s.1

/-- A run of `keyedTabImpl` from the key table `T` is a run of `keyedJointImpl T`. -/
lemma simulateQ_keyedTabImpl_run {α : Type} (puzzle : Puzzle n S L Salt) (b : Bool)
    (oa : OracleComp ((unifSpec + LeftOrRight.spec Plaintext ByteArray) +
      (sealSpec n S L Salt Ctx N K).batch) α)
    (s : (sealSpec n S L Salt Ctx N K).QueryCache × ℕ) (T : Fin (2 * qEnc) → K) :
    (simulateQ (keyedTabImpl prf codec encodePuzzle qEnc puzzle b) oa).run (s, T) =
      (fun p => (p.1, (p.2, T))) <$>
        (simulateQ (keyedJointImpl prf codec encodePuzzle qEnc T puzzle b) oa).run s := by
  rw [OracleComp.simulateQ_run_eq_of_snd_invariant _ T (fun t s x hx => by
    simp only [keyedTabImpl, StateT.run_mk, support_map] at hx
    obtain ⟨z, -, rfl⟩ := hx
    rfl)]
  congr 3
  funext t
  refine StateT.ext fun s => ?_
  simp [QueryImpl.fixSndStateT, keyedTabImpl, Functor.map_map]

/-- The key table of `G₂` read off a state of the online phase of `G₁½` with the log: a uniform key
table of `prf.multiKey` overwritten, at the instances of each logged encryption, by its subkeys
(`keyTable`). -/
@[expose]
noncomputable def keyFill (s : (sealSpec n S L Salt Ctx N K).QueryCache × (ℕ × CounterLog N K)) :
    ProbComp (((sealSpec n S L Salt Ctx N K).QueryCache × ℕ) × (Fin (2 * qEnc) → K)) :=
  (fun T => ((s.1, s.2.1), keyTable qEnc T s.2.2)) <$> (prf.multiKey (Fin (2 * qEnc))).keygen

/-- **The key table intertwines `G₁½` with `G₂`.** Under `prf.UniformKey`, on the states whose
log holds one entry per accepted encryption within the budget, a step of the online handler of
`G₁½` followed by `keyFill` has the law of `keyFill` followed by a step of `keyedTabImpl`. Local
coins and rounds do not touch the counter, the log or the key table. An accepted encryption within
the budget draws a fresh pair of subkeys in `G₁½` and writes it at the cells of its counter, which
`keyTable` has not yet overwritten, so these cells are uniform and independent of the rest. -/
theorem intertwinesOn_keyFill (hprf : prf.UniformKey) (puzzle : Puzzle n S L Salt) (b : Bool) :
    QueryImpl.IntertwinesOn (fun s => CounterInv qEnc s.2)
      (keyFill (n := n) (S := S) (L := L) (Salt := Salt) (Ctx := Ctx) prf qEnc)
      (counterJointImpl prf codec encodePuzzle qEnc puzzle b)
      (keyedTabImpl prf codec encodePuzzle qEnc puzzle b) := by
  intro t s hs γ _ f
  rcases t with (k | ⟨m₀, m₁⟩) | ts
  · simp only [counterJointImpl_run_unif, keyedTabImpl, StateT.run_mk, keyedJointImpl_run_unif,
      keyFill, bind_map_left, Functor.map_map]
    exact (EvalDistEq.bind_bind_swap _ _ _).evalDist_eq
  · obtain ⟨c, j, l⟩ := s
    simp only [counterJointImpl_run_challenge, keyedTabImpl, StateT.run_mk,
      keyedJointImpl_run_challenge, keyFill, bind_map_left]
    by_cases hl : plaintextLength m₀ = plaintextLength m₁
    · by_cases hj : j < qEnc
      · obtain rfl : l.length = j := by
          simp only [CounterInv] at hs
          omega
        simp only [hl, hj, ↓reduceIte, dite_true, bind_assoc, pure_bind,
          keyTable_cons _ _ _ _ hj, keyTable_apply_of_le qEnc _ l _ ⟨l.length, hj⟩ le_rfl]
        have hne := instanceIndex_zero_ne_one qEnc ⟨l.length, hj⟩
        refine Eq.trans ?_ (EvalDistEq.bind_bind_swap _ _ _).evalDist_eq.symm
        refine evalDist_bind_congr_of_support _ _ _ fun η _ => ?_
        have h := evalDist_uniformSample_bind_multiKey_keygen_update prf (Fin (2 * qEnc)) hprf hne
          (fun g => f (some (sealWith prf codec (encodePuzzle puzzle) η
            (g (instanceIndex 0 ⟨l.length, hj⟩), g (instanceIndex 1 ⟨l.length, hj⟩))
            (if b = true then m₁ else m₀))) ((c, l.length + 1), keyTable qEnc g l))
        simp only [Function.update_self, Function.update_of_ne hne,
          keyTable_update qEnc _ l ⟨l.length, hj⟩ le_rfl] at h
        exact h
      · simp [hl, hj]
    · simp [hl]
  · simp only [counterJointImpl_run_batch, keyedTabImpl, StateT.run_mk, keyedJointImpl_run_batch,
      keyFill, bind_map_left, Functor.map_map]
    exact (EvalDistEq.bind_bind_swap _ _ _).evalDist_eq

/-- **One online phase, from `G₁½` to `G₂`.** Under `prf.UniformKey`, from any cache `c`, the
output of the online handler of `G₁½` from the counter `0` and the empty log has the law of the
output of the online handler of `G₂` from the counter `0`, under a uniform key table of
`prf.multiKey`. -/
theorem counterJointImpl_evalDistEq_keyedJointImpl (hprf : prf.UniformKey)
    (puzzle : Puzzle n S L Salt) (b : Bool) {α : Type}
    (oa : OracleComp ((unifSpec + LeftOrRight.spec Plaintext ByteArray) +
      (sealSpec n S L Salt Ctx N K).batch) α) (c : (sealSpec n S L Salt Ctx N K).QueryCache) :
    Prod.fst <$> (simulateQ (counterJointImpl prf codec encodePuzzle qEnc puzzle b) oa).run
        (c, (0, [])) =ᵈ
      (prf.multiKey (Fin (2 * qEnc))).keygen >>= fun T =>
        Prod.fst <$> (simulateQ (keyedJointImpl prf codec encodePuzzle qEnc T puzzle b) oa).run
          (c, 0) := by
  let : MeasurableSpace α := ⊤
  have h := EvalDistEq.of_evalDist_eq
    ((intertwinesOn_keyFill prf codec encodePuzzle qEnc hprf puzzle b).evalDist_simulateQ_run
      (preservesInv_counterJointImpl_counterInv prf codec encodePuzzle qEnc puzzle b) oa
      (c, (0, [])) (by simp [CounterInv]) fun a _ => pure a)
  refine EvalDistEq.trans ?_ (h.trans ?_)
  · rw [map_eq_bind_pure_comp]
    exact EvalDistEq.bind_right _ fun z => (EvalDistEq.bind_const _ _).symm
  · simp [keyFill, simulateQ_keyedTabImpl_run, map_eq_bind_pure_comp]

/-- The random-oracle run, with the key table `T`, of the online phase of `indexedExperiment`,
which runs its online handler on the counter inside the run on the cache, is equal in distribution
to the run of `keyedJointImpl T` on the cache with the counter `0`. -/
lemma run_keyedRomImpl_evalDistEq_keyedJointImpl {α : Type} (T : Fin (2 * qEnc) → K)
    (puzzle : Puzzle n S L Salt) (b : Bool)
    (oa : OracleComp ((unifSpec + LeftOrRight.spec Plaintext ByteArray) +
      (sealSpec n S L Salt Ctx N K).batch) α) (c : (sealSpec n S L Salt Ctx N K).QueryCache) :
    (simulateQ (keyedRomImpl prf qEnc T)
      ((simulateQ (indexedOnlineImpl (Ctx := Ctx) codec encodePuzzle qEnc puzzle b)
        (simulateQ (sealSpec n S L Salt Ctx N K).unbatch oa)).run' 0)).run c =ᵈ
      (fun z => (z.1, z.2.1)) <$>
        (simulateQ (keyedJointImpl prf codec encodePuzzle qEnc T puzzle b) oa).run (c, 0) := by
  rw [QueryImpl.simulateQ_simulateQ_unbatch]
  have h := simulateQ_run_simulateQ_run_evalDistEq (keyedRomImpl prf qEnc T)
    (indexedOnlineImpl (Ctx := Ctx) codec encodePuzzle qEnc puzzle b).batch'
    (keyedJointImpl prf codec encodePuzzle qEnc T puzzle b) (fun t s q => by
      rw [keyedJointImpl, StateT.run_mk, Functor.map_map]
      simp) oa 0 c
  rw [StateT.run'_eq, simulateQ_map, StateT.run_map]
  refine (h.map fun z => (z.1.1, z.2)).trans ?_
  rw [Functor.map_map]

/-- **From `G₁½` to `G₂`.** Under `prf.UniformKey`, for any hiding adversary `adv` and either hidden
bit, the guess in the random oracle model of `counterExperiment` has the law of the real world of
`prf.multiKey` over `2 qEnc` instances against `indexedRun`.

The two share preprocessing and key generation, where the oracles of `G₂` are the random oracle
model through `keyedRomImpl`. Their online phases are, up to distribution, `counterJointImpl` and
`keyedJointImpl` under a uniform key table, related by `intertwinesOn_keyFill`. -/
theorem counterExperiment_eq_prfReal [NeZero n] [AddCommGroup L] [SampleableType Salt]
    (hprf : prf.UniformKey) (mkCtx : Salt → Ctx) (initAcc : Ctx → S)
    (adv : HidingAdversary (sealSpec n S L Salt Ctx N K) (Puzzle n S L Salt) Plaintext ByteArray)
    (b : Bool) :
    Prod.fst <$> (simulateQ (sealSpec n S L Salt Ctx N K).romImpl
        (counterExperiment m prf codec encodePuzzle qEnc mkCtx initAcc adv b)).run' ∅ =ᵈ
      (prf.multiKey (Fin (2 * qEnc))).prfRealExperiment
        (indexedRun m codec encodePuzzle qEnc mkCtx initAcc adv b) := by
  have hrun : ∀ T, simulateQ ((prf.multiKey (Fin (2 * qEnc))).prfRealQueryImpl T)
      (indexedRun m codec encodePuzzle qEnc mkCtx initAcc adv b) =
      (simulateQ (keyedRomImpl (n := n) (S := S) (L := L) (Salt := Salt) (Ctx := Ctx) prf qEnc T)
        (indexedExperiment m codec encodePuzzle qEnc mkCtx initAcc adv b)).run' ∅ := fun T => by
    rw [indexedRun]
    change simulateQ _ ((simulateQ (indexedRunImpl (n := n) (S := S) (L := L) (Salt := Salt)
      (Ctx := Ctx) (N := N) (K := K) qEnc) _).run' ∅) = _
    rw [QueryImpl.simulateQ_mapStateTBase_run', mapStateTBase_indexedRunImpl]
  simp only [prfRealExperiment, hrun]
  simp only [counterExperiment, guessExperiment, indexedExperiment, counterAdversary,
    simulateQ_bind, StateT.run'_eq, StateT.run_bind, bind_pure_comp,
    simulateQ_keyedRomImpl_liftComp, map_bind]
  refine EvalDistEq.trans ?_ (EvalDistEq.bind_bind_swap _ _ _).symm
  refine EvalDistEq.bind_right _ fun p => ?_
  refine EvalDistEq.trans ?_ (EvalDistEq.bind_bind_swap _ _ _).symm
  refine EvalDistEq.bind_right _ fun p₁ => ?_
  have h₁ := run_romImpl_counterImpl_evalDistEq_counterJointImpl prf codec encodePuzzle qEnc
    p₁.1.1 b (adv.online p.1 p₁.1.1) p₁.2
  have h₂ := counterJointImpl_evalDistEq_keyedJointImpl prf codec encodePuzzle qEnc hprf p₁.1.1 b
    (adv.online p.1 p₁.1.1) p₁.2
  have h₃ := fun T => run_keyedRomImpl_evalDistEq_keyedJointImpl prf codec encodePuzzle qEnc T
    p₁.1.1 b (adv.online p.1 p₁.1.1) p₁.2
  simp only [StateT.run'_eq] at h₁ h₃
  rw [simulateQ_map, StateT.run_map]
  simp only [Functor.map_map]
  refine ((h₁.map _).trans ?_).trans (EvalDistEq.bind_right _ fun T => (h₃ T).map _).symm
  simp only [Functor.map_map]
  exact h₂

/-- **From `G₁` to `G₂`.** Under `prf.UniformKey`, for a hiding adversary `adv` making at most
`qEnc` challenge queries, at either hidden bit, the probabilities that `privateExperiment` returns
the guess `true` and that the real world of `prf.multiKey` over `2 qEnc` instances against
`indexedRun` returns `true` differ by at most `qEnc² / (2 |N|)`: the nonce hop
(`absDiff_privateExperiment_counterExperiment_le`) followed by the equality in law
`counterExperiment_eq_prfReal`. -/
theorem absDiff_privateExperiment_indexed_le [NeZero n] [AddCommGroup L] [SampleableType Salt]
    [Fintype N] (mkCtx : Salt → Ctx) (initAcc : Ctx → S)
    (adv : HidingAdversary (sealSpec n S L Salt Ctx N K) (Puzzle n S L Salt) Plaintext ByteArray)
    (hprf : prf.UniformKey) (hadv : adv.MakesAtMostQueries qEnc) (b : Bool) :
    ENNReal.absDiff
      (Pr{let z ← (simulateQ (sealSpec n S L Salt Ctx N K).romImpl
        (privateExperiment m prf codec encodePuzzle mkCtx initAcc adv b)).run' ∅}[z.1 = true])
      (Pr{let g ← ((prf.multiKey (Fin (2 * qEnc))).prfRealExperiment
        (indexedRun m codec encodePuzzle qEnc mkCtx initAcc adv b))}[g = true]) ≤
      (qEnc : ℝ≥0∞) ^ 2 / (2 * Fintype.card N) := by
  rw [← (counterExperiment_eq_prfReal prf codec encodePuzzle qEnc hprf mkCtx initAcc adv
    b).prEvent_eq, prEvent_map]
  refine (absDiff_privateExperiment_counterExperiment_le prf codec encodePuzzle qEnc mkCtx initAcc
    adv hadv b).trans (ENNReal.div_le_div_right ?_ _)
  rw [sq]
  exact_mod_cast Nat.mul_le_mul_left qEnc (Nat.sub_le qEnc 1)

end PRFHop

end PointerChainPuzzle
