/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.Schemes.PointerChainPuzzle.Delay
public import VCVio.Schemes.PointerChainPuzzle.Envelope
public import VCVio.CryptoFoundations.TimeLockPuzzle.LogSide
public import VCVio.CryptoFoundations.TimeLockPuzzle.Hiding

/-!
# Time-lock encryption with the pointer-chain puzzle: the private-subkey hybrid

leanSeal encrypts under a pointer-chain puzzle and its key with the envelope of
`VCVio.Schemes.PointerChainPuzzle.Envelope`, whose subkeys for a nonce `η` are two labelled hashes
of the key and the nonce (SPEC §7): `k_enc = H_enc(K ‖ η)` and `k_mac = H_mac(K ‖ η)`. In the
typed model these are two random oracles on `S × N`, with values in the PRF key type `K`, joined
to the six typed oracles of the puzzle as a summand (`sealSpec`). The puzzle runs unchanged over
the larger specification (`sealScheme`, the lift `TimeLockPuzzle.liftSpec`), and the envelope
derives its subkeys with one query to each subkey oracle (`sealDerive`, `sealDEM`). The hiding game
leaks the message length (`plaintextLength`).

## The private-subkey hybrid

The first hop of the hiding proof replaces the subkeys of the challenger's encryptions by those of
a private random function of the nonce (`privateSpec`). In the hybrid (`privateExperiment`) the
challenger draws a uniform nonce, takes both subkeys from the private function at the nonce
(`privateEncrypt`), and never queries the subkey oracles the adversary sees, nor uses the puzzle
key. The challenger's encryptions are inlined into the adversary (`privateImpl`,
`privateAdversary`): the result is a two-phase adversary against `sealScheme` whose output is the
guess of the hidden bit, within the budgets of the hiding adversary, since challenge queries are on
the free summand and the challenger's derivations are not the adversary's
(`isQueryBound_privateAdversary`).

The hybrid differs from the hiding experiment only once the oracle cache holds a subkey point at
the key (`BadK`). Because the challenger's derivations go to its private function, every such
point was queried by the adversary. The adversary's subkey points are its log (`logSide`), which
the puzzle never reads, and the key components of the logged points are at most `Q_pre + Q_on`
guesses of the key; the delay theorem with that many guesses bounds `BadK`
(`prEvent_privateExperiment_badK_le`).

## From the hiding experiment to the hybrid

The hiding experiment and the hybrid share preprocessing and key generation and differ in their
online phases, each run as one handler: on the cache of the random oracle for the experiment
(`hidingOnlineImpl`), and on the pair of that cache and the private cache for the hybrid
(`privateOnlineImpl`, fused from the nested runs by
`OracleComp.simulateQ_run_simulateQ_run_evalDistEq`). Laying the private cache over the subkey
points at the key (`overlayCache`) maps the hybrid's state to the experiment's. Off `BadK`, a step
of the hybrid read through this map is a step of the experiment
(`dominatedUntilBad_privateOnlineImpl`), and `BadK` is sticky
(`preservesInv_privateOnlineImpl_badK`); domination until bad bounds the gap between the two
experiments by `BadK` in the hybrid, from every shared cache, including one that already holds a
subkey point at the key (`absDiff_hidingExperiment_privateExperiment_le`).

## Main definitions

* `PointerChainPuzzle.subkeySpec`, `PointerChainPuzzle.sealSpec`: the two subkey oracles, and the
  oracles of time-lock encryption.
* `PointerChainPuzzle.sealDerive`: the subkeys of a key and a nonce.
* `PointerChainPuzzle.sealScheme`: the pointer-chain puzzle over the oracles with subkeys.
* `PointerChainPuzzle.sealDEM`: the envelope over the oracles with subkeys, keyed by a puzzle and
  its key.
* `PointerChainPuzzle.plaintextLength`: the leakage of the hiding game.
* `PointerChainPuzzle.privateSpec`, `PointerChainPuzzle.privateEncrypt`,
  `PointerChainPuzzle.privateImpl`, `PointerChainPuzzle.privateAdversary`,
  `PointerChainPuzzle.privateExperiment`: the private challenger and the hybrid.
* `PointerChainPuzzle.BadK`: a subkey point at the key is cached.
* `PointerChainPuzzle.overlayCache`, `PointerChainPuzzle.hidingOnlineImpl`,
  `PointerChainPuzzle.privateOnlineImpl`: the state map and the online handlers of the first hop.

## Main statements

* `PointerChainPuzzle.delayAdvantage_sealScheme_le`: `sealScheme` has the delay bound of
  `scheme`.
* `PointerChainPuzzle.isQueryBound_privateAdversary`: inlining the private challenger keeps the
  preprocessing and online budgets.
* `PointerChainPuzzle.prEvent_privateExperiment_badK_le`: in the hybrid, `BadK` has probability at
  most `[n ≥ 2] Q_on / |L| + Q_pre / (|Salt| |L|) + (Q P + P² + Q) / |S|`, with
  `P = solvePoints n m` and `Q = Q_pre + Q_on`.
* `PointerChainPuzzle.absDiff_hidingExperiment_privateExperiment_le`: the probabilities that the
  hiding experiment returns `true` and that the hybrid returns the guess `true` differ by at most
  the probability of `BadK` in the hybrid.
-/

public section

open OracleSpec OracleComp TimeLockPuzzle
open scoped ENNReal

namespace PointerChainPuzzle

open LeanSeal Envelope

variable {n m : ℕ} {S L Salt Ctx N K : Type}

/-! ## The oracles with subkeys -/

variable (S N K) in
/-- The two subkey oracles of the envelope (SPEC §7): on a key of the puzzle and a nonce, the
encryption subkey `H_enc(K ‖ η)` (left) and the MAC subkey `H_mac(K ‖ η)` (right), each a key of
the PRF. -/
abbrev subkeySpec : OracleSpec (S × N ⊕ S × N) := (S × N →ₒ K) + (S × N →ₒ K)

variable (n S L Salt Ctx N K) in
/-- The oracles of time-lock encryption with the pointer-chain puzzle and the envelope: the six
typed oracles of the puzzle and the two subkey oracles, as a summand. -/
abbrev sealSpec := oracleSpec n S L Salt Ctx + subkeySpec S N K

/-- The subkeys under the key `key` and the nonce `nonce`: one query to each subkey oracle, at
`(key, nonce)`. -/
@[expose]
def sealDerive (key : S) (nonce : N) : OracleComp (sealSpec n S L Salt Ctx N K) (K × K) := do
  let kEnc ← (sealSpec n S L Salt Ctx N K).query (.inr (.inl (key, nonce)))
  let kMac ← (sealSpec n S L Salt Ctx N K).query (.inr (.inr (key, nonce)))
  return (kEnc, kMac)

variable (n m) in
/-- The pointer-chain puzzle over the oracles with subkeys: `scheme` lifted along
`oracleSpec ⊂ₒ sealSpec`. Its generator and solver never query the subkey oracles. -/
@[expose]
def sealScheme [NeZero n] (mkCtx : Salt → Ctx) (initAcc : Ctx → S) (N K : Type) [AddCommGroup L]
    [DecidableEq S] [SampleableType Salt] [SampleableType L] :
    TimeLockPuzzle (sealSpec n S L Salt Ctx N K) (Puzzle n S L Salt) S :=
  (scheme n m mkCtx initAcc).liftSpec (sealSpec n S L Salt Ctx N K)

variable (prf : PRFScheme K ByteArray (Bytes 32)) {w : ℕ} (codec : FixedCodec N w)
  (encodePuzzle : Puzzle n S L Salt → ByteArray)

/-- The envelope over the oracles with subkeys, keyed by a puzzle together with its key: a uniform
nonce, the subkeys of the key and the nonce (`sealDerive`), and the envelope under them. -/
@[expose]
def sealDEM [SampleableType N] :
    DEMScheme (OracleComp (unifSpec + sealSpec n S L Salt Ctx N K)) (Puzzle n S L Salt × S)
      Plaintext ByteArray :=
  dem prf codec (sealDerive (n := n) (L := L) (Salt := Salt) (Ctx := Ctx)) encodePuzzle

/-- The leakage of the hiding game: the length of the message. -/
@[expose]
def plaintextLength (msg : Plaintext) : ℕ := msg.1.size

/-! ## The hybrid with private subkeys -/

/-- A private random function of the nonce, giving both subkeys. -/
abbrev privateSpec (N K : Type) : OracleSpec N := N →ₒ (K × K)

/-- `BadK`: the cache `c` holds a subkey point, of either subkey oracle, whose key component is
`key`. -/
@[expose]
def BadK (key : S) (c : (sealSpec n S L Salt Ctx N K).QueryCache) : Prop :=
  ∃ x : S × N ⊕ S × N, (c (.inr x)).isSome ∧ Sum.elim Prod.fst Prod.fst x = key

/-- A program of local coins, lifted to the free summand, submits no round. -/
private lemma isOnlineQueryBound_liftM_probComp {ι : Type} {spec : OracleSpec.{0, 0} ι}
    {α : Type} (oa : ProbComp α) (b : ℕ × ℕ) :
    IsOnlineQueryBound (liftM oa : OracleComp (unifSpec + spec.batch) α) b := by
  rw [← liftComp_eq_liftM]
  exact isOnlineQueryBound_liftComp oa b

section Private

variable [SampleableType N] [DecidableEq N] [SampleableType K]

/-- The private challenger's encryption of `msg` under the puzzle bytes `pz`: a uniform nonce
from local coins, both subkeys from the private random function at the nonce, on the private
cache, and the envelope under them. It never queries the oracles with subkeys. -/
@[expose]
def privateEncrypt (pz : ByteArray) (msg : Plaintext) :
    StateT (privateSpec N K).QueryCache
      (OracleComp (unifSpec + (sealSpec n S L Salt Ctx N K).batch)) ByteArray := do
  let nonce ← (liftM (liftM ($ᵗ N : ProbComp N) :
    OracleComp (unifSpec + (sealSpec n S L Salt Ctx N K).batch) N) :
      StateT (privateSpec N K).QueryCache
        (OracleComp (unifSpec + (sealSpec n S L Salt Ctx N K).batch)) N)
  let ks ← (liftM ((privateSpec N K).randomOracle nonce) :
    StateT (privateSpec N K).QueryCache
      (OracleComp (unifSpec + (sealSpec n S L Salt Ctx N K).batch)) (K × K))
  return sealWith prf codec pz nonce ks msg

/-- The handler of the private challenger at hidden bit `b` for the puzzle `puzzle`: local coins
are forwarded, a challenge query is answered by the left-or-right oracle over `privateEncrypt`
under the puzzle's bytes, and rounds are forwarded. -/
@[expose]
def privateImpl (puzzle : Puzzle n S L Salt) (b : Bool) :
    QueryImpl ((unifSpec + LeftOrRight.spec Plaintext ByteArray) +
        (sealSpec n S L Salt Ctx N K).batch)
      (StateT (privateSpec N K).QueryCache
        (OracleComp (unifSpec + (sealSpec n S L Salt Ctx N K).batch))) :=
  (((QueryImpl.ofLift unifSpec
        (OracleComp (unifSpec + (sealSpec n S L Salt Ctx N K).batch))).liftTarget
      (StateT (privateSpec N K).QueryCache
        (OracleComp (unifSpec + (sealSpec n S L Salt Ctx N K).batch)))) +
    LeftOrRight.oracle (privateEncrypt (n := n) (S := S) (L := L) (Salt := Salt) (Ctx := Ctx)
      prf codec (encodePuzzle puzzle)) plaintextLength b) +
    (fun ts => liftM ((unifSpec + (sealSpec n S L Salt Ctx N K).batch).query (.inr ts)) :
      QueryImpl (sealSpec n S L Salt Ctx N K).batch (StateT (privateSpec N K).QueryCache
        (OracleComp (unifSpec + (sealSpec n S L Salt Ctx N K).batch))))

/-- The hiding adversary `adv` with the private challenger at hidden bit `b` inlined: a two-phase
adversary against the oracles with subkeys, with local coins as its free oracles, whose output is
the guess of the hidden bit. The private cache starts empty when the online phase starts. -/
@[expose]
def privateAdversary
    (adv : HidingAdversary (sealSpec n S L Salt Ctx N K) (Puzzle n S L Salt) Plaintext ByteArray)
    (b : Bool) : TwoPhaseAdversary unifSpec (sealSpec n S L Salt Ctx N K) (Puzzle n S L Salt) Bool
    where
  State := adv.State
  preprocess := adv.preprocess
  online σ puzzle := StateT.run'
    (simulateQ (privateImpl prf codec encodePuzzle puzzle b) (adv.online σ puzzle)) ∅

/-- The private challenger's encryption submits no round, from every private cache. -/
lemma isOnlineQueryBound_privateEncrypt_run (pz : ByteArray) (msg : Plaintext)
    (s : (privateSpec N K).QueryCache) (b : ℕ × ℕ) :
    IsOnlineQueryBound ((privateEncrypt (n := n) (S := S) (L := L) (Salt := Salt) (Ctx := Ctx)
      prf codec pz msg).run s) b := by
  simp only [privateEncrypt, QueryImpl.withCaching_apply, uniformSampleImpl_apply,
    liftM_StateT_eq, StateT.run_bind, StateT.run_get, pure_bind, bind_pure_comp,
    StateT.run_monadLift, monadLift_self, StateT.run_map, StateT.run_mk, bind_map_left]
  exact isOnlineQueryBound_bind_le (0, 0) (0, 0) (isOnlineQueryBound_liftM_probComp _ _)
    (fun _ => (isQueryBound_map_iff _ _ _ _ _).2 (isOnlineQueryBound_liftM_probComp _ _))
    (by simp)

/-- **Inlining the private challenger keeps the budgets.** If the hiding adversary `adv` makes at
most `Q` preprocessing queries and its online phase submits at most `b'.1` rounds holding at most
`b'.2` points, then so does `privateAdversary adv b`, at either hidden bit: challenge queries are
answered with local coins and the private cache, and cost no round. -/
theorem isQueryBound_privateAdversary
    {adv : HidingAdversary (sealSpec n S L Salt Ctx N K) (Puzzle n S L Salt) Plaintext ByteArray}
    {Q : ℕ} {b' : ℕ × ℕ} (h : adv.IsQueryBound Q b') (b : Bool) :
    (privateAdversary prf codec encodePuzzle adv b).IsQueryBound Q b' := by
  refine ⟨h.1, fun σ puzzle => ?_⟩
  have key := IsQueryBound.simulateQ_run_of_step (h.2 σ puzzle) (combine := (· + ·))
    (mapBudget := id) (stepBudget := fun t _ => onlineStep t)
    (impl := privateImpl prf codec encodePuzzle puzzle b)
    (fun h₁ h₂ => isOnlineQueryBound_bind h₁ h₂) (fun t b s _ => ?_) (fun t b ht => ?_) ∅
  · simpa [privateAdversary, StateT.run'_eq, IsOnlineQueryBound, isQueryBound_map_iff] using key
  · rcases t with (k | ⟨m₀, m₁⟩) | ts
    · simp only [privateImpl, add_apply_inl, onlineStep_inl]
      exact isOnlineQueryBound_liftM_probComp (unifSpec.query k) _
    · simp only [privateImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr, LeftOrRight.oracle]
      by_cases hm : plaintextLength m₀ = plaintextLength m₁
      · simp only [hm, ↓reduceIte, StateT.run_map]
        exact (isQueryBound_map_iff _ _ _ _ _).2 (isOnlineQueryBound_privateEncrypt_run _ _ _ _ _ _)
      · simp only [hm, ↓reduceIte, StateT.run_pure]
        exact isOnlineQueryBound_pure _ _
    · simp [privateImpl]
  · rcases t with k | ts
    · simp
    · simp only [onlineCanQuery_inr] at ht
      refine Prod.ext ?_ ?_ <;> simp <;> omega

variable (m) in
/-- **The hybrid `G₁`.** The delay experiment for any output (`TimeLockPuzzle.guessExperiment`) of
`sealScheme` against `privateAdversary adv b`: the hiding experiment at hidden bit `b` with the
private challenger, returning the guess together with the puzzle key. -/
@[expose]
def privateExperiment [NeZero n] [AddCommGroup L] [DecidableEq S] [SampleableType Salt]
    [SampleableType L] (mkCtx : Salt → Ctx) (initAcc : Ctx → S)
    (adv : HidingAdversary (sealSpec n S L Salt Ctx N K) (Puzzle n S L Salt) Plaintext ByteArray)
    (b : Bool) : OracleComp (unifSpec + sealSpec n S L Salt Ctx N K) (Bool × S) :=
  (sealScheme n m mkCtx initAcc N K).guessExperiment (privateAdversary prf codec encodePuzzle adv b)

end Private

/-! ## Delay and `BadK` -/

section Bounds

variable [DecidableEq S] [DecidableEq L] [DecidableEq Salt] [DecidableEq Ctx]
  [SampleableType S] [SampleableType L] [SampleableType Salt] [NeZero n] [AddCommGroup L]
  [DecidableEq N] [SampleableType K]

/-- **The delay theorem for `sealScheme`.** For injective `mkCtx` and an adversary against the
oracles with subkeys with at most `Q_pre` preprocessing queries and an online phase within
`keyRound n m - 1` rounds holding at most `Q_on` points, the delay bound of `scheme`
(`delayAdvantage_scheme_le`) holds: the subkey oracles are an independent summand, which the
adversary simulates itself within the same budgets (`TimeLockPuzzle.delayAdvantage_liftSpec_add`,
`TimeLockPuzzle.TwoPhaseAdversary.isQueryBound_simulateSide`). -/
theorem delayAdvantage_sealScheme_le [Finite Ctx] [Fintype S] [Fintype L] [Fintype Salt]
    (mkCtx : Salt → Ctx) (initAcc : Ctx → S) (hctx : Function.Injective mkCtx) {Qpre Qon : ℕ}
    {adv : TimeLockPuzzle.Adversary (sealSpec n S L Salt Ctx N K) (Puzzle n S L Salt) S}
    (hadv : adv.IsQueryBound Qpre (keyRound n m - 1, Qon)) :
    (sealScheme n m mkCtx initAcc N K).delayAdvantage adv ≤
      (if 2 ≤ n then (Qon : ℝ≥0∞) / Fintype.card L else 0) +
        Qpre / (Fintype.card Salt * Fintype.card L) +
          ((Qpre + Qon) * solvePoints n m + (solvePoints n m : ℝ≥0∞) ^ 2 + 1) /
            Fintype.card S :=
  (delayAdvantage_liftSpec_add (scheme n m mkCtx initAcc) adv).trans_le
    (delayAdvantage_scheme_le hctx (TwoPhaseAdversary.isQueryBound_simulateSide hadv))

/-- **The `BadK` bound.** For injective `mkCtx` and a hiding adversary with at most `Q_pre`
preprocessing queries and an online phase within `keyRound n m - 1` rounds holding at most `Q_on`
points, at either hidden bit, the final cache of the random-oracle run of the hybrid
`privateExperiment` holds a subkey point at the puzzle key with probability at most
`[n ≥ 2] Q_on / |L| + Q_pre / (|Salt| |L|) + (Q P + P² + Q) / |S|`, with `P = solvePoints n m` and
`Q = Q_pre + Q_on`.

The generator never queries the subkey oracles and the private challenger derives its subkeys
privately, so the cached subkey points are those the adversary queried, its log
(`TimeLockPuzzle.map_guessExperiment_logSide`, `TimeLockPuzzle.cache_inr_isSome_iff_mem_log`),
which holds at most `Q` points
(`TimeLockPuzzle.length_le_of_mem_support_guessExperiment_logSide`). Simulating the subkey oracles
(`TimeLockPuzzle.evalDist_guessExperiment_liftSpec_add`), the key components of the log are at
most `Q` guesses of the key against `scheme`, and the delay theorem for any event
(`prEvent_guessExperiment_scheme_le_of_forall`) bounds them, each guess costing `1 / |S|`. -/
theorem prEvent_privateExperiment_badK_le [Finite Ctx] [Fintype S] [Fintype L] [Fintype Salt]
    [SampleableType N] (mkCtx : Salt → Ctx) (initAcc : Ctx → S) (hctx : Function.Injective mkCtx)
    {adv : HidingAdversary (sealSpec n S L Salt Ctx N K) (Puzzle n S L Salt) Plaintext ByteArray}
    {Qpre Qon : ℕ} (hadv : adv.IsQueryBound Qpre (keyRound n m - 1, Qon)) (b : Bool) :
    Pr{let z ← (simulateQ (sealSpec n S L Salt Ctx N K).romImpl
        (privateExperiment m prf codec encodePuzzle mkCtx initAcc adv b)).run ∅}[BadK z.1.2 z.2] ≤
      (if 2 ≤ n then (Qon : ℝ≥0∞) / Fintype.card L else 0) +
        Qpre / (Fintype.card Salt * Fintype.card L) +
          ((Qpre + Qon) * solvePoints n m + (solvePoints n m : ℝ≥0∞) ^ 2 + (Qpre + Qon)) /
            Fintype.card S := by
  have hA := isQueryBound_privateAdversary prf codec encodePuzzle hadv b
  set A := privateAdversary prf codec encodePuzzle adv b
  set E : Bool × List (S × N ⊕ S × N) → S → Prop :=
    fun out key => ∃ x ∈ out.2.take (Qpre + Qon), Sum.elim Prod.fst Prod.fst x = key
  rw [privateExperiment, sealScheme, ← map_guessExperiment_logSide, simulateQ_map, StateT.run_map,
    prEvent_map]
  refine le_trans (prEvent_mono_of_support (m := ProbComp) _ _ (fun z => E z.1.1 z.1.2) ?_) ?_
  · -- A cached subkey point at the key is a logged one, and the log is within `Q` points.
    intro z hz hbad
    obtain ⟨x, hx, hkey⟩ := hbad
    have hmem := (cache_inr_isSome_iff_mem_log _ A hz x).1 hx
    have hz' : z.1 ∈ support (((scheme n m mkCtx initAcc).liftSpec
        (sealSpec n S L Salt Ctx N K)).guessExperiment A.logSide) :=
      support_simulateQ_run'_subset (sealSpec n S L Salt Ctx N K).romImpl _ ∅
        (by rw [StateT.run'_eq, support_map]; exact ⟨z, hz, rfl⟩)
    have hlen := length_le_of_mem_support_guessExperiment_logSide _ hA hz'
    exact ⟨x, by rwa [List.take_of_length_le hlen], hkey⟩
  · -- The event reads the output alone; simulate the subkey oracles and apply the delay theorem.
    have hrun : Pr{let z ← (simulateQ (sealSpec n S L Salt Ctx N K).romImpl
          (((scheme n m mkCtx initAcc).liftSpec (sealSpec n S L Salt Ctx N K)).guessExperiment
            A.logSide)).run ∅}[E z.1.1 z.1.2] =
        Pr{let z ← (simulateQ (sealSpec n S L Salt Ctx N K).romImpl
          (((scheme n m mkCtx initAcc).liftSpec (sealSpec n S L Salt Ctx N K)).guessExperiment
            A.logSide)).run' ∅}[E z.1 z.2] := by
      rw [StateT.run'_eq, prEvent_map]
    rw [hrun, (evalDist_guessExperiment_liftSpec_add _ A.logSide).prEvent_eq]
    refine (prEvent_guessExperiment_scheme_le_of_forall hctx
      (TwoPhaseAdversary.isQueryBound_simulateSide (TwoPhaseAdversary.isQueryBound_logSide hA))
      (E := E) (ε := ((Qpre + Qon : ℕ) : ℝ≥0∞) / Fintype.card S) fun out => ?_).trans
      (le_of_eq ?_)
    · set l := out.2.take (Qpre + Qon)
      have h := SampleableType.prEvent_uniformSample_exists_eq_le
        (fun i : Fin l.length => Sum.elim Prod.fst Prod.fst l[i])
      refine le_trans (le_of_eq_of_le (prEvent_congr _ _ _ fun u => ?_) h) ?_
      · change (∃ x ∈ l, _ = u) ↔ _
        constructor
        · rintro ⟨x, hx, rfl⟩
          obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
          exact ⟨⟨i, hi⟩, rfl⟩
        · rintro ⟨i, rfl⟩
          exact ⟨_, List.getElem_mem _, rfl⟩
      · gcongr
        exact List.length_take_le _ _
    · rw [add_assoc _ (_ / _), ENNReal.div_add_div_same]
      push_cast
      ring_nf

end Bounds

/-! ## From the hiding experiment to the hybrid -/

section StateMap

variable [DecidableEq S]

/-- The state map of the first hop: the cache `c` of the hybrid's oracles with the private cache
`p` laid over its subkey points at the key `key`, each subkey of a nonce `η` cached in `p` as
`(k_enc, k_mac)` becoming the entries `k_enc` at `.inr (.inl (key, η))` and `k_mac` at
`.inr (.inr (key, η))`. Away from the key it is `c`. -/
def overlayCache (key : S) (c : (sealSpec n S L Salt Ctx N K).QueryCache)
    (p : (privateSpec N K).QueryCache) : (sealSpec n S L Salt Ctx N K).QueryCache :=
  QueryCache.ofFn fun
    | .inl q => c (.inl q)
    | .inr (.inl x) => if x.1 = key then (p x.2).map Prod.fst else c (.inr (.inl x))
    | .inr (.inr x) => if x.1 = key then (p x.2).map Prod.snd else c (.inr (.inr x))

lemma overlayCache_apply_inl (key : S) (c : (sealSpec n S L Salt Ctx N K).QueryCache)
    (p : (privateSpec N K).QueryCache) (q : Point n S L Salt Ctx) :
    overlayCache key c p (.inl q) = c (.inl q) := by
  rw [overlayCache, QueryCache.ofFn_apply]

lemma overlayCache_apply_enc (key : S) (c : (sealSpec n S L Salt Ctx N K).QueryCache)
    (p : (privateSpec N K).QueryCache) (x : S × N) :
    overlayCache key c p (.inr (.inl x)) =
      if x.1 = key then (p x.2).map Prod.fst else c (.inr (.inl x)) := by
  rw [overlayCache, QueryCache.ofFn_apply]
  rfl

lemma overlayCache_apply_mac (key : S) (c : (sealSpec n S L Salt Ctx N K).QueryCache)
    (p : (privateSpec N K).QueryCache) (x : S × N) :
    overlayCache key c p (.inr (.inr x)) =
      if x.1 = key then (p x.2).map Prod.snd else c (.inr (.inr x)) := by
  rw [overlayCache, QueryCache.ofFn_apply]
  rfl

/-- Away from the subkey points at the key, the overlay is the cache. -/
lemma overlayCache_apply_of_ne (key : S) (c : (sealSpec n S L Salt Ctx N K).QueryCache)
    (p : (privateSpec N K).QueryCache) {t : (sealSpec n S L Salt Ctx N K).Domain}
    (ht : ∀ x, t = .inr x → Sum.elim Prod.fst Prod.fst x ≠ key) :
    overlayCache key c p t = c t := by
  rcases t with q | x | x
  · rfl
  · have := ht (.inl x) rfl
    simp_all [overlayCache_apply_enc]
  · have := ht (.inr x) rfl
    simp_all [overlayCache_apply_mac]

/-- Overlaying the empty private cache on a cache without subkey points at the key changes
nothing. -/
lemma overlayCache_empty {key : S} {c : (sealSpec n S L Salt Ctx N K).QueryCache}
    (h : ¬BadK key c) : overlayCache key c ∅ = c := by
  ext t : 1
  rcases t with q | x | x
  · rfl
  · rw [overlayCache_apply_enc]
    split_ifs with hx
    · cases hc : c (.inr (.inl x))
      · rfl
      · exact absurd ⟨.inl x, by simp [hc], hx⟩ h
    · rfl
  · rw [overlayCache_apply_mac]
    split_ifs with hx
    · cases hc : c (.inr (.inr x))
      · rfl
      · exact absurd ⟨.inr x, by simp [hc], hx⟩ h
    · rfl

variable [DecidableEq L] [DecidableEq Salt] [DecidableEq Ctx] [DecidableEq N]

/-- Caching an answer away from the subkey points at the key commutes with the overlay. -/
lemma overlayCache_cacheQuery_of_ne (key : S) (c : (sealSpec n S L Salt Ctx N K).QueryCache)
    (p : (privateSpec N K).QueryCache) {t : (sealSpec n S L Salt Ctx N K).Domain}
    (ht : ∀ x, t = .inr x → Sum.elim Prod.fst Prod.fst x ≠ key)
    (u : (sealSpec n S L Salt Ctx N K).Range t) :
    overlayCache key (c.cacheQuery t u) p = (overlayCache key c p).cacheQuery t u := by
  ext t' : 1
  by_cases h : t' = t
  · subst h
    rw [QueryCache.cacheQuery_self, overlayCache_apply_of_ne _ _ _ ht, QueryCache.cacheQuery_self]
  · rw [QueryCache.cacheQuery_of_ne _ _ h]
    rcases t' with q | x | x
    · simp only [overlayCache_apply_inl, QueryCache.cacheQuery_of_ne _ _ h]
    · simp only [overlayCache_apply_enc, QueryCache.cacheQuery_of_ne _ _ h]
    · simp only [overlayCache_apply_mac, QueryCache.cacheQuery_of_ne _ _ h]

/-- Caching both subkeys `u` of the nonce `η` in the private cache is caching `u.1` at the
encryption subkey point and `u.2` at the MAC subkey point of the key and `η` in the overlay. -/
lemma overlayCache_cacheQuery_private (key : S) (c : (sealSpec n S L Salt Ctx N K).QueryCache)
    (p : (privateSpec N K).QueryCache) (η : N) (u : K × K) :
    overlayCache key c (p.cacheQuery η u) =
      ((overlayCache key c p).cacheQuery (.inr (.inl (key, η))) u.1).cacheQuery
        (.inr (.inr (key, η))) u.2 := by
  ext t : 1
  rcases t with q | x | x
  · simp [overlayCache_apply_inl]
  · by_cases hx : x = (key, η)
    · subst hx
      simp [overlayCache_apply_enc]
    · rw [QueryCache.cacheQuery_of_ne _ _ (by simp), QueryCache.cacheQuery_of_ne _ _ (by simpa),
        overlayCache_apply_enc, overlayCache_apply_enc]
      split_ifs with h
      · rw [QueryCache.cacheQuery_of_ne _ _ fun h' => hx (Prod.ext h h')]
      · rfl
  · by_cases hx : x = (key, η)
    · subst hx
      simp [overlayCache_apply_mac]
    · rw [QueryCache.cacheQuery_of_ne _ _ (by simpa), QueryCache.cacheQuery_of_ne _ _ (by simp),
        overlayCache_apply_mac, overlayCache_apply_mac]
      split_ifs with h
      · rw [QueryCache.cacheQuery_of_ne _ _ fun h' => hx (Prod.ext h h')]
      · rfl

end StateMap

section Hop

variable [DecidableEq S] [DecidableEq L] [DecidableEq Salt] [DecidableEq Ctx]
  [SampleableType S] [SampleableType L] [DecidableEq N] [SampleableType N] [SampleableType K]

/-- The online phase of the hiding experiment at hidden bit `b` for the puzzle `puzzle` and its
key `key`, as one handler of the adversary's online oracles on the cache of the random oracle:
the challenger of `TimeLockPuzzle.hidingExperiment` over `sealDEM`, with rounds answered point by
point, followed by the random oracle. -/
noncomputable def hidingOnlineImpl (puzzle : Puzzle n S L Salt) (key : S) (b : Bool) :
    QueryImpl ((unifSpec + LeftOrRight.spec Plaintext ByteArray) +
        (sealSpec n S L Salt Ctx N K).batch)
      (StateT (sealSpec n S L Salt Ctx N K).QueryCache ProbComp) :=
  (sealSpec n S L Salt Ctx N K).romImpl ∘ₛ
    QueryImpl.batch' ((unifSpec.passthrough + LeftOrRight.oracle
        ((sealDEM (Ctx := Ctx) prf codec encodePuzzle).encrypt (puzzle, key)) plaintextLength b) +
      (QueryImpl.id' (sealSpec n S L Salt Ctx N K)).liftTarget
        (OracleComp (unifSpec + sealSpec n S L Salt Ctx N K)))

/-- The online phase of the hybrid at hidden bit `b` for the puzzle `puzzle`, as one handler of
the adversary's online oracles on the pair of the cache of the random oracle and the private
cache: a step of `privateImpl` on the private cache, with rounds rewritten as single queries
answered by the random oracle on the shared cache. -/
noncomputable def privateOnlineImpl (puzzle : Puzzle n S L Salt) (b : Bool) :
    QueryImpl ((unifSpec + LeftOrRight.spec Plaintext ByteArray) +
        (sealSpec n S L Salt Ctx N K).batch)
      (StateT ((sealSpec n S L Salt Ctx N K).QueryCache × (privateSpec N K).QueryCache)
        ProbComp) :=
  fun t => StateT.mk fun s => (fun z => (z.1.1, (z.2, z.1.2))) <$>
    (simulateQ (sealSpec n S L Salt Ctx N K).romImpl
      (simulateQ (sealSpec n S L Salt Ctx N K).unbatch
        ((privateImpl prf codec encodePuzzle puzzle b t).run s.2))).run s.1

lemma hidingOnlineImpl_run_unif (puzzle : Puzzle n S L Salt) (key : S) (b : Bool) (k : ℕ)
    (c : (sealSpec n S L Salt Ctx N K).QueryCache) :
    (hidingOnlineImpl (Ctx := Ctx) prf codec encodePuzzle puzzle key b (.inl (.inl k))).run c =
      (unifFwdImpl (sealSpec n S L Salt Ctx N K) k).run c := by
  simp [hidingOnlineImpl]

lemma privateOnlineImpl_run_unif (puzzle : Puzzle n S L Salt) (b : Bool) (k : ℕ)
    (s : (sealSpec n S L Salt Ctx N K).QueryCache × (privateSpec N K).QueryCache) :
    (privateOnlineImpl (Ctx := Ctx) prf codec encodePuzzle puzzle b (.inl (.inl k))).run s =
      (fun z => (z.1, (z.2, s.2))) <$> (unifFwdImpl (sealSpec n S L Salt Ctx N K) k).run s.1 := by
  simp only [add_apply_inl, privateOnlineImpl, privateImpl, QueryImpl.add_apply_inl,
    PFunctor.Handler.liftTarget_apply, ofPFunctor_toPFunctor, QueryImpl.ofLift_apply,
    StateT.run_monadLift, monadLift_self, bind_pure_comp, simulateQ_map,
    simulateQ_romImpl_simulateQ_unbatch, StateT.run_map, Functor.map_map, StateT.run_mk,
    Prod.mk.injEq, and_true, and_imp, Prod.forall, forall_apply_eq_imp_iff, forall_eq',
    Prod.mk.eta, implies_true, map_inj_right_of_nonempty]
  rw [OracleComp.liftM_eq_liftM_liftM, OracleQuery.liftM_add_left_query, simulateQ_spec_query]
  rfl

lemma hidingOnlineImpl_run_challenge (puzzle : Puzzle n S L Salt) (key : S) (b : Bool)
    (m₀ m₁ : Plaintext) (c : (sealSpec n S L Salt Ctx N K).QueryCache) :
    (hidingOnlineImpl (Ctx := Ctx) prf codec encodePuzzle puzzle key b
        (.inl (.inr (m₀, m₁)))).run c =
      if plaintextLength m₀ = plaintextLength m₁ then (do
        let nonce ← $ᵗ N
        let z₁ ← ((sealSpec n S L Salt Ctx N K).randomOracle (.inr (.inl (key, nonce)))).run c
        let z₂ ← ((sealSpec n S L Salt Ctx N K).randomOracle (.inr (.inr (key, nonce)))).run z₁.2
        pure (some (sealWith prf codec (encodePuzzle puzzle) nonce (z₁.1, z₂.1)
          (if b then m₁ else m₀)), z₂.2))
      else pure (none, c) := by
  by_cases h : plaintextLength m₀ = plaintextLength m₁
  · simp [hidingOnlineImpl, LeftOrRight.oracle, h, sealDEM, dem, sealDerive, roSim.run_liftM,
      QueryImpl.simulateQ_add_liftM_right]
  · simp [hidingOnlineImpl, LeftOrRight.oracle, h]

lemma privateOnlineImpl_run_challenge (puzzle : Puzzle n S L Salt) (b : Bool) (m₀ m₁ : Plaintext)
    (s : (sealSpec n S L Salt Ctx N K).QueryCache × (privateSpec N K).QueryCache) :
    (privateOnlineImpl (Ctx := Ctx) prf codec encodePuzzle puzzle b (.inl (.inr (m₀, m₁)))).run s =
      if plaintextLength m₀ = plaintextLength m₁ then (do
        let nonce ← $ᵗ N
        let z ← ((privateSpec N K).randomOracle nonce).run s.2
        pure (some (sealWith prf codec (encodePuzzle puzzle) nonce z.1 (if b then m₁ else m₀)),
          (s.1, z.2)))
      else pure (none, s) := by
  by_cases h : plaintextLength m₀ = plaintextLength m₁
  · simp only [privateOnlineImpl, privateImpl, StateT.run_mk, QueryImpl.add_apply_inl,
      QueryImpl.add_apply_inr, LeftOrRight.oracle, h, ↓reduceIte]
    simp [privateEncrypt, simulateQ_romImpl_simulateQ_unbatch, QueryImpl.simulateQ_add_liftM_left,
      unifFwdImpl.simulateQ_run]
  · simp only [privateOnlineImpl, privateImpl, StateT.run_mk, QueryImpl.add_apply_inl,
      QueryImpl.add_apply_inr, LeftOrRight.oracle, h, ↓reduceIte]
    simp

lemma hidingOnlineImpl_run_batch (puzzle : Puzzle n S L Salt) (key : S) (b : Bool)
    (ts : List (sealSpec n S L Salt Ctx N K).Domain)
    (c : (sealSpec n S L Salt Ctx N K).QueryCache) :
    (hidingOnlineImpl (Ctx := Ctx) prf codec encodePuzzle puzzle key b (.inr ts)).run c =
      ((sealSpec n S L Salt Ctx N K).randomOracle.batch ts).run c := by
  simp only [add_apply_inr, hidingOnlineImpl, QueryImpl.passthrough_add, QueryImpl.batch'_add,
    QueryImpl.apply_compose, QueryImpl.add_apply_inr]
  rw [← QueryImpl.apply_compose, QueryImpl.compose_batch]
  congr 2
  funext t
  rw [QueryImpl.apply_compose, QueryImpl.liftTarget_apply, QueryImpl.id'_apply,
    QueryImpl.simulateQ_add_liftM_right, simulateQ_spec_query]

lemma privateOnlineImpl_run_batch (puzzle : Puzzle n S L Salt) (b : Bool)
    (ts : List (sealSpec n S L Salt Ctx N K).Domain)
    (s : (sealSpec n S L Salt Ctx N K).QueryCache × (privateSpec N K).QueryCache) :
    (privateOnlineImpl (Ctx := Ctx) prf codec encodePuzzle puzzle b (.inr ts)).run s =
      (fun z => (z.1, (z.2, s.2))) <$>
        ((sealSpec n S L Salt Ctx N K).randomOracle.batch ts).run s.1 := by
  simp only [add_apply_inr, privateOnlineImpl, privateImpl, QueryImpl.add_apply_inr,
    StateT.run_monadLift, bind_pure_comp, simulateQ_map, simulateQ_query, OracleQuery.input_query,
    OracleQuery.cont_query, unbatch_apply_inr, id_map, StateT.run_map, Functor.map_map,
    StateT.run_mk, Prod.mk.injEq, and_true, and_imp, Prod.forall, forall_apply_eq_imp_iff,
    forall_eq', Prod.mk.eta, implies_true, map_inj_right]
  rw [← QueryImpl.apply_compose, QueryImpl.compose_batch]
  congr 3
  funext t
  simp only [QueryImpl.apply_compose, simulateQ_query, OracleQuery.input_query, add_apply_inr,
    OracleQuery.cont_query, QueryImpl.add_apply_inr, QueryImpl.withCaching_apply,
    uniformSampleImpl_apply, map_bind, id_map]

/-- A step of the hybrid's online handler only extends the cache of the random oracle. -/
lemma le_of_mem_support_privateOnlineImpl_run (puzzle : Puzzle n S L Salt) (b : Bool)
    (t : ((unifSpec + LeftOrRight.spec Plaintext ByteArray) +
      (sealSpec n S L Salt Ctx N K).batch).Domain)
    (s : (sealSpec n S L Salt Ctx N K).QueryCache × (privateSpec N K).QueryCache)
    {z} (hz : z ∈ support ((privateOnlineImpl (Ctx := Ctx) prf codec encodePuzzle puzzle b
      t).run s)) : s.1 ≤ z.2.1 := by
  rcases t with (k | ⟨m₀, m₁⟩) | ts
  · rw [privateOnlineImpl_run_unif, support_map] at hz
    obtain ⟨z', hz', rfl⟩ := hz
    exact (unifFwdImpl.snd_eq_of_mem_support_run k s.1 hz').ge
  · rw [privateOnlineImpl_run_challenge] at hz
    by_cases h : plaintextLength m₀ = plaintextLength m₁
    · simp only [h, ↓reduceIte, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
      obtain ⟨_, _, _, _, rfl⟩ := hz
      exact le_rfl
    · simp only [h, ↓reduceIte] at hz
      rw [mem_support_pure_iff] at hz
      subst hz
      exact le_rfl
  · rw [privateOnlineImpl_run_batch, support_map] at hz
    obtain ⟨z', hz', rfl⟩ := hz
    exact (QueryImpl.withCaching_batch_le_and_isSome_iff _ hz').1

/-- **`BadK` is sticky in the hybrid.** Once the cache of the random oracle holds a subkey point
at the key, every step of the hybrid's online handler keeps it. -/
lemma preservesInv_privateOnlineImpl_badK (puzzle : Puzzle n S L Salt) (key : S) (b : Bool) :
    QueryImpl.PreservesInv (privateOnlineImpl (Ctx := Ctx) prf codec encodePuzzle puzzle b)
      (fun s => BadK key s.1) := by
  rintro t s ⟨x, hx, hkey⟩ z hz
  exact ⟨x, QueryCache.isSome_mono
    (le_of_mem_support_privateOnlineImpl_run prf codec encodePuzzle puzzle b t s hz) hx, hkey⟩

/-- **The handlers agree off `BadK`.** Read through `overlayCache key`, each step of the hybrid's
online handler is a step of the hiding experiment's, unless all its post-states hold a subkey point
at the key: local coins are forwarded by both; a challenge draws the same nonce, and the private
cache at the nonce, laid over the shared cache, answers the two subkey points at the key and the
nonce as the random oracle does; a round with no subkey point at the key commutes with the overlay,
and a round with one caches it. -/
theorem dominatedUntilBad_privateOnlineImpl (puzzle : Puzzle n S L Salt) (key : S) (b : Bool) :
    QueryImpl.DominatedUntilBad (privateOnlineImpl (Ctx := Ctx) prf codec encodePuzzle puzzle b)
      (hidingOnlineImpl prf codec encodePuzzle puzzle key b)
      (fun s => overlayCache key s.1 s.2) (fun _ => True) (fun s => BadK key s.1) := by
  refine QueryImpl.DominatedUntilBad.of_evalDistEq_or_bad fun t s _ _ => ?_
  rcases t with (k | ⟨m₀, m₁⟩) | ts
  · left
    simp only [privateOnlineImpl_run_unif, hidingOnlineImpl_run_unif, unifFwdImpl,
      QueryImpl.liftTarget_apply, StateT.run_liftM, bind_pure_comp, Functor.map_map]
    rfl
  · left
    rw [privateOnlineImpl_run_challenge, hidingOnlineImpl_run_challenge]
    by_cases h : plaintextLength m₀ = plaintextLength m₁
    · simp only [h, ↓reduceIte, map_bind, map_pure]
      refine EvalDistEq.bind_right _ fun nonce => ?_
      rw [randomOracle.run_eq, randomOracle.run_eq, overlayCache_apply_enc]
      simp only [↓reduceIte]
      cases hp : s.2 nonce with
      | some ks =>
        simp only [Option.map_some, pure_bind]
        rw [randomOracle.run_eq, overlayCache_apply_mac]
        simp [hp]
      | none =>
        simp only [Option.map_none, bind_assoc, pure_bind]
        rw [SampleableType.uniformSample_prod_eq_bind, bind_assoc]
        refine EvalDistEq.bind_right _ fun u₁ => ?_
        simp only [bind_assoc, pure_bind]
        rw [randomOracle.run_eq, QueryCache.cacheQuery_of_ne _ _ (by simp),
          overlayCache_apply_mac]
        simp only [↓reduceIte, hp, Option.map_none, bind_assoc, pure_bind]
        refine EvalDistEq.bind_right _ fun u₂ => ?_
        rw [overlayCache_cacheQuery_private]
    · simp only [h, ↓reduceIte, map_pure]
      rfl
  · by_cases hk : ∃ t ∈ ts, ∃ x, t = .inr x ∧ Sum.elim Prod.fst Prod.fst x = key
    · right
      obtain ⟨t, ht, x, rfl, hx⟩ := hk
      intro z hz
      rw [privateOnlineImpl_run_batch, support_map] at hz
      obtain ⟨z', hz', rfl⟩ := hz
      exact ⟨x, ((QueryImpl.withCaching_batch_le_and_isSome_iff _ hz').2 _).2 (Or.inr ht), hx⟩
    · left
      push Not at hk
      rw [privateOnlineImpl_run_batch, hidingOnlineImpl_run_batch, Functor.map_map,
        ← QueryImpl.map_withCaching_batch_run_of_commute uniformSampleImpl
          (fun c => overlayCache key c s.2)
          (P := fun t => ∀ x, t = .inr x → Sum.elim Prod.fst Prod.fst x ≠ key)
          (fun c _ ht => overlayCache_apply_of_ne key c s.2 ht)
          (fun c _ u ht => overlayCache_cacheQuery_of_ne key c s.2 ht u) hk s.1]
      rfl

/-- **One online phase, from the hiding experiment to the hybrid.** From any cache `c`, an event of
the output of the hiding experiment's online handler has at most the mass of the event, or
`BadK` of the final cache, in the hybrid's online handler started from `c` and the empty private
cache. From a cache without subkey points at the key the overlay of the empty private cache is
`c`, and domination until `BadK` applies; from a cache with one, `BadK` holds throughout. -/
theorem prEvent_hidingOnlineImpl_le {α : Type} (puzzle : Puzzle n S L Salt) (key : S) (b : Bool)
    (oa : OracleComp ((unifSpec + LeftOrRight.spec Plaintext ByteArray) +
      (sealSpec n S L Salt Ctx N K).batch) α) (c : (sealSpec n S L Salt Ctx N K).QueryCache)
    (P : α → Prop) :
    Pr{let z ← (simulateQ (hidingOnlineImpl prf codec encodePuzzle puzzle key b) oa).run c}[
        P z.1] ≤
      Pr{let z ← (simulateQ (privateOnlineImpl (Ctx := Ctx) prf codec encodePuzzle puzzle b)
        oa).run (c, ∅)}[P z.1 ∨ BadK key z.2.1] := by
  by_cases hc : BadK key c
  · rw [prEvent_eq_one_of_forall_mem_support _ _ fun z hz => Or.inr
      (simulateQ_run_preservesInv _ _ (preservesInv_privateOnlineImpl_badK prf codec encodePuzzle
        puzzle key b) oa (c, ∅) hc z hz)]
    exact prEvent_le_one _
  · have := (dominatedUntilBad_privateOnlineImpl prf codec encodePuzzle puzzle key b
      ).prEvent_simulateQ_run_le_map_or_bad (fun _ _ _ _ _ => trivial)
      (preservesInv_privateOnlineImpl_badK prf codec encodePuzzle puzzle key b) oa (c, ∅) trivial
      fun z => P z.1
    simpa only [overlayCache_empty hc] using this

/-- **One online phase, from the hybrid to the hiding experiment.** From any cache `c`, an event of
the output of the hybrid's online handler started from `c` and the empty private cache, conjoined
with the absence of `BadK` in the final cache, has at most the mass of the event in the hiding
experiment's online handler. -/
theorem prEvent_privateOnlineImpl_and_not_badK_le {α : Type} (puzzle : Puzzle n S L Salt)
    (key : S) (b : Bool) (oa : OracleComp ((unifSpec + LeftOrRight.spec Plaintext ByteArray) +
      (sealSpec n S L Salt Ctx N K).batch) α) (c : (sealSpec n S L Salt Ctx N K).QueryCache)
    (P : α → Prop) :
    Pr{let z ← (simulateQ (privateOnlineImpl (Ctx := Ctx) prf codec encodePuzzle puzzle b)
        oa).run (c, ∅)}[P z.1 ∧ ¬BadK key z.2.1] ≤
      Pr{let z ← (simulateQ (hidingOnlineImpl prf codec encodePuzzle puzzle key b) oa).run c}[
        P z.1] := by
  by_cases hc : BadK key c
  · rw [prEvent_eq_zero_of_forall_mem_support _ _ fun z hz hz' => hz'.2
      (simulateQ_run_preservesInv _ _ (preservesInv_privateOnlineImpl_badK prf codec encodePuzzle
        puzzle key b) oa (c, ∅) hc z hz)]
    exact zero_le
  · have := (dominatedUntilBad_privateOnlineImpl prf codec encodePuzzle puzzle key b
      ).prEvent_simulateQ_run_map_and_not_bad_le (fun _ _ _ _ _ => trivial)
      (preservesInv_privateOnlineImpl_badK prf codec encodePuzzle puzzle key b) oa (c, ∅) trivial
      fun z => P z.1
    simpa only [overlayCache_empty hc] using this

/-- The random-oracle run of the online phase of the hiding experiment is the run of its online
handler. -/
lemma simulateQ_romImpl_hidingChallenger {α : Type} (puzzle : Puzzle n S L Salt) (key : S)
    (b : Bool) (oa : OracleComp ((unifSpec + LeftOrRight.spec Plaintext ByteArray) +
      (sealSpec n S L Salt Ctx N K).batch) α) :
    simulateQ (sealSpec n S L Salt Ctx N K).romImpl
      (simulateQ ((unifSpec.passthrough + LeftOrRight.oracle
          ((sealDEM (Ctx := Ctx) prf codec encodePuzzle).encrypt (puzzle, key)) plaintextLength b) +
        (QueryImpl.id' (sealSpec n S L Salt Ctx N K)).liftTarget
          (OracleComp (unifSpec + sealSpec n S L Salt Ctx N K)))
        (simulateQ (sealSpec n S L Salt Ctx N K).unbatch oa)) =
      simulateQ (hidingOnlineImpl prf codec encodePuzzle puzzle key b) oa := by
  rw [QueryImpl.simulateQ_simulateQ_unbatch, hidingOnlineImpl, QueryImpl.simulateQ_compose]

/-- The random-oracle run of the online phase of the hybrid, which runs `privateImpl` on the
private cache inside the run on the shared cache, is equal in distribution to the run of its
online handler on the pair of caches (`OracleComp.simulateQ_run_simulateQ_run_evalDistEq`). -/
lemma run_romImpl_privateImpl_evalDistEq {α : Type} (puzzle : Puzzle n S L Salt) (b : Bool)
    (oa : OracleComp ((unifSpec + LeftOrRight.spec Plaintext ByteArray) +
      (sealSpec n S L Salt Ctx N K).batch) α) (c : (sealSpec n S L Salt Ctx N K).QueryCache) :
    (simulateQ (sealSpec n S L Salt Ctx N K).romImpl
      (simulateQ (sealSpec n S L Salt Ctx N K).unbatch
        ((simulateQ (privateImpl prf codec encodePuzzle puzzle b) oa).run' ∅))).run c =ᵈ
      (fun z => (z.1, z.2.1)) <$>
        (simulateQ (privateOnlineImpl (Ctx := Ctx) prf codec encodePuzzle puzzle b) oa).run
          (c, ∅) := by
  have h := simulateQ_run_simulateQ_run_evalDistEq
    ((sealSpec n S L Salt Ctx N K).romImpl ∘ₛ (sealSpec n S L Salt Ctx N K).unbatch)
    (privateImpl prf codec encodePuzzle puzzle b)
    (privateOnlineImpl (Ctx := Ctx) prf codec encodePuzzle puzzle b) (fun t s q => by
      rw [privateOnlineImpl, StateT.run_mk, Functor.map_map, QueryImpl.simulateQ_compose]
      simp) oa ∅ c
  rw [QueryImpl.simulateQ_compose] at h
  rw [StateT.run'_eq, simulateQ_map, simulateQ_map, StateT.run_map]
  refine (h.map fun z => (z.1.1, z.2)).trans ?_
  rw [Functor.map_map]

/-- **From the hiding experiment to the hybrid (`G₀ → G₁`).** For a hiding adversary `adv` against
`sealScheme` with `sealDEM` and leakage `plaintextLength`, at either hidden bit, the probabilities
that the hiding experiment returns `true` and that the hybrid `privateExperiment` returns the
guess `true` differ by at most the probability of `BadK` in the hybrid.

The two experiments share preprocessing and key generation. From the resulting cache, the online
phases are the runs of `hidingOnlineImpl` and, up to distribution, of `privateOnlineImpl` with an
empty private cache (`run_romImpl_privateImpl_evalDistEq`); the hybrid's handler is dominated by
the experiment's through `overlayCache` until `BadK` (`dominatedUntilBad_privateOnlineImpl`),
which is sticky (`preservesInv_privateOnlineImpl_badK`), giving the bound in each direction
(`prEvent_hidingOnlineImpl_le`, `prEvent_privateOnlineImpl_and_not_badK_le`). -/
theorem absDiff_hidingExperiment_privateExperiment_le [SampleableType Salt] [NeZero n]
    [AddCommGroup L] (mkCtx : Salt → Ctx) (initAcc : Ctx → S)
    (adv : HidingAdversary (sealSpec n S L Salt Ctx N K) (Puzzle n S L Salt) Plaintext ByteArray)
    (b : Bool) :
    ENNReal.absDiff
      ((ProbCompRuntime.rom (sealSpec n S L Salt Ctx N K)).evalDist
        ((sealScheme n m mkCtx initAcc N K).hidingExperiment
          (sealDEM (Ctx := Ctx) prf codec encodePuzzle) plaintextLength adv b) {true})
      (Pr{let z ← (simulateQ (sealSpec n S L Salt Ctx N K).romImpl
        (privateExperiment m prf codec encodePuzzle mkCtx initAcc adv b)).run ∅}[z.1.1 = true]) ≤
      Pr{let z ← (simulateQ (sealSpec n S L Salt Ctx N K).romImpl
        (privateExperiment m prf codec encodePuzzle mkCtx initAcc adv b)).run ∅}[
          BadK z.1.2 z.2] := by
  rw [ProbCompRuntime.rom_evalDist, ← prEvent_eq_evalDist_singleton, StateT.run'_eq, prEvent_map]
  have hA : Pr{let x ← (simulateQ (sealSpec n S L Salt Ctx N K).romImpl
      ((sealScheme n m mkCtx initAcc N K).hidingExperiment
        (sealDEM (Ctx := Ctx) prf codec encodePuzzle) plaintextLength adv b)).run ∅}[x.1 = true] ≤
      Pr{let z ← (simulateQ (sealSpec n S L Salt Ctx N K).romImpl
        (privateExperiment m prf codec encodePuzzle mkCtx initAcc adv b)).run ∅}[z.1.1 = true ∨
          BadK z.1.2 z.2] := by
    simp only [TimeLockPuzzle.hidingExperiment, privateExperiment, guessExperiment, simulateQ_bind,
      StateT.run_bind]
    refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun p => ?_
    refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun ⟨⟨puzzle, key⟩, c⟩ => ?_
    dsimp only
    rw [simulateQ_romImpl_hidingChallenger]
    simp only [simulateQ_pure, StateT.run_pure, bind_pure_comp, prEvent_map, privateAdversary]
    rw [(run_romImpl_privateImpl_evalDistEq prf codec encodePuzzle puzzle b _ c).prEvent_eq,
      prEvent_map]
    exact prEvent_hidingOnlineImpl_le prf codec encodePuzzle puzzle key b _ c (· = true)
  have hB : Pr{let z ← (simulateQ (sealSpec n S L Salt Ctx N K).romImpl
        (privateExperiment m prf codec encodePuzzle mkCtx initAcc adv b)).run ∅}[z.1.1 = true ∧
          ¬BadK z.1.2 z.2] ≤
      Pr{let x ← (simulateQ (sealSpec n S L Salt Ctx N K).romImpl
        ((sealScheme n m mkCtx initAcc N K).hidingExperiment
          (sealDEM (Ctx := Ctx) prf codec encodePuzzle) plaintextLength adv b)).run ∅}[
          x.1 = true] := by
    simp only [TimeLockPuzzle.hidingExperiment, privateExperiment, guessExperiment, simulateQ_bind,
      StateT.run_bind]
    refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun p => ?_
    refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun ⟨⟨puzzle, key⟩, c⟩ => ?_
    dsimp only
    rw [simulateQ_romImpl_hidingChallenger]
    simp only [simulateQ_pure, StateT.run_pure, bind_pure_comp, prEvent_map, privateAdversary]
    rw [(run_romImpl_privateImpl_evalDistEq prf codec encodePuzzle puzzle b _ c).prEvent_eq,
      prEvent_map]
    exact prEvent_privateOnlineImpl_and_not_badK_le prf codec encodePuzzle puzzle key b _ c
      (· = true)
  refine ENNReal.absDiff_le_iff.2 ⟨hA.trans (prEvent_or_le _ _ _), ?_⟩
  rw [add_comm]
  exact prEvent_le_prEvent_add_of_prEvent_and_not_le _ _ _ _ _ hB

end Hop

end PointerChainPuzzle
