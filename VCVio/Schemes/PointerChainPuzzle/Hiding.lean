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

## Main statements

* `PointerChainPuzzle.delayAdvantage_sealScheme_le`: `sealScheme` has the delay bound of
  `scheme`.
* `PointerChainPuzzle.isQueryBound_privateAdversary`: inlining the private challenger keeps the
  preprocessing and online budgets.
* `PointerChainPuzzle.prEvent_privateExperiment_badK_le`: in the hybrid, `BadK` has probability at
  most `[n ≥ 2] Q_on / |L| + Q_pre / (|Salt| |L|) + (Q P + P² + Q) / |S|`, with
  `P = solvePoints n m` and `Q = Q_pre + Q_on`.
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

end PointerChainPuzzle
