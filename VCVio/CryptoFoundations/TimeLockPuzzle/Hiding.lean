/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.TimeLockPuzzle
public import VCVio.CryptoFoundations.DataEncapMech

/-!
# Hiding for time-lock puzzles: time-lock encryption

A time-lock puzzle together with a data encapsulation mechanism encrypts to the future: the
sender generates a puzzle with its key, encrypts with the DEM, and sends the puzzle with the
ciphertexts. The puzzle is a key encapsulation mechanism with no public key and a time bound:
anyone can decapsulate, by solving the puzzle, but not within fewer rounds than the solver needs.
The DEM is keyed by the generator's whole output, the puzzle together with its key, so that it can
bind the puzzle it travels with, for example by authenticating it. A DEM under the key alone is
the case that ignores the puzzle (`DEMScheme.comap Prod.snd`), and since the adversary holds the
puzzle anyway, keying the DEM by it hides nothing extra.

Hiding is multi-message IND-CPA of this time-lock encryption. The adversary's preprocessing phase
queries the oracles before the puzzle exists; its online phase receives the puzzle, submits rounds
of parallel queries, and asks the left-or-right challenge oracle `LeftOrRight.oracle` of
`VCVio.CryptoFoundations.LeftOrRight` for encryptions, under the puzzle and its key, of the
message that a hidden bit selects. Preprocessing, generation, the online phase and the
challenger's encryptions all query one oracle, which in the random oracle model is one lazily
sampled cache.

* **Not a `KEMScheme`.** `KEMScheme` has a public key and no time bound: its IND-CPA adversary
  receives the public key and is not limited in the rounds it takes. A time-lock puzzle has no
  public key, and its security holds only against an online phase within fewer rounds than the
  solver needs, so the game is stated on the puzzle itself.
* **No split into key indistinguishability and DEM security.** The DEM runs over the puzzle's
  oracles, `DEMScheme (OracleComp (unifSpec + spec))`, so a DEM in the random oracle model derives
  its subkeys from the oracle the puzzle uses and the adversary queries. The key is then not
  independent of the oracle the DEM evaluates, and hiding does not follow from a key
  indistinguishability game for the puzzle composed with the DEM's game under an independent key.
* **The DEM's multi-query game with a generated puzzle.** The challenge oracle is the one of the
  multi-query DEM game `DEMScheme.IND_CPA_Experiment`, built from the DEM's encryption, a leakage
  function and the hidden bit. The DEM game encrypts under a uniform key; the hiding game encrypts
  under a generated puzzle together with its key, gives the adversary the puzzle, and limits its
  online phase in rounds.

## Main definitions

* `TimeLockPuzzle.HidingAdversary`: the two-phase adversary whose online phase also queries local
  coins and the challenge oracle at no cost, and outputs a guess of the hidden bit.
* `TimeLockPuzzle.HidingAdversary.MakesAtMostQueries`: the encryption budget.
* `TimeLockPuzzle.hidingExperiment`: the hiding experiment at a fixed hidden bit.
* `TimeLockPuzzle.hidingAdvantage`: the distance between the experiment's two branches against one
  lazily sampled random oracle.
* `TimeLockPuzzle.HidingSecure`: hiding against adversaries within preprocessing, online and
  encryption budgets.
* `TimeLockPuzzle.cappedHidingExperiment`, `TimeLockPuzzle.cappedHidingAdvantage`: the hiding
  experiment and advantage with a capped challenger, which answers `none` after `qEnc` accepted
  requests, against adversaries with no encryption budget.
* `TimeLockPuzzle.HidingAdversary.capChallenges`: the adapter that runs an adversary of the
  capped game as an adversary within an encryption budget.

## Main statements

* `TimeLockPuzzle.hidingAdvantage_eq`: the hiding advantage is the distance between the
  probabilities that the two branches return `true` in the random oracle model.
* `TimeLockPuzzle.hidingAdvantage_eq_zero_of_makesAtMostQueries_zero`: an adversary that makes no
  challenge query has hiding advantage `0`.
* `TimeLockPuzzle.hidingExperiment_capChallenges`: at each hidden bit, the hiding experiment of
  the adapted adversary is the capped experiment of the original one, and
  `TimeLockPuzzle.cappedHidingAdvantage_eq_hidingAdvantage_capChallenges` equates the two
  advantages.

## The capped challenger

The encryption budget `HidingAdversary.MakesAtMostQueries` counts every challenge request. The
game can also be stated with the count kept by the challenger: the challenger accepts at most
`qEnc` requests with equal leakage, answers every later request with `none`, and puts no budget
on the adversary. Requests with unequal leakage are answered with `none` in both forms and do not
count against the challenger's cap. The two forms agree through the adapter
`HidingAdversary.capChallenges`, which keeps the challenger's counter on the adversary's side, so
a theorem for adversaries within an encryption budget covers every adversary of the capped game.
-/

public section

open OracleSpec OracleComp ENNReal MeasureTheory

namespace TimeLockPuzzle

variable {ι : Type} {spec : OracleSpec.{0, 0} ι} {Puzzle Key M C : Type}

/-! ## The hiding adversary -/

/-- An adversary in the hiding experiment: a two-phase adversary whose online phase queries local
coins and the left-or-right challenge oracle `LeftOrRight.spec M C` beside its rounds, and outputs
a guess of the hidden bit. Its preprocessing and online budgets are
`TwoPhaseAdversary.IsQueryBound`, under which challenge queries cost no round and no point; its
encryption budget is `HidingAdversary.MakesAtMostQueries`. -/
abbrev HidingAdversary (spec : OracleSpec.{0, 0} ι) (Puzzle M C : Type) : Type 1 :=
  TwoPhaseAdversary (unifSpec + LeftOrRight.spec M C) spec Puzzle Bool

/-- A hiding adversary `MakesAtMostQueries q` when, on every state and puzzle, its online phase
makes at most `q` queries to the challenge oracle. Local coins are unrestricted, and rounds are
limited by `TwoPhaseAdversary.IsQueryBound`. -/
@[expose]
def HidingAdversary.MakesAtMostQueries (adv : HidingAdversary spec Puzzle M C) (q : ℕ) : Prop :=
  ∀ σ puzzle, IsQueryBoundP (adv.online σ puzzle) (· matches .inl (.inr _)) q

/-! ## The hiding experiment -/

variable {Λ : Type} [DecidableEq Λ]

/-- The hiding experiment `Hide_b` at hidden bit `b`, for the DEM `dem` over the puzzle's oracles
and the leakage function `leak`: run the preprocessing phase, generate a puzzle with its key, run
the online phase on the state and the puzzle, and return its guess. The online phase's rounds are
rewritten as single queries (`OracleSpec.unbatch`); then local coins and queries to `spec` are
forwarded, and challenge queries are answered by
`LeftOrRight.oracle (dem.encrypt (puzzle, key)) leak b`: a pair with equal leakage by the
encryption, under the puzzle and its key, of the message that `b` selects, any other pair by
`none`.

* **The DEM is keyed by the puzzle and its key.** Time-lock encryption sends the puzzle with the
  ciphertexts, and its DEM is keyed by the generator's whole output, so that it can bind the
  puzzle, for example by authenticating it. A DEM under the key alone is the case that ignores
  the puzzle (`DEMScheme.comap Prod.snd`). The adversary holds the puzzle anyway, so this hides
  nothing extra.
* **The key enters through `dem.encrypt (puzzle, key)`.** The challenge oracle is the library's
  left-or-right oracle, which never sees the key: the experiment supplies it in the encryption
  function, as the DEM game supplies a uniform key and a public-key game supplies `encrypt pk`.
* **One oracle.** The three phases and the challenger's encryptions query the one oracle `spec`,
  and in the random oracle model one cache: a DEM whose subkeys are derived through `spec`
  derives them through the oracle that the adversary queries.
* **Rounds are the adversary's own.** The online budget counts the rounds that the online phase
  submits. The challenger's encryptions query `spec` directly, outside the online phase's rounds,
  and challenge queries are on the free summand, so neither costs the adversary a round. -/
@[expose]
def hidingExperiment (tlp : TimeLockPuzzle spec Puzzle Key)
    (dem : DEMScheme (OracleComp (unifSpec + spec)) (Puzzle × Key) M C) (leak : M → Λ)
    (adv : HidingAdversary spec Puzzle M C) (b : Bool) : OracleComp (unifSpec + spec) Bool := do
  let σ ← adv.preprocess
  let (puzzle, key) ← simulateQ spec.unbatch tlp.gen
  simulateQ ((unifSpec.passthrough + LeftOrRight.oracle (dem.encrypt (puzzle, key)) leak b) +
      (QueryImpl.id' spec).liftTarget (OracleComp (unifSpec + spec)))
    (simulateQ spec.unbatch (adv.online σ puzzle))

section advantage

variable [DecidableEq ι] [∀ t, SampleableType (spec.Range t)]

/-- The hiding advantage of `adv`: the distance between the probabilities that the hiding
experiment returns `true` at hidden bits `true` and `false`, against one lazily sampled random
oracle starting from the empty cache. It is the left-or-right advantage
`|Pr[Hide_1 = 1] - Pr[Hide_0 = 1]|`, with no factor from a hidden-bit normalization. -/
noncomputable def hidingAdvantage (tlp : TimeLockPuzzle spec Puzzle Key)
    (dem : DEMScheme (OracleComp (unifSpec + spec)) (Puzzle × Key) M C) (leak : M → Λ)
    (adv : HidingAdversary spec Puzzle M C) : ℝ≥0∞ :=
  ((ProbCompRuntime.rom spec).evalDist (tlp.hidingExperiment dem leak adv true)).boolDist
    ((ProbCompRuntime.rom spec).evalDist (tlp.hidingExperiment dem leak adv false))

/-- The hiding advantage is the distance between the probabilities that the hiding experiment
returns `true` at the two hidden bits, against one lazily sampled random oracle. -/
theorem hidingAdvantage_eq (tlp : TimeLockPuzzle spec Puzzle Key)
    (dem : DEMScheme (OracleComp (unifSpec + spec)) (Puzzle × Key) M C) (leak : M → Λ)
    (adv : HidingAdversary spec Puzzle M C) :
    hidingAdvantage tlp dem leak adv =
      ENNReal.absDiff
        ((ProbCompRuntime.rom spec).evalDist (tlp.hidingExperiment dem leak adv true) {true})
        ((ProbCompRuntime.rom spec).evalDist (tlp.hidingExperiment dem leak adv false) {true}) := by
  rw [hidingAdvantage, Measure.boolDist]

/-- Hiding: every adversary with at most `Q` preprocessing queries, an online budget of `b.1`
rounds and `b.2` points, and at most `qEnc` challenge queries has hiding advantage at most `ε`.
For a puzzle whose honest solver derives the key in round `T`, the meaningful budgets are
`b = (T - 1, q)`. -/
@[expose]
def HidingSecure (tlp : TimeLockPuzzle spec Puzzle Key)
    (dem : DEMScheme (OracleComp (unifSpec + spec)) (Puzzle × Key) M C) (leak : M → Λ) (Q : ℕ)
    (b : ℕ × ℕ) (qEnc : ℕ) (ε : ℝ≥0∞) : Prop :=
  ∀ adv : HidingAdversary spec Puzzle M C,
    adv.IsQueryBound Q b → adv.MakesAtMostQueries qEnc → hidingAdvantage tlp dem leak adv ≤ ε

end advantage

/-! ## No challenge query, no advantage -/

/-- An adversary that makes no challenge query cannot tell the hidden bits apart: the hiding
experiment is the same computation at both bits, since the hidden bit enters only through the
answers of the challenge oracle. -/
theorem hidingExperiment_eq_of_makesAtMostQueries_zero (tlp : TimeLockPuzzle spec Puzzle Key)
    (dem : DEMScheme (OracleComp (unifSpec + spec)) (Puzzle × Key) M C) (leak : M → Λ)
    {adv : HidingAdversary spec Puzzle M C} (h : adv.MakesAtMostQueries 0) (b b' : Bool) :
    tlp.hidingExperiment dem leak adv b = tlp.hidingExperiment dem leak adv b' := by
  simp only [hidingExperiment]
  refine bind_congr fun σ => bind_congr fun pk => ?_
  rcases pk with ⟨puzzle, key⟩
  dsimp only
  rw [QueryImpl.simulateQ_simulateQ_unbatch, QueryImpl.simulateQ_simulateQ_unbatch]
  have h := h σ puzzle
  generalize adv.online σ puzzle = oa at h
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t mx ih =>
    rw [isQueryBoundP_query_bind_iff, Nat.zero_sub, ite_self] at h
    simp only [simulateQ_query_bind]
    rcases t with (n | mm) | ts
    · exact congrArg (_ >>= ·) (funext fun u => ih u (h.2 u))
    · simp at h
    · exact congrArg (_ >>= ·) (funext fun u => ih u (h.2 u))

/-- An adversary that makes no challenge query has hiding advantage `0`, for every puzzle, DEM
and leakage function. -/
theorem hidingAdvantage_eq_zero_of_makesAtMostQueries_zero [DecidableEq ι]
    [∀ t, SampleableType (spec.Range t)] (tlp : TimeLockPuzzle spec Puzzle Key)
    (dem : DEMScheme (OracleComp (unifSpec + spec)) (Puzzle × Key) M C) (leak : M → Λ)
    {adv : HidingAdversary spec Puzzle M C} (h : adv.MakesAtMostQueries 0) :
    hidingAdvantage tlp dem leak adv = 0 := by
  rw [hidingAdvantage_eq, hidingExperiment_eq_of_makesAtMostQueries_zero tlp dem leak h true false,
    ENNReal.absDiff_self]

/-! ## The capped challenger -/

/-- The hiding experiment with a capped challenger, at hidden bit `b`: the hiding experiment
`hidingExperiment`, except that challenge queries are answered by
`LeftOrRight.cappedOracle (dem.encrypt (puzzle, key)) leak qEnc b` from the counter `0`. The first
`qEnc` pairs with equal leakage are encrypted as in the hiding experiment; every later request,
and every pair with unequal leakage, is answered with `none`, and only accepted pairs advance the
counter. The adversary has no encryption budget: the cap is the challenger's. -/
@[expose]
def cappedHidingExperiment (tlp : TimeLockPuzzle spec Puzzle Key)
    (dem : DEMScheme (OracleComp (unifSpec + spec)) (Puzzle × Key) M C) (leak : M → Λ)
    (qEnc : ℕ) (adv : HidingAdversary spec Puzzle M C) (b : Bool) :
    OracleComp (unifSpec + spec) Bool := do
  let σ ← adv.preprocess
  let (puzzle, key) ← simulateQ spec.unbatch tlp.gen
  StateT.run' (simulateQ ((unifSpec.passthrough +
        LeftOrRight.cappedOracle (dem.encrypt (puzzle, key)) leak qEnc b) +
      (QueryImpl.id' spec).liftTarget (StateT ℕ (OracleComp (unifSpec + spec))))
    (simulateQ spec.unbatch (adv.online σ puzzle))) 0

section advantage

variable [DecidableEq ι] [∀ t, SampleableType (spec.Range t)]

/-- The hiding advantage of `adv` against the capped challenger: the distance between the
probabilities that the capped hiding experiment returns `true` at hidden bits `true` and `false`,
against one lazily sampled random oracle starting from the empty cache. -/
noncomputable def cappedHidingAdvantage (tlp : TimeLockPuzzle spec Puzzle Key)
    (dem : DEMScheme (OracleComp (unifSpec + spec)) (Puzzle × Key) M C) (leak : M → Λ)
    (qEnc : ℕ) (adv : HidingAdversary spec Puzzle M C) : ℝ≥0∞ :=
  ((ProbCompRuntime.rom spec).evalDist
      (tlp.cappedHidingExperiment dem leak qEnc adv true)).boolDist
    ((ProbCompRuntime.rom spec).evalDist (tlp.cappedHidingExperiment dem leak qEnc adv false))

/-- The capped hiding advantage is the distance between the probabilities that the capped hiding
experiment returns `true` at the two hidden bits, against one lazily sampled random oracle. -/
theorem cappedHidingAdvantage_eq (tlp : TimeLockPuzzle spec Puzzle Key)
    (dem : DEMScheme (OracleComp (unifSpec + spec)) (Puzzle × Key) M C) (leak : M → Λ)
    (qEnc : ℕ) (adv : HidingAdversary spec Puzzle M C) :
    cappedHidingAdvantage tlp dem leak qEnc adv =
      ENNReal.absDiff
        ((ProbCompRuntime.rom spec).evalDist (tlp.cappedHidingExperiment dem leak qEnc adv true)
          {true})
        ((ProbCompRuntime.rom spec).evalDist (tlp.cappedHidingExperiment dem leak qEnc adv false)
          {true}) := by
  rw [cappedHidingAdvantage, Measure.boolDist]

end advantage

/-! ## The challenge-cap adapter -/

namespace HidingAdversary

/-- The handler of `HidingAdversary.capChallenges`, with the number of forwarded challenge
requests as state. A pair with equal leakage, asked while fewer than `qEnc` pairs have been
forwarded, is forwarded to the challenge oracle and advances the counter; every other challenge
request is answered locally with `none`. Local coins and rounds are forwarded unchanged. -/
@[expose]
def capChallengesImpl (leak : M → Λ) (qEnc : ℕ) :
    QueryImpl ((unifSpec + LeftOrRight.spec M C) + spec.batch)
      (StateT ℕ (OracleComp ((unifSpec + LeftOrRight.spec M C) + spec.batch)))
  | .inl (.inl n) =>
      monadLift (((unifSpec + LeftOrRight.spec M C) + spec.batch).query (.inl (.inl n)))
  | .inl (.inr mm) => LeftOrRight.cap leak qEnc
      (fun mm => liftM (((unifSpec + LeftOrRight.spec M C) + spec.batch).query (.inl (.inr mm))))
      mm
  | .inr ts => monadLift (((unifSpec + LeftOrRight.spec M C) + spec.batch).query (.inr ts))

/-- **The challenge-cap adapter.** The adversary `adv` with the challenger's cap moved to its own
side: its online phase runs through `HidingAdversary.capChallengesImpl` from the counter `0`, so
it forwards at most `qEnc` pairs with equal leakage to the challenge oracle and answers every
other challenge request itself with `none`. Its preprocessing phase, local coins and rounds are
those of `adv`.

The adapted adversary is within the encryption budget `qEnc`
(`HidingAdversary.makesAtMostQueries_capChallenges`) and within every round and point budget of
`adv` (`HidingAdversary.isQueryBound_capChallenges`), and its hiding experiment is the capped
hiding experiment of `adv` (`hidingExperiment_capChallenges`). A bound on the hiding advantage of
adversaries within an encryption budget therefore bounds the capped hiding advantage of every
adversary. -/
@[expose]
def capChallenges (adv : HidingAdversary spec Puzzle M C) (leak : M → Λ) (qEnc : ℕ) :
    HidingAdversary spec Puzzle M C where
  State := adv.State
  preprocess := adv.preprocess
  online σ puzzle := (simulateQ (capChallengesImpl leak qEnc) (adv.online σ puzzle)).run' 0

/-- The adapted adversary makes at most `qEnc` challenge queries, whatever `adv` asks. -/
theorem makesAtMostQueries_capChallenges (adv : HidingAdversary spec Puzzle M C)
    (leak : M → Λ) (qEnc : ℕ) : (adv.capChallenges leak qEnc).MakesAtMostQueries qEnc := by
  intro σ puzzle
  suffices h : ∀ {α : Type} (oa : OracleComp ((unifSpec + LeftOrRight.spec M C) + spec.batch) α)
      (j : ℕ), IsQueryBoundP ((simulateQ (capChallengesImpl leak qEnc) oa).run j)
        (· matches .inl (.inr _)) (qEnc - j) by
    have h' := h (adv.online σ puzzle) 0
    rw [Nat.sub_zero, ← isQueryBoundP_map_iff _ Prod.fst, ← StateT.run'_eq] at h'
    exact (isQueryBoundP_congr_pred fun _ => Iff.rfl).mp h'
  intro α oa
  induction oa using OracleComp.inductionOn with
  | pure x => intro j; simp
  | query_bind t mx ih =>
    intro j
    rcases t with (n | ⟨m₀, m₁⟩) | ts
    · simpa [capChallengesImpl] using fun u => ih u j
    · by_cases h : leak m₀ = leak m₁ ∧ j < qEnc
      · simpa [capChallengesImpl, LeftOrRight.run_cap_apply, h, Nat.sub_sub] using
          fun u => ih u (j + 1)
      · simpa [capChallengesImpl, LeftOrRight.run_cap_apply, h] using ih none j
    · simpa [capChallengesImpl] using fun u => ih u j

/-- The adapted adversary keeps the preprocessing budget and the online budget of `adv`:
challenge requests, forwarded or answered locally, cost no round and no point, and rounds are
forwarded unchanged. -/
theorem isQueryBound_capChallenges {adv : HidingAdversary spec Puzzle M C} {Q : ℕ}
    {b : ℕ × ℕ} (h : adv.IsQueryBound Q b) (leak : M → Λ) (qEnc : ℕ) :
    (adv.capChallenges leak qEnc).IsQueryBound Q b := by
  refine ⟨h.1, fun σ puzzle => ?_⟩
  have key := IsQueryBound.simulateQ_run_of_step (h.2 σ puzzle) (combine := (· + ·))
    (mapBudget := id) (stepBudget := fun t _ => onlineStep t)
    (impl := capChallengesImpl leak qEnc) (fun h₁ h₂ => isOnlineQueryBound_bind h₁ h₂)
    (fun t b s _ => ?_) (fun t b ht => ?_) 0
  · simpa [capChallenges, StateT.run'_eq, IsOnlineQueryBound, isQueryBound_map_iff] using key
  · rcases t with (n | ⟨m₀, m₁⟩) | ts
    · simp [capChallengesImpl, isQueryBound_map_iff]
    · rw [capChallengesImpl, LeftOrRight.run_cap_apply]
      split_ifs <;> simp [isQueryBound_map_iff]
    · simp [capChallengesImpl, isQueryBound_map_iff]
  · rcases t with n | ts
    · simp
    · simp only [onlineCanQuery_inr] at ht
      refine Prod.ext ?_ ?_ <;> simp <;> omega

end HidingAdversary

open HidingAdversary in
/-- **The challenge-cap bridge.** At each hidden bit, the hiding experiment of the adapted
adversary `adv.capChallenges leak qEnc` is the capped hiding experiment of `adv`, as a
computation. The two differ only in where the counter of accepted pairs lives, in the adversary's
handler or in the challenger, and both count the same pairs. -/
theorem hidingExperiment_capChallenges (tlp : TimeLockPuzzle spec Puzzle Key)
    (dem : DEMScheme (OracleComp (unifSpec + spec)) (Puzzle × Key) M C) (leak : M → Λ)
    (qEnc : ℕ) (adv : HidingAdversary spec Puzzle M C) (b : Bool) :
    tlp.hidingExperiment dem leak (adv.capChallenges leak qEnc) b =
      tlp.cappedHidingExperiment dem leak qEnc adv b := by
  simp only [hidingExperiment, cappedHidingExperiment, capChallenges]
  refine bind_congr fun σ => bind_congr fun pk => ?_
  rcases pk with ⟨puzzle, key⟩
  dsimp only
  rw [QueryImpl.simulateQ_simulateQ_unbatch, QueryImpl.simulateQ_simulateQ_unbatch,
    StateT.run'_eq, StateT.run'_eq, simulateQ_map, simulateQ_StateT_compose _ _ _ ?_]
  intro q s
  rcases q with (n | ⟨m₀, m₁⟩) | ts
  · simp only [add_apply_inl, QueryImpl.passthrough_add, QueryImpl.batch'_add, capChallengesImpl,
      StateT.run_monadLift, bind_pure_comp, simulateQ_map, simulateQ_query,
      OracleQuery.input_query, OracleQuery.cont_query, QueryImpl.add_apply_inl,
      PFunctor.Handler.liftTarget_apply, ofPFunctor_toPFunctor, QueryImpl.id'_apply, id_map,
      QueryImpl.batch'_apply_inl]
    rw [map_eq_bind_pure_comp]
    rfl
  · rw [capChallengesImpl, LeftOrRight.run_cap_apply]
    simp [LeftOrRight.cappedOracle, LeftOrRight.run_cap_apply]
  · simp only [add_apply_inr, QueryImpl.passthrough_add, QueryImpl.batch'_add, capChallengesImpl,
      StateT.run_monadLift, bind_pure_comp, simulateQ_map, simulateQ_query,
      OracleQuery.input_query, OracleQuery.cont_query, QueryImpl.add_apply_inr, id_map,
      QueryImpl.batch'_apply_inr, PFunctor.Handler.liftTarget_apply, ofPFunctor_toPFunctor,
      QueryImpl.id'_apply]
    exact (QueryImpl.run_batch_liftTarget _ ts s).symm

/-- **Branchwise bridge in the random oracle model.** At each hidden bit, the hiding experiment of
the adapted adversary and the capped hiding experiment of `adv` have the same law against one
lazily sampled random oracle. -/
theorem evalDist_hidingExperiment_capChallenges [DecidableEq ι]
    [∀ t, SampleableType (spec.Range t)] (tlp : TimeLockPuzzle spec Puzzle Key)
    (dem : DEMScheme (OracleComp (unifSpec + spec)) (Puzzle × Key) M C) (leak : M → Λ)
    (qEnc : ℕ) (adv : HidingAdversary spec Puzzle M C) (b : Bool) :
    (ProbCompRuntime.rom spec).evalDist
        (tlp.hidingExperiment dem leak (adv.capChallenges leak qEnc) b) =
      (ProbCompRuntime.rom spec).evalDist (tlp.cappedHidingExperiment dem leak qEnc adv b) := by
  rw [hidingExperiment_capChallenges]

/-- The capped hiding advantage of `adv` is the hiding advantage of the adapted adversary
`adv.capChallenges leak qEnc`, which is within the encryption budget `qEnc`. -/
theorem cappedHidingAdvantage_eq_hidingAdvantage_capChallenges [DecidableEq ι]
    [∀ t, SampleableType (spec.Range t)] (tlp : TimeLockPuzzle spec Puzzle Key)
    (dem : DEMScheme (OracleComp (unifSpec + spec)) (Puzzle × Key) M C) (leak : M → Λ)
    (qEnc : ℕ) (adv : HidingAdversary spec Puzzle M C) :
    tlp.cappedHidingAdvantage dem leak qEnc adv =
      hidingAdvantage tlp dem leak (adv.capChallenges leak qEnc) := by
  simp only [cappedHidingAdvantage, hidingAdvantage, evalDist_hidingExperiment_capChallenges]

end TimeLockPuzzle
