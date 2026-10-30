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

## Main statements

* `TimeLockPuzzle.hidingAdvantage_eq`: the hiding advantage is the distance between the
  probabilities that the two branches return `true` in the random oracle model.
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

end TimeLockPuzzle
