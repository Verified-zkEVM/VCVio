/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.TimeLockPuzzle

/-!
# The pointer-chain time-lock puzzle over typed oracles

The time-lock puzzle of Mahmoody, Moran and Vadhan (CRYPTO 2011) with an accumulated key, as
instantiated by leanSeal: `n` hash chains of `m` steps each, where each chain's start link after
the first is published only masked under a hash of the end of the chain before it, and the key is
a hash of all chain ends in order. The honest solver runs the chains one after the other.

The six oracles are independent and typed (`PointerChainPuzzle.oracleSpec`), over states `S`,
links `L` (an additive group, bytewise XOR in leanSeal), salts `Salt` and contexts `Ctx`. A
context is formed from the salt by `mkCtx`, and the accumulator starts at `initAcc ctx`.

| Oracle   | Point                 | Answer |
|----------|-----------------------|--------|
| `start`  | `Ctx × Fin n × L`     | `S`    |
| `step`   | `Salt × Fin n × S`    | `S`    |
| `mask`   | `Ctx × S`             | `L`    |
| `acc`    | `S × S`               | `S`    |
| `key`    | `Ctx × S`             | `S`    |
| `commit` | `Ctx × S`             | `S`    |

Chains are indexed from `0`. For a salt, links `x_i`, and `ctx = mkCtx salt`, chain `i` starts at
`s_i = start(ctx, i, x_i)` and takes `m` steps `y ↦ step(salt, i, y)` to its end `y_i`. The masks
are `μ_i = mask(ctx, y_i)` for `i < n - 1`, the accumulators `a_0 = initAcc ctx` and
`a_{i+1} = acc(a_i, y_i)`, the key `K = key(ctx, a_n)` and the commitment `C = commit(ctx, K)`.
The puzzle is the salt, `C`, `x_0` and the masked links `z_i = μ_i + x_{i+1}`.

All algorithms submit rounds of parallel queries (`OracleSpec.batch`), built with
`OracleComp.queryRound`, `OracleComp.queryRound₂` and `OracleComp.queryPoint`:

* `gen` draws the salt and the links, queries the `n` starts in one round, takes the `m` steps of
  all chains in parallel, queries the masks of all chains but the last together with `a_1`, then
  `a_2, …, a_n` one per round, then the key, then the commitment: `m + n + 3` rounds.
* `derive` follows the chains one after the other: for each chain its start, its `m` steps, and
  one round with its accumulator and, except for the last chain, its mask, which unmasks the next
  link; then the key. It holds the key after `keyRound n m = n (m + 2) + 1` rounds.
* `solve` checks the derived key against the commitment in one more round, for
  `n (m + 3) + 1` points in all.

The values the honest solver obtains, with the rounds in which it obtains them, are in
`VCVio/Schemes/PointerChainPuzzle/Path.lean`.

The shape forces sequential work. A chain is a sequence of `m` dependent hashes, so it takes `m`
rounds however many processors run it. The generator knows every link and runs all chains in
parallel, but the puzzle publishes only the first link: the start of chain `i + 1` is unmasked by
the end of chain `i`, so a solver cannot begin a chain before it has finished the previous one.
The key hashes the accumulator over all chain ends, so no chain can be skipped, and the commitment
lets the solver check the derived key. These are the paper's `Build` and `Open` (leanSeal SPEC §4
and §5), with the labelled hashes as separate typed oracles; the byte-level encoding into one hash
is in `VCVio/Schemes/PointerChainPuzzle/LeanSeal.lean`.

## Main statements

* `scheme_correct`: the solver returns the generated key with probability one.
* `isGenQueryBound_scheme`, `isOnlineQueryBound_derive`, `isSolveQueryBound_scheme`: the honest
  round and point counts.
-/

public section

open OracleSpec OracleComp

namespace PointerChainPuzzle

/-! ## The typed oracles -/

/-- The points of the six typed oracles of the pointer-chain puzzle with `n` chains. -/
inductive Point (n : ℕ) (S L Salt Ctx : Type)
  /-- The start of chain `i` from the context and its link. -/
  | start (ctx : Ctx) (i : Fin n) (x : L)
  /-- One step of chain `i`, keyed by the salt. -/
  | step (salt : Salt) (i : Fin n) (s : S)
  /-- The mask derived from the end of a chain. -/
  | mask (ctx : Ctx) (y : S)
  /-- Absorb a chain end into the accumulator. -/
  | acc (a y : S)
  /-- The key from the final accumulator. -/
  | key (ctx : Ctx) (a : S)
  /-- The commitment to the key. -/
  | commit (ctx : Ctx) (k : S)
  deriving DecidableEq

/-- The six typed oracles of the pointer-chain puzzle as one specification: masks are links, every
other answer is a state. -/
@[expose, reducible]
def oracleSpec (n : ℕ) (S L Salt Ctx : Type) : OracleSpec.{0, 0} (Point n S L Salt Ctx)
  | .mask _ _ => L
  | _ => S

variable {n m : ℕ} {S L Salt Ctx : Type}

instance [SampleableType S] [SampleableType L] (t : Point n S L Salt Ctx) :
    SampleableType ((oracleSpec n S L Salt Ctx).Range t) :=
  match t with
  | .start .. => inferInstanceAs (SampleableType S)
  | .step .. => inferInstanceAs (SampleableType S)
  | .mask .. => inferInstanceAs (SampleableType L)
  | .acc .. => inferInstanceAs (SampleableType S)
  | .key .. => inferInstanceAs (SampleableType S)
  | .commit .. => inferInstanceAs (SampleableType S)

/-- Programs that sample local coins and submit rounds of parallel queries to the pointer-chain
oracles. -/
abbrev RoundComp (n : ℕ) (S L Salt Ctx : Type) :=
  OracleComp (unifSpec + (oracleSpec n S L Salt Ctx).batch)

/-- A puzzle: the salt, the commitment to the key, the first link, and the masked links
`z_i = μ_i + x_{i+1}` for `i < n - 1`. -/
structure Puzzle (n : ℕ) (S L Salt : Type) where
  /-- The salt, from which the context is formed. -/
  salt : Salt
  /-- The commitment to the key. -/
  commitment : S
  /-- The link of the first chain. -/
  firstLink : L
  /-- The links of chains `1, …, n - 1`, each masked under the end of the chain before it. -/
  maskedLinks : Fin (n - 1) → L

/-! ## Counts -/

/-- The round in which the honest solver holds the key: `n (m + 2) + 1`. -/
@[expose]
def keyRound (n m : ℕ) : ℕ := n * (m + 2) + 1

/-- The number of points the honest solver queries, the commitment included: `n (m + 3) + 1`. -/
@[expose]
def solvePoints (n m : ℕ) : ℕ := n * (m + 3) + 1

/-- The number of rounds of the generator: `m + n + 3`. -/
@[expose]
def genRounds (n m : ℕ) : ℕ := m + n + 3

/-! ## Generation -/

lemma lt_of_le_sub_one [NeZero n] {k : ℕ} (h : k ≤ n - 1) : k < n :=
  Nat.lt_of_le_of_lt h (Nat.sub_one_lt (NeZero.ne n))

/-- Chain `i` as an index of the `n` chains, for `i < n - 1`. -/
@[expose]
def chainOf (i : Fin (n - 1)) : Fin n := ⟨i, by omega⟩

/-- The chain after chain `i`, for `i < n - 1`. -/
@[expose]
def nextChain (i : Fin (n - 1)) : Fin n := ⟨i + 1, by omega⟩

/-- The last chain. -/
@[expose]
def lastChain [NeZero n] : Fin n := ⟨n - 1, Nat.sub_one_lt (NeZero.ne n)⟩

/-- `k` rounds of steps on all chains in parallel, from the states `ys`. -/
@[expose]
def stepRounds (salt : Salt) : ℕ → (Fin n → S) → RoundComp n S L Salt Ctx (Fin n → S)
  | 0, ys => pure ys
  | k + 1, ys => do
      let ys' ← queryRound fun i => Point.step salt i (ys i)
      stepRounds salt k ys'

/-- Absorb the chain ends `ys k, ys (k + 1), …` into the accumulator `a`, one per round, for at
most `r` rounds and up to the last chain. -/
@[expose]
def accRounds (ys : Fin n → S) : ℕ → ℕ → S → RoundComp n S L Salt Ctx S
  | 0, _, a => pure a
  | r + 1, k, a =>
      if h : k < n then do
        let a' ← queryPoint (Point.acc (Salt := Salt) (Ctx := Ctx) a (ys ⟨k, h⟩))
        accRounds ys r (k + 1) a'
      else pure a

/-- The generator on a given salt and given links. -/
@[expose]
def genWith [NeZero n] (m : ℕ) (mkCtx : Salt → Ctx) (initAcc : Ctx → S) (salt : Salt)
    (xs : Fin n → L) [AddCommGroup L] : RoundComp n S L Salt Ctx (Puzzle n S L Salt × S) := do
  let ctx := mkCtx salt
  let ss ← queryRound fun i => Point.start (Salt := Salt) ctx i (xs i)
  let ys ← stepRounds salt m ss
  let masks : (Fin (n - 1) → L) × (Fin 1 → S) ←
    queryRound₂ (fun i : Fin (n - 1) => Point.mask (Salt := Salt) ctx (ys (chainOf i)))
      (fun _ : Fin 1 => Point.acc (Salt := Salt) (Ctx := Ctx) (initAcc ctx) (ys 0))
  let a ← accRounds ys (n - 1) 1 (masks.2 0)
  let key ← queryPoint (Point.key (Salt := Salt) ctx a)
  let commitment ← queryPoint (Point.commit (Salt := Salt) ctx key)
  return (⟨salt, commitment, xs 0, fun i => masks.1 i + xs (nextChain i)⟩, key)

/-- The generator: draw the salt and the links, and build the puzzle and its key. -/
@[expose]
def gen [NeZero n] (m : ℕ) (mkCtx : Salt → Ctx) (initAcc : Ctx → S) [AddCommGroup L]
    [SampleableType Salt] [SampleableType L] :
    RoundComp n S L Salt Ctx (Puzzle n S L Salt × S) := do
  let salt ← $ᵗ Salt
  let xs ← $ᵗ (Fin n → L)
  genWith m mkCtx initAcc salt xs

/-! ## Solving -/

/-- `k` steps of chain `i`, one per round, from the state `s`. -/
@[expose]
def stepsFrom (salt : Salt) (i : Fin n) : ℕ → S → RoundComp n S L Salt Ctx S
  | 0, s => pure s
  | k + 1, s => do
      let s' ← queryPoint (Point.step (L := L) (Ctx := Ctx) salt i s)
      stepsFrom salt i k s'

/-- Run chain `i` from its link `x`: the start and `m` steps, one per round. -/
@[expose]
def runChain (m : ℕ) (ctx : Ctx) (salt : Salt) (i : Fin n) (x : L) :
    RoundComp n S L Salt Ctx S := do
  let s ← queryPoint (Point.start (Salt := Salt) ctx i x)
  stepsFrom salt i m s

/-- Run chains `k, k + 1, …` before the last one, at most `r` of them, from the accumulator and
link `st`. After each chain one round queries its accumulator and its mask, which unmasks the
next link. -/
@[expose]
def maskedChains [AddCommGroup L] (m : ℕ) (mkCtx : Salt → Ctx) (puzzle : Puzzle n S L Salt) :
    ℕ → ℕ → S × L → RoundComp n S L Salt Ctx (S × L)
  | 0, _, st => pure st
  | r + 1, k, st =>
      if h : k < n - 1 then do
        let ctx := mkCtx puzzle.salt
        let y ← runChain m ctx puzzle.salt ⟨k, by omega⟩ st.2
        let am : (Fin 1 → S) × (Fin 1 → L) ←
          queryRound₂ (fun _ : Fin 1 => Point.acc (Salt := Salt) (Ctx := Ctx) st.1 y)
            (fun _ : Fin 1 => Point.mask (Salt := Salt) ctx y)
        maskedChains m mkCtx puzzle r (k + 1) (am.1 0, puzzle.maskedLinks ⟨k, h⟩ - am.2 0)
      else pure st

/-- The key-deriving solver: run the chains in order, unmasking each next link, absorb every
chain end into the accumulator, and query the key. -/
@[expose]
def derive [NeZero n] [AddCommGroup L] (m : ℕ) (mkCtx : Salt → Ctx) (initAcc : Ctx → S)
    (puzzle : Puzzle n S L Salt) : RoundComp n S L Salt Ctx S := do
  let ctx := mkCtx puzzle.salt
  let st ← maskedChains m mkCtx puzzle (n - 1) 0 (initAcc ctx, puzzle.firstLink)
  let y ← runChain m ctx puzzle.salt lastChain st.2
  let a ← queryPoint (Point.acc (Salt := Salt) (Ctx := Ctx) st.1 y)
  queryPoint (Point.key (Salt := Salt) ctx a)

/-- Check a key against the commitment of the puzzle in one round: `none` on a mismatch. -/
@[expose]
def check [DecidableEq S] (mkCtx : Salt → Ctx) (puzzle : Puzzle n S L Salt) (key : S) :
    RoundComp n S L Salt Ctx (Option S) := do
  let commitment : S ← queryPoint (Point.commit (Salt := Salt) (mkCtx puzzle.salt) key)
  return if commitment = puzzle.commitment then some key else none

/-- The solver: derive the key and check it against the commitment. -/
@[expose]
def solve [NeZero n] [AddCommGroup L] [DecidableEq S] (m : ℕ) (mkCtx : Salt → Ctx)
    (initAcc : Ctx → S) (puzzle : Puzzle n S L Salt) : RoundComp n S L Salt Ctx (Option S) :=
  derive m mkCtx initAcc puzzle >>= check mkCtx puzzle

/-- The pointer-chain puzzle with `n` chains of `m` steps as a time-lock puzzle. -/
@[expose]
def scheme (n m : ℕ) [NeZero n] (mkCtx : Salt → Ctx) (initAcc : Ctx → S) [AddCommGroup L]
    [DecidableEq S] [SampleableType Salt] [SampleableType L] :
    TimeLockPuzzle (oracleSpec n S L Salt Ctx) (Puzzle n S L Salt) S where
  gen := gen m mkCtx initAcc
  solve := solve m mkCtx initAcc

/-! ## Honest values

The values the honest algorithms compute when the six oracles are fixed functions. -/

/-- Six functions, one for each oracle of the pointer-chain puzzle. -/
structure Oracles (n : ℕ) (S L Salt Ctx : Type) where
  /-- The start oracle. -/
  start : Ctx → Fin n → L → S
  /-- The step oracle. -/
  step : Salt → Fin n → S → S
  /-- The mask oracle. -/
  mask : Ctx → S → L
  /-- The accumulator oracle. -/
  acc : S → S → S
  /-- The key oracle. -/
  key : Ctx → S → S
  /-- The commitment oracle. -/
  commit : Ctx → S → S

namespace Oracles

/-- The six functions as a deterministic implementation of the oracles. -/
@[expose]
def toImpl (O : Oracles n S L Salt Ctx) : QueryImpl (oracleSpec n S L Salt Ctx) Id
  | .start ctx i x => O.start ctx i x
  | .step salt i s => O.step salt i s
  | .mask ctx y => O.mask ctx y
  | .acc a y => O.acc a y
  | .key ctx a => O.key ctx a
  | .commit ctx k => O.commit ctx k

/-- The six functions of a deterministic implementation of the oracles. -/
@[expose]
def ofImpl (f : QueryImpl (oracleSpec n S L Salt Ctx) Id) : Oracles n S L Salt Ctx where
  start ctx i x := (f (.start ctx i x)).run
  step salt i s := (f (.step salt i s)).run
  mask ctx y := (f (.mask ctx y)).run
  acc a y := (f (.acc a y)).run
  key ctx a := (f (.key ctx a)).run
  commit ctx k := (f (.commit ctx k)).run

lemma toImpl_ofImpl (f : QueryImpl (oracleSpec n S L Salt Ctx) Id) : (ofImpl f).toImpl = f := by
  funext t
  cases t <;> rfl

end Oracles

section Honest

variable (m : ℕ) (mkCtx : Salt → Ctx) (initAcc : Ctx → S) (O : Oracles n S L Salt Ctx)

/-- The state of chain `i` after `k` steps from its link `x`; after `0` steps it is the chain
start. -/
@[expose]
def chainState (salt : Salt) (i : Fin n) (x : L) (k : ℕ) : S :=
  (O.step salt i)^[k] (O.start (mkCtx salt) i x)

/-- The end of chain `i` for the links `xs`. -/
@[expose]
def chainEnd (salt : Salt) (xs : Fin n → L) (i : Fin n) : S :=
  chainState mkCtx O salt i (xs i) m

/-- Absorb the values `ys 0, ys 1, …, ys (k - 1)` into the accumulator starting at `a`, stopping
at the last chain. -/
@[expose]
def accFold (a : S) (ys : Fin n → S) : ℕ → S
  | 0 => a
  | k + 1 => if h : k < n then O.acc (accFold a ys k) (ys ⟨k, h⟩) else accFold a ys k

/-- The accumulator after the first `k` chains, `a_k`. -/
@[expose]
def accAfter (salt : Salt) (xs : Fin n → L) (k : ℕ) : S :=
  accFold O (initAcc (mkCtx salt)) (chainEnd m mkCtx O salt xs) k

/-- The honest key for the salt and the links `xs`. -/
@[expose]
def honestKey (salt : Salt) (xs : Fin n → L) : S :=
  O.key (mkCtx salt) (accAfter m mkCtx initAcc O salt xs n)

/-- The honest puzzle for the salt and the links `xs`. -/
@[expose]
def honestPuzzle [NeZero n] [AddCommGroup L] (salt : Salt) (xs : Fin n → L) :
    Puzzle n S L Salt where
  salt := salt
  commitment := O.commit (mkCtx salt) (honestKey m mkCtx initAcc O salt xs)
  firstLink := xs 0
  maskedLinks i := O.mask (mkCtx salt) (chainEnd m mkCtx O salt xs (chainOf i)) +
    xs (nextChain i)

variable {m mkCtx initAcc O}

lemma accFold_succ_of_lt {a : S} {ys : Fin n → S} {k : ℕ} (h : k < n) :
    accFold O a ys (k + 1) = O.acc (accFold O a ys k) (ys ⟨k, h⟩) := by
  simp [accFold, h]

lemma accFold_add_of_le {a : S} {ys : Fin n → S} {k : ℕ} (h : n ≤ k) (j : ℕ) :
    accFold O a ys (k + j) = accFold O a ys k := by
  induction j with
  | zero => rfl
  | succ j ih =>
      have hj : ¬ k + j < n := by omega
      rw [← ih]
      change accFold O a ys (k + j + 1) = _
      simp only [accFold, hj, ↓reduceDIte]

/-- The oracles `O` answering every point, rounds point by point. -/
local notation "T" => QueryImpl.batch' (unifFwdAnswerImpl (Oracles.toImpl O))

lemma simulateQ_stepRounds (salt : Salt) (k : ℕ) (ys : Fin n → S) :
    simulateQ T (stepRounds (L := L) (Ctx := Ctx) salt k ys) =
      pure fun i => (O.step salt i)^[k] (ys i) := by
  induction k generalizing ys with
  | zero => rfl
  | succ k ih =>
      rw [stepRounds, simulateQ_bind, simulateQ_queryRound, pure_bind]
      exact ih _

lemma simulateQ_accRounds (a : S) (ys : Fin n → S) (r k : ℕ) :
    simulateQ T (accRounds (L := L) (Salt := Salt) (Ctx := Ctx) ys r k (accFold O a ys k)) =
      pure (accFold O a ys (k + r)) := by
  induction r generalizing k with
  | zero => rfl
  | succ r ih =>
      rw [accRounds]
      split_ifs with h
      · rw [simulateQ_bind, simulateQ_queryPoint, pure_bind]
        change simulateQ T (accRounds ys r (k + 1) (O.acc (accFold O a ys k) (ys ⟨k, h⟩))) = _
        rw [← accFold_succ_of_lt h, ih, Nat.add_right_comm, Nat.add_assoc]
      · rw [simulateQ_pure, accFold_add_of_le (k := k) (by omega) (r + 1)]

lemma simulateQ_accRounds_of_eq (a : S) (ys : Fin n → S) (r k : ℕ) {a' : S}
    (ha : a' = accFold O a ys k) :
    simulateQ T (accRounds (L := L) (Salt := Salt) (Ctx := Ctx) ys r k a') =
      pure (accFold O a ys (k + r)) := by
  rw [ha, simulateQ_accRounds]

lemma simulateQ_stepsFrom (salt : Salt) (i : Fin n) (k : ℕ) (s : S) :
    simulateQ T (stepsFrom (L := L) (Ctx := Ctx) salt i k s) = pure ((O.step salt i)^[k] s) := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
      rw [stepsFrom, simulateQ_bind, simulateQ_queryPoint, pure_bind]
      exact ih _

lemma simulateQ_runChain (ctx : Ctx) (salt : Salt) (i : Fin n) (x : L) :
    simulateQ T (runChain m ctx salt i x) = pure ((O.step salt i)^[m] (O.start ctx i x)) := by
  rw [runChain, simulateQ_bind, simulateQ_queryPoint, pure_bind]
  exact simulateQ_stepsFrom salt i m _

lemma simulateQ_genWith [NeZero n] [AddCommGroup L] (salt : Salt) (xs : Fin n → L) :
    simulateQ T (genWith m mkCtx initAcc salt xs) =
      pure (honestPuzzle m mkCtx initAcc O salt xs, honestKey m mkCtx initAcc O salt xs) := by
  rw [genWith]
  simp only [simulateQ_bind, simulateQ_queryRound, pure_bind]
  rw [simulateQ_stepRounds, pure_bind]
  simp only [simulateQ_queryRound₂, pure_bind]
  rw [simulateQ_accRounds_of_eq (initAcc (mkCtx salt)) _ _ 1 ?ha, pure_bind,
    Nat.add_sub_cancel' NeZero.one_le]
  · simp only [simulateQ_queryPoint, pure_bind, simulateQ_pure]
    rfl
  · rw [accFold_succ_of_lt (NeZero.pos n)]
    rfl

lemma accAfter_succ_of_lt {salt : Salt} {xs : Fin n → L} {k : ℕ} (h : k < n) :
    accAfter m mkCtx initAcc O salt xs (k + 1) =
      O.acc (accAfter m mkCtx initAcc O salt xs k) (chainEnd m mkCtx O salt xs ⟨k, h⟩) :=
  accFold_succ_of_lt h

lemma simulateQ_maskedChains [NeZero n] [AddCommGroup L] (salt : Salt) (xs : Fin n → L)
    (r k : ℕ) (hk : k + r ≤ n - 1) {st : S × L}
    (hst : st = (accAfter m mkCtx initAcc O salt xs k, xs ⟨k, lt_of_le_sub_one (by omega)⟩)) :
    simulateQ T (maskedChains m mkCtx (honestPuzzle m mkCtx initAcc O salt xs) r k st) =
      pure (accAfter m mkCtx initAcc O salt xs (k + r), xs ⟨k + r, lt_of_le_sub_one hk⟩) := by
  induction r generalizing k st with
  | zero => subst hst; rfl
  | succ r ih =>
      subst hst
      have hk' : k < n - 1 := by omega
      rw [maskedChains]
      simp only [hk', ↓reduceDIte, simulateQ_bind, simulateQ_runChain, pure_bind,
        simulateQ_queryRound₂]
      rw [ih (k + 1) (by omega) ?_]
      · simp only [Nat.add_right_comm k 1 r, Nat.add_assoc]
      · refine Prod.ext ?_ ?_
        · exact (accAfter_succ_of_lt (lt_of_le_sub_one (by omega))).symm
        · exact add_sub_cancel_left _ _

lemma simulateQ_derive [NeZero n] [AddCommGroup L] (salt : Salt) (xs : Fin n → L) :
    simulateQ T (derive m mkCtx initAcc (honestPuzzle m mkCtx initAcc O salt xs)) =
      pure (honestKey m mkCtx initAcc O salt xs) := by
  rw [derive]
  simp only [simulateQ_bind]
  rw [simulateQ_maskedChains salt xs (n - 1) 0 (by omega) (by rfl), pure_bind]
  simp only [simulateQ_runChain, simulateQ_queryPoint, pure_bind]
  have hn : n - 1 + 1 = n := Nat.sub_add_cancel NeZero.one_le
  have h := accAfter_succ_of_lt (m := m) (mkCtx := mkCtx) (initAcc := initAcc) (O := O)
    (salt := salt) (xs := xs) (Nat.sub_one_lt (NeZero.ne n))
  rw [hn] at h
  simp only [Oracles.toImpl, Id.run, Nat.zero_add, honestKey, h]
  rfl

lemma simulateQ_check [DecidableEq S] (puzzle : Puzzle n S L Salt) (key : S) :
    simulateQ T (check mkCtx puzzle key) =
      pure (if O.commit (mkCtx puzzle.salt) key = puzzle.commitment then some key else none) := by
  simp only [check, simulateQ_bind, simulateQ_queryPoint, pure_bind, simulateQ_pure]
  rfl

lemma simulateQ_solve [NeZero n] [AddCommGroup L] [DecidableEq S] (salt : Salt)
    (xs : Fin n → L) :
    simulateQ T (solve m mkCtx initAcc (honestPuzzle m mkCtx initAcc O salt xs)) =
      pure (some (honestKey m mkCtx initAcc O salt xs)) := by
  rw [solve, simulateQ_bind, simulateQ_derive, pure_bind, simulateQ_check]
  simp [honestPuzzle]

end Honest

/-! ## Honest round and point counts -/

section Counts

lemma isOnlineQueryBound_stepRounds (salt : Salt) (k : ℕ) (ys : Fin n → S) :
    IsOnlineQueryBound (stepRounds (L := L) (Ctx := Ctx) salt k ys) (k, k * n) := by
  induction k generalizing ys with
  | zero => exact isOnlineQueryBound_pure _ _
  | succ k ih =>
      rw [stepRounds]
      exact isOnlineQueryBound_bind_le (1, n) (k, k * n) (isOnlineQueryBound_queryRound _) ih
        ⟨by omega, by rw [Nat.succ_mul]; omega⟩

lemma isOnlineQueryBound_accRounds (ys : Fin n → S) (r k : ℕ) (a : S) :
    IsOnlineQueryBound (accRounds (L := L) (Salt := Salt) (Ctx := Ctx) ys r k a) (r, r) := by
  induction r generalizing k a with
  | zero => exact isOnlineQueryBound_pure _ _
  | succ r ih =>
      rw [accRounds]
      split_ifs
      · exact isOnlineQueryBound_bind_le (1, 1) (r, r) (isOnlineQueryBound_queryPoint _)
          (fun a' => ih (k + 1) a') ⟨by omega, by omega⟩
      · exact isOnlineQueryBound_pure _ _

lemma isOnlineQueryBound_genWith [NeZero n] [AddCommGroup L] (m : ℕ) (mkCtx : Salt → Ctx)
    (initAcc : Ctx → S) (salt : Salt) (xs : Fin n → L) :
    IsOnlineQueryBound (genWith m mkCtx initAcc salt xs) (genRounds n m, solvePoints n m) := by
  have hn := NeZero.one_le (n := n)
  have hmul : n * (m + 3) = m * n + 3 * n := by ring
  rw [genWith]
  refine isOnlineQueryBound_bind_le (1, n) (m + n + 2, m * n + 2 * n + 1)
    (isOnlineQueryBound_queryRound _) (fun ss => ?_)
    ⟨by simp only [genRounds]; omega, by simp only [solvePoints]; omega⟩
  refine isOnlineQueryBound_bind_le (m, m * n) (n + 2, 2 * n + 1)
    (isOnlineQueryBound_stepRounds _ _ _) (fun ys => ?_) ⟨by omega, by omega⟩
  refine isOnlineQueryBound_bind_le (1, n - 1 + 1) (n + 1, n + 1)
    (isOnlineQueryBound_queryRound₂ _ _) (fun masks => ?_) ⟨by omega, by omega⟩
  refine isOnlineQueryBound_bind_le (n - 1, n - 1) (2, 2)
    (isOnlineQueryBound_accRounds _ _ _ _) (fun a => ?_) ⟨by omega, by omega⟩
  refine isOnlineQueryBound_bind_le (1, 1) (1, 1)
    (isOnlineQueryBound_queryPoint _) (fun key => ?_) ⟨le_rfl, le_rfl⟩
  exact isOnlineQueryBound_bind_le (1, 1) (0, 0)
    (isOnlineQueryBound_queryPoint _) (fun _ => isOnlineQueryBound_pure _ _) ⟨le_rfl, le_rfl⟩

/-- The generator submits `m + n + 3` rounds holding `n (m + 3) + 1` points. -/
theorem isOnlineQueryBound_gen [NeZero n] [AddCommGroup L] (m : ℕ) (mkCtx : Salt → Ctx)
    (initAcc : Ctx → S) [SampleableType Salt] [SampleableType L] :
    IsOnlineQueryBound (gen (L := L) m mkCtx initAcc (n := n))
      (genRounds n m, solvePoints n m) := by
  rw [gen]
  refine isOnlineQueryBound_bind_le (0, 0) (genRounds n m, solvePoints n m)
    (isOnlineQueryBound_liftComp ($ᵗ Salt) (0, 0)) (fun salt => ?_) ⟨by omega, by omega⟩
  exact isOnlineQueryBound_bind_le (0, 0) (genRounds n m, solvePoints n m)
    (isOnlineQueryBound_liftComp ($ᵗ (Fin n → L)) (0, 0))
    (fun xs => isOnlineQueryBound_genWith m mkCtx initAcc salt xs) ⟨by omega, by omega⟩

lemma isOnlineQueryBound_stepsFrom (salt : Salt) (i : Fin n) (k : ℕ) (s : S) :
    IsOnlineQueryBound (stepsFrom (L := L) (Ctx := Ctx) salt i k s) (k, k) := by
  induction k generalizing s with
  | zero => exact isOnlineQueryBound_pure _ _
  | succ k ih =>
      rw [stepsFrom]
      exact isOnlineQueryBound_bind_le (1, 1) (k, k) (isOnlineQueryBound_queryPoint _) ih
        ⟨by omega, by omega⟩

lemma isOnlineQueryBound_runChain (m : ℕ) (ctx : Ctx) (salt : Salt) (i : Fin n) (x : L) :
    IsOnlineQueryBound (runChain (S := S) m ctx salt i x) (m + 1, m + 1) := by
  rw [runChain]
  exact isOnlineQueryBound_bind_le (1, 1) (m, m) (isOnlineQueryBound_queryPoint _)
    (isOnlineQueryBound_stepsFrom salt i m) ⟨by omega, by omega⟩

lemma isOnlineQueryBound_maskedChains [AddCommGroup L] (m : ℕ) (mkCtx : Salt → Ctx)
    (puzzle : Puzzle n S L Salt) (r k : ℕ) (st : S × L) :
    IsOnlineQueryBound (maskedChains (Ctx := Ctx) m mkCtx puzzle r k st)
      (r * (m + 2), r * (m + 3)) := by
  induction r generalizing k st with
  | zero => exact isOnlineQueryBound_pure _ _
  | succ r ih =>
      rw [maskedChains]
      split_ifs
      · refine isOnlineQueryBound_bind_le (m + 1, m + 1) (r * (m + 2) + 1, r * (m + 3) + 2)
          (isOnlineQueryBound_runChain _ _ _ _ _) (fun y => ?_)
          ⟨by simp only [Nat.add_one_mul]; omega, by simp only [Nat.add_one_mul]; omega⟩
        exact isOnlineQueryBound_bind_le (1, 1 + 1) (r * (m + 2), r * (m + 3))
          (isOnlineQueryBound_queryRound₂ _ _) (fun am => ih (k + 1) _) ⟨by omega, by omega⟩
      · exact isOnlineQueryBound_pure _ _

/-- The key-deriving solver holds the key after `keyRound n m = n (m + 2) + 1` rounds, having
queried `n (m + 3)` points. -/
theorem isOnlineQueryBound_derive [NeZero n] [AddCommGroup L] (m : ℕ) (mkCtx : Salt → Ctx)
    (initAcc : Ctx → S) (puzzle : Puzzle n S L Salt) :
    IsOnlineQueryBound (derive (Ctx := Ctx) m mkCtx initAcc puzzle)
      (keyRound n m, n * (m + 3)) := by
  obtain ⟨n', hn'⟩ : ∃ k, n = k + 1 := ⟨n - 1, (Nat.sub_add_cancel NeZero.one_le).symm⟩
  have h₁ : (n - 1) * (m + 2) + (m + 3) = keyRound n m := by
    simp only [keyRound, hn', Nat.add_sub_cancel]; ring
  have h₂ : (n - 1) * (m + 3) + (m + 3) = n * (m + 3) := by
    simp only [hn', Nat.add_sub_cancel]; ring
  rw [derive]
  refine isOnlineQueryBound_bind_le ((n - 1) * (m + 2), (n - 1) * (m + 3)) (m + 3, m + 3)
    (isOnlineQueryBound_maskedChains _ _ _ _ _ _) (fun st => ?_) ⟨h₁.le, h₂.le⟩
  refine isOnlineQueryBound_bind_le (m + 1, m + 1) (2, 2)
    (isOnlineQueryBound_runChain _ _ _ _ _) (fun y => ?_) ⟨by omega, by omega⟩
  exact isOnlineQueryBound_bind_le (1, 1) (1, 1) (isOnlineQueryBound_queryPoint _)
    (fun a => isOnlineQueryBound_queryPoint _) ⟨le_rfl, le_rfl⟩

lemma isOnlineQueryBound_check [DecidableEq S] (mkCtx : Salt → Ctx) (puzzle : Puzzle n S L Salt)
    (key : S) : IsOnlineQueryBound (check (Ctx := Ctx) mkCtx puzzle key) (1, 1) := by
  rw [check]
  exact isOnlineQueryBound_bind_le (1, 1) (0, 0) (isOnlineQueryBound_queryPoint _)
    (fun _ => isOnlineQueryBound_pure _ _) ⟨le_rfl, le_rfl⟩

/-- The solver finishes after `keyRound n m + 1` rounds, having queried
`solvePoints n m = n (m + 3) + 1` points. -/
theorem isOnlineQueryBound_solve [NeZero n] [AddCommGroup L] [DecidableEq S] (m : ℕ)
    (mkCtx : Salt → Ctx) (initAcc : Ctx → S) (puzzle : Puzzle n S L Salt) :
    IsOnlineQueryBound (solve (Ctx := Ctx) m mkCtx initAcc puzzle)
      (keyRound n m + 1, solvePoints n m) :=
  isOnlineQueryBound_bind_le _ (1, 1) (isOnlineQueryBound_derive m mkCtx initAcc puzzle)
    (isOnlineQueryBound_check mkCtx puzzle) ⟨le_rfl, le_rfl⟩

theorem isGenQueryBound_scheme [NeZero n] [AddCommGroup L] (m : ℕ) (mkCtx : Salt → Ctx)
    (initAcc : Ctx → S) [DecidableEq S] [SampleableType Salt] [SampleableType L] :
    (scheme n m mkCtx initAcc (L := L)).IsGenQueryBound (genRounds n m, solvePoints n m) :=
  isOnlineQueryBound_gen m mkCtx initAcc

theorem isSolveQueryBound_scheme [NeZero n] [AddCommGroup L] (m : ℕ) (mkCtx : Salt → Ctx)
    (initAcc : Ctx → S) [DecidableEq S] [SampleableType Salt] [SampleableType L] :
    (scheme n m mkCtx initAcc (L := L)).IsSolveQueryBound (keyRound n m + 1, solvePoints n m) :=
  isOnlineQueryBound_solve m mkCtx initAcc

end Counts

/-! ## Correctness -/

/-- The pointer-chain puzzle is perfectly correct: run against one lazily sampled random oracle,
the solver returns the generated key with probability one. -/
theorem scheme_correct [NeZero n] (m : ℕ) (mkCtx : Salt → Ctx) (initAcc : Ctx → S)
    [AddCommGroup L] [DecidableEq S] [DecidableEq L] [DecidableEq Salt] [DecidableEq Ctx]
    [SampleableType S] [SampleableType L] [SampleableType Salt] :
    (scheme n m mkCtx initAcc (L := L)).Correct := by
  rw [TimeLockPuzzle.Correct, ProbCompRuntime.rom_evalDist,
    show ({true} : Set Bool) = {b | b = true} from rfl,
    evalDist_apply_setOf_simulateQ_romImpl_run'_eq_one_iff]
  intro f _
  rw [evalDist_apply_setOf_eq_one_iff_forall_mem_support, TimeLockPuzzle.correctnessExperiment,
    QueryImpl.simulateQ_simulateQ_unbatch, ← Oracles.toImpl_ofImpl f]
  intro b hb
  simp only [scheme, gen, bind_assoc, simulateQ_bind, simulateQ_genWith, pure_bind,
    simulateQ_solve, simulateQ_pure, support_bind, Set.mem_iUnion] at hb
  obtain ⟨_, _, _, _, hb⟩ := hb
  simpa using hb

end PointerChainPuzzle
