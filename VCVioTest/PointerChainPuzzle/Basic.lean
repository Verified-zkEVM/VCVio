/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.TimeLockPuzzle
public import VCVio.Schemes.PointerChainPuzzle.Path
import all VCVio.Schemes.PointerChainPuzzle.Basic
import all VCVio.Schemes.PointerChainPuzzle.Path

/-!
# The pointer-chain puzzle on small parameters

Runs of the pointer-chain puzzle over small finite types, with concrete oracles and a handler that
records every round: the solver recovers the generated key; the generator, the key derivation and
the solver use the stated number of rounds and points, for a single chain (`n = 1`), for `n = 2`,
and for leanSeal's `n = 3`, `m = 2` parameters (the key in round 13, the check in round 14, the
generator in 8 rounds); and the honest solver queries the path input of every path value in its
round `ρ`. The checks reduce the derived decidable equality of points and path values, so the
scheme modules are imported with `import all`; `TimeLockPuzzle` is imported only publicly, and
its delay advantage is rewritten through the public equation `delayAdvantage_eq`.
-/

public section

open OracleComp OracleSpec PointerChainPuzzle

namespace VCVioTest.PointerChainPuzzle.Basic

/-- States are `Fin 11`, links `Fin 5`, salts and contexts `Fin 3`. -/
abbrev S := Fin 11

/-- Links. -/
abbrev L := Fin 5

/-- Salts and contexts. -/
abbrev Salt := Fin 3

/-- Reduce a natural number to a state. -/
def toS (k : ℕ) : S := ⟨k % 11, Nat.mod_lt _ (by decide)⟩

/-- The context of a salt. -/
def mkCtx (salt : Salt) : Salt := salt + 1

/-- The initial accumulator of a context. -/
def initAcc (ctx : Salt) : S := toS (ctx + 6)

/-- Concrete oracles, each mixing all of its inputs. -/
def oracles (n : ℕ) : Oracles n S L Salt Salt where
  start ctx i x := toS (1 + ctx + 2 * i + 3 * x)
  step salt i s := toS (2 * s + salt + 5 * i + 1)
  mask ctx y := ⟨(y + ctx) % 5, Nat.mod_lt _ (by decide)⟩
  acc a y := toS (3 * a + y + 1)
  key ctx a := toS (a * a + ctx + 4)
  commit ctx k := toS (7 * k + ctx + 2)

/-- Answer local coins with `0` and every round from `oracles n`, recording the points of each
round in order. -/
def recordRounds (n : ℕ) :
    QueryImpl (unifSpec + (oracleSpec n S L Salt Salt).batch)
      (StateM (List (List (Point n S L Salt Salt)))) :=
  QueryImpl.add (fun _ => pure 0) fun ts => do
    modify (· ++ [ts])
    pure ((oracles n).toImpl.batch ts).run

/-- Run a program against `recordRounds`, returning its output and its rounds. -/
def record {n : ℕ} {α : Type} (oa : RoundComp n S L Salt Salt α) :
    α × List (List (Point n S L Salt Salt)) :=
  ((simulateQ (recordRounds n) oa).run []).run

/-- The number of rounds and of points of a run. -/
def counts {α : Type} {P : Type} (r : α × List (List P)) : ℕ × ℕ :=
  (r.2.length, (r.2.map List.length).sum)

/-- The fixed salt of the runs below. -/
def salt₀ : Salt := 2

/-- The fixed links of the runs below, `x_i = i + 1`. -/
def links (n : ℕ) : Fin n → L := fun i => ⟨(i + 1) % 5, Nat.mod_lt _ (by decide)⟩

/-- Generate a puzzle from `salt₀` and `links n`, then solve it. -/
def genThenSolve (n m : ℕ) [NeZero n] : RoundComp n S L Salt Salt (S × Option S) := do
  let pk ← genWith m mkCtx initAcc salt₀ (links n)
  let key' ← solve m mkCtx initAcc pk.1
  pure (pk.2, key')

/-- The honest puzzle for `salt₀` and `links n`. -/
def puzzle₀ (n m : ℕ) [NeZero n] : Puzzle n S L Salt :=
  honestPuzzle m mkCtx initAcc (oracles n) salt₀ (links n)

/-! ## Counts -/

example : keyRound 2 2 = 9 := rfl
example : solvePoints 2 2 = 11 := rfl
example : genRounds 2 2 = 7 := rfl

/-- leanSeal's parameters: the key in round 13, the check in round 14, the generator in 8. -/
example : keyRound 3 2 = 13 := rfl
example : keyRound 3 2 + 1 = 14 := rfl
example : solvePoints 3 2 = 16 := rfl
example : genRounds 3 2 = 8 := rfl

example : (scheme 3 2 mkCtx initAcc (L := L)).IsGenQueryBound (8, 16) :=
  isGenQueryBound_scheme 2 mkCtx initAcc

example : (scheme 3 2 mkCtx initAcc (L := L)).IsSolveQueryBound (14, 16) :=
  isSolveQueryBound_scheme 2 mkCtx initAcc

example (puzzle : Puzzle 3 S L Salt) :
    IsOnlineQueryBound (derive (Ctx := Salt) 2 mkCtx initAcc puzzle) (13, 15) :=
  isOnlineQueryBound_derive 2 mkCtx initAcc puzzle

/-! ## The delay advantage -/

/-- The delay advantage against the puzzle rewrites, through an ordinary import, to the
probability that the delay experiment returns `true`. -/
example (adv : TimeLockPuzzle.Adversary (oracleSpec 2 S L Salt Salt) (Puzzle 2 S L Salt) S) :
    TimeLockPuzzle.delayAdvantage (scheme 2 2 mkCtx initAcc (L := L)) adv =
      (ProbCompRuntime.rom _).evalDist
        ((scheme 2 2 mkCtx initAcc (L := L)).delayExperiment adv) {true} := by
  rw [TimeLockPuzzle.delayAdvantage_eq]

/-! ## Runs with a single chain, `n = 1`, `m = 2` -/

example : keyRound 1 2 = 5 := rfl
example : solvePoints 1 2 = 6 := rfl
example : genRounds 1 2 = 6 := rfl

/-- The solver returns the generated key; generating and solving take `6 + 6` rounds of one
point each. -/
example : (record (genThenSolve 1 2)).1.2 = some (record (genThenSolve 1 2)).1.1 := by
  decide +kernel

example : counts (record (genThenSolve 1 2)) = (12, 12) := by decide +kernel

/-- The generator takes `m + n + 3 = 6` rounds and `n (m + 3) + 1 = 6` points. -/
example : counts (record (genWith 2 mkCtx initAcc salt₀ (links 1))) = (6, 6) := by decide +kernel

/-- The key derivation holds the key after `keyRound 1 2 = 5` rounds, the solver checks it in
round 6. -/
example : counts (record (derive 2 mkCtx initAcc (puzzle₀ 1 2))) = (5, 5) := by decide +kernel

example : counts (record (solve 2 mkCtx initAcc (puzzle₀ 1 2))) = (6, 6) := by decide +kernel

/-- With one chain the path input of every path value is still queried in its round `ρ`. -/
example : ∀ v : PathValue 1 2,
    pathInput 2 mkCtx initAcc (puzzle₀ 1 2)
        (honestValue 2 mkCtx initAcc (oracles 1) salt₀ (links 1)) v ∈
      (record (solve 2 mkCtx initAcc (puzzle₀ 1 2))).2.getD (v.rho - 1) [] := by
  decide +kernel

/-! ## Runs with `n = 2`, `m = 2` -/

/-- Correctness against one lazily sampled random oracle. -/
example : (scheme 2 2 mkCtx initAcc (L := L)).Correct := scheme_correct 2 mkCtx initAcc

/-- The solver returns the generated key. -/
example : (record (genThenSolve 2 2)).1.2 = some (record (genThenSolve 2 2)).1.1 := by
  decide +kernel

/-- The generator takes `m + n + 3 = 7` rounds and `n (m + 3) + 1 = 11` points. -/
example : counts (record (genWith 2 mkCtx initAcc salt₀ (links 2))) = (7, 11) := by decide +kernel

/-- The key derivation holds the key after `keyRound 2 2 = 9` rounds and `n (m + 3) = 10`
points, the last round asking for the key. -/
example : counts (record (derive 2 mkCtx initAcc (puzzle₀ 2 2))) = (9, 10) := by decide +kernel

/-- The solver takes one more round, `10`, and `solvePoints 2 2 = 11` points. -/
example : counts (record (solve 2 mkCtx initAcc (puzzle₀ 2 2))) = (10, 11) := by decide +kernel

/-- On the honest puzzle the solver returns the honest key. -/
example : (record (solve 2 mkCtx initAcc (puzzle₀ 2 2))).1 =
    some (honestKey 2 mkCtx initAcc (oracles 2) salt₀ (links 2)) := by decide +kernel

/-- On a puzzle with a wrong commitment the solver rejects. -/
example : (record (solve 2 mkCtx initAcc
    { puzzle₀ 2 2 with commitment := (puzzle₀ 2 2).commitment + 1 })).1 = none := by decide +kernel

/-! ## Runs with leanSeal's `n = 3`, `m = 2` -/

/-- The solver returns the generated key. -/
example : (record (genThenSolve 3 2)).1.2 = some (record (genThenSolve 3 2)).1.1 := by
  decide +kernel

/-- The generator takes 8 rounds. -/
example : counts (record (genWith 2 mkCtx initAcc salt₀ (links 3))) = (8, 16) := by decide +kernel

/-- The key derivation takes 13 rounds, the last of which is the key query alone. -/
example : counts (record (derive 2 mkCtx initAcc (puzzle₀ 3 2))) = (13, 15) := by decide +kernel

example : (record (derive 2 mkCtx initAcc (puzzle₀ 3 2))).2.getLast? =
    some [.key (mkCtx salt₀) (accAfter 2 mkCtx initAcc (oracles 3) salt₀ (links 3) 3)] := by
  decide +kernel

/-- The solver takes 14 rounds, the last of which is the commitment check. -/
example : counts (record (solve 2 mkCtx initAcc (puzzle₀ 3 2))) = (14, 16) := by decide +kernel

example : (record (solve 2 mkCtx initAcc (puzzle₀ 3 2))).2.getLast? =
    some [.commit (mkCtx salt₀) (honestKey 2 mkCtx initAcc (oracles 3) salt₀ (links 3))] := by
  decide +kernel

/-! ## Path values -/

example : Fintype.card (PathValue 3 2) = solvePoints 3 2 := PathValue.card_eq

example : Fintype.card (PathValue 3 2) = 16 := by decide +kernel

example : PathValue.rho (.key : PathValue 3 2) = 13 := rfl

/-- Every path value but `s_0` is received one round after its last predecessor. -/
example : ∀ v : PathValue 3 2, v ≠ PathValue.firstStart →
    v.rho = (v.preds.sup PathValue.rho) + 1 := by decide +kernel

/-- The rounds of the path values are the rounds of the solver. -/
example : (Finset.univ.image (PathValue.rho (n := 3) (m := 2))) = Finset.Icc 1 14 := by
  decide +kernel

/-- The honest solver queries the path input of every path value, formed from the honest values,
in the round `ρ` of that value. -/
example : ∀ v : PathValue 3 2,
    pathInput 2 mkCtx initAcc (puzzle₀ 3 2)
        (honestValue 2 mkCtx initAcc (oracles 3) salt₀ (links 3)) v ∈
      (record (solve 2 mkCtx initAcc (puzzle₀ 3 2))).2.getD (v.rho - 1) [] := by
  decide +kernel

end VCVioTest.PointerChainPuzzle.Basic
