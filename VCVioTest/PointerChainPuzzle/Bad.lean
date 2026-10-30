/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.Schemes.PointerChainPuzzle.Bad
import all VCVio.Schemes.PointerChainPuzzle.Basic
import all VCVio.Schemes.PointerChainPuzzle.Path
import all VCVio.Schemes.PointerChainPuzzle.Ideal
import all VCVio.Schemes.PointerChainPuzzle.Handler

/-!
# Bad events of the ideal experiment on small parameters

Checks of Claim 3 for the pointer-chain puzzle:

* the bound `prEvent_idealExperiment_bad_le` instantiates for two chains of one step (`n = 2`,
  `m = 1`) over `S = Fin 11`, `L = Fin 5` and `Salt = Fin 3`, where it reads
  `Q_on / 5 + Q_pre / 15 + ((Q_pre + Q_on) 9 + 81) / 11`;
* for one chain (`n = 1`) the link term `Q_on / |L|` is absent;
* the case split on a concrete labelling: the start of the second chain has the mask `μ_0` as its
  only predecessor (case 3), the start of a single chain has none, a key query against nothing
  reached hits (case 4), and distinct path values have distinct path inputs (no collision).

The concrete checks reduce the derived decidable equality of points and path values and the
definitions of path inputs, so the scheme modules are imported with `import all`. The answer types
are sampled through `SampleableType.Fin`, so loading this module enumerates no type.
-/

public section

open OracleComp OracleSpec PointerChainPuzzle
open scoped ENNReal

namespace VCVioTest.PointerChainPuzzle.Bad

/-- States are `Fin 11`. -/
abbrev S := Fin 11

/-- Links are `Fin 5`. -/
abbrev L := Fin 5

/-- Salts and contexts are `Fin 3`. -/
abbrev Salt := Fin 3

/-- The context of a salt. -/
def mkCtx (salt : Salt) : Salt := salt + 1

/-- The initial accumulator of a context. -/
def initAcc (ctx : Salt) : S := ⟨ctx.val + 6, by omega⟩

/-- Adding one is injective on `Fin 3`. -/
lemma mkCtx_injective : Function.Injective mkCtx := fun a b h => by
  simpa [mkCtx] using h

/-! ## Claim 3 at small parameters -/

/-- Claim 3 for two chains of one step: `P = solvePoints 2 1 = 9`. -/
example {adv : TimeLockPuzzle.Adversary (oracleSpec 2 S L Salt Salt) (Puzzle 2 S L Salt) S}
    {Qpre r Qon : ℕ} (hadv : adv.IsQueryBound Qpre (r, Qon)) :
    Pr{let res ← idealExperiment adv 1 mkCtx initAcc}[
      res.genBad = true ∨ res.onlineBad = true] ≤
      (Qon : ℝ≥0∞) / 5 + Qpre / (3 * 5) + ((Qpre + Qon) * 9 + 9 ^ 2) / 11 := by
  have hP : solvePoints 2 1 = 9 := rfl
  simpa [hP] using prEvent_idealExperiment_bad_le (m := 1) (initAcc := initAcc) mkCtx_injective hadv

/-- Claim 3 for one chain: the link term is absent. -/
example {S L Salt Ctx : Type} [DecidableEq S] [DecidableEq L] [DecidableEq Salt] [DecidableEq Ctx]
    [SampleableType S] [SampleableType L] [SampleableType Salt] [Fintype S] [Fintype L]
    [Fintype Salt] [AddCommGroup L] {m : ℕ} {mkCtx : Salt → Ctx} {initAcc : Ctx → S}
    (hctx : Function.Injective mkCtx)
    {adv : TimeLockPuzzle.Adversary (oracleSpec 1 S L Salt Ctx) (Puzzle 1 S L Salt) S}
    {Qpre r Qon : ℕ} (hadv : adv.IsQueryBound Qpre (r, Qon)) :
    Pr{let res ← idealExperiment adv m mkCtx initAcc}[
      res.genBad = true ∨ res.onlineBad = true] ≤
      Qpre / (Fintype.card Salt * Fintype.card L) +
        ((Qpre + Qon) * solvePoints 1 m + (solvePoints 1 m : ℝ≥0∞) ^ 2) / Fintype.card S := by
  simpa using prEvent_idealExperiment_bad_le hctx hadv

/-- The per-point weight for two chains is `1 / |L| + P / |S|`, and for one chain `P / |S|`. -/
example : hitBound 2 1 S L = 5⁻¹ + 9 / 11 := by
  simp [hitBound, show solvePoints 2 1 = 9 from rfl]

example : hitBound 1 1 S L = 5 / 11 := by
  simp [hitBound, show solvePoints 1 1 = 5 from rfl]

/-! ## The case split on a concrete labelling -/

/-- Labels of two chains of one step: state `y_{i,k}` has label `3 i + k + 1`, mask `μ_0` has
label `2`, accumulator `a_i` has label `7 + i`, the key `9` and the commitment `10`. -/
def labels : Labels 2 1 S L
  | .state i k => ⟨3 * i.val + k.val + 1, by omega⟩
  | .mask _ => 2
  | .acc i => ⟨7 + i.val, by omega⟩
  | .key => 9
  | .commit => 10

/-- A puzzle with salt `2`, first link `3` and masked link `4`, committing to the key label. -/
def puzzle : Puzzle 2 S L Salt := labelPuzzle 2 3 (fun _ => 4) labels

/-- The path input of a path value. -/
def input (v : PathValue 2 1) : Point 2 S L Salt Salt :=
  pathInput 1 mkCtx initAcc puzzle labels v

/-- Case 3: the start of the second chain has the mask `μ_0` as its only predecessor, so its start
point hits while `μ_0` is unreached, and does not once `μ_0` is reached. -/
example : (PathValue.state 1 0 : PathValue 2 1).preds = {.mask 0} := by decide +kernel

example : HitAt 1 mkCtx initAcc puzzle labels ∅ (input (.state 1 0)) := by
  simp only [HitAt]
  decide +kernel

example : ¬HitAt 1 mkCtx initAcc puzzle labels {.mask 0} (input (.state 1 0)) := by
  simp only [HitAt, not_exists, not_and, not_not]
  decide +kernel

/-- Case 3 is absent for one chain: its start has no predecessor. -/
example : (PathValue.state 0 0 : PathValue 1 1).preds = ∅ := by decide +kernel

/-- Case 4: the key query, submitted with nothing reached, hits; it is not a start point. -/
example : HitAt 1 mkCtx initAcc puzzle labels ∅ (input .key) := by
  simp only [HitAt]
  decide +kernel

example : ∀ ctx i x, input .key ≠ .start ctx i x := by
  intro ctx i x h
  simp [input, pathInput] at h

/-- No collision on this labelling: distinct path values have distinct path inputs. -/
example : ∀ v w : PathValue 2 1, input v = input w → v = w := by decide +kernel

end VCVioTest.PointerChainPuzzle.Bad
