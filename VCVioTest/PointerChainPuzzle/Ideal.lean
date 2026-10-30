/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.Schemes.PointerChainPuzzle.Ideal
import all VCVio.Schemes.PointerChainPuzzle.Basic
import all VCVio.Schemes.PointerChainPuzzle.Path
import all VCVio.Schemes.PointerChainPuzzle.Ideal

/-!
# Masked links and programmed caches on small parameters

Checks of the first two game hops of the pointer-chain delay proof for two chains of one step
(`n = 2`, `m = 1`) over states `Fin 5`, links `Fin 3` and salts and contexts `Fin 2`: the link map
`maskLinks` is a bijection; for a concrete labelling and a preprocessing cache holding one point
off the path, `Bad` fails, so the programmed cache answers the path input of every path value with
its label (`programmedCache_pathInput`) and keeps the off-path point
(`programCache_apply_of_forall_ne`); `Bad` holds once the cache already holds a path input; and
for one chain of two steps (`n = 1`, `m = 2`) whose first two states share a label, the two step
inputs coincide, so `Bad` holds with an empty cache.
Bijectivity, `Bad` and the off-path condition are decided by kernel reduction of the derived
decidable equality of points and path values, so the scheme modules are imported with
`import all`.
-/

public section

open OracleSpec PointerChainPuzzle

namespace VCVioTest.PointerChainPuzzle.Ideal

/-- States. -/
abbrev S := Fin 5

/-- Links. -/
abbrev L := Fin 3

/-- Salts and contexts. -/
abbrev Salt := Fin 2

/-- Reduce a natural number to a state. -/
def toS (k : ℕ) : S := ⟨k % 5, Nat.mod_lt _ (by decide)⟩

/-- Reduce a natural number to a link. -/
def toL (k : ℕ) : L := ⟨k % 3, Nat.mod_lt _ (by decide)⟩

/-- The context of a salt. -/
def mkCtx (salt : Salt) : Salt := salt + 1

/-- The initial accumulator of a context. -/
def initAcc (ctx : Salt) : S := toS ctx

/-- Concrete oracles for two chains, each mixing all of its inputs. -/
def oracles : Oracles 2 S L Salt Salt where
  start ctx i x := toS (1 + ctx + 2 * i + 3 * x)
  step salt i s := toS (2 * s + salt + 3 * i + 1)
  mask ctx y := toL (y + ctx)
  acc a y := toS (3 * a + y + 1)
  key ctx a := toS (a * a + ctx + 4)
  commit ctx k := toS (2 * k + ctx + 2)

/-- The fixed salt of the checks below. -/
def salt₀ : Salt := 0

/-! ## The link map -/

/-- With the salt and the oracles fixed, the links determine the first link and the masked
links, and conversely. -/
example : Function.Bijective (maskLinks 1 mkCtx oracles salt₀) := by decide +kernel

/-! ## The programmed cache -/

/-- A labelling: distinct labels for the two accumulators, and the first accumulator away from
`initAcc (mkCtx salt₀)`. -/
def ℓ₀ : Labels 2 1 S L
  | .state i k => toS (2 * i + k + 1)
  | .mask _ => 2
  | .acc i => toS (i + 3)
  | .key => 0
  | .commit => 1

/-- The puzzle of `ℓ₀`, with first link `1` and masked link `2`. -/
def P₀ : Puzzle 2 S L Salt := labelPuzzle salt₀ 1 (fun _ => 2) ℓ₀

/-- A preprocessing cache holding one key point, under the context `0`, which no path input
uses. -/
def c₀ : (oracleSpec 2 S L Salt Salt).QueryCache :=
  (∅ : (oracleSpec 2 S L Salt Salt).QueryCache).cacheQuery (.key 0 0) (3 : S)

/-- A preprocessing cache that already holds the path input of the commitment. -/
def c₁ : (oracleSpec 2 S L Salt Salt).QueryCache :=
  c₀.cacheQuery (.commit (mkCtx salt₀) (ℓ₀ .key)) (4 : S)

/-- The concrete data avoid `Bad`: the nine path inputs are distinct and none is in `c₀`. -/
theorem not_bad₀ : ¬Bad 1 mkCtx initAcc c₀ P₀ ℓ₀ := by decide +kernel

example : Bad 1 mkCtx initAcc c₁ P₀ ℓ₀ := by decide +kernel

/-- No path input of the concrete data is the key point held by `c₀`. -/
theorem pathInput_ne_key₀ : ∀ w : PathValue 2 1, pathInput 1 mkCtx initAcc P₀ ℓ₀ w ≠ .key 0 0 := by
  decide +kernel

/-- Off `Bad`, the programmed cache answers the path input of every path value with its label. -/
example : ∀ v : PathValue 2 1,
    (programmedCache 1 mkCtx initAcc c₀ P₀ ℓ₀ (pathInput 1 mkCtx initAcc P₀ ℓ₀ v)).map
      (cast (range_pathInput 1 mkCtx initAcc P₀ ℓ₀ v)) = some (ℓ₀ v) := fun v => by
  rw [programmedCache_pathInput 1 mkCtx initAcc not_bad₀ v, Option.map_some, cast_cast, cast_eq]

/-- The commitment's path input is answered with its label, without a cast. -/
example : (programmedCache 1 mkCtx initAcc c₀ P₀ ℓ₀ (pathInput 1 mkCtx initAcc P₀ ℓ₀ .commit) :
    Option S) = some (ℓ₀ .commit) :=
  (programmedCache_pathInput 1 mkCtx initAcc not_bad₀ .commit).trans
    (congrArg some (cast_eq _ _))

/-- The mask's path input is answered with its link label, without a cast. -/
example : (programmedCache 1 mkCtx initAcc c₀ P₀ ℓ₀ (pathInput 1 mkCtx initAcc P₀ ℓ₀ (.mask 0)) :
    Option L) = some (ℓ₀ (.mask 0)) :=
  (programmedCache_pathInput 1 mkCtx initAcc not_bad₀ (.mask 0)).trans
    (congrArg some (cast_eq _ _))

/-- The off-path point of the preprocessing cache keeps its answer. -/
example : programmedCache 1 mkCtx initAcc c₀ P₀ ℓ₀ (.key 0 0) = some (3 : S) :=
  (programCache_apply_of_forall_ne 1 mkCtx initAcc P₀ ℓ₀ (fun w _ => pathInput_ne_key₀ w)
    c₀).trans (QueryCache.cacheQuery_self _ _ _)

/-! ## A path-input collision -/

/-- A labelling of one chain of two steps whose first two states share a label. -/
def ℓ₂ : Labels 1 2 S L
  | .state _ k => if k.val ≤ 1 then 3 else 4
  | .mask _ => 0
  | .acc _ => 1
  | .key => 2
  | .commit => 0

/-- The puzzle of `ℓ₂`, with first link `1`. -/
def P₂ : Puzzle 1 S L Salt := labelPuzzle salt₀ 1 (fun i => i.elim0) ℓ₂

/-- The two steps of the chain have the same input, since the states they start from share a
label. -/
example : pathInput 2 mkCtx initAcc P₂ ℓ₂ (.state 0 1) =
    pathInput 2 mkCtx initAcc P₂ ℓ₂ (.state 0 2) := by
  decide +kernel

/-- The collision is `Bad`, even with an empty preprocessing cache. -/
example : Bad 2 mkCtx initAcc (∅ : (oracleSpec 1 S L Salt Salt).QueryCache) P₂ ℓ₂ := by
  decide +kernel

end VCVioTest.PointerChainPuzzle.Ideal
