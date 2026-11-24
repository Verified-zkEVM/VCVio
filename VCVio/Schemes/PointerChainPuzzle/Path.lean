/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.Schemes.PointerChainPuzzle.Basic

/-!
# Path values of the pointer-chain puzzle

The values the honest solver of the pointer-chain puzzle (`PointerChainPuzzle.solve`) obtains
are the *path values* (`PointerChainPuzzle.PathValue`): the states `y_{i,k}` of each chain
(`y_{i,0} = s_i`), the masks, the accumulators `a_1, …, a_n`, the key and the commitment. Each is
the answer on its *path input* (`PointerChainPuzzle.pathInput`), which is formed from the values
of its *predecessors* (`PathValue.preds`) and, for the starts, from the salt, `x_0` and the masked
links; the start of chain `i + 1` has the mask `μ_i` among its predecessors. `PathValue.rho` is
the round in which the honest solver receives a value.

## Main statements

* `PathValue.card_eq`: there are `solvePoints n m = n (m + 3) + 1` path values.
* `PathValue.rho_eq_sup_preds`: every value but `s_0` is received one round after the last of
  its predecessors; `PathValue.rho_key`: the key is received in round `keyRound n m`.
* `pathInput_congr`: a path input depends on the values only through the predecessors.
* `honestValue_eq_answer`: the honest values are the answers on their path inputs.
-/

public section

open OracleSpec OracleComp

namespace PointerChainPuzzle

variable {n m : ℕ} {S L Salt Ctx : Type}

/-! ## Path values

The values the honest solver obtains, indexed by `PathValue n m`, with the round `PathValue.rho`
in which the solver receives each and the predecessors `PathValue.preds` from whose values its
path input is formed. -/

/-- The path values of the pointer-chain puzzle with `n` chains of `m` steps. -/
inductive PathValue (n m : ℕ)
  /-- `y_{i,k}`, the state of chain `i` after `k` steps; `y_{i,0}` is the chain start `s_i`. -/
  | state (i : Fin n) (k : Fin (m + 1))
  /-- `μ_i`, the mask of chain `i < n - 1`. -/
  | mask (i : Fin (n - 1))
  /-- `a_{i+1}`, the accumulator after chain `i`. -/
  | acc (i : Fin n)
  /-- The key `K`. -/
  | key
  /-- The commitment `C`. -/
  | commit
  deriving DecidableEq

namespace PathValue

/-- Path values as a sum of finite types. -/
@[expose]
def equivSum : PathValue n m ≃ (Fin n × Fin (m + 1)) ⊕ Fin (n - 1) ⊕ Fin n ⊕ Bool where
  toFun
    | .state i k => .inl (i, k)
    | .mask i => .inr (.inl i)
    | .acc i => .inr (.inr (.inl i))
    | .key => .inr (.inr (.inr false))
    | .commit => .inr (.inr (.inr true))
  invFun
    | .inl (i, k) => .state i k
    | .inr (.inl i) => .mask i
    | .inr (.inr (.inl i)) => .acc i
    | .inr (.inr (.inr false)) => .key
    | .inr (.inr (.inr true)) => .commit
  left_inv v := by cases v <;> rfl
  right_inv x := by rcases x with ⟨i, k⟩ | i | i | _ | _ <;> rfl

instance : Fintype (PathValue n m) := Fintype.ofEquiv _ equivSum.symm

/-- There are `solvePoints n m = n (m + 3) + 1` path values. -/
theorem card_eq [NeZero n] : Fintype.card (PathValue n m) = solvePoints n m := by
  obtain ⟨n', rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, (Nat.sub_add_cancel NeZero.one_le).symm⟩
  rw [Fintype.card_congr equivSum]
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool,
    Nat.add_sub_cancel, solvePoints]
  ring

/-- The type of a path value: masks are links, every other path value is a state. -/
@[expose, reducible]
def Val (S L : Type) : PathValue n m → Type
  | .mask _ => L
  | _ => S

/-- `s_0 = y_{0,0}`, the start of the first chain, the only path value without predecessors. -/
@[expose]
def firstStart [NeZero n] : PathValue n m := .state ⟨0, Nat.pos_of_neZero n⟩ ⟨0, m.succ_pos⟩

/-- The round in which the honest solver receives a path value:
`ρ(y_{i,k}) = i (m + 2) + k + 1`, `ρ(μ_i) = ρ(a_{i+1}) = i (m + 2) + m + 2`, `ρ(K) = keyRound n m`,
and `ρ(C) = keyRound n m + 1`. -/
@[expose]
def rho : PathValue n m → ℕ
  | .state i k => i * (m + 2) + k + 1
  | .mask i => i * (m + 2) + m + 2
  | .acc i => i * (m + 2) + m + 2
  | .key => keyRound n m
  | .commit => keyRound n m + 1

/-- The predecessors of a path value: the path values from which its path input is formed. The
start of chain `i + 1` depends on the mask `μ_i` that unmasks its link. -/
@[expose]
def preds [NeZero n] : PathValue n m → Finset (PathValue n m)
  | .state ⟨0, _⟩ ⟨0, _⟩ => ∅
  | .state ⟨i + 1, h⟩ ⟨0, _⟩ => {.mask ⟨i, by omega⟩}
  | .state i ⟨k + 1, h⟩ => {.state i ⟨k, by omega⟩}
  | .mask i => {.state (chainOf i) (Fin.last m)}
  | .acc ⟨0, h⟩ => {.state ⟨0, h⟩ (Fin.last m)}
  | .acc ⟨i + 1, h⟩ => {.acc ⟨i, by omega⟩, .state ⟨i + 1, h⟩ (Fin.last m)}
  | .key => {.acc lastChain}
  | .commit => {.key}

@[simp] lemma rho_key : rho (.key : PathValue n m) = keyRound n m := rfl

@[simp] lemma rho_commit : rho (.commit : PathValue n m) = keyRound n m + 1 := rfl

lemma rho_firstStart [NeZero n] : rho (firstStart : PathValue n m) = 1 := by
  simp [firstStart, rho]

lemma preds_eq_empty_iff [NeZero n] (v : PathValue n m) : preds v = ∅ ↔ v = firstStart := by
  rcases v with ⟨⟨_ | i, hi⟩, ⟨_ | k, hk⟩⟩ | i | ⟨_ | i, hi⟩ | _ | _ <;>
    simp [preds, firstStart]

/-- Every path value other than `s_0` is received one round after the last of its
predecessors: `ρ(v) = 1 + max ρ(w)` over the predecessors `w` of `v`. -/
theorem rho_eq_sup_preds [NeZero n] {v : PathValue n m} (hv : v ≠ firstStart) :
    rho v = (preds v).sup rho + 1 := by
  rcases v with ⟨⟨_ | i, hi⟩, ⟨_ | k, hk⟩⟩ | i | ⟨_ | i, hi⟩ | _ | _
  · exact absurd rfl hv
  · simp [preds, rho]
  · simp [preds, rho]
    ring
  · simp [preds, rho]
    omega
  · simp [preds, rho, chainOf]
  · simp [preds, rho]
  · simp [preds, rho]
  · obtain ⟨n', rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, (Nat.sub_add_cancel NeZero.one_le).symm⟩
    simp [preds, rho, keyRound, lastChain]
    ring
  · simp [preds, rho]

end PathValue

/-! ## Path inputs -/

section PathInputs

variable (m : ℕ) (mkCtx : Salt → Ctx) (initAcc : Ctx → S)

/-- The path input of each path value, the point on which the oracles answer it, formed from the
puzzle and the values `ν` of its predecessors: `u(y_{0,0}) = start(ctx, 0, x_0)`,
`u(y_{i+1,0}) = start(ctx, i + 1, z_i - μ_i)`, `u(y_{i,k+1}) = step(salt, i, y_{i,k})`,
`u(μ_i) = mask(ctx, y_{i,m})`, `u(a_{i+1}) = acc(a_i, y_{i,m})` with `a_0 = initAcc ctx`,
`u(K) = key(ctx, a_n)` and `u(C) = commit(ctx, K)`, where `ctx = mkCtx salt`. -/
@[expose]
def pathInput [NeZero n] [AddCommGroup L] (puzzle : Puzzle n S L Salt)
    (ν : (v : PathValue n m) → v.Val S L) : PathValue n m → Point n S L Salt Ctx
  | .state ⟨0, h⟩ ⟨0, _⟩ => .start (mkCtx puzzle.salt) ⟨0, h⟩ puzzle.firstLink
  | .state ⟨i + 1, h⟩ ⟨0, _⟩ =>
      .start (mkCtx puzzle.salt) ⟨i + 1, h⟩
        (puzzle.maskedLinks ⟨i, by omega⟩ - ν (.mask ⟨i, by omega⟩))
  | .state i ⟨k + 1, h⟩ => .step puzzle.salt i (ν (.state i ⟨k, by omega⟩))
  | .mask i => .mask (mkCtx puzzle.salt) (ν (.state (chainOf i) (Fin.last m)))
  | .acc ⟨0, h⟩ => .acc (initAcc (mkCtx puzzle.salt)) (ν (.state ⟨0, h⟩ (Fin.last m)))
  | .acc ⟨i + 1, h⟩ => .acc (ν (.acc ⟨i, by omega⟩)) (ν (.state ⟨i + 1, h⟩ (Fin.last m)))
  | .key => .key (mkCtx puzzle.salt) (ν (.acc lastChain))
  | .commit => .commit (mkCtx puzzle.salt) (ν .key)

/-- The path input of a path value depends on the values only through its predecessors. -/
theorem pathInput_congr [NeZero n] [AddCommGroup L] (puzzle : Puzzle n S L Salt)
    {ν ν' : (v : PathValue n m) → v.Val S L} (v : PathValue n m)
    (h : ∀ w ∈ v.preds, ν w = ν' w) :
    pathInput m mkCtx initAcc puzzle ν v = pathInput m mkCtx initAcc puzzle ν' v := by
  rcases v with ⟨⟨_ | i, hi⟩, ⟨_ | k, hk⟩⟩ | i | ⟨_ | i, hi⟩ | _ | _ <;>
    simp_all [PathValue.preds, pathInput]

/-- The oracle answering the path input of a path value answers in the type of that value. -/
lemma range_pathInput [NeZero n] [AddCommGroup L] (puzzle : Puzzle n S L Salt)
    (ν : (v : PathValue n m) → v.Val S L) (v : PathValue n m) :
    (oracleSpec n S L Salt Ctx).Range (pathInput m mkCtx initAcc puzzle ν v) = v.Val S L := by
  rcases v with ⟨⟨_ | i, hi⟩, ⟨_ | k, hk⟩⟩ | i | ⟨_ | i, hi⟩ | _ | _ <;> rfl

variable (O : Oracles n S L Salt Ctx)

/-- The honest path values for the salt and the links `xs`, when the oracles are `O`. -/
@[expose]
def honestValue (salt : Salt) (xs : Fin n → L) : (v : PathValue n m) → v.Val S L
  | .state i k => chainState mkCtx O salt i (xs i) k
  | .mask i => O.mask (mkCtx salt) (chainEnd m mkCtx O salt xs (chainOf i))
  | .acc i => accAfter m mkCtx initAcc O salt xs (i + 1)
  | .key => honestKey m mkCtx initAcc O salt xs
  | .commit => O.commit (mkCtx salt) (honestKey m mkCtx initAcc O salt xs)

/-- Each honest path value is the answer of the oracles on its path input, formed from the honest
puzzle and the honest values of its predecessors. -/
theorem honestValue_heq_answer [NeZero n] [AddCommGroup L] (salt : Salt) (xs : Fin n → L)
    (v : PathValue n m) :
    HEq (honestValue m mkCtx initAcc O salt xs v)
      (O.toImpl (pathInput m mkCtx initAcc (honestPuzzle m mkCtx initAcc O salt xs)
        (honestValue m mkCtx initAcc O salt xs) v)).run := by
  rcases v with ⟨⟨_ | i, hi⟩, ⟨_ | k, hk⟩⟩ | i | ⟨_ | i, hi⟩ | _ | _
  · apply heq_of_eq
    change O.start (mkCtx salt) _ (xs _) = O.start (mkCtx salt) _ (xs 0)
    simp
  · exact heq_of_eq (Function.iterate_succ_apply' _ _ _)
  · apply heq_of_eq
    change O.start (mkCtx salt) _ (xs _) =
      O.start (mkCtx salt) _ (O.mask _ _ + xs (nextChain _) - O.mask _ _)
    rw [add_sub_cancel_left]
    rfl
  · exact heq_of_eq (Function.iterate_succ_apply' _ _ _)
  · rfl
  · exact heq_of_eq (accAfter_succ_of_lt hi)
  · exact heq_of_eq (accAfter_succ_of_lt hi)
  · apply heq_of_eq
    change O.key _ _ = O.key _ (accAfter m mkCtx initAcc O salt xs (n - 1 + 1))
    rw [Nat.sub_add_cancel NeZero.one_le]
    rfl
  · rfl

/-- Each honest path value is the answer of the oracles on its path input. -/
theorem honestValue_eq_answer [NeZero n] [AddCommGroup L] (salt : Salt) (xs : Fin n → L)
    (v : PathValue n m) :
    honestValue m mkCtx initAcc O salt xs v =
      cast (range_pathInput m mkCtx initAcc _ _ v)
        (O.toImpl (pathInput m mkCtx initAcc (honestPuzzle m mkCtx initAcc O salt xs)
          (honestValue m mkCtx initAcc O salt xs) v)).run :=
  (cast_eq_iff_heq.mpr (honestValue_heq_answer m mkCtx initAcc O salt xs v).symm).symm

end PathInputs

end PointerChainPuzzle
