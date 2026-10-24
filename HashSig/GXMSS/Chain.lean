/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.HashInstance

/-!
# Positive-step hash chains

Construction 2 of ePrint 2025/055 hashes at steps `k+1` through `k+s`.
The recurrence is deterministic and requires no injectivity assumption on the hash.
-/

public section

namespace GXMSS

/-- Iterate a position-dependent function, starting at positive step `k+1`. -/
@[expose] def chainWith {H : Type*} (step : ℕ → H → H) (k : ℕ) : ℕ → H → H
  | 0, x => x
  | s + 1, x => step (k + s + 1) (chainWith step k s x)

/-- A zero-length chain preserves its input. -/
@[simp] theorem chainWith_zero {H : Type*} (step : ℕ → H → H) (k : ℕ) (x : H) :
    chainWith step k 0 x = x := rfl

/-- The final call of a chain of length `s+1` uses position `k+s+1`. -/
theorem chainWith_succ {H : Type*} (step : ℕ → H → H) (k s : ℕ) (x : H) :
    chainWith step k (s + 1) x = step (k + s + 1) (chainWith step k s x) := rfl

/-- Splitting the ordered sequence of chain calls preserves the output. -/
theorem chainWith_add {H : Type*} (step : ℕ → H → H) (k s t : ℕ) (x : H) :
    chainWith step k (s + t) x = chainWith step (k + s) t (chainWith step k s x) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Nat.add_succ, chainWith_succ, chainWith_succ, ih]
    simp [Nat.add_assoc]

/-- A chain depends only on step functions at its visited positive positions. -/
theorem chainWith_congr {H : Type*} (step₁ step₂ : ℕ → H → H) (k s : ℕ) (x : H)
    (hstep : ∀ j, k < j → j ≤ k + s → ∀ y, step₁ j y = step₂ j y) :
    chainWith step₁ k s x = chainWith step₂ k s x := by
  induction s with
  | zero => rfl
  | succ s ih =>
    rw [chainWith_succ, chainWith_succ, ih (by intros; apply hstep <;> omega)]
    exact hstep _ (by omega) le_rfl _

variable {PP T X H : Type} {h w v : ℕ}

namespace HashInstance

/-- Hash at a legal positive chain position. Outside the paper domain the extension is the
identity; bounded chain statements never use that extension. -/
private def chainStep (P : HashInstance PP T X H h w v) (pp : PP)
    (e : Fin (2 ^ h)) (i : Fin v) (j : ℕ) (x : H) : H :=
  if hj : 0 < j ∧ j ≤ 2 ^ w - 1 then
    (HashInstance.thf P).eval pp (P.chainTweak (e, i, ⟨j - 1, by omega⟩)) (P.digestInput x)
  else x

/-- A bounded-domain positive step evaluates the common hash under its chain tweak. -/
private theorem chainStep_of_pos_le (P : HashInstance PP T X H h w v) (pp : PP)
    (e : Fin (2 ^ h)) (i : Fin v) (j : ℕ) (x : H)
    (hj : 0 < j ∧ j ≤ 2 ^ w - 1) :
    P.chainStep pp e i j x =
    (HashInstance.thf P).eval pp (P.chainTweak (e, i, ⟨j - 1, by omega⟩)) (P.digestInput x) := by
  simp [chainStep, hj]

/-- Construction 2's chain at public seed, epoch, chain label, start and length. -/
def chain (P : HashInstance PP T X H h w v) (pp : PP)
    (e : Fin (2 ^ h)) (i : Fin v) (k s : ℕ) (x : H) : H :=
  chainWith (P.chainStep pp e i) k s x

/-- A zero-length common-hash chain preserves the input. -/
@[simp] theorem chain_zero (P : HashInstance PP T X H h w v) (pp : PP)
    (e : Fin (2 ^ h)) (i : Fin v) (k : ℕ) (x : H) : P.chain pp e i k 0 x = x := by
  simp only [chain, chainWith_zero]

/-- Every bounded successor hashes at the paper's positive position `k+s+1`. -/
theorem chain_succ (P : HashInstance PP T X H h w v) (pp : PP)
    (e : Fin (2 ^ h)) (i : Fin v) (k s : ℕ) (x : H) (hs : k + s + 1 ≤ 2 ^ w - 1) :
    P.chain pp e i k (s + 1) x = (HashInstance.thf P).eval pp
      (P.chainTweak (e, i, ⟨k + s, by omega⟩)) (P.digestInput (P.chain pp e i k s x)) := by
  simp [chain, chainWith_succ, chainStep, hs]

/-- Composition of the total chain operation requires no address-bound premise. -/
theorem chain_add (P : HashInstance PP T X H h w v) (pp : PP)
    (e : Fin (2 ^ h)) (i : Fin v) (k s t : ℕ) (x : H) :
    P.chain pp e i k (s + t) x = P.chain pp e i (k + s) t (P.chain pp e i k s x) :=
  chainWith_add _ _ _ _ _

/-- Lemma 2: complete a prefix of length `s` to the endpoint at `2^w-1`. -/
theorem chain_complete (P : HashInstance PP T X H h w v) (pp : PP)
    (e : Fin (2 ^ h)) (i : Fin v) (s : ℕ) (x : H) (hs : s ≤ 2 ^ w - 1) :
    P.chain pp e i s (2 ^ w - 1 - s) (P.chain pp e i 0 s x) =
      P.chain pp e i 0 (2 ^ w - 1) x := by
  simpa [Nat.add_sub_of_le hs] using (P.chain_add pp e i 0 s (2 ^ w - 1 - s) x).symm

/-- An encoding digit carries the bound needed to complete its chain. -/
theorem chain_complete_digit (P : HashInstance PP T X H h w v) (pp : PP)
    (e : Fin (2 ^ h)) (i : Fin v) (digit : Fin (2 ^ w)) (x : H) :
    P.chain pp e i digit (2 ^ w - 1 - digit.val) (P.chain pp e i 0 digit x) =
      P.chain pp e i 0 (2 ^ w - 1) x :=
  P.chain_complete pp e i digit x (by omega)

/-- The two hash instances agree at the same public seed on finite positions
visited by this span. -/
@[expose] def ChainHashAgreement (P Q : HashInstance PP T X H h w v) (pp : PP)
    (e : Fin (2 ^ h)) (i : Fin v) (k s : ℕ) : Prop :=
  ∀ j : Fin (2 ^ w - 1), k ≤ j.val → j.val < k + s → ∀ x,
    (HashInstance.thf P).eval pp (P.chainTweak (e, i, j)) (P.digestInput x) =
      (HashInstance.thf Q).eval pp (Q.chainTweak (e, i, j)) (Q.digestInput x)

/-- A total chain depends only on hashes at its visited finite positions. -/
theorem chain_congr (P Q : HashInstance PP T X H h w v) (pp : PP)
    (e : Fin (2 ^ h)) (i : Fin v) (k s : ℕ) (x : H)
    (hagree : P.ChainHashAgreement Q pp e i k s) :
    P.chain pp e i k s x = Q.chain pp e i k s x := by
  apply chainWith_congr
  intro j hj hjs y
  by_cases hlegal : 0 < j ∧ j ≤ 2 ^ w - 1
  · rw [chainStep_of_pos_le _ _ _ _ _ _ hlegal, chainStep_of_pos_le _ _ _ _ _ _ hlegal]
    exact hagree ⟨j - 1, by omega⟩ (by dsimp; omega) (by dsimp; omega) y
  · simp [chainStep, hlegal]

end HashInstance

end GXMSS
