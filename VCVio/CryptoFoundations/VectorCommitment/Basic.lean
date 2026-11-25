/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.OracleComp.ProbComp.Basic
public import VCVio.OracleComp.SimSemantics.Append

/-!
# Vector commitments in the model of one oracle

A vector commitment to messages `m : Fin ℓ → Msg` relative to one classical oracle `X →ₒ Y`
(Chiesa, Di, Hu and Zheng, *How to Prove Post-Quantum Security for Succinct Non-Interactive
Reductions*, ePrint 2025/2166, §3.5, pp. 26–27) consists of three algorithms:

* `Commit^f(m) → (cm, td)` samples coins and queries the oracle;
* `Open(Q, td) → pf` is oracle-free and may sample coins;
* `Check^f(cm, Q, ans, pf) → {0, 1}` queries the oracle and may sample coins.

`VectorCommitment` is this general form: coins come from `unifSpec`, oracle queries go to
`X →ₒ Y`. `DetVectorCommitment` is the specialization with a deterministic `Open` and a coin-free
`Check`, the form of every scheme in §8 of ePrint 2025/2166;
`DetVectorCommitment.toVectorCommitment` embeds it into the general form.

The pair `(Q, ans)` with `ans ∈ Σ^Q` is one partial vector `ans : Fin ℓ → Option Msg` with
`Q = dom ans`; the same type holds the extracted messages `m ∈ (Σ ∪ {⊥})^ℓ` of §7
(ePrint 2025/2166, p. 49). The paper's `Dom(m)` (§3, p. 22) and `m[Q] = ans` (Def 7.3, p. 51) are
`PartialVec.dom` and `PartialVec.Agrees`.

The modules beside this file state completeness (`Completeness`, `RomCompleteness`) and the
security properties position binding (`PositionBinding`) and hiding (`Hiding`) of a scheme, and
`NonadaptiveCheck` records a structural property of `Check`: it rechecks a query log computed
without the oracle. The properties use two oracle models. Completeness is relative to an
arbitrary distribution `D` on oracle functions, following ePrint 2025/2166 (`completenessProb`).
Position binding and hiding are stated in the random oracle model, against the lazily sampled
random oracle `ProbCompRuntime.rom (X →ₒ Y)`, as in Chiesa–Yogev, Version 1.2, Chapter 18.
`RomCompleteness` transfers completeness against every fixed function to that oracle.

## Universes

The oracle input type `X` and the message type `Msg` are in arbitrary universes. The oracle
output type `Y`, the commitments `Cm`, the trapdoors `Td` and the proofs `Pf` are in `Type`: they
are answers of oracle queries or outputs of oracle computations whose combined specification
includes the uniform-sampling oracle `unifSpec`, and the semantics of `OracleComp` (`simulateQ`,
`evalDist`) places outputs in the universe of the oracle answers. The partial vectors are fully
universe-polymorphic.

## Main definitions

* `PartialVec ℓ Msg`, with `PartialVec.dom`, `PartialVec.Agrees`, `PartialVec.Conflict` and
  `PartialVec.restrict`.
* `VectorCommitment X Y Msg Cm Td Pf ℓ` and `VectorCommitment.fixedOracleImpl`.
* `DetVectorCommitment X Y Msg Cm Td Pf ℓ` and `DetVectorCommitment.toVectorCommitment`.

## References

* [Chiesa, Di, Hu and Zheng, *How to Prove Post-Quantum Security for Succinct Non-Interactive
  Reductions*, ePrint 2025/2166](https://eprint.iacr.org/2025/2166), §3 (`Dom`, p. 22), §3.5
  (vector commitments and Def 3.7, pp. 26–27), §7 (extracted messages, p. 49; `Dom(m)` and `m[Q]`
  in Def 7.3, pp. 50–51), §8 (deterministic schemes, Thm 8.4 condition 1, p. 53).
* [Chiesa–Yogev, *Building Cryptographic Proofs from Hash Functions*, Version 1.2, Chapter 18,
  Merkle commitment scheme](https://github.com/hash-based-snargs-book/hash-based-snargs-book/blob/305fa3d9d19ee6dba135de64b3156d1760df8426/snargs-book.tex#L12395-L14597).
-/

public section

open OracleComp OracleSpec

universe u v uX uM

/-! ## Partial vectors -/

/-- A partial vector of length `ℓ`: a value at each position of its domain `dom`, and `none`
elsewhere. It holds a set of opened positions together with their values, and an extracted
message whose undetermined positions are `none`. -/
abbrev PartialVec (ℓ : ℕ) (Msg : Type u) := Fin ℓ → Option Msg

namespace PartialVec

variable {ℓ : ℕ} {Msg : Type u}

/-- The positions at which a partial vector is defined. -/
@[expose]
def dom (v : PartialVec ℓ Msg) : Finset (Fin ℓ) :=
  Finset.univ.filter fun q ↦ (v q).isSome

/-- A position is in the domain exactly when the entry is present. -/
@[simp]
theorem mem_dom {v : PartialVec ℓ Msg} {q : Fin ℓ} : q ∈ v.dom ↔ (v q).isSome := by
  simp [dom]

/-- `m[Q] = ans` with `Q = dom ans`: `m` agrees with `ans` wherever `ans` is defined. -/
@[expose]
def Agrees (m ans : PartialVec ℓ Msg) : Prop :=
  ∀ q a, ans q = some a → m q = some a

/-- Agreement is decidable: it is a finite conjunction. -/
instance [DecidableEq Msg] (m ans : PartialVec ℓ Msg) : Decidable (Agrees m ans) :=
  decidable_of_iff (∀ q, ∀ a ∈ ans q, m q = some a) (by simp [Agrees])

/-- Two partial vectors conflict when some position is defined in both with different values. -/
@[expose]
def Conflict (a b : PartialVec ℓ Msg) : Prop :=
  ∃ q x y, a q = some x ∧ b q = some y ∧ x ≠ y

/-- Conflict is decidable: it is a finite disjunction. -/
instance [DecidableEq Msg] (a b : PartialVec ℓ Msg) : Decidable (Conflict a b) :=
  decidable_of_iff (∃ q, ∃ x ∈ a q, ∃ y ∈ b q, x ≠ y) (by simp [Conflict])

/-- Conflict is symmetric. -/
theorem Conflict.symm {a b : PartialVec ℓ Msg} (h : Conflict a b) : Conflict b a :=
  let ⟨q, x, y, hx, hy, hxy⟩ := h
  ⟨q, y, x, hy, hx, hxy.symm⟩

/-- Conflict is symmetric. -/
theorem conflict_comm {a b : PartialVec ℓ Msg} : Conflict a b ↔ Conflict b a :=
  ⟨Conflict.symm, Conflict.symm⟩

/-- A partial vector never conflicts with itself. -/
@[simp]
theorem not_conflict_self (a : PartialVec ℓ Msg) : ¬ Conflict a a := by
  rintro ⟨q, x, y, hx, hy, hxy⟩
  exact hxy (Option.some_injective _ (hx.symm.trans hy))

/-- The restriction `m[Q]` of a total vector to the positions `Q`. -/
@[expose]
def restrict (m : Fin ℓ → Msg) (Q : Finset (Fin ℓ)) : PartialVec ℓ Msg :=
  fun q ↦ if q ∈ Q then some (m q) else none

/-- The entries of a restriction. -/
@[simp]
theorem restrict_apply (m : Fin ℓ → Msg) (Q : Finset (Fin ℓ)) (q : Fin ℓ) :
    restrict m Q q = if q ∈ Q then some (m q) else none :=
  rfl

/-- The restriction to `Q` is defined exactly on `Q`. -/
@[simp]
theorem dom_restrict (m : Fin ℓ → Msg) (Q : Finset (Fin ℓ)) : (restrict m Q).dom = Q := by
  ext q
  by_cases hq : q ∈ Q <;> simp [hq]

/-- Every partial vector agrees with itself. -/
theorem agrees_refl (m : PartialVec ℓ Msg) : Agrees m m :=
  fun _ _ h ↦ h

end PartialVec

/-! ## Vector commitments -/

/-- A vector commitment to messages `Fin ℓ → Msg` in the model of one oracle `X →ₒ Y`, in its
general form.

`commit` and `check` sample coins with `unifSpec` and query the oracle; `opening` is oracle-free
and samples coins. A scheme with a deterministic `Open` and a coin-free `Check` is a
`DetVectorCommitment`. -/
structure VectorCommitment (X : Type uX) (Y : Type) (Msg : Type uM) (Cm Td Pf : Type)
    (ℓ : ℕ) where
  /-- `Commit^f(m) → (cm, td)`. -/
  commit : (Fin ℓ → Msg) → OracleComp (unifSpec + (X →ₒ Y)) (Cm × Td)
  /-- `Open(Q, td) → pf`. -/
  opening : Finset (Fin ℓ) → Td → ProbComp Pf
  /-- `Check^f(cm, Q, ans, pf) → {0, 1}`, with `Q = dom ans`. -/
  check : Cm → PartialVec ℓ Msg → Pf → OracleComp (unifSpec + (X →ₒ Y)) Bool

namespace VectorCommitment

/-! ### Answering the oracle with a fixed function -/

section FixedOracle

variable {X : Type uX} {Y : Type}

/-- Answering every query of `X →ₒ Y` with `pure (H x)` evaluates the computation at `H`. -/
theorem simulateQ_pure_eq_evalWithAnswerFn {m : Type → Type v} [Monad m] [LawfulMonad m]
    (H : X → Y) {α : Type} (oa : OracleComp (X →ₒ Y) α) :
    simulateQ ⟨fun x ↦ (pure (H x) : m Y)⟩ oa =
      pure (evalWithAnswerFn (QueryImpl.ofFn H) oa) := by
  exact (PFunctor.FreeM.liftM_natural (s := QueryImpl.ofFn H) (MonadHom.pure m) oa).symm

/-- The implementation of `unifSpec + (X →ₒ Y)` in `ProbComp` that passes the coins through and
answers every oracle query with the fixed function `H`. -/
@[expose]
def fixedOracleImpl (H : X → Y) : QueryImpl (unifSpec + (X →ₒ Y)) ProbComp :=
  QueryImpl.id' unifSpec + (⟨fun x ↦ pure (H x)⟩ : QueryImpl (X →ₒ Y) ProbComp)

/-- Against `fixedOracleImpl H`, a coin-free computation over `X →ₒ Y` is evaluated at `H`. -/
theorem simulateQ_fixedOracleImpl_liftComp (H : X → Y) {α : Type}
    (oa : OracleComp (X →ₒ Y) α) :
    simulateQ (fixedOracleImpl H) (liftComp oa (unifSpec + (X →ₒ Y))) =
      pure (evalWithAnswerFn (QueryImpl.ofFn H) oa) := by
  rw [fixedOracleImpl, QueryImpl.simulateQ_add_liftComp_right (QueryImpl.id' unifSpec)
    ⟨fun x ↦ (pure (H x) : ProbComp Y)⟩ oa, simulateQ_pure_eq_evalWithAnswerFn]

end FixedOracle

end VectorCommitment

/-! ## Deterministic vector commitments -/

/-- A vector commitment with a deterministic `Open` and a coin-free `Check`. `Commit` still
samples coins. `toVectorCommitment` embeds it into the general form. -/
structure DetVectorCommitment (X : Type uX) (Y : Type) (Msg : Type uM) (Cm Td Pf : Type)
    (ℓ : ℕ) where
  /-- `Commit^f(m) → (cm, td)`. -/
  commit : (Fin ℓ → Msg) → OracleComp (unifSpec + (X →ₒ Y)) (Cm × Td)
  /-- `Open(Q, td) → pf`, deterministic. -/
  opening : Finset (Fin ℓ) → Td → Pf
  /-- `Check^f(cm, Q, ans, pf) → {0, 1}`, with `Q = dom ans`, deterministic given the oracle. -/
  check : Cm → PartialVec ℓ Msg → Pf → OracleComp (X →ₒ Y) Bool

namespace DetVectorCommitment

variable {X : Type uX} {Y : Type} {Msg : Type uM} {Cm Td Pf : Type} {ℓ : ℕ}

/-- A deterministic vector commitment as a general one: `Open` returns its proof without coins, and
`Check` is lifted to the combined specification without using the coins. -/
@[expose]
def toVectorCommitment (vc : DetVectorCommitment X Y Msg Cm Td Pf ℓ) :
    VectorCommitment X Y Msg Cm Td Pf ℓ where
  commit := vc.commit
  opening Q td := pure (vc.opening Q td)
  check cm ans pf := liftComp (vc.check cm ans pf) (unifSpec + (X →ₒ Y))

end DetVectorCommitment
