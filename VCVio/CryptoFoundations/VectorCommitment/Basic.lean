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
Reductions*, ePrint 2025/2166, §3.5, Def 3.5 and Def 3.7) consists of three algorithms:

* `Commit^f(m) → (cm, td)` samples coins and queries the oracle;
* `Open(Q, td) → pf` is oracle-free and may sample coins;
* `Check^f(cm, Q, ans, pf) → {0, 1}` queries the oracle and may sample coins.

`VectorCommitment` is this general form: coins come from `unifSpec`, oracle queries go to
`X →ₒ Y`. `DetVectorCommitment` is the specialization with a deterministic `Open` and a coin-free
`Check`, the form of every scheme in §8 of ePrint 2025/2166;
`DetVectorCommitment.toVectorCommitment` embeds it into the general form.

The pair `(Q, ans)` with `ans ∈ Σ^Q` is one partial vector `ans : Fin ℓ → Option Msg` with
`Q = dom ans`; the same type holds the extracted messages `m ∈ (Σ ∪ {⊥})^ℓ` of §7
(ePrint 2025/2166, p. 49).

Security properties live beside this file: `Completeness`, `NonadaptiveCheck`, `PositionBinding`
and `Hiding`.

## Universes

The oracle input type `X` and the message type `Msg` are in arbitrary universes. The oracle
output type `Y`, the commitments `Cm`, the trapdoors `Td` and the proofs `Pf` are in `Type`: they
are answers of oracle queries or outputs of oracle computations whose combined specification
includes the uniform-sampling oracle `unifSpec`, and the semantics of `OracleComp` (`simulateQ`,
`evalDist`) places outputs in the universe of the oracle answers. The partial vectors are fully
universe-polymorphic.

## Main definitions

* `PartialVec ℓ Msg`, with `PartialVec.dom`, `PartialVec.Agrees` and `PartialVec.restrict`.
* `VectorCommitment X Y Msg Cm Td Pf ℓ` and `VectorCommitment.fixedOracleImpl`.
* `DetVectorCommitment X Y Msg Cm Td Pf ℓ` and `DetVectorCommitment.toVectorCommitment`.
-/

public section

open OracleComp OracleSpec

universe u v uX uM

/-! ## Partial vectors -/

/-- A partial vector of length `ℓ`. It encodes the pair `(Q, ans)` of ePrint 2025/2166,
Def 3.5 (p. 26), as one function with `Q = dom ans`, and an extracted message
`m ∈ (Σ ∪ {⊥})^ℓ` (p. 49), where `none` is `⊥`. -/
abbrev PartialVec (ℓ : ℕ) (Msg : Type u) := Fin ℓ → Option Msg

namespace PartialVec

variable {ℓ : ℕ} {Msg : Type u}

/-- The positions at which a partial vector is defined (`Dom(m)`, p. 51). -/
@[expose]
def dom (v : PartialVec ℓ Msg) : Finset (Fin ℓ) :=
  Finset.univ.filter fun q ↦ (v q).isSome

/-- A position is in the domain exactly when the entry is present. -/
@[simp]
theorem mem_dom {v : PartialVec ℓ Msg} {q : Fin ℓ} : q ∈ v.dom ↔ (v q).isSome := by
  simp [dom]

/-- `m[Q] = ans` with `Q = dom ans` (p. 51): `m` agrees with `ans` wherever `ans` is defined. -/
@[expose]
def Agrees (m ans : PartialVec ℓ Msg) : Prop :=
  ∀ q a, ans q = some a → m q = some a

/-- Agreement is decidable: it is a finite conjunction. -/
instance [DecidableEq Msg] (m ans : PartialVec ℓ Msg) : Decidable (Agrees m ans) :=
  decidable_of_iff (∀ q, ∀ a ∈ ans q, m q = some a) (by simp [Agrees])

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

/-- A vector commitment to messages `Fin ℓ → Msg` in the model of one oracle `X →ₒ Y`
(ePrint 2025/2166, Def 3.5, pp. 26–27), in its general form.

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
    simulateQ (fun x ↦ (pure (H x) : m Y)) oa =
      pure (evalWithAnswerFn (QueryImpl.ofFn H) oa) := by
  exact (PFunctor.FreeM.liftM_natural (s := QueryImpl.ofFn H) (MonadHom.pure m) oa).symm

/-- The implementation of `unifSpec + (X →ₒ Y)` in `ProbComp` that passes the coins through and
answers every oracle query with the fixed function `H`. -/
@[expose]
def fixedOracleImpl (H : X → Y) : QueryImpl (unifSpec + (X →ₒ Y)) ProbComp :=
  QueryImpl.id' unifSpec + fun x ↦ (pure (H x) : ProbComp Y)

/-- Against `fixedOracleImpl H`, a coin-free computation over `X →ₒ Y` is evaluated at `H`. -/
theorem simulateQ_fixedOracleImpl_liftComp (H : X → Y) {α : Type}
    (oa : OracleComp (X →ₒ Y) α) :
    simulateQ (fixedOracleImpl H) (liftComp oa (unifSpec + (X →ₒ Y))) =
      pure (evalWithAnswerFn (QueryImpl.ofFn H) oa) := by
  rw [fixedOracleImpl, QueryImpl.simulateQ_add_liftComp_right (QueryImpl.id' unifSpec)
    (fun x ↦ (pure (H x) : ProbComp Y)) oa, simulateQ_pure_eq_evalWithAnswerFn]

end FixedOracle

end VectorCommitment

/-! ## Deterministic vector commitments -/

/-- A vector commitment with a deterministic `Open` and a coin-free `Check`
(ePrint 2025/2166, Def 3.5, pp. 26–27, specialized). `Commit` still samples coins. Every scheme of
§8 has this form, and Thm 8.4 condition 1 (p. 53) asks for a deterministic `Check`.
`toVectorCommitment` embeds it into the general form. -/
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
