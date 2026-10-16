/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.OracleComp.ProbComp.Basic
public import VCVio.OracleComp.SimSemantics.Append
public import VCVio.OracleComp.Support
public import VCVio.OracleComp.EvalDist.Measure

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

Perfect completeness (Def 3.7) is relative to a distribution `D` on oracle functions, a
probability measure on `X → Y` (`VectorCommitment.PerfectlyComplete`): the honest experiment
accepts with probability `1` when the oracle is sampled from `D`. Completeness against every
fixed function (`VectorCommitment.PerfectlyCompleteForAll`, and
`DetVectorCommitment.PerfectlyComplete` for a deterministic scheme) is a sufficient condition for
every `D`.

The check of every vector commitment in §8 of ePrint 2025/2166 has a special form
(Def 8.1 and Thm 8.4 condition 1, pp. 52–53): an oracle-free, non-adaptive
`OutputIO` step lists input-output pairs, and `CheckIO^f` queries every input and compares the
answer with the listed output. `VectorCommitment.CheckIOForm` records this form, which makes
`Check` deterministic and coin-free while leaving `Open` general, together with a non-decreasing
bound `qVC` on the number of pairs (§3.5, p. 27).

## Universes

The oracle input type `X` and the message type `Msg` are in arbitrary universes. The oracle
output type `Y`, the commitments `Cm`, the trapdoors `Td` and the proofs `Pf` are in `Type`: they
are answers of oracle queries or outputs of oracle computations whose combined specification
includes the uniform-sampling oracle `unifSpec`, and the semantics of `OracleComp` (`simulateQ`,
`evalDist`) places outputs in the universe of the oracle answers. The partial vectors and the
table check `checkIOOn` are fully universe-polymorphic.

## Main definitions

* `PartialVec ℓ Msg`, with `PartialVec.dom`, `PartialVec.Agrees` and `PartialVec.restrict`.
* `VectorCommitment X Y Msg Cm Td Pf ℓ`, `VectorCommitment.completenessExp`,
  `VectorCommitment.PerfectlyComplete` and `VectorCommitment.PerfectlyCompleteForAll`.
* `DetVectorCommitment X Y Msg Cm Td Pf ℓ`, `DetVectorCommitment.toVectorCommitment` and
  `DetVectorCommitment.PerfectlyComplete`.
* `checkIO io`: query every listed input and compare; `checkIOOn D io`: the same check against a
  partial table `D : X → Option Y`, rejecting at an empty cell.
* `VectorCommitment.CheckIOForm`: `Check` is `OutputIO` followed by `CheckIO`.

## Main results

* `VectorCommitment.PerfectlyCompleteForAll.perfectlyComplete`: completeness against every fixed
  function gives Def 3.7 for every oracle distribution.
* `VectorCommitment.perfectlyComplete_iff`: Def 3.7 holds for `D` exactly when the honest
  experiment accepts on every outcome, for `D`-almost every function.
* `DetVectorCommitment.PerfectlyComplete.toVectorCommitment`: the same sufficient condition for a
  deterministic scheme.
* `evalWithAnswerFn_checkIO`: against a fixed function `H`, `checkIO io` accepts exactly when
  `H x = y` for every listed pair.
* `checkIOOn_dedup`: removing duplicate pairs does not change acceptance.
* `VectorCommitment.CheckIOForm.simulateQ_check`: against a fixed function, a check of the
  `CheckIO` form returns the table check `checkOn`.
* `VectorCommitment.CheckIOForm.length_le_of_card_le`: `qVC qs` bounds the check for every
  budget `qs ≥ |Q|`.
-/

public section

open OracleComp OracleSpec MeasureTheory

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
  induction oa using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih => simp [ih]

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

/-! ### Completeness -/

variable {X : Type uX} {Y : Type} {Msg : Type uM} {Cm Td Pf : Type} {ℓ : ℕ}

/-- The experiment of Def 3.7 (p. 27) for a message `m` and a query set `Q`, with the oracle
left abstract: `(cm, td) ← Commit^f(m)`, `pf ← Open(Q, td)`, and return
`Check^f(cm, Q, m[Q], pf)`. -/
@[expose]
def completenessExp (vc : VectorCommitment X Y Msg Cm Td Pf ℓ) (m : Fin ℓ → Msg)
    (Q : Finset (Fin ℓ)) : OracleComp (unifSpec + (X →ₒ Y)) Bool := do
  let z ← vc.commit m
  let pf ← liftComp (vc.opening Q z.2) (unifSpec + (X →ₒ Y))
  vc.check z.1 (PartialVec.restrict m Q) pf

/-- The acceptance probability of the experiment of Def 3.7 (p. 27) when the oracle is
sampled from the measure `D` on functions,
`Pr[Check^f(cm, Q, m[Q], pf) = 1 : f ← D, (cm, td) ← Commit^f(m), pf ← Open(Q, td)]`, extended to
an arbitrary measurable space on `X → Y` as the lower integral over `D` of the acceptance
probability against each fixed function. The integrand need not be measurable, and the lower
integral then may undercount: with the indiscrete σ-algebra on `Unit → Bool`, `D` the Dirac
measure at `fun _ ↦ true`, and a check that returns the oracle answer, the value is `0` although
the experiment against that function accepts. When the integrand is measurable, for example on a
countable function space with the discrete σ-algebra, the value is the operational acceptance
probability. `perfectlyComplete_iff` characterizes the value `1` without any measurability. -/
@[expose]
noncomputable def completenessProb [MeasurableSpace (X → Y)]
    (vc : VectorCommitment X Y Msg Cm Td Pf ℓ) (D : Measure (X → Y)) (m : Fin ℓ → Msg)
    (Q : Finset (Fin ℓ)) : ENNReal :=
  ∫⁻ H, Pr{let b ← simulateQ (fixedOracleImpl H) (vc.completenessExp m Q)}[b = true] ∂D

/-- **Perfect completeness** in the `D`-oracle model (ePrint 2025/2166, Def 3.7, p. 27):
for every message `m` and every query set `Q`, the experiment accepts with probability `1` when
the oracle is sampled from `D`. `D` is meant to be a probability measure. -/
@[expose]
def PerfectlyComplete [MeasurableSpace (X → Y)] (vc : VectorCommitment X Y Msg Cm Td Pf ℓ)
    (D : Measure (X → Y)) : Prop :=
  ∀ (m : Fin ℓ → Msg) (Q : Finset (Fin ℓ)), vc.completenessProb D m Q = 1

/-- Perfect completeness against every fixed function `H`: for every message and query set, every
outcome of the experiment with the oracle answered by `H` accepts. It implies Def 3.7 for every
oracle distribution (`PerfectlyCompleteForAll.perfectlyComplete`). -/
@[expose]
def PerfectlyCompleteForAll (vc : VectorCommitment X Y Msg Cm Td Pf ℓ) : Prop :=
  ∀ (H : X → Y) (m : Fin ℓ → Msg) (Q : Finset (Fin ℓ)),
    ∀ b ∈ support (simulateQ (fixedOracleImpl H) (vc.completenessExp m Q)), b = true

/-- Def 3.7 holds for a probability measure `D` exactly when, for every message and query set and
for `D`-almost every function `H`, every outcome of the experiment with the oracle answered by `H`
accepts. No measurability of the acceptance probability in `H` is needed. -/
theorem perfectlyComplete_iff [MeasurableSpace (X → Y)]
    (vc : VectorCommitment X Y Msg Cm Td Pf ℓ) (D : Measure (X → Y)) [IsProbabilityMeasure D] :
    vc.PerfectlyComplete D ↔ ∀ (m : Fin ℓ → Msg) (Q : Finset (Fin ℓ)), ∀ᵐ H ∂D,
      ∀ b ∈ support (simulateQ (fixedOracleImpl H) (vc.completenessExp m Q)), b = true := by
  refine forall₂_congr fun m Q ↦ ?_
  set p : (X → Y) → ENNReal :=
    fun H ↦ Pr{let b ← simulateQ (fixedOracleImpl H) (vc.completenessExp m Q)}[b = true]
  have hp : ∀ H, p H = 1 ↔
      ∀ b ∈ support (simulateQ (fixedOracleImpl H) (vc.completenessExp m Q)), b = true :=
    fun H ↦ prEvent_eq_one_iff _ _
  have hle : ∀ H, p H ≤ 1 := fun H ↦ prEvent_le_one _
  change ∫⁻ H, p H ∂D = 1 ↔ _
  constructor
  · intro h
    obtain ⟨g, hg, hgp, hint⟩ := exists_measurable_le_lintegral_eq D p
    have hg1 : g =ᵐ[D] fun _ ↦ 1 :=
      ae_eq_of_ae_le_of_lintegral_le (Filter.Eventually.of_forall fun H ↦ (hgp H).trans (hle H))
        (by rw [← hint, h]; exact ENNReal.one_ne_top) aemeasurable_const
        (by rw [← hint, h, lintegral_const, measure_univ, mul_one])
    filter_upwards [hg1] with H hH
    exact (hp H).mp (le_antisymm (hle H) (hH ▸ hgp H))
  · intro h
    rw [lintegral_congr_ae (h.mono fun H hH ↦ (hp H).mpr hH), lintegral_const, measure_univ,
      mul_one]

/-- Completeness against every fixed function gives Def 3.7 for every oracle distribution `D`. -/
theorem PerfectlyCompleteForAll.perfectlyComplete [MeasurableSpace (X → Y)]
    {vc : VectorCommitment X Y Msg Cm Td Pf ℓ} (h : vc.PerfectlyCompleteForAll)
    (D : Measure (X → Y)) [IsProbabilityMeasure D] : vc.PerfectlyComplete D :=
  (perfectlyComplete_iff vc D).mpr fun m Q ↦ Filter.Eventually.of_forall fun H ↦ h H m Q

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

/-- Perfect completeness of a deterministic scheme against every fixed function `H`
(ePrint 2025/2166, Def 3.7, p. 27): for every message `m`, every query set `Q` and every outcome
of `Commit^H(m)`, the honest opening of `Q` passes `Check^H` on `m[Q]`. It implies Def 3.7 for
every oracle distribution (`PerfectlyComplete.toVectorCommitment`). -/
@[expose]
def PerfectlyComplete (vc : DetVectorCommitment X Y Msg Cm Td Pf ℓ) : Prop :=
  ∀ (H : X → Y) (m : Fin ℓ → Msg) (Q : Finset (Fin ℓ)),
    ∀ z ∈ support (simulateQ (VectorCommitment.fixedOracleImpl H) (vc.commit m)),
      evalWithAnswerFn (QueryImpl.ofFn H)
        (vc.check z.1 (PartialVec.restrict m Q) (vc.opening Q z.2)) = true

/-- Pointwise completeness of a deterministic scheme is pointwise completeness of its general
form. -/
theorem PerfectlyComplete.perfectlyCompleteForAll {vc : DetVectorCommitment X Y Msg Cm Td Pf ℓ}
    (h : vc.PerfectlyComplete) : vc.toVectorCommitment.PerfectlyCompleteForAll := by
  intro H m Q b hb
  simp only [VectorCommitment.completenessExp, toVectorCommitment, simulateQ_bind] at hb
  rw [mem_support_bind_iff] at hb
  obtain ⟨z, hz, hb⟩ := hb
  rw [liftComp_pure, simulateQ_pure, pure_bind,
    VectorCommitment.simulateQ_fixedOracleImpl_liftComp, support_pure,
    Set.mem_singleton_iff] at hb
  exact hb ▸ h H m Q z hz

/-- **Perfect completeness relative to every oracle distribution** (Def 3.7, p. 27) of a
deterministic scheme that is complete against every fixed function. -/
theorem PerfectlyComplete.toVectorCommitment [MeasurableSpace (X → Y)]
    {vc : DetVectorCommitment X Y Msg Cm Td Pf ℓ} (h : vc.PerfectlyComplete)
    (D : Measure (X → Y)) [IsProbabilityMeasure D] : vc.toVectorCommitment.PerfectlyComplete D :=
  h.perfectlyCompleteForAll.perfectlyComplete D

end DetVectorCommitment

/-! ## Input-output checks -/

section CheckIOOn

variable {X : Type u} {Y : Type v} [DecidableEq Y]

/-- `CheckIO` against a partial table `D` (p. 53): accept when every listed input has the listed
output in `D`; an empty cell rejects. Stated on `X → Option Y`, the type of
`Quantum.Database X Y`. -/
@[expose]
def checkIOOn (D : X → Option Y) (io : List (X × Y)) : Bool :=
  io.all fun p ↦ decide (D p.1 = some p.2)

/-- `checkIOOn` accepts exactly when every listed pair is in the table. -/
theorem checkIOOn_eq_true_iff (D : X → Option Y) (io : List (X × Y)) :
    checkIOOn D io = true ↔ ∀ p ∈ io, D p.1 = some p.2 := by
  simp [checkIOOn]

/-- Repeating a check is idempotent: removing duplicate pairs does not change acceptance. -/
theorem checkIOOn_dedup [DecidableEq X] (D : X → Option Y) (io : List (X × Y)) :
    checkIOOn D io.dedup = checkIOOn D io := by
  rw [Bool.eq_iff_iff, checkIOOn_eq_true_iff, checkIOOn_eq_true_iff]
  simp [List.mem_dedup]

end CheckIOOn

section CheckIO

variable {X : Type uX} {Y : Type} [DecidableEq Y]

/-- One step of `CheckIO`: query `p.1`, compare the answer with `p.2`, and conjoin the result
with the running verdict `acc`. -/
@[expose]
def checkIOStep (acc : Bool) (p : X × Y) : OracleComp (X →ₒ Y) Bool := do
  let y : Y ← (X →ₒ Y).query p.1
  pure (acc && decide (y = p.2))

/-- `CheckIO^f(x, y)` (ePrint 2025/2166, Def 8.1, p. 52): query every listed input `x` and
compare the answer with the listed output `y`. Every query is made, with no short-circuit. -/
@[expose]
def checkIO (io : List (X × Y)) : OracleComp (X →ₒ Y) Bool :=
  io.foldlM checkIOStep true

/-- One step of `CheckIO` against a fixed function compares the answer with the expected output. -/
@[simp]
theorem evalWithAnswerFn_checkIOStep (H : X → Y) (acc : Bool) (p : X × Y) :
    evalWithAnswerFn (QueryImpl.ofFn H) (checkIOStep acc p) = (acc && decide (H p.1 = p.2)) :=
  rfl

private theorem evalWithAnswerFn_foldlM_checkIOStep (H : X → Y) (io : List (X × Y))
    (acc : Bool) :
    evalWithAnswerFn (QueryImpl.ofFn H) (io.foldlM checkIOStep acc) =
      (acc && io.all fun p ↦ decide (H p.1 = p.2)) := by
  induction io generalizing acc with
  | nil => simp
  | cons p io ih =>
      rw [List.foldlM_cons, evalWithAnswerFn_bind, ih, evalWithAnswerFn_checkIOStep]
      simp [Bool.and_assoc]

/-- Against a fixed function `H`, `checkIO io` accepts exactly when `H x = y` for every listed
pair `(x, y)`. -/
theorem evalWithAnswerFn_checkIO (H : X → Y) (io : List (X × Y)) :
    evalWithAnswerFn (QueryImpl.ofFn H) (checkIO io) = io.all fun p ↦ decide (H p.1 = p.2) := by
  rw [checkIO, evalWithAnswerFn_foldlM_checkIOStep, Bool.true_and]

/-- Against a total table, `checkIOOn` is `checkIO` evaluated at the tabulated function. -/
theorem checkIOOn_some (H : X → Y) (io : List (X × Y)) :
    checkIOOn (fun x ↦ some (H x)) io =
      evalWithAnswerFn (QueryImpl.ofFn H) (checkIO io) := by
  simp [checkIOOn, evalWithAnswerFn_checkIO]

/-- Removing duplicate pairs does not change the acceptance of `checkIO` against any fixed
function. -/
theorem evalWithAnswerFn_checkIO_dedup [DecidableEq X] (H : X → Y) (io : List (X × Y)) :
    evalWithAnswerFn (QueryImpl.ofFn H) (checkIO io.dedup) =
      evalWithAnswerFn (QueryImpl.ofFn H) (checkIO io) := by
  rw [← checkIOOn_some, ← checkIOOn_some, checkIOOn_dedup]

end CheckIO

namespace VectorCommitment

variable {X : Type uX} {Y : Type} {Msg : Type uM} {Cm Td Pf : Type} {ℓ : ℕ} [DecidableEq Y]

/-- The `CheckIO` form of a check (ePrint 2025/2166, Thm 8.4 condition 1, p. 53): `Check`
uses no coins and runs an oracle-free, non-adaptive `OutputIO` followed by `CheckIO`; `Open` is
unconstrained. `OutputIO` returns `none` when the proof does not parse; the check then rejects
without a query, the projector `P̂ = 0` of p. 52.

`qVC` bounds the number of listed pairs by the size of the opened set and is non-decreasing, as
§3.5 assumes (p. 27), so `qVC qs` bounds the check of every opened set of size at most `qs`
(`length_le_of_card_le`). The paper's second argument `ℓ` of `q_VC(qs, ℓ)` (p. 54) is fixed by
the scheme and absorbed into `qVC`. -/
structure CheckIOForm (vc : VectorCommitment X Y Msg Cm Td Pf ℓ) where
  /-- `OutputIO(cm, Q, ans, pf) → (x, y)`, or `none` when `pf` does not parse. -/
  outputIO : Cm → PartialVec ℓ Msg → Pf → Option (List (X × Y))
  /-- `Check` is `OutputIO` followed by `CheckIO`, with no coins. -/
  check_eq : ∀ cm ans pf, vc.check cm ans pf =
    liftComp ((outputIO cm ans pf).elim (pure false) checkIO) (unifSpec + (X →ₒ Y))
  /-- The query complexity, as a function of the size of the opened set. -/
  qVC : ℕ → ℕ
  /-- The query complexity is non-decreasing (p. 27). -/
  qVC_mono : Monotone qVC
  /-- `OutputIO` lists at most `qVC |Q|` pairs. -/
  length_le : ∀ cm ans pf io, outputIO cm ans pf = some io → io.length ≤ qVC ans.dom.card

namespace CheckIOForm

variable {vc : VectorCommitment X Y Msg Cm Td Pf ℓ}

/-- `qVC qs` bounds the number of listed pairs for every budget `qs ≥ |Q|` (p. 27). -/
theorem length_le_of_card_le (h : CheckIOForm vc) {cm : Cm} {ans : PartialVec ℓ Msg} {pf : Pf}
    {io : List (X × Y)} (hio : h.outputIO cm ans pf = some io) {qs : ℕ}
    (hqs : ans.dom.card ≤ qs) : io.length ≤ h.qVC qs :=
  (h.length_le cm ans pf io hio).trans (h.qVC_mono hqs)

/-- `Check^D` against a partial table `D` (p. 53): reject when the proof does not parse, and
otherwise run `checkIOOn D` on the listed pairs. -/
@[expose]
def checkOn (h : CheckIOForm vc) (D : X → Option Y) (cm : Cm) (ans : PartialVec ℓ Msg)
    (pf : Pf) : Bool :=
  (h.outputIO cm ans pf).elim false (checkIOOn D)

/-- Against a total table, `checkOn` is the coin-free check evaluated at the tabulated
function. -/
theorem checkOn_some (h : CheckIOForm vc) (H : X → Y) (cm : Cm) (ans : PartialVec ℓ Msg)
    (pf : Pf) :
    h.checkOn (fun x ↦ some (H x)) cm ans pf =
      evalWithAnswerFn (QueryImpl.ofFn H) ((h.outputIO cm ans pf).elim (pure false) checkIO) := by
  rw [checkOn]
  cases h.outputIO cm ans pf <;> simp [checkIOOn_some]

/-- Against a fixed function `H`, a check of the `CheckIO` form deterministically returns the table
check at the tabulated function. -/
theorem simulateQ_check (h : CheckIOForm vc) (H : X → Y) (cm : Cm) (ans : PartialVec ℓ Msg)
    (pf : Pf) :
    simulateQ (fixedOracleImpl H) (vc.check cm ans pf) =
      pure (h.checkOn (fun x ↦ some (H x)) cm ans pf) := by
  rw [h.check_eq, simulateQ_fixedOracleImpl_liftComp, checkOn_some]

end CheckIOForm

end VectorCommitment
