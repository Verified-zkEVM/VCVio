/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.VectorCommitment.Basic
public import VCVio.OracleComp.QueryTracking.QueryLogCheck

/-!
# Non-adaptive checks of vector commitments

The check of every vector commitment in §8 of ePrint 2025/2166 has a special form
(Def 8.1 and Thm 8.4 condition 1, pp. 52–53): an oracle-free, non-adaptive step computes a query
log, and `QueryLog.recheck` queries every logged input and compares the answer with the logged
one. `VectorCommitment.NonadaptiveCheck` records this non-adaptive check, which makes `Check`
deterministic and coin-free while leaving `Open` general, together with a non-decreasing bound
`qVC` on the length of the log (§3.5, p. 27).

## Main definitions

* `VectorCommitment.NonadaptiveCheck`: `Check` rechecks an oracle-free query log, and
  `VectorCommitment.NonadaptiveCheck.checkOn` checks the same log against a partial table.

## Main results

* `VectorCommitment.NonadaptiveCheck.simulateQ_check`: against a fixed function, a non-adaptive
  check returns the table check `checkOn`.
* `VectorCommitment.NonadaptiveCheck.length_le_of_card_le`: `qVC qs` bounds the check for every
  budget `qs ≥ |Q|`.
-/

public section

open OracleComp OracleSpec

universe uX uM

namespace VectorCommitment

variable {X : Type uX} {Y : Type} {Msg : Type uM} {Cm Td Pf : Type} {ℓ : ℕ} [DecidableEq Y]

/-- A non-adaptive check (Chiesa, Di, Hu and Zheng, ePrint 2025/2166, Thm 8.4 condition 1,
p. 53): `Check` uses no coins and computes an oracle-free, fixed query log from `(cm, ans, pf)`
alone (the paper's `OutputIO`), followed by `QueryLog.recheck`, which queries the logged inputs in
order; `Open` is unconstrained. `log` returns `none` when the proof does not parse; the check then
rejects without a query, the projector `P̂ = 0` of p. 52.

`qVC` bounds the length of the log by the size of the opened set and is non-decreasing, as
§3.5 assumes (p. 27), so `qVC qs` bounds the check of every opened set of size at most `qs`
(`length_le_of_card_le`). The paper's second argument `ℓ` of `q_VC(qs, ℓ)` (p. 54) is fixed by
the scheme and absorbed into `qVC`. -/
structure NonadaptiveCheck (vc : VectorCommitment X Y Msg Cm Td Pf ℓ) where
  /-- The query log to check at `(cm, ans, pf)`, or `none` when `pf` does not parse. -/
  log : Cm → PartialVec ℓ Msg → Pf → Option (QueryLog (X →ₒ Y))
  /-- `Check` rechecks the log, with no coins. -/
  check_eq : ∀ cm ans pf, vc.check cm ans pf =
    liftComp ((log cm ans pf).elim (pure false) QueryLog.recheck) (unifSpec + (X →ₒ Y))
  /-- The query complexity, as a function of the size of the opened set. -/
  qVC : ℕ → ℕ
  /-- The query complexity is non-decreasing (p. 27). -/
  qVC_mono : Monotone qVC
  /-- The log has at most `qVC |Q|` entries. -/
  length_le : ∀ cm ans pf L, log cm ans pf = some L → L.length ≤ qVC ans.dom.card

namespace NonadaptiveCheck

variable {vc : VectorCommitment X Y Msg Cm Td Pf ℓ}

/-- `qVC qs` bounds the length of the log for every budget `qs ≥ |Q|` (p. 27). -/
theorem length_le_of_card_le (h : NonadaptiveCheck vc) {cm : Cm} {ans : PartialVec ℓ Msg} {pf : Pf}
    {log : QueryLog (X →ₒ Y)} (hlog : h.log cm ans pf = some log) {qs : ℕ}
    (hqs : ans.dom.card ≤ qs) : log.length ≤ h.qVC qs :=
  (h.length_le cm ans pf log hlog).trans (h.qVC_mono hqs)

/-- `Check^D` against a partial table `D` (p. 53): reject when the proof does not parse, and
otherwise check the log against `D` with `QueryLog.agreesWith`. -/
@[expose]
def checkOn (h : NonadaptiveCheck vc) (D : X → Option Y) (cm : Cm) (ans : PartialVec ℓ Msg)
    (pf : Pf) : Bool :=
  (h.log cm ans pf).elim false (QueryLog.agreesWith (.ofFn D))

/-- Against a total table, `checkOn` is the coin-free check evaluated at the tabulated
function. -/
theorem checkOn_some (h : NonadaptiveCheck vc) (H : X → Y) (cm : Cm) (ans : PartialVec ℓ Msg)
    (pf : Pf) :
    h.checkOn (fun x ↦ some (H x)) cm ans pf =
      evalWithAnswerFn (QueryImpl.ofFn H)
        ((h.log cm ans pf).elim (pure false) QueryLog.recheck) := by
  rw [checkOn]
  cases h.log cm ans pf <;> simp [QueryLog.agreesWith_ofFn_some]

/-- Against a fixed function `H`, a non-adaptive check deterministically returns the table check
at the tabulated function. -/
theorem simulateQ_check (h : NonadaptiveCheck vc) (H : X → Y) (cm : Cm) (ans : PartialVec ℓ Msg)
    (pf : Pf) :
    simulateQ (fixedOracleImpl H) (vc.check cm ans pf) =
      pure (h.checkOn (fun x ↦ some (H x)) cm ans pf) := by
  rw [h.check_eq, simulateQ_fixedOracleImpl_liftComp, checkOn_some]

end NonadaptiveCheck

end VectorCommitment
