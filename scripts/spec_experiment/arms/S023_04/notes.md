# S023_04 programmedPreimage_perKey_eq_tsum — arm A

- Minutes: ~4
- Original: 15 lines / 440 HB (14 statement lines + `rw [OracleComp.prEvent_bind_eq_tsum]`).
- A: 15 lines / 418 HB, 197 tokens (vs 200): term proof `OracleComp.prEvent_bind_eq_tsum ..`.
- Reason code: NO-ROOM (one-step proof; the statement is the whole line count).
- Missing: nothing; the generic bind-to-tsum event lemma exists. (The theorem itself is a
  specialisation of `prEvent_bind_eq_tsum` and arguably need not exist.)

## B
- Minutes: ~1. B.lean = A.lean + import. 15 lines / 418 HB (A: 15 / 418).
- Library lemmas used: none. Looked at T1 `ProbBounds` (`prEvent_run_bind_eq_tsum`,
  `prEvent_simulateQ_run_bind_eq_tsum`): these are the StateT/simulateQ versions of the core
  `prEvent_bind_eq_tsum` that A already applies; this goal is a plain `ProbComp` bind.
