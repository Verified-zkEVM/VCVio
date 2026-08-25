# S00 adversarial review — re-review 4

Verdict: **FAIL**

No repository edits were made.

Reproduced counterexamples under Lean 4.32.2:

1. **CRITICAL — initializer attribute-command bypass**

```lean
def r4Init : IO Unit := pure ()
attribute [init] r4Init
```

The `builtin_init` variant also compiles. Both return `policy_findings = []`; the checker only recognizes `@[init]`/`@[builtin_init]`, not the valid `attribute [...]` command.

2. **CRITICAL — unprefixed interpolation admission bypass**

```lean
def r4DbgHidden : Nat :=
  dbg_trace "{(by sorry : Nat)}"; 0
```

Lean reports `declaration uses sorry`; `#print axioms r4DbgHidden` reports `[sorryAx]`, while `policy_findings = []`. The lexer skips Lean’s built-in unprefixed `interpolatedStr` grammar.

3. **HIGH — macro-expanded initializer bypass**

Both commands compile and return no policy finding:

```lean
register_option r4ReviewOption : Bool := { defValue := false }
register_builtin_option r4ReviewBuiltinOption : Bool := { defValue := false }
```

They macro-expand to `initialize`/`builtin_initialize` declarations. `register_label_attr` similarly compiled without a finding.

4. **HIGH — generated-axiom tactic bypass**

```lean
theorem r4NativeDecide : (1 : Nat) = 1 := by
  native_decide
```

`#print axioms` reports:

```text
[r4NativeDecide._native.native_decide.ax_1_1]
```

The checker returns `[]`.

Other evidence:

- `./scripts/slhdsa/validate.sh --docs-only`: PASS.
- `./scripts/slhdsa/validate.sh`: PASS, including builds, isolation checks, and both regressions.
- Reference manifest verified 18 local entries.
- FIPS parameter/API/source spot checks found no additional issue before the stop request.
- TeX build from the report directory: PASS, four pages, only minor overfull-box warnings.
- `git diff --check`: PASS.
- No Python bytecode debris was produced.

The token policy is therefore not fail-closed over the runtime/admission surfaces it claims to reject. S01 remains blocked pending repair and fresh review.
