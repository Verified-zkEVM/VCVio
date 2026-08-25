# S00 adversarial review — re-review 8

Verdict: **FAIL**

Reviewer: independent R8 review sub-agent; not an S00 implementer

Reviewed commit/tree: VCVio `f1853af40da1efa11a71c2d7011996eebdbf6938`, branch `codex/sphincsplus-formalization`, plus the uncommitted S00 allowlisted tree under `docs/slhdsa/**` and `scripts/slhdsa/**`

Date: 2026-08-24

Independence statement: I did not implement S00 or its r8 repair and made no repository edits. I reviewed the source, Lean import APIs, generated fixture design, and independently constructed isolated `/tmp` import comparisons.

## Required checks

- [x] `PolicyAudit.lean` has no source import of `HashSig`.
- [x] The primary audit programmatically imports `HashSig` with `isMeta := true` and `loadExts := false`.
- [x] Declaration, transitive-axiom, compiler-helper, and eight module-entry decisions consume the returned environment.
- [x] Lean’s `importModules` implementation confirms `loadExts := false` avoids persistent-extension finalization and initializer execution.
- [x] The primary policy audit reproduces the 31 historical findings, external-axiom fixture, four raw mapper surfaces, seven helpers, 23 modules, 680 constants, and exact axiom union.
- [x] The compiled victim source contains no prohibited token, while its external macro expands to a side-effecting regular initializer.
- [ ] The inventory documentation accurately explains the 647-to-680 count change.
- [ ] Full validation, compiled sentinel execution, and TeX reruns were stopped after the decisive documentation issue, per the zero-issue rule.

## Commands and evidence

Repository state:

```text
git branch --show-current
codex/sphincsplus-formalization

git rev-parse HEAD
f1853af40da1efa11a71c2d7011996eebdbf6938
```

`git status --short` showed only the untracked S00 `docs/slhdsa/**` and `scripts/slhdsa/**` trees. `git diff --check` passed.

Primary semantic audit:

```text
lake env lean scripts/slhdsa/PolicyAudit.lean
```

reported:

```text
SLH-DSA historical elaborated-policy fixtures: PASS (31 exact findings)
SLH-DSA external-axiom owned-subset fixture: PASS
SLH-DSA raw extension-entry fixture: PASS (4 current-state surfaces via production mapper)
SLH-DSA static meta import: HashSig; loadExts=false; initializer execution false→false; 23 HashSig modules
SLH-DSA compiler-helper allowlist: PASS (7 exact `_unsafe_rec` auxiliaries)
SLH-DSA HashSig inventory: 680 owned constants; transitive axiom union exactly [propext, Classical.choice, Quot.sound, sorryAx]
SLH-DSA HashSig elaborated policy audit: PASS
```

I then independently imported the same compiled `HashSig` target three ways using `Lean.importModules`, always with `loadExts := false`, and counted declarations by defining module:

```text
R8 ordinary-exported: owned=647, regular=(0, 0)
R8 ordinary-private: owned=680, regular=(0, 0)
R8 meta-private: owned=680, regular=(0, 0)
```

The isolated script was `/tmp/slhdsa-r8-count.lean`; no repository file was changed.

## Prior-finding dispositions

The r7 implementation defect is substantially repaired in code:

- `PolicyAudit.lean` imports only Lean audit dependencies at source level.
- `importStaticTargetEnvironment` requests a meta import and explicitly passes `loadExts := false`.
- It checks initializer execution is disabled both before and after import.
- `collectAudit`, `validateCompilerHelpers`, and `collectHashSigModuleEntryFindings` all receive the returned environment.
- The production scanner retrieves all eight ordinary/IR arrays and sends them through the shared surface-labelled mapper.
- The external fixture macro genuinely expands to an initializer whose body writes the configured sentinel.
- The victim module imports that macro normally and invokes only its otherwise unrecognized command.
- The wrapper uses a quoted `mktemp` path, checks for a nonempty `.ir`, configures the sentinel, and installs an EXIT cleanup trap.

The earlier r0–r6 semantic defenses also remain present and reproduce in the primary audit. This does not dispose the new documentation finding below.

## New findings

1. **MEDIUM — the inventory delta is falsely attributed to IR-visible declarations.**

   `validation.md` states:

   > “The 33-constant increase over the obsolete ordinary-import count of 647 reflects IR-visible declarations.”

   The controlled import comparison disproves that causal explanation. An ordinary, non-meta import at `.private` level already contains all 680 owned constants. Changing only `isMeta` from false to true adds no owned constants. The exact 647-to-680 change is caused by moving from exported-level source-import visibility to private-level programmatic import visibility, not by loading IR.

   This matters because the count is presented as evidence about what the repaired IR path exposes. The actual IR coverage should instead be evidenced by the nonempty compiled initializer extension entries; the declaration-count delta cannot support that claim.

   Required disposition:

   - Correct `validation.md` to attribute the additional constants to private import level.
   - Keep IR coverage evidence separate and tied to the compiled fixture’s nonempty ordinary/IR extension findings and absent sentinel.
   - Receive a fresh independent re-review.

## Verdict rationale

The critical r7 import-path repair appears technically well directed, and the primary semantic audit passes. However, S00’s zero-issue rule explicitly includes documentation overclaims. The independently reproduced counts contradict the harness’s explanation of its new inventory evidence. R8 therefore fails and S01 remains blocked.

Full validation, compiled-sentinel execution, and TeX were not rerun after this decisive finding. I made no repository edits; all additional evidence was produced under `/tmp`.
