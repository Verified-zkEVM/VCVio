# S00 adversarial review — re-review 9

Verdict: **PASS**

Reviewer: independent R9 review sub-agent; not an S00 implementer

Reviewed commit/tree: VCVio `f1853af40da1efa11a71c2d7011996eebdbf6938`, branch `codex/sphincsplus-formalization`, plus the uncommitted S00 allowlisted tree under `docs/slhdsa/**` and `scripts/slhdsa/**`

Date: 2026-08-24

Independence statement: I did not implement S00 or any r9 repair and made no repository edits. Independent reproduction scripts and TeX output were confined to `/tmp`.

## Required checks

- [x] Every finding through r8 has an evidence-backed disposition.
- [x] The immutable r8 artifact remains `FAIL`, and the frozen r9 artifact was `PENDING` before this reviewer-authored verdict.
- [x] Inventory evidence distinguishes ordinary-exported 647 from ordinary-private and meta-private 680 without attributing the 33 private declarations to IR or meta loading.
- [x] IR coverage rests on the compiled victim’s nonempty exact ordinary/IR initializer entries and absent side-effect sentinel.
- [x] `PolicyAudit.lean` has no source import of `HashSig`.
- [x] The primary audit imports `HashSig` with `isMeta := true` and `loadExts := false`.
- [x] Declaration, transitive-axiom, compiler-helper, and all eight module-entry decisions consume the returned static environment.
- [x] The 31 historical findings, external-axiom fixture, four raw current-state surfaces, and seven exact compiler helpers pass bijective or exact checks.
- [x] The wrapper’s path handling, environment setup, sentinel checks, temporary-artifact cleanup, and command scope are safe and effective.
- [x] Current gate, session, findings, TCB, report, and review indexes consistently described r8 as failed and r9 as pending before independent acceptance.
- [x] Docs-only validation, shell syntax, full validation, root axiom inspection, TeX, diff, scope, and hygiene checks pass.

## Commands and evidence

Repository state:

```text
git branch --show-current
codex/sphincsplus-formalization

git rev-parse HEAD
f1853af40da1efa11a71c2d7011996eebdbf6938
```

`git status --porcelain=v1 -uall` showed only files under the S00 allowlist:

```text
docs/slhdsa/**
scripts/slhdsa/**
```

There were no tracked or staged changes, no generated Python or TeX debris in the allowlisted tree, and `git diff --check` passed.

I independently imported the same compiled `HashSig` target four ways, always with `loadExts := false`:

```text
R9 ordinary-exported: owned=647, regular=(0, 0), init=false→false
R9 ordinary-private: owned=680, regular=(0, 0), init=false→false
R9 meta-exported: owned=647, regular=(0, 0), init=false→false
R9 meta-private: owned=680, regular=(0, 0), init=false→false
```

This confirms that the 647-to-680 declaration delta is entirely an exported-to-private visibility change. Switching ordinary to meta import changes neither exported nor private declaration counts.

Lean 4.32.2’s `finalizeImport` installs ordinary serialized entries and IR base entries before its conditional `if loadExts` branch. Thus `loadExts := false` preserves the static entry arrays without finalizing persistent extensions. `PolicyAudit.lean` requests a meta import, verifies initializer execution is false before and after import, and passes the returned environment to declaration, axiom, helper, and module-entry checks.

The defense-in-depth source policy reports no finding for the compiled victim:

```text
[]
```

The external fixture command nevertheless expands that victim to a side-effecting regular initializer, so the fixture is a genuine reproduction of the r7 source-policy evasion.

Direct authoritative audit:

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

Code inspection confirmed that the shared production mapper labels all eight surfaces:

```text
regular-init/ordinary
regular-init/ir
builtin-init/ordinary
builtin-init/ir
extern/ordinary
extern/ir
implemented-by/ordinary
implemented-by/ir
```

The imported-module scanner retrieves every corresponding ordinary and IR array from the returned static environment. The raw current-state fixture exports the actual private states for regular init, builtin init, extern, and `implemented_by`, filters its four targets, and passes them through that same mapper.

Full validation:

```text
./scripts/slhdsa/validate.sh
```

passed, including:

```text
Build completed successfully (3007 jobs).
Build completed successfully (2744 jobs).
SLH-DSA compiled fixture entries:
  regular/ordinary=[(hiddenInitializer, ...)]
  regular/ir=[(hiddenInitializer, ...)]
SLH-DSA compiled initializer fixture: REJECTED on exact ordinary and IR surfaces; configured sentinel remained absent
No update necessary
Extern isolation check: OK.
Interop TCB isolation check: OK.
SLH-DSA-SHA2-128-24 KAT: PASS (valid signature accepted, tampered rejected)
SLH-DSA-C13 KAT: PASS (valid signature accepted, tampered rejected)
SLH-DSA full baseline validation: PASS
```

The wrapper required a nonempty victim `.ir`, checked the sentinel before and after the audit, and removed the quoted `mktemp` directory through its EXIT trap. The logged temporary directory and sentinel were absent after completion.

Independent root inspection reported:

```text
SLHDSA.slhVerifyInternal_slhSignInternal:
  [propext, Classical.choice, Quot.sound]

SLHDSA.slhdsaAlg_perfectlyComplete:
  [propext, Classical.choice, Quot.sound]

SLHDSA.Concrete.shaPrimitives_perfectlyComplete:
  [propext, Classical.choice, Quot.sound]

SLHDSA.slhdsa_euf_cma_security:
  [propext, sorryAx, Classical.choice, Quot.sound]

SLHDSA.C13.slhVerifyInternal_slhSignInternal:
  [propext, Classical.choice, Quot.sound]
```

This agrees with the declared S00 exception and exact union. The one `sorryAx` remains confined to the explicitly open security placeholder.

Additional gates:

```text
./scripts/slhdsa/validate.sh --docs-only
SLH-DSA harness check: PASS
SLH-DSA docs-only validation: PASS

bash -n scripts/slhdsa/validate.sh
PASS

latexmk -pdf -interaction=nonstopmode -halt-on-error \
  -outdir=/tmp/slhdsa-r9-tex slhdsa-formalization-audit.tex
PASS, 4-page PDF
```

The TeX build had only minor overfull-box warnings.

## Prior-finding dispositions

- The r0–r4 source-policy bypass classes are covered by the authoritative semantic audit and the bijective table of 31 exact elaborated findings. The source lexer is accurately limited to defense in depth.
- The r5 external-axiom ownership bypass is rejected by auditing each owned theorem’s complete transitive axiom set; the dedicated excluded-owner fixture passes exactly.
- The r5 aggregate-fixture weakness is repaired by bidirectional exact matching: every expected finding matches once, every actual finding matches once, and sizes agree.
- The r6 handcrafted raw-entry weakness is repaired by exporting four actual private extension states and feeding their targets through the production mapper.
- The r7 ordinary-import IR invisibility is repaired by removing the HashSig source import, using `isMeta := true` with `loadExts := false`, and auditing the returned environment throughout.
- The compiled r7 fixture independently proves that the token-free victim exposes nonempty regular ordinary and IR entries through the production scanner and that static import does not execute its initializer.
- The r8 documentation overclaim is corrected everywhere outside the immutable historical review: controlled counts attribute the 33 declarations solely to private visibility, while IR coverage is tied only to the compiled extension entries and absent sentinel.
- The current session, validation, findings, TCB, report, and review indexes consistently preserved r8 as failed and did not self-certify r9 before this review.

## New findings

None.

## Verdict rationale

The r7 implementation repair is effective, and the r8 causal documentation error is fully corrected. Independent controlled imports reproduce the visibility explanation; the compiled fixture supplies direct, nonempty IR evidence without executing its initializer. The complete docs-only and full gates, exact semantic fixtures, root axiom inspection, TeX build, scope check, and hygiene checks pass with no issue.

S00 passes independent re-review r9 and may serve as the accepted predecessor for S01.
