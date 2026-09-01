# Validation boundary

The authoritative commands are:

```text
./scripts/slhdsa/validate.sh --docs-only
./scripts/slhdsa/validate.sh
```

The docs-only mode runs the deterministic harness and ACVP provenance verifier. The full mode also
builds the repository and HashSig libraries, checks exact axiom footprints and source policy,
checks generated imports/isolation, runs construction and primitive executables, and executes the
fresh strict-parser gate.

## Permanent logical audits

`scripts/slhdsa/AxiomAudit.lean` names 151 unique load-bearing roots. It checks equality with exact
expected axiom sets, not merely absence of admissions: 6 roots are axiom-free, 25 use only
`propext`, 10 use `propext` and `Quot.sound`, and 110 use the standard
`{propext, Classical.choice, Quot.sound}` set.

`scripts/slhdsa/PolicyAudit.lean` inventories HashSig-owned declarations and rejects unexpected
axioms, `unsafe`, `extern`, initializer, runtime-override, and persistent-environment mutation
surfaces. Under Lean 4.33.1 it accepts exactly 17 generated unsafe recursion helpers, each tied to a
named safe construction/query parent and checked for module ownership, partiality, and absence of
other privileged surfaces. Qualified proof identifiers ending in names such as `run_bind` are not
environment-mutation commands; token-boundary fixtures distinguish these from real commands.

## Build, import, isolation, and runtime gates

The wrapper runs the aggregate build plus `HashSig` and `HashSigTest`; validates the generated
umbrella; and checks ordinary/interop isolation. Runtime targets cover legacy regressions, all-set
parameter/codec behavior, primitive vectors and grammar fingerprints, WOTS, XMSS, FORS, and the
strict ACVP parser. These runs are construction regressions: they do not establish cryptographic
hardness, ACVP certification, or deployment refinement.

## Strict ACVP parser gate

The harness checks the parser/schema/strict-JSON source grammar, exact Lake target shape, public and
private declaration visibility, and statically named typed dependency tokens. Eight public/root
probe cases must elaborate and thirteen private/false cases must be rejected. Mutation fixtures
cover source declarations, dependency substitution, imports, Lake configuration, output names,
path arguments, cache selectors, and object ownership.

The full wrapper builds into an initially absent mode-700 private root with caches disabled. It
requires the exact source/module/C/object/link-trace/sidecar inventory, recognizes both supported
Lean/Lake link-trace schemas, rejects dependency substitution or ambiguous object ownership, and
resolves the exact ordinary executable without symlink or special-file fallback. Descriptor-relative
no-follow traversal binds identity and SHA-256 before and after execution. Cleanup tests cover
ordinary success, explicit failure, errexit, handled signals, and restoration failure; SIGKILL
cannot run shell EXIT traps.

The parser output must be exactly the three frozen PASS lines for 16 positive, 52 negative, and 68
total cases. Extra, missing, or blank output is rejected.

focused-parser-partition: legacy=8; source-object-link=21; imports=4; sha-output-binding=9; path-cli=20; output-types=2; artifacts=130; wrong-srcdir=2; stale=2; fresh-root=5; query-output=5; replacement-cache=3; descriptor-lifecycle=6; descriptor-ownership=17; total=234; sha-cli-is-subset-of-path-cli=6; nominal-success-excluded=true

## Provenance and authority gates

The manifest pins controlling FIPS, primitive, ACVP, draft-profile, security, repository, and
fixture records. Validation reproduces the active Lean source composite and its mutation canary,
checks the FIPS and draft profile matrices, and validates the 15 ACVP sample hashes plus bounded
projections. ACVP sample JSON has `isSample = true`; positive coverage is measured per cell and is
not generalized beyond observed evidence.

Identity scanning rejects deprecated or reconstructed profile spellings across active tracked and
untracked files. Current matrix bytes are pinned in the harness in addition to structured schema and
semantic checks. Changing a matrix therefore requires an explicit pin update together with the
technical record change.

## Trust boundary

The Lean kernel, compiler/code generator, Mathlib/VCVio dependencies, installed Lake/Python/shell
tools, external source bytes, and test-vector provenance remain trusted inputs as recorded in
`matrices/tcb.csv`. Sequential before/after hashing is not an atomic replacement barrier, and shell
cleanup cannot survive SIGKILL. The validation wrapper is designed to expose these limits rather
than convert them into implementation or security claims.
