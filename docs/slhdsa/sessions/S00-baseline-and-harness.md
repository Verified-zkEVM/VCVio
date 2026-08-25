# S00 — baseline and PR harness

Status: **ACCEPTED BY INDEPENDENT R9 PASS**

Input: VCVio `f1853af40da1efa11a71c2d7011996eebdbf6938`, branch
`codex/sphincsplus-formalization`

Allowed changes: `docs/slhdsa/**`, `scripts/slhdsa/**`

## Deliverables

S00 establishes the profile boundary, pinned source ledger and report corrections, current/target
specification, Lean/security blueprint, session plan, checked obligations, independent-review and
validation protocols, decision/finding logs, report scaffold, matrix schemas/seed rows, and safe
validators. It creates no formalization/library Lean source and makes no proof/conformance claim;
`scripts/slhdsa/PolicyAudit.lean` is a validation script outside `HashSig`.

## Captured baseline

| Check | Result | Interpretation |
|---|---|---|
| Lean | `v4.32.2` | Toolchain identity |
| `lake build` | PASS, 3008 jobs | Elaboration; inherited sorries exist elsewhere |
| `lake build HashSig` | PASS, 2744 jobs | Elaboration; local security sorry remains |
| `lake exe slhdsa_kat` | PASS | Runtime reduced SHA2-128-24 regression, not FIPS conformance |
| `lake exe slhdsa_c13_kat` | PASS | Runtime C13 regression, not FIPS conformance |
| HashSig `mk_all --check` | no update | Generated umbrella consistent |
| extern/interop isolation | PASS | Repository dependency boundary |
| EasyCrypt | not run; absent from PATH | No reproduction claim |

The only current `HashSig/**` sorry token is line 175 of `Security.lean`, in the theorem whose
declaration starts at line 150. `#print axioms` evidence is recorded in `validation.md`.

## Repair after the first review FAIL

The repair preserves the failed review and adds a pending `-r1` artifact. It:

- replaces regex checks with a comment/string-aware source-token layer over all `HashSig/**/*.lean`
  and an adversarial fixture corpus. Subsequent r1--r4 reviews proved that layer incomplete; it is now
  retained only as defense in depth while `PolicyAudit.lean` is authoritative;
- adds direct token fixtures for the r1--r3 spellings: interpolators, source `partial`/runtime
  overrides, qualified constructors, command-time mutation, initializer, and computed-field syntax;
- makes review verdict transitions exact, accepts a future single PASS, and rejects conflicting
  states and generated Python bytecode;
- adds machine-readable exact FIPS parameter/API/primitive data and a reproducible reference
  manifest/source-composite recipe;
- corrects the CCS WOTS-proof invalidation/repair boundary, nuanced FORS changes, WOTS checksum
  shift, and EasyCrypt classical-versus-quantum scope throughout the ledger/findings/report;
- repairs and checks declaration endpoint coordinates and records the concrete completeness axiom
  footprint; and
- changes scope choices from unapproved `ACCEPTED` prose to proposals with explicit approver/evidence
  fields.

No `HashSig` or other formalization Lean source is changed by this repair.

## Repair after the r4 review FAIL

R4 demonstrated four more source-token bypasses: `attribute [init]`, unprefixed interpolated strings,
option/label registration macros, and `native_decide` generated axioms. The r5 repair no longer
claims a source lexer can parse all Lean. The lexer remains a deterministic defense-in-depth check
with direct fixtures for those spellings. At that stage the full gate imported the completed HashSig
environment and identified declarations by their defining module, then rejected explicit/generated
axioms, transitive `sorryAx` except the exact S00 security placeholder, source/user partials, unsafe,
extern, initializer, and runtime-override entries. Compiled fixtures outside HashSig reproduced every
historical class, including the `native_decide` generated axiom. R5 later demonstrated that the axiom
policy and fixture matching were still incomplete; the next section records their replacement.

Lean 4.32.2 emits seven partial `._unsafe_rec` runtime helpers for ordinary recursive HashSig
definitions. They are not source `partial def`s. The audit pins their exact names and requires for
each the compiler-recursion name relation, same defining module as a safe non-partial parent, and no
unsafe/extern/init/runtime-override/axiom/`sorryAx` surface. Additions, removals, or renames fail.

Compiler warning-as-error source re-elaboration was evaluated but not added: warnings are configurable,
the exact Security placeholder needs a semantic exception, and source warnings do not expose every
macro/tactic-generated declaration. The authoritative audit instead uses the elaborated constants and
transitive `collectAxioms` result; ordinary build warnings remain visible review evidence.

## Repair after the r5 review FAIL

R5 demonstrated that a HashSig-owned theorem could transitively depend on a nonstandard axiom owned
by another module, and that aggregate fixture checks did not prove every historical counterexample
was individually detected. The r6 repair applies one decision function to every owned declaration's
complete `collectAxioms` result. It permits exactly `propext`, `Classical.choice`, and `Quot.sound`,
plus `sorryAx` only for `SLHDSA.slhdsa_euf_cma_security`. It gates the current union exactly and logs
the then-observed source-import/exported inventory of 647 owned constants without treating that
count as a permanent invariant.

The compiled self-test now requires a bijection between every actual finding and a table entry for
each historical declaration or generated-name pattern. It separately owns a theorem while excluding
its dependency axiom to reproduce the external-ownership attack. Attribute controls cover both
per-declaration status and persistent-extension entries contributed by each imported HashSig module:
ordinary and IR regular/builtin initializers, extern entries, and `implemented_by` entries. Its raw
entry test was intended to exercise that decision path, but r6 established that it handcrafted the
finding instead; the replacement is described below.

## Repair after the r6 review FAIL

R6 showed that the raw-entry test handcrafted a finding instead of exercising the production
module-entry mapping. The r7 repair replaces that path with one pure mapper over ordinary and IR
arrays for regular init, builtin init, extern, and `implemented_by`. The imported HashSig scan
retrieves all eight arrays and calls this mapper. The current-state fixture inserts raw entries for
all four attribute families, exports the actual private extension states, selects those fixture
entries, and calls the same mapper. Its exact expected table retains contributing-module and surface
identity, and finding/expectation matching remains bijective.

This fixture proves current-state extraction and production mapping for the four ordinary surfaces.
It does not compile and re-import a fixture module, so it does not independently test `.olean`
serialization or execute the imported IR getters. Those production getter calls remain subject to
API/line inspection and the blocking scan of every actual imported HashSig module; no stronger test
claim is made in S00.

## Repair after the r7 review FAIL

R7 proved that ordinary source import does not load a dependency's regular-initializer `.ir`
entries: the production scanner called `getModuleIREntries`, but the environment did not contain
those entries. An externally defined command generated a regular initializer from victim source
that contained no prohibited token, so both the defense-in-depth source policy and the nominally
passing semantic audit missed it.

The r8 repair removes the source import of `HashSig`. The authoritative audit now programmatically
meta-imports the compiled target with `loadExts := false`, checks that initializer execution is
disabled before and after import, and performs declaration, axiom, exact-helper, and all eight
persistent-extension decisions against that returned environment. The static import exposes 23
HashSig modules and 680 owned constants; the exact transitive axiom union is unchanged.

The full wrapper also compiles a temporary `HashSig.PolicyIRFixture` whose external command expands
to a side-effecting regular initializer although its victim source has no prohibited token. It
requires a nonempty `.ir`, rejects the exact `regular-init/ordinary` and `regular-init/ir` entries
through the same production importer/scanner/mapper, and proves the configured sentinel remains
absent. All generated fixture
artifacts live under a `mktemp` directory and are removed by a trap.

## Disposition after the r8 review FAIL

R8 found a false causal explanation in the validation prose. A controlled `loadExts := false`
comparison observes ordinary-exported 647, ordinary-private 680, and meta-private 680 HashSig-owned
constants. The 33-constant delta is therefore caused by private import visibility, not by meta import
or IR loading. The inventory figures remain reproducible observations rather than permanent gates.

IR coverage is evidenced independently: the compiled victim has nonempty regular ordinary and IR
persistent-extension entries; the production importer/scanner/mapper rejects both exact surfaces;
and the side-effect sentinel is absent before and after the static import. The r9 review must assess
this corrected disposition and the existing repair without treating declaration counts as IR
evidence.

## S00 acceptance gate

The implementer runs the docs-only validator and TeX build. A fresh reviewer must then validate all
FAIL-class findings, challenge authority/profile separation, inspect validator safety, reproduce the
baseline in proportion to risk, and complete `reviews/S00-adversarial-review.md`. That review failed
with eight findings; its r1 review then found an interpolation admission bypass and an untracked
`partial def` runtime boundary. R2 then found qualified admissions, separated/imported
interpolators, and command-time axiom injection. R3 then found initializer and computed-field runtime
attribute bypasses. R4 then found attribute-command, unprefixed-interpolation, macro-generated
initializer, and `native_decide` generated-axiom bypasses. R5 found the external-axiom dependency
bypass and non-bijective fixture assertions. R6 found that the raw extension test bypassed the
production mapper and covered only regular init. R7 proved that ordinary import left compiled
regular-initializer IR invisible to the production environment. R8 found that the harness falsely
attributed the 647-to-680 inventory delta to IR visibility; controlled imports instead attribute it
to private visibility. Independent r9 reproduced the corrected comparison and all blocking gates,
reported no new finding, and recorded PASS in `reviews/S00-adversarial-review-r9.md`. S00 is accepted
as the predecessor for S01.
