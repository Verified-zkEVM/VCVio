# Validation gates

## S00 harness gate

`scripts/slhdsa/check-harness.py` deterministically checks required files, verdict state, exact CSV
schemas/status vocabularies, the FIPS profile, reference manifest/hash recipe, JSONL endpoint columns
and bootstrap consistency, tree hygiene, and the exact current source sorry allowlist. Its
comment/string-aware token scan covers known dangerous spellings and direct r1--r4 counterexamples,
including `attribute [init]`, unprefixed brace interpolation, option/label registration macros, and
`native_decide`. This source scan is defense in depth: it is not a complete Lean lexer/parser,
elaborator, or declaration exporter and makes no fail-closed claim. The JSONL declaration inventory
remains explicitly manual/bootstrap until a later elaborated exporter is reviewed.

For S01's repaired HashSigTest inventory rows DECL-011 through DECL-014, dependency strings use a
typed, pipe-delimited convention that the normal checker validates exactly:

```text
lean-public|Fully.Qualified.Name
source-private-direct|repository/relative/file.lean|sourceName|line
root-entry-transitive|repository/relative/file.lean|main|line
lake-exe-direct|target
```

`lean-public` is an immediate public Lean callee. `source-private-direct` is an immediate edge to or
from a private source declaration, depending on whether it occurs in `direct_dependencies` or
`reverse_dependencies`; it is deliberately a source-logical anchor and never an externally
resolvable Lean name. `root-entry-transitive` is allowed only in `reverse_dependencies` and records
the downstream root-level executable entrypoint, not an immediate caller. `lake-exe-direct` is
likewise reverse-only and records the Lake target that directly selects the root module.

The normal Python/docs gate does not depend on prebuilt oleans. It byte-pins the three frozen ACVP
Lean sources, then uses the conservative comment/string-aware lexer on those exact files. This is
an intentionally narrow grammar for the frozen sources, not a general Lean parser: every active
backtick-parenthesis syntax quotation and macro/syntax/elab/run-command family is rejected before
source-logical declaration claims. A focused declaration extractor tracks named namespaces and the
one exact mutual block, fails closed on malformed lexical or scope state, and derives each active
declaration's fully qualified name, visibility, keyword, and line. It requires every public token to
source-resolve uniquely, every private token to name one active `private def` at its exact
path/name/line, and `main` to be one active public `def` in the empty namespace.

Literal comment-aware parsing of `lean_exe`/`root` stanzas remains defense in depth, not authority.
The normal gate runs `lake -R translate-config toml` against the actual repository into an absent
disposable `/tmp` path and parses it with Python `tomllib`. Under the pinned Lake 5 semantics,
package `srcDir` is inherited by a target that omits its own selector, while target `srcDir` is
relative to that package source root and is passed to Lean as `-R`. The live package must omit
`srcDir`, `moreLeanArgs`, and `weakLeanArgs`; the latter argument arrays could inject another `-R`.
The unique parser target must have exactly the `name` and `root` fields, so target-level source and
argument overrides and every other target override are rejected. `buildDir`, linker fields, and
dependency locations select output/tool inputs rather than the root Lean source; they are not used
as source identity evidence. Missing, duplicate, wrong-type, wrong-root, and selector records fail.
The exact r7 macro/quotation project and both r8 target/package `WrongSrc` projects are reconstructed
and rejected. Translation command failure, timeout, invalid TOML/schema, or non-ordinary output
fails closed and no translated file is written in the repository.

The full wrapper adds the elaborated layer only after `lake build HashSigTest`. It reruns the checker
in `--elaborated-s01-dependencies` mode, derives eight public/root names from the current inventory
rows and tokens, and imports ParserTests from a disposable external Lean file. All eight must
resolve; all eleven private source spellings plus both formerly claimed qualified-main spellings
must remain unresolvable. A dynamic `Does.Not.Exist` substitution is independently rejected by
Lean, so a consistent row/expected/pin mutation cannot pass merely by changing duplicated text.
Twenty-three direct source/token/static-Lake mutations cover the old names, false
line/name/direction/path, commented and quoted private anchors, balanced `Fake.main`, malformed/
underflow/unclosed state, nested/malformed quotations, metaprogramming families, missing/wrong/
duplicate literal mappings, and the r6 comment-shadowed four-root permutation. Nine selector-source
and thirteen translated-Lake mutations cover the r7 macro project, both r8 source-directory levels,
textual aliases, package Lean-argument selectors, and missing/wrong-type/wrong-root/duplicate records.

Immediately before parser runtime, the wrapper repeats the translated-configuration audit, creates
a mode-700 temporary parent, and designates an exact initially absent child as the root package's
build directory. The package's byte-pinned Lake configuration consumes only the checked
`-KbuildDir=<absolute-child>` override. The gate runs
`lake -R -H --no-cache -KbuildDir=<absolute-child> -J query slhdsa_acvp_parser:exe`: `-R`
re-elaborates configuration, `-H` rehashes inputs, and `--no-cache` prevents root-package artifact
restoration. Query status and its one JSON output record are checked byte-exactly. For each of
ParserTests, Schema, and StrictJson, one exact manifest names eight current files: `.olean`,
`.olean.hash`, module `.trace`, generated `.c`, `.c.hash`, `.c.o.export`, `.c.o.export.hash`, and
export-object `.trace`. All 24 paths must exist exactly once as ordinary non-symlink files inside
the newly created child. The three sidecars must be exact canonical 16-hex records equal to the
module trace's `o[0]` and `c` tokens and the object trace/executable-link token respectively. Each
module must have one exact canonical source input with its frozen SHA-256 and exact module identity;
the structured
trace follows its generated-C hash into the export object and requires that object/hash once in the
fresh executable's `linkObjs`. It also requires the structured ParserTests-to-Schema and
Schema-to-StrictJson direct import-artifact relationships. These records derive their relevance
from being created in the initially empty private root during this invocation; they are not treated
as self-authenticating records. Lake's `.ilean`, `.ir`, `.olean.server`, `.olean.private`, setup,
server, and other private-support outputs are outside this consumed/claimed artifact manifest and
provide no S01 acceptance evidence.

Before any filesystem access, the CLI rejects non-canonical raw absolute spellings, including
relative, root-equal, empty, `.`, `..`, duplicate-separator, and trailing-separator forms. Shared
functions require a nonempty proper relative component list. On Linux, traversal opens `/`, every
absolute root component, every relative parent, and the final file with descriptor-relative
`stat(..., follow_symlinks=False)` and `O_DIRECTORY|O_NOFOLLOW|O_CLOEXEC`/`O_NOFOLLOW` opens,
requiring metadata/opened device-and-inode identity at each step. Intermediate and final symlinks
therefore reject without following their targets. The checker hashes the exact fresh executable
with Python `hashlib.sha256` through that retained descriptor, streams the bytes, and rejects any
identity, size, or modification-time change across the read. The wrapper carries
the resolved path and SHA-256 in separate ordinary exclusive files, compares the path byte-for-byte
with the one permitted fresh-root location, recomputes SHA-256 immediately before and after
exact-path execution, and preserves stderr and exit status. It performs no second target lookup and
does not use Lake's adjacent `.hash` as cryptographic content authority. These sequential checks
assume no concurrent writer; they detect a post-execution change but are not an atomic
no-replacement primitive. The installed Lake/Lean/compiler, Python SHA-256 implementation, and
reused external dependency artifacts are in the TCB; reusable default root-package build artifacts
are outside the accepted parser gate.

Lake caches an elaborated package configuration in the repository even when root build artifacts
are redirected. Only after the bound post-execution SHA-256 succeeds, the wrapper reruns the same
translated-configuration audit without the override to restore the byte-pinned default build
directory before later repository-wide Lake commands. The checker requires both the pre-query
audit and this post-gate restoration; neither restoration nor default output contributes evidence
to the already completed accepted parser execution.

This typed convention is intentionally scoped to DECL-011--DECL-014. DECL-001--DECL-010 retain
legacy manual/bootstrap strings and receive no global external-resolution guarantee; F-018 remains
open until an elaborated exporter replaces the incomplete manual inventory. In the repaired rows,
DECL-011 now names its actual immediate `parameterByName` consumer, DECL-013 names private `runAll`,
and DECL-012/DECL-014 distinguish immediate private runtime consumers from the transitive root
`main` entrypoint.

```text
./scripts/slhdsa/validate.sh --docs-only
```

This is a documentation/schema/source-policy/provenance check. When the supplied sibling reference
bundle is present it reproduces all local hashes/revisions; otherwise it validates the immutable
manifest and prints how to set `SLHDSA_REFERENCE_ROOT`. It does not build libraries, run algorithms,
or run the external Lean dependency probe, but it does invoke Lake to re-elaborate and translate the
configuration as described above. The checker and wrapper set/expect bytecode-free execution and
reject `__pycache__`, `.pyc`, and `.pyo` debris.

## Full baseline/PR gate

```text
./scripts/slhdsa/validate.sh
```

The full wrapper runs the harness check, the builds, then
`lake env lean scripts/slhdsa/PolicyAudit.lean`. That script is the authoritative policy component.
It does not source-import `HashSig`: it programmatically meta-imports the compiled umbrella with
`loadExts := false`, verifies initializer execution is disabled before and after import, and applies
all decisions to the returned static environment. It determines declaration ownership from the
defining module (`HashSig`/`HashSig.*`). For every owned declaration it permits exactly the
transitive axioms `propext`, `Classical.choice`, and `Quot.sound`. The former S00
`SLHDSA.slhdsa_euf_cma_security` exception was removed by upstream main during B01; `sorryAx` is no
longer permitted anywhere in HashSig. Every other self, generated, or externally owned axiom
dependency fails. It also rejects unsafe and source/user partial constants, extern attributes, regular/builtin
initializer entries, and `implemented_by` runtime overrides.

The meta import loads reachable IR without finalizing persistent extensions or executing their
initializers. The audit inspects the ordinary and IR persistent-extension entries contributed by
every imported HashSig module for regular/builtin initializers, extern attributes, and
`implemented_by`; target-declaration ownership does not hide a module-owned entry. One pure mapper
receives all eight entry arrays with the contributing module and records the exact surface identity.
The production scanner retrieves each array from the corresponding extension and calls that mapper.
Compiled fixtures
outside HashSig exercise direct/qualified/interpolated admissions, command-injected and
`native_decide` axioms, unsafe/partial/extern, direct and macro-generated initializers, computed
fields, and runtime overrides. The 31 historical findings must match the expectation table
bijectively. Separate semantic fixtures own only a theorem that depends on an excluded axiom and
inject raw current-module entries for regular init, builtin init, extern, and `implemented_by`.
The latter fixture exports the real private extension states, filters its four targets, passes them
through the production mapper, and bijectively checks module and ordinary-surface identity.

The raw fixture establishes current-state extraction and mapping for the four ordinary surfaces.
In addition, the wrapper compiles an external command module and a `HashSig.PolicyIRFixture` victim
whose source has no prohibited policy token. The generated regular initializer has a side-effecting
sentinel body and a nonempty `.ir`. A second policy invocation imports that target through the same
static importer, retrieves the production regular-initializer ordinary and IR arrays, requires both
exact expected rejections (so loss of either path fails), and checks that the sentinel remains absent
before and after audit. The temporary
`.olean`, `.ilean`, `.ir`, and C artifacts are confined to a `mktemp` directory removed on exit.
The wrapper then runs the exact S03, 11-root S04, 14-root S05, 22-root S06, 15-root B02, and 27-root B03
declaration/axiom probes, generated umbrella check, extern and interop isolation, the two inherited
SLH-DSA KAT executables, and the S03 data/codec, S04 primitive, S05 WOTS, and S06 XMSS construction
executables. The KAT PASS results are legacy runtime regression evidence only, and the S03 PASS
result covers exact table rows, endian fixtures, ADRS,
and rejecting fixed-width codecs. The S04 result covers official SHA/HMAC/SHAKE vectors, derived
MGF1 regressions, padding/rate/domain boundaries, checked SHA2 addresses, output widths, and exact
all-twelve grammar fingerprints without claiming construction correctness, ACVP certification, or
mathematical refinement. It also verifies the primitive projection's whole-file SHA-256, parses the
four active SHAKE boundary records, and exact-compares their outputs to the runtime constants: the
empty-input 272-byte record is an official NIST example prefix, while the 135/136/137-byte `0x61`
input records are independently derived regressions. The S05 result covers all twelve approved
SHA2/SHAKE profiles, compares signing/recovery with public-key generation, and explicitly checks
every reachable SHA2 WOTS address through the rejecting adapter. Its separate `lgw = 2` canary
distinguishes the correct byte-aligned shift-zero encoding from erroneous shift-eight truncation;
neither result is claimed as a WOTS KAT or ACVP certificate. The
S06 result exhausts all four leaves and seven nodes of an address-sensitive height-two tree,
enumerates reachable address acceptance/round trips cheaply for all twelve approved profiles, and
checks bounded sign/recovery/root equality at indices 0 and 7 for SHA2/SHAKE-128f and SHA2-192f.
It is construction regression evidence, not an XMSS KAT, ACVP certificate, hash refinement, or
security reduction. A successful
`lake build` is elaboration evidence; it does not demonstrate concrete hash/vector execution. The
repository-wide `lake build` remains a final pre-review gate when changes touch shared VCVio
infrastructure.

Lean 4.33.1 generates exactly these seventeen partial runtime auxiliaries for safe, ordinary recursive
definitions in the current HashSig environment:

```text
SLHDSA.base2bFill._unsafe_rec
SLHDSA.base2bGo._unsafe_rec
SLHDSA.WotsChecksum.digitsOfBaseW._unsafe_rec
SLHDSA.chainWith._unsafe_rec
SLHDSA.xmssAuthPathWith._unsafe_rec
SLHDSA.forsAuthPathVectorM._unsafe_rec
SLHDSA.forsAuthPathVector._unsafe_rec
SLHDSA.LayerPosition.atWithLayer._unsafe_rec
SLHDSA.GeneralHypertree.signFromPositionWith._unsafe_rec
SLHDSA.GeneralHypertree.signFromPosition._unsafe_rec
SLHDSA.GeneralHypertree.signFromPositionM._unsafe_rec
SLHDSA.GeneralHypertree.recoverFromPositionWith._unsafe_rec
SLHDSA.GeneralHypertree.recoverFromPosition._unsafe_rec
SLHDSA.GeneralHypertree.recoverFromPositionM._unsafe_rec
SLHDSA.GeneralHypertree.signLoopQueryBound._unsafe_rec
SLHDSA.Security.perfectInternalCoords._unsafe_rec
SLHDSA.C13.chain._unsafe_rec
```

They are an exact compiler-helper allowlist, not a suffix rule. The semantic audit fails on a changed
set and checks `Lean.Compiler.isUnsafeRecName?`, equal defining modules, an existing safe/non-partial
parent, helper partiality, and absence of unsafe/extern/init/override/axiom/`sorryAx` surfaces.

A separate warning-as-error re-elaboration of every source module is not part of S00. Lean's warning
channel is configurable; at the current B01 boundary there is no HashSig admission exception.
per-file re-elaboration would also duplicate the build without establishing generated declarations or
transitive dependencies. The compiled-environment `collectAxioms` audit checks the exact empty admission policy and
macro/tactic-generated declarations directly. Build warnings remain review evidence, not the
authoritative admission decision.

The static audit observes 23 HashSig modules and 680 HashSig-owned constants. A controlled
`loadExts := false` comparison records `ordinary-exported: 647`, `ordinary-private: 680`, and
`meta-private: 680`. The 33 additional constants are caused by private import visibility, not by
meta import or IR loading. These counts are reproducible observations, not accepted as stable
invariants. IR coverage is separate evidence: the temporary compiled fixture has nonempty regular
ordinary and IR extension entries, both are rejected through the production path, and its side-effect
sentinel remains absent. The
union of their transitive axioms is gated exactly as
`{propext, Classical.choice, Quot.sound, sorryAx}` at S00, with `sorryAx` confined declaration-wise to
the one placeholder above. Additions and removals from this union fail.

At the repaired S03 candidate boundary the same audit observes 28 HashSig modules and 2,010 HashSig-owned
constants. It still finds exactly the seven compiler helpers above and exactly the same transitive
axiom union; these current counts are likewise inventory evidence rather than stable allowlist
values.

The S04 probe checks exact footprints for byte coherence, checked SHA2 address agreement, SHA2 and
SHAKE bundle selection/coherence, pure SHA-512, and SHAKE256. `ByteLaws.yToBytes_eq_iff` is
axiom-free; SHA2 roots use only `propext`, `Classical.choice`, and `Quot.sound`; SHAKE256 uses only
`propext` and `Quot.sound`. None depends on `sorryAx`. The full S04 candidate audit observes 29
HashSig modules and 2,139 HashSig-owned constants, retains exactly seven compiler helpers, and
retains the same exact transitive axiom union. These counts are observations, not stable limits.

At B01, upstream main and Lean 4.33.1 change the inventory to 32 HashSig modules and the exact five
helpers listed above. The aggregate upstream security placeholder is gone, so the transitive axiom
union shrinks monotonically to exactly `{propext, Classical.choice, Quot.sound}`. The semantic gate
continues to check every helper's generated-name relation, safe parent, ownership, and runtime
surfaces; neither the helper rule nor the axiom rule is broadened.

The S05 probe pins the checksum byte-capacity/equivalence roots, operational chain-length
equivalence and bounds, generic/checked SHA2 WOTS address roots, and the retained
`wotsPkFromSig_wotsSign` theorem. Their exact union remains within `{propext, Classical.choice,
Quot.sound}` and no root depends on `sorryAx`. The S05 candidate audit observes 34 HashSig modules
and 2,630 owned constants, with the same exact five compiler helpers and standard axiom union;
these counts remain reproducible observations rather than stable limits.

The S06 probe pins typed position and intrinsic authentication-path adapter/entry roots, the explicit FIPS
climb equalities, generic and checked concrete address boundaries, bounded honest correctness and
binding, and the retained canonical XMSS roots. The exact 22-root union remains within `{propext,
Classical.choice, Quot.sound}` and no root depends on `sorryAx`. The candidate audit observes 36
HashSig modules and 2,748 owned constants with the same exact five compiler helpers and standard
axiom union. These counts remain reproducible observations rather than stable limits.

The B02 probe pins exact message-digest byte extents and parsed indices, the valid-`d = 1`
tree-zero boundary, typed hypertree-position initialization/transition/final/address facts,
digest-derived FORS address fields, and retained Scheme query bounds and honest correctness. Its
15 exact roots remain within `{propext, Classical.choice, Quot.sound}` and none depends on
`sorryAx`. After integrating PR #595, the audit observes 37 HashSig modules and 2,852 owned
constants with the same exact five compiler helpers and standard axiom union. These counts are
reproducible observations rather than stable limits; general `LayerPosition` consumption remains
an S08/S09 construction obligation.

The B03 probe pins total typed layer trajectories; arbitrary-depth hypertree and general-scheme
naturality, deterministic interpretations, and honest correctness; depth-one output compatibility
with its explicit discarded-recovery trace; finite signing/recovery/verification query bounds;
encoded `AdrsKey` compatibility; the exact SUF event partition; structural reachable-target ledgers;
and the conditional scheme-interface/proposition shape. Its 27 exact roots remain within
`{propext, Classical.choice, Quot.sound}` and none depends on `sorryAx`. The query bounds are uniform
structural upper bounds, not exact message-dependent counts. The current audit observes 44 HashSig
modules and 3,447 owned constants and checks exactly seventeen named Lean-generated recursion
helpers with safe ordinary parents, including the generated `perfectInternalCoords` ledger helper,
and the unchanged standard axiom union. The callback-parametric `*With`
refinement, concrete encoded injectivity, actual-query/target-input coverage, canonical PR #594/#596
game adapters, the same-message SUF residual bound, and every security reduction remain open.

## Proof gate

For every completed load-bearing root, reviewers save exact `#print axioms` output. Acceptance
requires no `sorryAx`; any nonstandard axiom must resolve to `assumptions.csv` and `tcb.csv`. The S00
observations are:

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

The security root therefore fails the proof gate by design and cannot support any security claim.

## Vector and quantitative gate

Every vector record includes source repository/document, full revision/hash, test ID, profile,
interface, pure/pre-hash mode, expected disposition, and runner. ACVP results report positive and
negative coverage separately and never extrapolate across uncovered parameter/hash cells. Every
quantitative theorem has computable counts/losses, checked positivity and denominators, range bounds,
and evaluations for each claimed parameter set. An unevaluated symbolic expression is incomplete.

S01 adds two independent executable gates:

```text
python3 -B scripts/slhdsa/check-acvp-provenance.py
lake exe slhdsa_acvp_parser
```

The first is deterministic and network-free by default. It checks every committed fixture hash,
the hard-pinned upstream metadata, exact 12-set and 144-cell bijections, exact 24 positive pairs,
summary counts, and projection consistency. With `SLHDSA_ACVP_SERVER_ROOT` and/or
`SLHDSA_ACVP_PROTOCOL_ROOT` it additionally verifies a pinned full checkout, all 15 upstream files,
the protocol source/composite, and reproducible projections where the authoritative inputs exist.
Both normal gates compare exact-key/exact-value controlling records for final FIPS 205, current
ACVP-Server v1.1.0.43, the v1.1.0.38 compatibility boundary, the current protocol source, and the
SP 800-230 IPD/profile. This includes FIPS identity/locator/hash/size/final status/2024-08-13 date/
primary-normative classification, while the reference-manifest gate separately hashes the genuine
local PDF from the sibling bundle. Every normal run rejects mutations of FIPS date and authority,
current server release, protocol authority, compatibility commit, and draft status; the provenance
gate additionally mutates its compatibility/status records. No network is used.

The canonical `scope.md` table is parsed as data: the exact ordered six-profile set is unique, the
six-set IPD row is non-normative authority/profile only, and the distinct legacy row is one-set
current code only. Mutations changing the six-set row to either the deprecated ambiguous identifier
or the legacy identifier are rejected. A generic active-document scan rejects the deprecated ID
everywhere except the one exact historical F-031 line; immutable r0/r1/r2/r3 review occurrences are
allowed only because all four complete review-file hashes are separately fixed.

The active scan and whitespace gate cover all files under `docs/slhdsa/**`, `scripts/slhdsa/**`, and
the complete `HashSigTest/SLHDSA/**` test-support scope, including future untracked files. An exact
path-plus-normalized-line multiset registers every legitimate occurrence of the two current profile
IDs. Any added occurrence, even if it uses only current spellings, fails until intentionally added to
the manifest. Complete identity/claim/source/evidence/status/notes records are required for every
S01-relevant profile-bearing matrix row; the gate does not claim to understand arbitrary natural
language beyond those exact registered occurrences and records.

On the required Linux/Python platform, the walker opens the repository and each active root with
descriptor-relative `O_DIRECTORY|O_NOFOLLOW` operations. It enumerates held directory descriptors;
stats and opens every child relative to the same parent descriptor; and requires the opened type,
device, and inode to equal the no-follow metadata before any read or recursion. It never queues a
checked pathname. Platforms lacking these primitives fail closed. Deterministic pre-open hooks used
only by self-tests replace root, directory, and file objects and prove the production core rejects
before reading a replacement. Stable linked roots/files/directories, broken links, FIFOs, sockets,
devices, and every unsupported entry are also rejected. For each UTF-8 file
outside hash-locked review history, the gate also removes every non-ASCII-alphanumeric codepoint,
lowercases the result, and requires normalized identity counts to equal exact registered literal
counts. This catches comment/newline/quote/backtick/operator reconstruction; it is not a claim to
infer arbitrary prose semantics or recognize every Unicode confusable.

The canonical FIPS profile has an exact byte-size/SHA-256 pin plus exact top/API key sets,
authority, deterministic/hedged randomness, other-prehash rule, ordered Table-2 rows and OIDs, and
primitive grammars. The entire current `matrices/` path set and every file's bytes are likewise
pinned in addition to structured semantic checks. A later accepted session may change a matrix only
by deliberately updating its pin and receiving review; the policy does not freeze semantics forever.

Harness hygiene reads active files directly, so untracked S01 files cannot escape through
`git diff --check`. It rejects missing final LF, more than one terminal LF, internal tabs, and trailing spaces/tabs
under `docs/slhdsa/**`, `scripts/slhdsa/**`, and the full `HashSigTest/SLHDSA/**` tree. The only exclusions are
the exact two Markdown hard-break lines 7 and 32 in immutable historical
`reviews/S00-adversarial-review-r5.md`; changing any other active or historical line fails.

The Lean runtime uses a duplicate-preserving strict JSON parser before typed schema validation;
ordinary `Lean.Json.parse` is insufficient because duplicate object keys are overwritten. Positive
tests cover the three modes and all conditional group shapes. A separate negative corpus rejects
unknown/missing fields, duplicate or nonpositive IDs, empty collections, wrong discriminants/types,
invalid hex/widths, broken prompt/result bijections, invalid conditional fields, and 256-byte
contexts while accepting 255 bytes. It applies exact FIPS key/signature sizes but accepts all twelve
hash names advertised by ACVP rather than incorrectly imposing a FIPS pre-hash strength policy at
the transport-schema boundary.
The parsed-JSON prompt/results helpers and typed pair validator are private and explicitly consume
parser-established invariants. Public validation roots accept source strings only. The exact-wrapper
root strict-parses the complete `{prompt, expectedResults}` input, requires exactly those two keys,
and rejects top-level, nested, and escaped-equivalent duplicates plus unknown/missing wrapper keys.
The native gate currently executes 16 positive and 52 negative cases (68 total).
Immediately before execution the full wrapper repeats the authoritative translated-config audit.
It binds the resolved executable path and expected current SHA-256 in ordinary exact-record files,
recomputes the exact ordinary executable's SHA-256 immediately before runtime, and executes that exact path. It
captures stdout directly in an ordinary temporary file while leaving stderr visible and preserving
the executable status, prints that file, and byte-compares it with an exact 154-byte file containing
the positive-16, negative-52, and total-68 records and exactly one final LF. It then recomputes the
current hash even after successful stdout comparison and requires equality with the bound value.
Parser stdout and hash records never enter shell variables before byte comparison. File-comparator
self-tests reject C13, smoke, extra-nonblank,
missing-line, one-extra-terminal-blank, and multiple-extra-terminal-blank outputs; the same capture
path rejects an actual successful smoke executable and a nonzero producer.
The focused build-input partition is derived in the checker, compared with the observed conceptual
cases, and copied verbatim below. The six SHA-256 CLI cases are included within `path-cli=20`; they
are not a separate addend. Nominal successful resolution is a gate but not a mutation case.

focused-parser-partition: legacy=8; source-object-link=21; imports=4; sha-output-binding=9; path-cli=20; output-types=2; artifacts=130; wrong-srcdir=2; stale=2; fresh-root=5; query-output=5; replacement-cache=3; descriptor-lifecycle=6; descriptor-ownership=17; total=234; sha-cli-is-subset-of-path-cli=6; nominal-success-excluded=true

The descriptor-lifecycle category contains root-chain and relative-intermediate identity mismatch,
post-open `fstat` failure, and unexpected pre-`fstat` hook `RuntimeError`. Each of the six cases
repeats sixteen times, compares exact `/proc/self/fd` identity maps, keeps an unrelated sentinel
descriptor live, and requires the unexpected exception to propagate unchanged. The child owner
closes on every pre-transfer failure, and retained parents close on every propagated exception.
Final-file, stable-read/hash, fresh-root, sidecar-read, and exclusive-output paths use the same
non-retrying owner discipline. Shell-level expected/before/after hash-file mutations are separate.

The descriptor-ownership category contains seventeen production close-after-real-then-raise or
alias-preflight families. Each repeats at least sixteen times with two unrelated sentinels and exact
`/proc/self/fd` identity maps; hostile evidence and distinct-owner alias cases repeat 32 times:
forced same-number reuse in the older directory chain; active root, directory-at, recursive-file,
recursive-directory, top-level scan, and active-root loader cleanup; active read, SHA, and exclusive
output cleanup; nominal two-owner cleanup; fresh-root before/after cleanup; hostile active/nominal
evidence; and active/nominal distinct-owner aliasing with forced same-number reuse. One owner helper
preflights and marks all owners unowned, closes each unique integer at most once, preserves an active
original through explicit `BaseException.add_note`, derives evidence only from fixed strings and
builtin counts, and emits one deterministic nominal `CheckFailure` after every unique integer was
attempted. The exact scoped AST inventory records 10 production acquisitions/one close and 14
test-only acquisitions/18 real-close/real-dup captures; 30 alias, discard, rebinding, transfer,
consumer, and dynamic-import mutations reject. This is a narrow policy for the frozen source forms,
not a general proof against arbitrary Python reflection.

The wrapper runs seven production-state-machine cleanup regressions: explicit exit 7, errexit,
SIGTERM/143, initiating-failure plus restore failure, success plus restore failure, normal success,
and a representative resolve failure. Restoration is attempted while the temp root exists before
deletion; an initiating failure is never masked. SIGKILL cannot execute an EXIT trap.

`lake build HashSigTest` is a required elaboration gate because the library glob compiles every new
test module independently despite root-level `main` declarations. It does **not** execute those
entry points, so it cannot replace the explicit `lake exe slhdsa_acvp_parser` runtime command. The
dedicated executable target is necessary because imported parser definitions are not available to
Lean's source interpreter. The runtime parses bounded
committed projections rather than the roughly 69 MB full sigGen/sigVer source blobs; source hashes
and optional full-checkout verification retain provenance without imposing that memory cost on each
normal build.

Parser runtime success is parser/schema-format validation evidence only. It is explicitly not
implementation-conformance evidence, construction evidence, or security evidence. The normal gate
rejects the former unqualified phrase and requires this exact qualification. COV-005 remains
`missing`, S10-owned, and pending. The report's six-profile count is checked against the six exact
rows parsed from `scope.md`.

## Report gate

```text
cd docs/slhdsa/report
latexmk -pdf -interaction=nonstopmode -halt-on-error slhdsa-formalization-audit.tex
```

The compiled report is generated evidence and need not be committed. TeX success establishes syntax,
not substantive correctness. Traceability tables must agree with the machine-readable matrices.
