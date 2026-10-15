# Repository ownership and consolidation

Status: current placement policy; the migration table distinguishes planned moves.

## Source and build boundaries

| Area | Responsibility | Build and dependency boundary |
|---|---|---|
| `ToMathlib/` | General mathematical utilities intended for Mathlib | Below the cryptographic framework |
| `VCVio/` | Oracle computations, probability, program logic, crypto interfaces and reusable constructions | Main public library |
| `VCVio/Algorithms/` | Pure implementations, encodings and functional-correctness results | Planned destination; may use Mathlib, ToMathlib, generic PolyFun/CSLib and sibling algorithms |
| `VCVio/CryptoFoundations/` | Cryptographic interfaces, assumptions, games and generic reduction theory | Uses the framework; does not import concrete schemes |
| `VCVio/Schemes/` | Named constructions with their correctness and security proofs | Planned destination; uses algorithms and foundations, never Examples or widgets |
| `LatticeCrypto/`, `HashSig/` | Existing lattice and hash-signature libraries | Peers above VCVio; migrate only in dependency-complete slices |
| `VCVioCslib/` | Optional non-uniform complexity facade | Separate non-default Lake target |
| `VCVioComplexity/` | Optional concrete machine backend | Separate Lake package with coordinated pins |
| `Examples/` | Pedagogical consumers and proof walkthroughs | Above reusable libraries |
| `VCVioWidgets/` | Interactive proof visualizations | Presentation dependency, never a scheme dependency |
| `VCVioTest/`, `LatticeCryptoTest/`, `HashSigTest/` | Tests, vectors and executable regressions | Mirror the owning implementation; fixtures do not enter proof libraries |
| `Extern/`, `csrc/`, `third_party/` | FFI bindings, native shims and vendored backends | Proof libraries never import Extern; downstream links work without submodules |
| `Interop/` | Source-language models, imported references and conformance | Optional downstream development; core never imports it |
| `docs/`, `scripts/`, `.github/` | Guides, validation tools and CI | Commands and references follow the same ownership boundaries |

Root Lean files are public umbrellas; root Lake files define package and target boundaries.
Keep a separate library or package when dependency, trust or build isolation requires it.
A topic directory alone does not require another top-level library. In particular, shared
hash implementations belong in VCVio rather than in a new peer Algorithms library.

Keep one implementation and update its consumers when moving it. Preserve declaration names,
proof statements and attribution where a move changes only module ownership. Examples should
contain instructional uses, not forwarding aliases for library definitions. Test support may
be shared by other test libraries without pulling a scheme into pure implementation imports.

## Upstream comparison

[CSLib's algorithm policy](https://github.com/leanprover/cslib/blob/main/Cslib/Algorithms/README.md)
groups implementations and their correctness/complexity results, with language-specific
subdirectories and shared semantics elsewhere. VCVio currently has one native implementation
language, so an extra Lean directory would not distinguish implementations. Foreign source
models and conformance remain under Interop.

[PolyFun's ownership guide](https://github.com/Verified-zkEVM/PolyFun/blob/main/README.md)
places generic computation models, handlers and program logic below cryptographic applications.
Reusable semantic machinery belongs there; VCVio owns cryptographic interpretations and proofs.
Mathlib-facing additions remain in ToMathlib. Directory similarity to an upstream project does
not imply interchangeable semantics or justify copying its implementation.

Mathlib enforces directory independence with its
[`directoryDependency` linter](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Tactic/Linter/DirectoryDependency.lean),
including transitive imports. Its configuration is partly specific to Mathlib, and the v4.34
version keeps its rules in Lean. [importGraph](https://github.com/leanprover-community/import-graph)
provides reusable graph analysis; both projects use Lean's import parser.

VCVio uses `Lean.parseImports'` for its existing interop and FFI guards and the pure-algorithm
boundary. These are a few coarse independence requirements. The other placement rules above
are review guidance; the guard does not encode a total directory order or the whole framework
DAG. The source check needs the pinned Lean toolchain but no built modules or Lake dependencies.

## Migration slices

| Slice | Current location | Planned destination and prerequisites |
|---|---|---|
| Shared hashes | HashSig's SLH-DSA concrete modules | Algorithms in VCVio; pure tests and vector provenance in VCVioTest; retain SLH-DSA profile tests with HashSigTest |
| Schnorr and Pedersen | Examples | Schemes in VCVio, including the complete proof and test groups; keep instructional consumers |
| KEM–DEM and MAC-from-PRF | CryptoFoundations | Schemes in VCVio, including the measure component and security reductions |
| One-time pad | Examples | Separate its widget presentation before moving the reusable implementation |
| ElGamal | Examples | Move definitions, proofs, cost certificates and handler execution together after their dependency audit |
| GPV hash-and-sign | CryptoFoundations | Separate the generic preimage-sampling interface from the named construction, then update Falcon's consumer |
| HashSig and LatticeCrypto | Existing peer libraries | Later scheme-by-scheme moves with tests, FFI consumers and import updates; no wholesale relocation in this pass |

The first three slices are the current consolidation. Later rows record dependencies, not
claims that those moves or new proofs are already complete.

## Documentation checks

`scripts/check-agent-docs.py` inventories every tracked or non-ignored first-party Markdown
and Lean file. It checks local Markdown links and anchors, and repository-root file paths in
Markdown and Lean comments. Dependency URLs and explicitly historical or planned bare paths
are distinguished from live local references. Vendored submodules and ignored build artifacts
are outside that inventory; the CLAUDE symlink is checked through its canonical AGENTS source.

`scripts/check-doc-names.py --resolve` checks the agent guides against compiled declarations;
its retired-name pass also checks design notes, reading notes and source comments. Optional
backend names must be resolved in their owning environment. The reference audit also includes
build commands, dependency versions, upstream citations and script/CI consumers of moved files.
Generated guide fragments remain checked by `scripts/extract-doc-fragments.py --check`.

## Review stack and provenance

The review order is repository groundwork, shared algorithms, Lean 4.35 compatibility,
the remaining probability/program-logic work in PR #821, and Cryptol interop in PR #840.
Scheme moves branch after the refreshed #821 and do not block Cryptol review.

Preserved original inputs:

- Main: `afa6593f15e1e79ecb3cf22fc56191cecb452bb0`.
- PR #821: `53e93b7679cc222c26ad1027779e4840a4262a93`.
- PR #840: `2e26289cb94d2a287ae3a8a4f380304dd4b3cb99`.
- Remote archive branches: `archive/main-before-consolidation-20261015`,
  `archive/measure-before-consolidation-20261015`, and
  `archive/cryptol-before-consolidation-20261015`.

Extract the mixed commits by responsibility. The algorithm PR owns the native implementation,
its pure helper decomposition and tests; Cryptol source imports, semantic models and conformance
certificates stay in #840. The upgrade PR owns the dependency bump and required upstream API
port; the larger notation and tactic redesign stays in #821. Validate each PR against its own
base and pins, and compare the reconstructed combined tree against these preserved inputs.
