# Foundation / VCVio compression bridge

The optional Cryptol bridge certifies SHA-256 **compression** from a preserved
Foundation source description to VCVio's actual byte-array `VCVio.Algorithms.Sha2.compress`.
It accepts any eight-word chaining state and any valid 64-byte window, including
unaligned nonzero offsets. It also retains the six scalar correspondences,
round-level contracts, exported linearity property, and Keccak bit-order probe.

## Project boundaries

The [single project](../README.md) has separate Model, Translation and Bridge
libraries in VCVio's root Lake configuration. Model and Translation import no
probability or cryptography. Bridge owns Foundation extraction, SHA-256
correspondence, byte encodings and adaptive probability theorems. Core VCVio
and HashSig never import the bridge. SHA2 and Keccak implementations belong to
`VCVio/Algorithms/`; the bridge has no HashSig dependency.

PolyFun owns generic scoped syntax, folds, continuous domains, prefix
recurrences, represented-data correspondence and deterministic execution adapters.
All targets use VCVio's Lean `v4.35.0` toolchain and common
Mathlib/CSLib pins. The [upstream ledger](upstream.md) records the fork and
external PR audit. The root manifest pins the published companion PolyFun
revision, so the bridge and its separate consumer build without a local override.

## Checked connection

| Boundary | Theorem / artifact |
|---|---|
| Reified source | `SourceFoundation.lean` retains `fix`, finite `foldl`, integer indices, the conditional schedule equations, lets and constants. |
| Partial source normalization | `compressionSource_correct` identifies its meaning on arbitrary partial inputs, using the equations in `SourceScalars.lean`. |
| Recurrence compilation | `scheduleMeaning_value` uses strict-prefix uniqueness and the least-fixed-point constructor rule for all 64 entries. |
| Fold compilation | `compressionFold_value` proves every intermediate state; `compressionMeaning_value` includes all 64 rounds and feed-forward. |
| Finite executable description | `compressionTerm_denote` and `compressionCertified` connect the retained source to a total native interpretation. |
| VCVio bytes | `compress_eq_decoded` proves loading, schedule expansion, rounds and feed-forward for `st.size = 8` and `base + 64 ≤ bytes.size`. Decoding concatenates four bytes most-significant first. |
| Specifications | `compression_contract_iff` and `compression_byte_contract_iff` pull or push arbitrary Lean pre/postconditions and require a fully represented result. |
| Adaptive clients | `simulate_compressionHandler_eq` and `compression_event_eq` quantify arbitrary adaptive clients and retain equality of the joint output and call-count state. |

`CompressionRequest` packages the two byte-boundary hypotheses.
`compiledCompress_eq` exposes the resulting ordinary function equality. Clients
need not unfold the source or the fixed-point construction. A sampled client
may invoke the adaptive theorem under a probabilistic bind; the original
sampled two-call word experiment remains an example of that pattern.

These are equalities between Lean models and implementations. The trusted
inbound boundary is Cryptol 3.6.0's frontend, constraint erasure, `:extract-coq`
dump, and the scoped structural reifier. It instantiates types, translates
single-generator comprehensions, introduces explicit beta-redexes and names
closed scalar units/captured functions. It does **not** unroll the schedule or
prove the compilation certificate. The older scalar/round finite decoder
still generates candidate implementations; Lean checks their relation to the
preserved full source. Hashes and dependency identities live in
[`artifacts/manifest.json`](../artifacts/manifest.json).

The source printer is tested against both Cryptol evaluators. Neither the
printer/parser round trip nor the Haskell implementation is proved in Lean.
The target for partial behavior is Cryptol's pinned reference evaluator;
[documented evaluator differences](https://github.com/Verified-zkEVM/PolyFun/blob/main/PolyFunCryptol/docs/model.md#external-evidence-and-evaluator-discrepancies)
still apply. No SAW proof artifact, solver certificate, FFI assumption,
`native_decide` axiom or admitted proof is used by the bridge certificate.

## Checked typed-AST scalar

`ImportedScalar.lean` reads `artifacts/references/scalar-bundle.json`, exported for
`(sigma_256_0 : [32] -> [32])`, with `cryptol_import`, naming the root `smallSigma256Zero`. The bundle retains all seven
dependencies, source schemes, ordered type/proof applications and module digests.
The import does not specialize or normalize the expression.

`SourceElaboration.check` validates scopes, kinds, closed constraints, binder
identities, application types and result annotations before building typed
resolved syntax. The import's `smallSigma256Zero.accepted` checks the exact output in the
kernel, and `ImportedScalar.accepted` identifies it with the retained Foundation term;
`partial_correct` retains the existing partial-input equation and `core_correct`
proves agreement with the actual `Sha2.ssig0` for every `UInt32`. No sampled
evaluation or native proof oracle is used in that theorem. Mutation tests reject
wrong result/argument types, missing proofs, failed constraints and unsupported
primitives.

`ImportedScalar.compiled` is a native certificate for this exact imported source:
native evaluation of the import equals `Sha2.ssig0`, and PolyFun's fundamental lemma
supplies the lazy meaning. `core_contract_iff` transfers
arbitrary bitvector pre/postconditions to core `Sha2.ssig0` through the shared
PolyFun correspondence machinery.

This pilot does not turn the whole corpus into a verified frontend. Source-byte
provenance still uses the pinned exporter and regeneration hashes, and general
semantic preservation of the source-AST elaborator is a further obligation.
The existing compression path and probability theorems retain their boundaries.

## Checked upstream specialization

The official specializer produces `artifacts/references/specialized-scalar-bundle.json`;
`cryptol_import` checks its monomorphic local declarations and root schema. `ImportedSpecialization.correct`
proves equality of its partial meaning with `ImportedScalar`, whose native
certificate supplies the all-input agreement with `ssig0`. The corresponding core theorem
still quantifies over every input. This scalar pilot is independent of the older
full-compression certificate: that certificate has not yet migrated to the broader
typed-AST importer. See [tooling integration](tooling.md) for the whole-Foundation
census, canonical choices and remaining compression/CRC obligations.

## Reproduce

From the VCVio repository root, use the commands in the [project README](../README.md).
The optional driver builds and lints the model and bridge, checks zero axiom debt,
builds the ordinary-import consumer, exercises model and compression regressions,
and runs VCVio's SHA2/SHAKE primitive vectors. `--external` additionally reproduces
all generated artifacts and compares both Cryptol evaluators. Reports default to
`/tmp/vcvio-cryptol-validation`; set `CRYPTOL_REPORT_DIR` to choose a destination.

Regenerate artifacts with
`python3 Interop/Cryptol/scripts/extract_foundation.py --cryptol … --foundation …`;
add `--check` to require byte-for-byte reproduction. After staging new modules,
run `./scripts/update-lib.sh` to regenerate all optional umbrellas.

The optional `cryptol.yml` workflow takes an explicit PolyFun revision and runs
the Lean, lint, regression, and axiom checks. External Cryptol/Foundation checks
use the project README's command with the pinned tools. Manual dispatch requires the
workflow to be available on the default branch; this package stays outside the
default VCVio graph.

## Executable probes and limits

```bash
.lake/build/bin/cryptol-interop foundation emit-compression-source
.lake/build/bin/cryptol-interop foundation emit-compression
.lake/build/bin/cryptol-interop foundation compression-sizes
.lake/build/bin/cryptol-interop foundation compress BASE STATE_JSON BYTES_JSON
```

The last command requires eight unsigned 32-bit state words and a valid byte
window. Its JSON report compares the finite interpreter with the actual VCVio
function, and includes node counts and native elapsed time. External tests use
zero, all-one, one-hot/ramp and seeded random cases at offsets 0, 1, 2, 3 and 17;
they also mutate unused buffer prefixes/suffixes and reject invalid boundaries.
The three paths—Foundation, preserved export and compiled export—are checked
with both normal and reference evaluation. These comparisons are evidence about
the trusted boundaries, separate from the universal Lean theorem.

The pinned Lean `Fin.cases` implementation exposed a substantial vector-lookup
cost during this test. `ToCslib.Data.Fin.Cases` supplies proved compiler
simplifications for case analysis and its tuple/vector wrappers. Named scalar
source equations likewise keep normalization proof checking practical.

The reports record native execution time, retained and compiled source sizes,
and prefix-table growth. The prefix compiler stores a prefix reference and one
step per entry; `Term.nodeCount_prefixTable_le` proves a linear syntax-size bound
for uniformly bounded step bodies. Round syntax also grows linearly in the
number of updates. These are description-size properties; measured elapsed time
is diagnostic evidence, not a machine-independent resource bound.

This milestone does not prove full SHA-256 hashing or padding, Keccak
compression, a general recursion compiler, cryptographic security, or a
Cryptol runtime/resource bound. The adequate call-by-name core machine remains
a bounded demand probe; full compression uses the finite native interpreter.
The next broader language task is a reusable checked recurrence/loop compiler
with an explicit supported-shape certificate, evaluated on a second algorithm.

The [coverage catalogue and next milestones](coverage.md) record the broader
reference corpus and the distinction between tests and proved correspondence.
