# Cryptol interoperability

This optional development connects Cryptol definitions to native Lean
implementations and VCVio specifications. The Cryptol language model and the
checked typed-AST importer are PolyFun's optional
[`PolyFunCryptol` case study](https://github.com/Verified-zkEVM/PolyFun/blob/main/PolyFunCryptol/README.md).
That case study follows Cryptol **3.6.0's reference semantics** for its
supported fragment and is not a verification of the Haskell evaluator. This
directory owns the Foundation correspondences, the VCVio specification and
oracle-client theorems, and the Foundation algorithm artifacts they are built
from. PolyFun owns the typed-AST exporter, the Foundation census and status, and
the evaluator audit; see its [tooling guide](https://github.com/Verified-zkEVM/PolyFun/blob/main/PolyFunCryptol/docs/tooling.md). Its
[semantic survey](https://github.com/Verified-zkEVM/PolyFun/blob/main/PolyFunCryptol/docs/evaluators.md) recommends the documented lazy
language semantics as the anchor for broader imports, with versioned backend
compatibility claims and explicit proof gaps.
The [tooling integration report](docs/tooling.md) records the implemented route,
architecture decisions, literature ancestry and remaining gates.

The [unified development tracker](https://github.com/Verified-zkEVM/VCVio/issues/879)
coordinates whole-Foundation import and the companion PolyFun work. Its
workstream sections own assignments, dependencies and progress; the
[delivery contract](docs/tooling.md#coordinated-development-contract) records
the canonical architecture, completion criteria and consumer proof obligations.
PolyFun's [Foundation status](https://github.com/Verified-zkEVM/PolyFun/blob/main/PolyFunCryptol/docs/compatibility.md) records, for every
module instance, the independent blockers and the language features they need.

Run commands from the VCVio repository root:

```bash
lake build CryptolBridge CryptolTests --wfail
lake build cryptol-interop
lake exe cryptol-interop model run productive_stream
lake exe cryptol-interop model arx-native 32 8
./scripts/validate.sh --cryptol --lint --test --axioms
```

The root manifest pins the companion PolyFun development, which hosts `PolyFunCryptol`, at
`367623629125d1dbab590e73f6979bfa2011cf6a`. The commands above and the separate
`Consumer` use that published dependency; no sibling checkout is required.
For local development against a different PolyFun checkout:

```bash
lake -R -KpolyfunPath=/path/to/PolyFun update PolyFun --keep-toolchain
POLYFUN_PATH=/path/to/PolyFun bash Interop/Cryptol/scripts/validate.sh --lint --test --axioms
```

Keep the resulting local path override out of the committed dependency manifest.
The optional workflow runs on PR changes affecting this project and uses the
committed PolyFun pin by default. Manual and reusable invocations can supply
`polyfun_ref` to check a companion revision. External Cryptol and Foundation
comparisons remain an explicit local validation option.

| Directory | Responsibility | Imports |
|---|---|---|
| `Bridge` | Foundation source artifacts and imports, SHA-256 correspondence, byte encoding, CRC updates and VCVio probability theorems | PolyFunCryptol, VCVio |
| `Tests` | Foundation, imported-source, API and executable regressions | Bridge, PolyFunCryptol |
| `Consumer` | A separate ordinary-import consumer using the root toolchain and dependencies | The public APIs |
| `scripts`, `artifacts` | Generators and committed exports for the Foundation algorithm artifacts, using PolyFun's exporter and shared helpers | External Cryptol and Foundation checkouts, PolyFun's `PolyFunCryptol/scripts` |

Default VCVio libraries and tests do not import Cryptol. The dormant Rust/hax/aeneas
aggregate remains separate. The isolation checker enforces the core/interop, native-FFI
and pure-algorithm boundaries.
The generated `Bridge` umbrella is maintained by `scripts/update-lib.sh` after
new modules have been staged.

Both resolved source and the native IR are PolyFun scoped polynomial trees.
Variables are leaves; operations describe child types and their binders.
Cryptol typing, demand rules and adequacy live in the `PolyFunCryptol` case study,
together with the generic renaming, substitution, interpretation,
represented-data and transition APIs it uses. Foundation specialization stays here.
Native lowering has one semantic route: native IR → resolved source → core.
A source certificate then transports arbitrary pre/postconditions, and the bridge
connects the certified compression function to VCVio's byte implementation and
adaptive oracle clients. See the [model guide](https://github.com/Verified-zkEVM/PolyFun/blob/main/PolyFunCryptol/docs/model.md) and
[Foundation guide](docs/foundation.md) for the precise claims.

The native prefix builder binds both the prefix and the newly computed entry,
then stores a prefix reference and a single append node.
`Term.nodeCount_prefixTable_le` proves a linear description-size bound when step
bodies have a uniform size bound. This is not an evaluation-time bound.
Ordered numeric, type, and proof binders use PolyFun's context-changing binding
families. One finite syntax tree denotes polymorphic map at finite or infinite
lengths; another supplies XOR with a representation certificate for every finite
width, including zero. Recursive groups take a single fixed point before
instantiation. The semantics distinguishes errors at successive quantifiers,
outer divergence, and a returned family with divergent instances.

Public beta laws, the closed resolved embedding, per-instance specification
transfer, whole-term parameter identity/composition, parameter/value fusion,
value-substitution composition and general semantic preservation of both
substitutions are proved. These laws cover all current constructors and partial
environments, including simultaneous recursion. Polymorphic operational adequacy,
syntax-producing specialization and official frontend correspondence remain
open. The [next milestones](https://github.com/Verified-zkEVM/PolyFun/blob/main/PolyFunCryptol/docs/model.md#audited-next-milestones) give their
scope and acceptance criteria; monomorphic adequacy keeps its original scope.

External evidence uses clean, pinned checkouts:

```bash
CRYPTOL_BINARY=/path/to/cryptol-3.6.0/bin/cryptol \
FOUNDATION_PATH=/path/to/Foundation \
  bash Interop/Cryptol/scripts/validate.sh --lint --test --axioms --external
```

Foundation is pinned to `7d0528bd998682788f4e23661f2829298f9e47db`; the extraction
manifest records files, identities and hashes. Validation does not download or
install these tools.

The current fragment is intentionally narrower than full resolved Cryptol.
The [coverage and gap ledger](https://github.com/Verified-zkEVM/PolyFun/blob/main/PolyFunCryptol/docs/model.md#coverage-and-gap-ledger) separates
proved capabilities, semantic spikes, and missing language features. In particular,
the certified importer still targets the Foundation SHA-256 subset. The
[pinned typed-AST exporter](https://github.com/Verified-zkEVM/PolyFun/blob/main/PolyFunCryptol/exporter/README.md) additionally retains complete
definitions for 31 SHA2/SHA3/SHAKE, Keccak, AES and CRC entries. Lean checks their
scope and kinds, and separately checks closed numeric and class constraints.
The scalar `(sigma_256_0 : [32] -> [32])` additionally has checked expression
elaboration from its exact quoted seven-declaration dependency graph. The kernel
checks its resolved output, and `ImportedScalar.core_correct` proves agreement
with `VCVio.Algorithms.Sha2.ssig0` for every input. This gate also supports lexical monomorphic declarations, records, tuples,
sequence literals, projections, closed guards and single-generator comprehensions.
The official specializer supplies a candidate for the scalar; a Lean proof checks
its partial meaning, and native evaluation certifies the scalar against `ssig0`
(`ImportedScalar.compiled`). PolyFun's nine importer canaries cover higher-order composition, folds,
captured locals and finite observations of infinite sequences. The broader graph
still needs general elaboration and source correspondence. Component theorems
cover Keccak coordinate inverses and byte-aligned
CRC polynomial updates; whole-algorithm differential tests exercise all SHA2,
SHA3 and SHAKE cores, AES vectors and CRC splits. The tests retain the pinned
reference evaluator's negative-index failure in Foundation Keccak separately
from normal-evaluator agreement. No full Cryptol soundness theorem or imported
CRC implementation certificate is claimed.

PolyFun's [evaluator audit](https://github.com/Verified-zkEVM/PolyFun/blob/main/PolyFunCryptol/docs/evaluators.md) compares the release with
upstream Cryptol, maps the integer discrepancy to Cryptol #2060, and distinguishes
language intent from backend compatibility. The portable theta variant is tested
there separately; the imported Foundation source retains its original bytes.

The [coverage catalogue](docs/coverage.md) separates planned reference coverage,
external probes and all-input Lean certificates, and records the next semantic
and algorithm milestones. Shared hashes live in `VCVio/Algorithms/`; conformance
proofs stay in this optional project.

PolyFun's [Foundation status](https://github.com/Verified-zkEVM/PolyFun/blob/main/PolyFunCryptol/docs/compatibility.md) covers all 135 tracked
source files and 155 module instances: export, scope, linking and typed
elaboration, with every independent blocker. The retained utility bundle
`artifacts/modules/list.json` supplies the complete `Imperative` import here.
Imperative's two definitions import together with shared recursive references;
generated bodies are checked against the retained source, and `Bridge.Imperative`
exposes lazy loop equations. Module interpretation follows the source groups;
exports close with the canonical polynomial `letE`/`letRec`, with a proved
agreement to the shared environment. No imported CRC equivalence or general
source-preservation theorem is claimed. The implemented partial List view
follows the existing tuple carrier and observes only the finite prefix; the
independent native CRC register has proved chunk-composition laws and
normal/reference evaluator regressions. The local obligation ledger is empty;
future named proof admissions must pass the compiled dependency audit, while
admitted implementations remain rejected.
