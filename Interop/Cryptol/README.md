# Cryptol interoperability

This optional development connects resolved Cryptol descriptions, a lazy Lean
semantics, total native implementations, and VCVio specifications. It shares
VCVio's root toolchain and dependency manifest. The specification target is
Cryptol **3.6.0's reference evaluator**; normal-evaluator differences are recorded
in the [model guide](docs/model.md).

Run commands from the VCVio repository root:

```bash
lake build CryptolModel CryptolTranslation CryptolBridge CryptolTests --wfail
lake build cryptol-interop
lake exe cryptol-interop model run productive_stream
lake exe cryptol-interop model arx-native 32 8
./scripts/validate.sh --cryptol --lint --test --axioms
```

The root manifest pins the companion PolyFun development at
`c026908c752879cd08bf5fdc079162d543795476`. The commands above and the separate
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
| `Model` | Types, resolved and ordered polymorphic syntax, lazy domains, monomorphic operational semantics and adequacy, primitive demand rules | PolyFun, CSLib, Mathlib |
| `Translation` | Native scoped IR, representation relation, source translation, certificates, quotation and export | Model |
| `Bridge` | Foundation source artifacts, SHA-256 correspondence, byte encoding and VCVio probability theorems | Model, Translation, VCVio |
| `Tests` | Public API, semantic and rejection regressions | The three optional libraries |
| `Consumer` | A separate ordinary-import consumer using the root toolchain and dependencies | The public APIs |

Default VCVio libraries and tests do not import Cryptol. The dormant Rust/hax/aeneas
aggregate remains separate. The isolation checker enforces the core/interop, native-FFI
and pure-algorithm boundaries; the internal Model/Translation/Bridge direction guides review.
The three generated umbrellas are maintained by `scripts/update-lib.sh` after
new modules have been staged.

Both resolved source and the native IR are PolyFun scoped polynomial trees.
Variables are leaves; operations describe child types and their binders.
Renaming, substitution, interpretation and their general laws live upstream.
PolyFun also owns represented-data correspondence and deterministic transition
execution, including the adapter to resumable machines. Its strict scoped
arithmetic/let/loop example exercises these interfaces independently of Cryptol.
Cryptol typing, demand rules, adequacy and Foundation specialization stay here.
Native lowering has one semantic route: native IR → resolved source → core.
A source certificate then transports arbitrary pre/postconditions, and the bridge
connects the certified compression function to VCVio's byte implementation and
adaptive oracle clients. See the [model guide](docs/model.md) and
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
open. The [next milestones](docs/model.md#audited-next-milestones) give their
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
The [coverage and gap ledger](docs/model.md#coverage-and-gap-ledger) separates
proved capabilities, semantic spikes, and missing language features. In particular,
the certified importer still targets the Foundation SHA-256 subset. The
[pinned typed-AST exporter](exporter/README.md) additionally retains complete
definitions for 31 SHA2/SHA3/SHAKE, Keccak, AES and CRC entries. Lean checks their
scope and kinds, and separately checks closed numeric and class constraints.
The scalar `(sigma_256_0 : [32] -> [32])` additionally has checked expression
elaboration from its exact quoted seven-declaration dependency graph. The kernel
checks its resolved output, and `ImportedScalar.core_correct` proves agreement
with `VCVio.Algorithms.Sha2.ssig0` for every input. This gate supports explicit
nonrecursive specialization, lambdas, applications, conditionals and the scalar
primitive fragment; it rejects other constructs. The broader graph still needs
checked elaboration and a shared evaluator. Component theorems cover Keccak coordinate inverses and byte-aligned
CRC polynomial updates; whole-algorithm differential tests exercise all SHA2,
SHA3 and SHAKE cores, AES vectors and CRC splits. The tests retain the pinned
reference evaluator's negative-index failure in Foundation Keccak separately
from normal-evaluator agreement. No full Cryptol soundness theorem or imported
CRC implementation certificate is claimed.

The [evaluator audit](docs/evaluators.md) compares the release with upstream
`51405420cb90cf9959ca4349eea0ae8b77487855`, maps the integer discrepancy to
Cryptol #2060, and records why reference evaluation remains the semantic target.
Set `CRYPTOL_UPSTREAM_BINARY` during external validation to reproduce its
152 observations and compare the committed report. The portable theta variant
is tested separately; the imported Foundation source retains its original bytes.

The [coverage catalogue](docs/coverage.md) separates planned reference coverage,
external probes and all-input Lean certificates, and records the next semantic
and algorithm milestones. Shared hashes live in `VCVio/Algorithms/`; conformance
proofs stay in this optional project.
