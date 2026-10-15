# Foundation coverage and conformance

[`coverage.json`](../coverage.json) records the public entry points selected for
reference coverage, their parameter and input profiles, semantic requirements,
known dependencies, native counterparts and current proof strength. It is an
inventory of the intended corpus, not a claim that every entry is modeled.

`planned` means no Lean source correspondence is available. `probe` records
external evaluation or a small transcribed statement. `certified` requires a
Lean theorem relating the retained source to the named implementation for every
input in the stated profile. Executable test vectors never promote an entry to
`certified`. Source provenance and evaluator agreement remain separate from
kernel checking. Dependency lists marked `partial` are investigation leads;
the versioned typed-AST bundle separately retains a complete shared dependency
graph for 31 entries. `reference_import.stage = scoped` records only successful
decoding, scope and kind validation. It does not change the certificate status.

The [exporter](../exporter/README.md) retains 280 declarations from 49 loaded
modules, including the official `Cryptol::Reference` primitive fallbacks. Its
manifest identifies all 31 roots and hashes every input module. The committed
numeric and class cases are replayed locally; external regeneration checks them
against the actual pinned `InfNat` and class solver implementations. These import
checks do not claim expression typing, constraint entailment for open terms,
execution of the imported JSON graph, or implementation equivalence.

The separate scalar pilot in `artifacts/references/scalar-bundle.json` has a
stronger checked path: its exact quotation elaborates to typed resolved syntax,
and `ImportedScalar.core_correct` covers every input to core `Sha2.ssig0`.
This component certificate is recorded separately from the 57 whole-algorithm
entries; it does not promote the remaining shared graph beyond `scoped`.
See [the checked scalar boundary](foundation.md#checked-typed-ast-scalar).

The bridge validation checks the catalogue schema, source pins, declaration
references and status invariants. Its external pass loads the listed public
modules and asks the pinned Cryptol frontend for each entry's type. A successful
load is not a supported importer, a semantic preservation theorem, or a proof of
the source property. The existing compression source, recurrence compilation,
byte boundary and adaptive-client theorems remain the first complete chain.

## Endpoint and order

The first corpus endpoint is reference coverage of the non-ECDSA algorithm
families plus CRC, followed by a P-256 pilot. Full correspondence with actual
core implementations is first required for all SHA2 and SHA3/SHAKE variants.
Other families may initially have imported references and source properties
without an independently verified native implementation. New source features
must first pass partial-value and binder regressions, rather than being erased
by the importer to make a particular algorithm compile.

The [audited milestone plan](model.md#audited-next-milestones) gives the full
order and acceptance gates. Whole-term parameter/value algebra and general
semantic preservation are complete for the current syntax. Next come a pinned
checked elaboration of the typed-AST bundles and an explicit reference-core
correspondence, followed by a shared evaluator and polymorphic operational
adequacy. Syntax-producing specialization and certified native compilation
precede polymorphic export with semantic round trips.

Algorithm work consumes those reusable interfaces: bounded folds, prefix
recurrences and finite observations; full SHA-256 padding/block processing and
SHA2 variants; CRC/AES and Keccak/SHA3/SHAKE; compositions and remaining families
before P-256 arithmetic and termination. The catalogue has one certified entry,
30 executable probes and 26 planned entries. The 31 imported roots comprise the
certificate and the probes; their shared input graph remains at the scoped stage.

## What a guard establishes

A semantic certificate establishes equality in Lean of the imported meaning and
an actual implementation on an explicit admissible domain. This permits pulling
or pushing any Lean pre/postcondition over that domain. For a represented Boolean
source property, truth requires a defined `true` result: divergence and error
cannot satisfy the property. Bits and bytes require a proved codec and a stated
alignment restriction; an all-bit-length source claim does not follow from a
byte-oriented implementation theorem.

Checks of the source pin, dependency closure, typed export and printer protect
the trusted connection to Cryptol. Kernel checking protects the Lean semantic
proof and implementation correspondence. Differential evaluation protects
against mismatches at those trusted boundaries. None subsumes the others. A
Cryptol/SAW solver result is independent evidence unless its certificate is
checked in Lean.

The `component_equations` axis records the proofs in
[`KeccakCodec.lean`](../Bridge/KeccakCodec.lean) and
[`CRCUpdate.lean`](../Bridge/CRCUpdate.lean) separately from source certificates.
Keccak's two inverse laws hold at every finite lane width, including zero. CRC
updates compose for every monic binary generator and byte-aligned message, with
or without input reflection, and under any final state observation. These prove
transcribed coordinate and polynomial equations; source elaboration and the
bitvector/polynomial `pmod` connection are still required for source certificates.

[`test_references.py`](../scripts/test_references.py) compares the actual Lean
SHA2/SHA3/SHAKE cores with Python's `hashlib` (OpenSSL for SHA-512/t when the system
Python omits it), and, in external mode, with whole Foundation definitions. The
cases include empty messages, padding and block boundaries, and multiple SHAKE
squeeze blocks. AES uses the three FIPS 197 Appendix C encryption/decryption
vectors; CRC uses independent CRC32 values, incremental splits and running CRCs;
Keccak checks both coordinate properties at six widths. RawSHAKE is checked via
its domain-bit relation to SHAKE. Both external evaluators are checked,
with a smaller reference-evaluator matrix. A timeout fails the check; it never
counts as agreement. These tests execute pinned Cryptol source, not the JSON AST.

Foundation's Keccak theta step uses `C@((x-1) % 5)`. At `x=0`, Cryptol 3.6.0's
reference integer remainder produces `-1`, so the selected SHA3 and SHAKE
reference computations fail with an invalid index. The normal evaluator uses
Euclidean remainder and agrees with the Lean hashes. The driver checks a minimal
theta example and the actual whole hashes, recording `documented-index-error`
separately from `agreed`. Preserving the reference semantics therefore cannot
by itself establish the intended total SHA3 behavior of this unmodified source.

Mutation tests should alter constants, byte order, shifts, field
selection, constraint evidence and instantiations, and report which gate rejects
each mutation. Record proof and execution costs alongside semantic coverage.
