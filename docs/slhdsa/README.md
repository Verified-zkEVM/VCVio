# SLH-DSA formalization

This directory records the durable specification, evidence, and validation boundary for the
SLH-DSA/SPHINCS+ development. Normative FIPS 205 construction claims, abstract security claims,
legacy regressions, and deployment refinement are kept separate. A successful executable test is
not, by itself, an ACVP certificate, a cryptographic reduction, or a deployment proof.

## Implemented construction surface

- All twelve FIPS 205 parameter sets, fixed-width encodings, address types, digest splitting, and
  typed hypertree positions.
- Pure Lean SHA-2/SHAKE primitive grammars with checked SHA-2 address compression and standard
  vector regressions.
- WOTS+, XMSS, and FORS construction layers, including FIPS checksum/digest-index pipelines,
  intrinsic signature widths, checked reachable addresses, and bounded concrete regressions.
- Arbitrary-depth hypertree and internal-scheme programs with typed position evolution, callback to
  query/pure refinement, structural query upper bounds, and honest sign/recover/verify correctness.
- Exact structured public-key, secret-key, and arbitrary-depth signature codecs for all twelve
  approved profiles, with component projections, inverse laws, and strict length rejection.
- A legacy depth-one compatibility surface, plus non-normative legacy and C13 executable
  regressions.

External pure/pre-hash APIs, context/OID domain separation, mode-specific rejection, and complete
ACVP implementation evidence remain open.

## Security boundary

The repository contains classical game interfaces, exact target-count formulas, transcript/query
surfaces, an exact SUF event partition, canonical generic-game instantiations, and structural
reachable-target ledgers. These are conditional infrastructure. The selected proof's counting
interface, concrete reduction adversaries, outer-CMA log refinement, FORS/XMSS/hypertree trace
bridges, concrete encoded-target injectivity and pairing, experiment equivalences, the
same-message SUF bound, and the final master inequality remain unproved. No QROM lifting or
asymptotic theorem is claimed.

## Durable records

- [Scope and profiles](scope.md)
- [Source ledger](source-ledger.md) and checked [reference manifest](reference-manifest.json)
- [Specification](specification.md)
- [Lean blueprint](lean-blueprint.md)
- [Proof obligations](proof-obligations.md)
- [Security architecture](security-architecture.md)
- [Validation](validation.md)
- Machine-readable [matrices](matrices/), including exact FIPS 205 and SP 800-230 IPD profile
  records

## Validation

```text
./scripts/slhdsa/validate.sh --docs-only
./scripts/slhdsa/validate.sh
python3 -B scripts/slhdsa/check-acvp-provenance.py
lake exe slhdsa_acvp_parser
```

The full wrapper builds the libraries, runs the permanent exact axiom audit and policy audit,
checks generated imports and isolation, runs construction and primitive regressions, and then
builds and executes the strict ACVP parser from an attested private artifact root. The parser gate
binds source, objects, link trace, executable path, and executable hashes; it also exercises
negative schema, path, cache, mutation, descriptor-lifecycle, and cleanup cases. See
[validation.md](validation.md) for the exact boundary.
