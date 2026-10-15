# Pinned Cryptol typed-AST exporter

This executable links Cryptol 3.6.0 at commit
`61dd17b0c45ddf8c5c1e952afd5e789c4dc4ec4b`. It exports full dependency closures
from the official typed AST, retaining ordered type/proof binders, schemes,
recursive declaration groups, guards, comprehension branches, and foreign
fallback bodies. It also retains the official `Cryptol::Reference` fallback
definitions for polynomial arithmetic and folds/scans. Locations on expressions
are currently erased; declaration identities and module content hashes remain.

The supported build uses GHC 9.6.7 and Cabal 3.12.1.0. `cabal.project.freeze`
records the resolved dependencies and Hackage index state. Z3 must be on `PATH`
for the frontend's type checker. The executable is threaded because Cryptol's
solver process needs the threaded Haskell runtime.

```bash
cd Interop/Cryptol/exporter
cabal build cryptol-lean-export
cabal list-bin cryptol-lean-export
```

From the repository root, after `lake build cryptol-interop`:

```bash
python3 Interop/Cryptol/scripts/export_references.py \
  --exporter /path/to/cryptol-lean-export \
  --foundation /path/to/pinned/Foundation \
  --cryptol-source /path/to/pinned/cryptol
```

Add `--check` to require byte-identical committed artifacts. The driver checks
both clean source revisions, all loaded module digests, 2,020 numeric cases
against `InfNat`, 345 class/literal cases against the official class solver,
and Lean scope/kind validation. Temporary entry modules do not modify Foundation.

The checked corpus contains 31 roots and 280 shared declarations: SHA256
compression, six complete SHA2 hashes, four SHA3 hashes, four SHAKE/RawSHAKE
functions, six Keccak/state-conversion entries, six AES functions, and four CRC
entries. `artifacts/references/manifest.json` maps catalogue IDs to entry roots.
The JSON contains definitions and dependency edges, not output-vector stubs.

`source inspect` reports **scoped**. This establishes neither expression typing
nor semantic correctness of the Haskell frontend/exporter. The full source
graph still needs checked elaboration, a shared executable evaluator, and a
correspondence theorem before it can supply broader semantic certificates.
The existing SHA256 compression certificate uses its separately checked path.

The driver also exports the seven-declaration closure for
`(sigma_256_0 : [32] -> [32])` to `scalar-bundle.json` and quotes its constructors
into `Bridge/ImportedScalarSource.lean`. The quote generator does no semantic
normalization. `source elaborate …/scalar-bundle.json` reports **typed**, with
the checked resolved expression. `Bridge.ImportedScalar.accepted` verifies that
exact output in the kernel, and `core_correct` relates it to core `Sha2.ssig0`
on every 32-bit input. Its deliberately small elaboration fragment rejects
unsupported syntax and primitives; general frontend semantic preservation is
still a separate obligation. Both additional artifacts have manifest digests
and participate in byte-identical regeneration and negative typing tests.

`ImportedScalar.compiled` retains the finite native IR with a correctness
certificate for this exact imported source. `core_contract_iff` transfers
arbitrary bitvector pre/postconditions to core `Sha2.ssig0` through the shared
PolyFun correspondence machinery.

To include regeneration in optional external validation, set `CRYPTOL_EXPORTER`
and `CRYPTOL_SOURCE` alongside `CRYPTOL_BINARY` and `FOUNDATION_PATH`. Ordinary
validation checks the committed artifacts and all rejection cases without GHC,
Cabal, Cryptol, or network access.
