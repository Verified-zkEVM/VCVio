# SLH-DSA ACVP corpus format

`corpus.bin` is a lossless, deterministic encoding of the SLH-DSA `keyGen`, `sigGen`, and
`sigVer` sample suites in the pinned NIST ACVP-Server checkout. Binary storage avoids the 2x
expansion from hex-encoding roughly 34 MB of keys, messages, and signatures.

The format is test data, not a protocol or a serialization API. Version 1 uses big-endian unsigned
integers. A `blob` is `u32 byte_length || byte_string`. An optional blob is a one-byte presence tag
(`0` or `1`), followed by a blob only when present. The explicit tag distinguishes an absent context
from a present empty context.

## Top-level layout

```text
"VCVSLH1\0"                 8-byte magic
u16(1)                      format version
u16(3)                      section count
keyGen section
sigGen section
sigVer section
```

Each section begins with:

```text
u8 mode                     1=keyGen, 2=sigGen, 3=sigVer
u32 vsId
u16 group_count
u32 test_count
groups...
```

Each group begins with:

```text
u32 tgId
u8 test_type                1=AFT
u8 parameter_set            index in the FIPS Table-2 order below
u8 signature_interface      0=absent, 1=internal, 2=external
u8 prehash                  0=absent, 1=pure, 2=preHash
u8 deterministic            0=absent, 1=false, 2=true
u16 test_count
tests...
```

The parameter-set index order is SHA2-128s, SHAKE-128s, SHA2-128f, SHAKE-128f, SHA2-192s,
SHAKE-192s, SHA2-192f, SHAKE-192f, SHA2-256s, SHAKE-256s, SHA2-256f, SHAKE-256f.

## Test records

All records begin with `u32 tcId`.

```text
keyGen: blob(skSeed), blob(skPrf), blob(pkSeed), blob(pk), blob(sk)

sigGen: blob(sk), blob(message), option_blob(context), u8(hashAlg),
        option_blob(additionalRandomness), blob(signature)

sigVer: blob(pk), blob(message), option_blob(context), u8(hashAlg),
        blob(signature), u8(testPassed)
```

The hash selector is `0` when absent. Values 1 through 12 are SHA2-224, SHA2-256, SHA2-384,
SHA2-512, SHA2-512/224, SHA2-512/256, SHA3-224, SHA3-256, SHA3-384, SHA3-512, SHAKE-128, and
SHAKE-256, in that order. `testPassed` is exactly `0` or `1`.

## Reproduction and validation

From an ACVP-Server checkout at commit `975de31eb83d87039ec88934fdc47d8c312b892d`:

```bash
python3 scripts/slhdsa/generate-acvp-corpus.py \
  --source-root /path/to/ACVP-Server --write
```

Use `--check` instead of `--write` to regenerate in memory and compare both committed outputs
byte-for-byte. `corpus-manifest.json` records the six source file hashes, source commit, generation
command, exact counts, retained payload sizes, and output hash.

The Lean decoder in `HashSigTest.SLHDSA.ACVP.Corpus` rejects unknown tags, wrong counts or ID
sequences, malformed conditional fields, wrong parameter-dependent widths, empty or oversized
messages, oversized contexts, truncation, and trailing bytes. It retains the decoded bytes for the
separate cryptographic KAT runner; successful parsing alone is not a cryptographic conformance
claim.
