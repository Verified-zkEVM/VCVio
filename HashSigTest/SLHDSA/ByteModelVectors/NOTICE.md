# Byte-model vector provenance and notice

The three fixtures contain 15 SLH-DSA test records from NIST ACVP-Server release v1.1.0.43.
Each file records the SHA-256 digests of its upstream inputs and the vector-set, test-group
and test-case IDs. The table gives the test-case IDs. Signing and verification use the
internal interface. [Pinned NIST source](https://github.com/usnistgov/ACVP-Server/tree/975de31eb83d87039ec88934fdc47d8c312b892d) · [Executable checks](../ByteModel.lean)

| Parameter set and fixture | Key generation | Deterministic signing | Hedged signing | Accepting verification | Rejecting verification |
| --- | ---: | ---: | ---: | ---: | ---: |
| [SHAKE-128f](vectors.json) | 31 | 137 | 448 | 223 | 219 |
| [SHAKE-192f](vectors-192f.json) | 71 | 148 | 461 | 232 | 225 |
| [SHAKE-256f](vectors-256f.json) | 111 | 154 | 462 | 239 | 241 |

The National Institute of Standards and Technology is the source of these vectors. NIST-developed
software and data are provided by NIST as a public service, "AS IS", without warranty of any kind;
the software developed by NIST employees is not subject to copyright protection within the United
States. Their appearance here does not imply NIST endorsement of this project, and these records
are conformance evidence only, not an implementation-validation certificate.

Modification notice (2026-10-17): VCVio selected the five SHAKE-128f records from the upstream
keyGen expected results, sigGen expected results, and sigVer prompt and expected results, and
merged each test case's prompt and expected-result fields into one record. The byte strings are
unchanged upstream values, in upstream upper-case hexadecimal.

The SHAKE-192f and SHAKE-256f fixtures likewise project selected records from the pinned
sample suites. Each uses the first key-generation case, shortest-message deterministic and
hedged signing cases, and an accepting and a full-length rejecting verification case.
