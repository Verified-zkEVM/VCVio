# Byte-model vector provenance and notice

`vectors.json` holds five SLH-DSA-SHAKE-128f test records of the NIST ACVP-Server SLH-DSA sample
suites, at commit `975de31eb83d87039ec88934fdc47d8c312b892d` (release v1.1.0.43) of
https://github.com/usnistgov/ACVP-Server: keyGen test case 31, internal-interface sigGen test
cases 137 (deterministic) and 448 (hedged), and internal-interface sigVer test cases 223
(`testPassed` true) and 219 (`testPassed` false). `vectors.json` records the SHA-256 of each
upstream file the records come from, and their `vsId`, `tgId` and `tcId`.

The National Institute of Standards and Technology is the source of these vectors. NIST-developed
software and data are provided by NIST as a public service, "AS IS", without warranty of any kind;
the software developed by NIST employees is not subject to copyright protection within the United
States. Their appearance here does not imply NIST endorsement of this project, and these records
are conformance evidence only, not an implementation-validation certificate.

Modification notice (2026-10-17): VCVio selected the five records above from the upstream
keyGen expected results, sigGen expected results, and sigVer prompt and expected results, and
merged each test case's prompt and expected-result fields into one record. The byte strings are
unchanged upstream values, in upstream upper-case hexadecimal.
