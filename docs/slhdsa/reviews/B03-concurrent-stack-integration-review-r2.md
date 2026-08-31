# B03 concurrent-stack integration closure review r2

Date: 2026-08-31

Verdict: **PASS**

Blocking findings: **0**

Nonblocking findings: **0**

## Reviewed boundary

- candidate: `23a85b6db2dd57e79a5dfab67a31b6d121193b57`
- candidate tree: `3bb9f7d58de5a537caa846986f71c82f83c3e86b`
- parent, immutable r1 FAIL: `129d6a559da8847a747b94e6ff2d10aecec10a7c`
- r0 FAIL: `17f1b060861a146b0bd2c4e67b0a7637b788feb4`
- first documentation repair: `83fe7849a1bc8dfc8f046034b067200ac36a494b`
- implementation reviewed by r0: `157855d88b9bc550de5964bdd90d112ee16ae9dd`

The worktree was clean at review start. The ancestry is exactly implementation, r0 FAIL, first
repair, r1 FAIL, and final repair. The final repair changes only
`docs/slhdsa/reviews/README.md`. The first repair changes eight active documentation/matrix files;
its only script delta updates the exact byte-count and SHA-256 pins for the two edited CSV matrices.
There is no harness-behavior change and no Lean, `HashSig`, or `HashSigTest` source delta.

## Finding closure

All three r0 findings and the sole r1 finding are closed across the active main README, session
index, reviews index, B03 session, plan, specification, proof-obligation prose and CSV, and coverage
CSV:

- B03's `recoverFromPosition_signFromPosition`/`pkFromSig_sign` and
  `GeneralScheme.verifyInternal_signInternal` are consistently recorded as discharging
  pure/fixed-answer arbitrary-depth hypertree correctness and internal GeneralScheme completeness.
  The records do not promote this construction result into a callback, conformance, external API,
  or security result.
- PO-012 now owns the discharged legacy `d = 1` compatibility boundary. PO-021 owns discharged
  arbitrary-`d` hypertree correctness and PO-022 owns discharged internal GeneralScheme
  completeness. The corresponding coverage rows separate legacy d1 compatibility from the
  arbitrary-depth and internal-API results rather than retaining a duplicate general-d owner.
- S07 consumes accepted B03 infrastructure and owns FORS extraction/address/runtime conformance.
  S08 owns callback `*With` parity and concrete all-depth/profile conformance without rewriting the
  typed loop or its correctness theorem. S09 retains codecs, external pure/pre-hash APIs,
  domain/context/OID and mode handling, rejection behavior, and external completeness while
  preserving B03's internal theorem.
- B02 is consistently accepted at exact reviewed head
  `609185098935feea82f4d5b6fb7a9d62aefce9c9`. The reviews index now links both zero-finding B02
  reviews and no longer claims that B02 is pending review.
- The reviews index accurately retains B03 r0 as a zero-blocking/three-nonblocking FAIL on
  `157855d8...` and r1 as a zero-blocking/one-nonblocking FAIL on `83fe7849...`, with fresh
  successor review required. Neither historical artifact was rewritten.

The deliberately open boundaries also remain explicit. PO-024 retains callback parity; PO-023
retains FORS conformance; S09 retains codec/external API work; PO-003 retains construction of the
reduction system; PO-025 retains the unbounded same-message SUF residual; and PO-026 retains encoded
injectivity, nonempty game-batch packaging, actual-query/input alignment, validity/disjointness, and
canonical PR #594/#596 adapters. `ReductionSystem` remains assumed and
`RepairedMasterStatement` remains an unproved EUF-only proposition. Structural ledgers and the SUF
partition are not described as reductions.

## Immutability and source identity

The implementation and candidate `HashSig` trees are both
`c2ff05f401fd412ffdaf43b2e0e531efc9ca96e5`; their `HashSigTest` trees are both
`be6e935bb090ea72ecc89de091e3adf6cef092b1`. The exact 43-file source-composite recipe reproduces
`a96482af2c7035f9cb7ef460f839fe6896707d4eb0fd68909e1c5cdad2f1e612`, unchanged from r0.

The r0 review blob remains `5b0e08c5fb9e96b8bfe06de43d4e0418d902313c`, and the r1 review blob remains
`118bd6c0529cec052889630c00bb6d822e07b11b`. Their file SHA-256 values are respectively
`b93316cab5092a1a61def0f5379b38f2bb89bfa40d2032d11d706cf9c33f20c9` and
`ed9b4c2f44939ab5d99ef3e170977f6e3b14abcfb56cd7ab8175be7b1c1fe6bd`.

Historical S06 session/review blobs remain `96308d8b866b650615c0c231cd514143a2a8d1d5` and
`383072dad9c3cc4e1afaaf68001e318b4de540e6`. Historical B02 session, initial-review, and
reconciliation-review blobs remain `fc335f0f1633e3135cd0b4ca7523000a5857cf02`,
`f0807f75d0ec66188ec4473ea0295b0e252b4999`, and
`d3efae6554e2eeba229e3b09c6244930398bb7ed`.

## Proportional validation

```text
git rev-parse HEAD HEAD^{tree} HEAD^
23a85b6db2dd57e79a5dfab67a31b6d121193b57
3bb9f7d58de5a537caa846986f71c82f83c3e86b
129d6a559da8847a747b94e6ff2d10aecec10a7c

git diff --name-status 129d6a55..23a85b6d
M  docs/slhdsa/reviews/README.md

git diff --check 17f1b060..83fe7849
# no output
git diff --check 129d6a55..23a85b6d
# no output

wc -c docs/slhdsa/matrices/coverage.csv docs/slhdsa/matrices/proof-obligations.csv
8813 docs/slhdsa/matrices/coverage.csv
8992 docs/slhdsa/matrices/proof-obligations.csv

sha256sum docs/slhdsa/matrices/coverage.csv docs/slhdsa/matrices/proof-obligations.csv
7e986b8f14fc8b125327609a726e52d3387c5c6d5737327788388ec8636d3d1c  coverage.csv
6830a95ba15b2584024113286bd536e8c47ffa5578760bc39186b04cecb67015  proof-obligations.csv

LC_ALL=C sha256sum HashSig/SLHDSA/*.lean HashSig/SLHDSA/C13/*.lean \
  HashSig/SLHDSA/Concrete/*.lean HashSig/SLHDSA/HypertreeGeneral/*.lean \
  HashSig/SLHDSA/Security/*.lean | sha256sum
a96482af2c7035f9cb7ef460f839fe6896707d4eb0fd68909e1c5cdad2f1e612  -

./scripts/slhdsa/validate.sh --docs-only
SLH-DSA harness check: PASS
SLH-DSA ACVP provenance: PASS (9 committed artifacts; 15 server artifacts; 144 coverage cells/24 positive)
SLH-DSA docs-only validation: PASS
```

Focused positive searches found the exact B03 theorem ownership, PO-012/PO-021/PO-022 split,
accepted B02 head and both review links, successor-session roles, and still-open callback,
conformance, API, SUF, ledger, and reduction language. Focused stale searches found no superseded
general-correctness owner, pending-B02-review statement, or reopened PO-012/PO-021/PO-022 row. The
one broad textual match was the intended statement that external API completeness remains open.

No full Lean wrapper was run: the review request called for focused documentation, harness,
provenance, diff, identity, and immutable-blob checks, and the Lean source trees are exactly the
technically reviewed B03 implementation trees.

## Final assessment

The bounded repairs close every r0 and r1 finding without changing the reviewed Lean implementation
or weakening the remaining obligations. With zero blocking and zero nonblocking findings, exact
candidate `23a85b6db2dd57e79a5dfab67a31b6d121193b57` **PASSes** independent B03 closure review.
