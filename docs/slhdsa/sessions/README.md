# Session records

Each implementation session has one record describing the accepted input commit, exact diff scope,
commands/output, changed declarations, matrix/report updates, and handoff to independent review. A
record never self-certifies PASS. Session acceptance is determined only by the corresponding review.

Current records:

- [S00 — baseline and harness](S00-baseline-and-harness.md): accepted by independent r9 PASS after
  initial through r8 review FAILs.
- [S01 — authority and pinned conformance anchors](S01-authority-and-conformance.md): implementation
  reviews r0/r1/r2/r3/r4/r5/r6/r7/r8/r9/r10/r11/r12/r13/r14/r15 failed; independent r16 PASS accepted S01, making S02 eligible.
- [S02 — theorem, oracle, and security architecture](S02-security-architecture.md): independent
  r1/r2/r3/r5/r6/r7 failed; r4 acceptance was invalidated; independent r8 PASS accepted exact
  commit `a80e4d336276cd86fb80be64e82d9d57e7dfc8b3`.
- [S03 — data, widths, parameters, ADRS, and codecs](S03-data-widths-parameters-adrs-codecs.md):
  implemented from exact accepted S02; initial independent review of exact commit `963a3e7d...`
  failed with five blockers. R1 confirmed their repairs at `dab93b0a...` but failed on one active
  formula. Independent r2 accepted exact repair commit `79b42bf...` with zero findings.
- [S04 — primitive interfaces and SHA2/SHAKE instantiations](S04-primitives-sha2-shake.md):
  implementation candidate from exact accepted S03 r2; initial independent review of exact commit
  `7f115c0e...` failed only with S04-001. The vector-evidence repair descends from the immutable FAIL
  commit. Independent r1 accepted exact repair commit `00f1416e...` with zero findings; its review
  artifact is committed in exact accepted head `ca84e4f1...`.
- [B01 — upstream architecture and parameter boundary integration](B01-upstream-boundary-integration.md):
  history-preserving reconciliation of accepted S00--S04 with pinned upstream main and PR #593;
  independent r1 accepted exact repair commit `1f3cfa89...` with zero findings, and the acceptance
  artifact is committed/pushed at exact head `4161910f...`.
- [S05 — WOTS+ construction](S05-wots-construction.md): exact FIPS checksum byte pipeline,
  operational chain-length integration, checked SHA2 address closure, a discriminating
  non-`lg_w = 4` canary, and all-twelve approved-profile construction exercise. Independent r0
  accepted candidate `33770467...`; its review artifact is committed/pushed at `7e029e66...`.
- [S06 — Merkle and XMSS construction](S06-xmss-construction.md): local bounded FIPS §6 adapter
  over the canonical Merkle/XMSS engine, exact authentication positions and climb equation,
  checked concrete addresses, exhaustive height-two traces, and bounded concrete regressions.
  Independent r0 accepted candidate `91845ddf...`; its review artifact is committed/pushed at
  `91e97865...`.
- [B02 — PR #595 digest/position boundary integration](B02-pr595-digest-position-integration.md):
  history-preserving merge of the authoritative digest decomposition, FORS address, and typed
  hypertree-position surface, with the current Scheme d=1 limitation explicit. Its implementation
  and remote reconciliation are independently accepted at reviewed head `60918509...`.
- [B03 — concurrent construction/query/security-stack integration](B03-concurrent-stack-integration.md):
  history-preserving merge of the shared intrinsic-signature, arbitrary-depth construction,
  finite-query-bound, encoded-address, and conditional security-interface stack. Imported
  `recoverFromPosition_signFromPosition`/`pkFromSig_sign` and
  `GeneralScheme.verifyInternal_signInternal` discharge pure/fixed-answer arbitrary-depth
  correctness and internal completeness. Callback `*With` parity, S07 conformance/runtime, S09
  codecs/external APIs, and all security reductions remain open. Independent r2 accepted exact
  repair candidate `23a85b6d...` with zero findings.
- [B04 — canonical-game and construction-trace visibility integration](B04-canonical-game-trace-integration.md):
  history-preserving import of the canonical PR #594/#596 games, SLH-DSA problem instantiations,
  and WOTS address-trace contracts. These are conditional interfaces; reductions, outer-CMA log
  refinement, remaining construction traces, equivalences, and the master inequality stay open.

focused-parser-partition: legacy=8; source-object-link=21; imports=4; sha-output-binding=9; path-cli=20; output-types=2; artifacts=130; wrong-srcdir=2; stale=2; fresh-root=5; query-output=5; replacement-cache=3; descriptor-lifecycle=6; descriptor-ownership=17; total=234; sha-cli-is-subset-of-path-cli=6; nominal-success-excluded=true
