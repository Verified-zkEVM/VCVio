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
  implemented from exact accepted S02; gates pending and no review verdict exists.

focused-parser-partition: legacy=8; source-object-link=21; imports=4; sha-output-binding=9; path-cli=20; output-types=2; artifacts=130; wrong-srcdir=2; stale=2; fresh-root=5; query-output=5; replacement-cache=3; descriptor-lifecycle=6; descriptor-ownership=17; total=234; sha-cli-is-subset-of-path-cli=6; nominal-success-excluded=true
