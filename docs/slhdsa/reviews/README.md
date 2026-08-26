# Independent reviews

Review artifacts are written by a reviewer independent of the implementation session. Templates
start `PENDING`; implementers must not pre-fill a PASS. Failed reviews remain in history and re-review
files use the `-rN` suffix.

- [S00 adversarial review](S00-adversarial-review.md): FAIL.
- [S00 adversarial re-review 1](S00-adversarial-review-r1.md): FAIL.
- [S00 adversarial re-review 2](S00-adversarial-review-r2.md): FAIL.
- [S00 adversarial re-review 3](S00-adversarial-review-r3.md): FAIL.
- [S00 adversarial re-review 4](S00-adversarial-review-r4.md): FAIL.
- [S00 adversarial re-review 5](S00-adversarial-review-r5.md): FAIL.
- [S00 adversarial re-review 6](S00-adversarial-review-r6.md): FAIL.
- [S00 adversarial re-review 7](S00-adversarial-review-r7.md): FAIL.
- [S00 adversarial re-review 8](S00-adversarial-review-r8.md): FAIL.
- [S00 adversarial re-review 9](S00-adversarial-review-r9.md): PASS.
- [S01 authority and pinned conformance review](S01-authority-and-conformance-review.md): FAIL.
- [S01 authority and pinned conformance re-review r1](S01-authority-and-conformance-review-r1.md):
  FAIL.
- [S01 authority and pinned conformance re-review r2](S01-authority-and-conformance-review-r2.md):
  FAIL.
- [S01 authority and pinned conformance re-review r3](S01-authority-and-conformance-review-r3.md):
  FAIL.
- [S01 authority and pinned conformance re-review r4](S01-authority-and-conformance-review-r4.md):
  FAIL.
- [S01 authority and pinned conformance re-review r5](S01-authority-and-conformance-review-r5.md):
  FAIL.
- [S01 authority and pinned conformance re-review r6](S01-authority-and-conformance-review-r6.md):
  FAIL.
- [S01 authority and pinned conformance re-review r7](S01-authority-and-conformance-review-r7.md):
  FAIL.
- [S01 authority and pinned conformance re-review r8](S01-authority-and-conformance-review-r8.md):
  FAIL.
- [S01 authority and pinned conformance re-review r9](S01-authority-and-conformance-review-r9.md):
  FAIL.
- [S01 authority and pinned conformance re-review r10](S01-authority-and-conformance-review-r10.md):
  FAIL.
- [S01 authority and pinned conformance re-review r11](S01-authority-and-conformance-review-r11.md):
  FAIL.
- [S01 authority and pinned conformance re-review r12](S01-authority-and-conformance-review-r12.md):
  FAIL.
- [S01 authority and pinned conformance re-review r13](S01-authority-and-conformance-review-r13.md):
  FAIL.
- [S01 authority and pinned conformance re-review r14](S01-authority-and-conformance-review-r14.md):
  FAIL.
- [S01 authority and pinned conformance re-review r15](S01-authority-and-conformance-review-r15.md):
  FAIL.
- [S01 authority and pinned conformance re-review r16](S01-authority-and-conformance-review-r16.md):
  PASS; S01 accepted.
- [S02 security architecture review r1](S02-security-architecture-review-r1.md): FAIL.
- [S02 security architecture review r2](S02-security-architecture-review-r2.md): FAIL.
- [S02 security architecture review r3](S02-security-architecture-review-r3.md): FAIL.
- [S02 security architecture review r4](S02-security-architecture-review-r4.md): PASS with zero
  blocking and zero nonblocking findings; later invalidated by the complete r5 gate.
- [S02 security architecture review r5](S02-security-architecture-review-r5.md): FAIL with six
  blocking findings; S02 reopened and S03 blocked pending repair and r6.
- [S02 security architecture review r6](S02-security-architecture-review-r6.md): FAIL with five
  blocking findings; S03 remains blocked pending the second repair and r7.
- [S02 security architecture review r7](S02-security-architecture-review-r7.md): FAIL with one
  blocking successor-routing finding; all five r6 defects passed re-review.
- [S02 security architecture review r8](S02-security-architecture-review-r8.md): PASS with zero
  findings; exact commit `a80e4d336276cd86fb80be64e82d9d57e7dfc8b3` accepted and S03 eligible.

S03 implementation is underway from that exact accepted predecessor. No S03 review artifact or
verdict exists yet.

focused-parser-partition: legacy=8; source-object-link=21; imports=4; sha-output-binding=9; path-cli=20; output-types=2; artifacts=130; wrong-srcdir=2; stale=2; fresh-root=5; query-output=5; replacement-cache=3; descriptor-lifecycle=6; descriptor-ownership=17; total=234; sha-cli-is-subset-of-path-cli=6; nominal-success-excluded=true
