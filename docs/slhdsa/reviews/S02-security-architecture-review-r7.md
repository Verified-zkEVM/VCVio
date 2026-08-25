# S02 independent security-architecture review r7

Verdict: **FAIL**

Blocking findings: **1**
Nonblocking findings: **0**

Reviewer: fresh independent S02 r7 reviewer; not the S02 implementer.
Review date: 2026-08-26.
Reviewed repair commit: `2d7cc7532d0fce4e0a312ac9cc4b41d81f2f9863`, relative to r6-reviewed
repair commit `00634296d3f03a409fa3c39c6592ceb8cc73b1f7` and exact S02 repair base
`7b77e700b3d24a6ab94ed741a650954bbd90859a`.

Independence and write-scope statement: I began read-only from `AGENTS.md`, the review protocol,
accepted S01, the exact commit and cumulative S02 diff, immutable r5/r6 FAIL artifacts, all four S02
Lean modules, matrices, report, provenance records, generated/compiled inventories, and the pinned
primary sources. I did not implement a repair. This immutable r7 artifact is my only repository
edit. Read-only commands and temporary output below `/tmp` were the only other actions.

## Decision summary

All five r6 findings are technically repaired. The scheme bundle is now consistently described as
an arbitrary experiment interface, while general-construction coupling stays open. D-006 and D-009
remain proposed with no inferred approval and their dependent obligations remain pending. The
source composite checks its exact four-glob command recipe and rejects a controlled Security-source
byte mutation. The repository record requires the exact session-linked repair base rather than an
arbitrary ancestor. The declaration inventory has the corrected names and complete source spans,
and the S02 session accurately discloses its narrow harness changes.

The full technical evidence is also successful: documentation/provenance, focused elaboration,
repository and HashSig builds, the authoritative compiled policy, every completed load-bearing
axiom print, the six FIPS parameter-shape evaluations covering all twelve approved families, report
rendering, isolation gates, the fresh parser, and both legacy runtime KATs pass.

The exact reviewed tree nevertheless leaves its S03 successor record in a stale and contradictory
state. That record says it is blocked by r5 pending r6, promises to name the predecessor after r6,
and later instructs implementation to use the “accepted predecessor above”; the only commit named
above is the explicitly invalidated `7b77e700`. R6 is already an immutable FAIL and the active plan,
indexes, and S02 session correctly say r7 is the pending gate. Because successor eligibility is a
load-bearing part of this review and the zero-finding protocol makes any documentation defect a
failure, S02 cannot yet be accepted and S03 must not start from this tree.

## Exact reviewed state

The commit identity reproduced as:

```text
HEAD    2d7cc7532d0fce4e0a312ac9cc4b41d81f2f9863
parent  00634296d3f03a409fa3c39c6592ceb8cc73b1f7
subject fix(slhdsa): resolve S02 r6 review findings
status  clean before reviewer authorship
```

The r6-to-r7 repair changes three S02 source files, the S02 documentation/matrices/report, the
manifest and narrow provenance/declaration checks, the full-wrapper inventory invocation, and adds
the immutable r6 artifact plus `S02InventoryProbe.lean`. It does not edit the rejected legacy
`HashSig/SLHDSA/Security.lean`, construction implementations, primitive implementations, parser
sources, or vector artifacts. `git diff --check` passed for both
`00634296..2d7cc753` and accepted-S01-to-`2d7cc753` scopes.

The four current S02 source hashes are:

```text
f927253bf39108b4471a1cf50a043fde534116325510fb3ac64dee8918e30164  Notions.lean
64e2d767e0d16e2cddb2506156690610f0a099ce679717274a760fc028e1bac4  OracleSurface.lean
7b02ea5eb79a51805a4ae727c993be71a3670f58fd4d655afd272cc99aead71a  Transcript.lean
3fefd8776594b36b74590e3767a73d203cfea663f5b8106d6663ba6153596cee  Architecture.lean
```

The immutable earlier review hashes reproduced exactly:

```text
0c1ea5b29c49d7fc6640509bb974aefd73c1cab6587e2052e34ba57e91b55bb6  r5
39328910948604a1920b6956d33885ebca0520eaff7af7b66088c3a30f1f219d  r6
```

## Primary-source correspondence

The EasyCrypt authority checkout was clean at exactly
`a28e4c53897a4bb57b575a177225862d48f824b7`. The source/evidence hashes reproduced:

```text
3bb1ce65aec7af6ea91dc65be066ca2e7a1e7110e126acc02cd1886271372741  proofs/SPHINCS_PLUS.ec
67b0031db0fbd8c335b8008fe3c00fb5bc109d4902591fabfdbaf99c60a130d1  proofs/KeyedHashFunctions.eca
ac5e354b298bbb8760c483e0bd214c2f6bd78597fde5756f6428ef2bab043f7f  proofs/FORS_ES.ec
1e1f5c82fa6dcfd9a8b83004ea8df408fda8c7f87f03ae65d565dcd2ad904c92  proofs/TweakableHashFunctions.eca
d1ca5fff2e7544c3591d665cd04a2e0f7454c0a2971388911eb6f6303c026001  SPHINCS_EC.pdf
9b49545b61bc194f0d7793556b04ca8f2257990057e229f51164ce2aafe89aa6  sphincsplus-framework-CCS2019.pdf
```

`proofs/SPHINCS_PLUS.ec:4338-4370` gives in order the two PRF differences, Hmsg ITSR,
truncated DSPR-minus-SPprob, coefficient-three FORS-F TCR, FORS-H TCR-C, FORS-Tl TCR-C,
coefficient-`w-2` WOTS-F UD-C, WOTS-F TCR-C, WOTS-F PRE-C, WOTS-Tl TCR-C, and XMSS-H
TCR-C. `Architecture.lean:506-577` retains those twelve roles, order, coefficients, and the one
truncated subtraction.

The independently inspected game definitions retain the previously repaired correspondence:

- PRE samples one fresh hidden input per target query and returns its output;
- TCR and DSPR use chosen `(tweak,input)` target queries and validate a selected index;
- SPprob reruns the same DSPR adversary/program interface and ignores only its Boolean guess;
- real UD samples a fresh hidden input, ideal UD samples a fresh output, and neither exposes the
  hidden input;
- each `-C` adversary makes target and collection queries in one `pick` execution and the event
  checks target-tweak distinctness and cross-collection disjointness; and
- the ITSR default oracle samples fresh randomizers while the reduction program owns its post-hop
  setup and public Hmsg parameters.

No formula, role, target-timing, hidden-value, selected-index, collection-execution, or ITSR-setup
discrepancy was found.

## R6 finding dispositions

### S02-R6-001 / F-081 — repaired

`SchemeInterface` and every active S02 prose surface now call the bundle an arbitrary signature-
scheme experiment boundary. The code and documentation explicitly deny a refinement/correctness law
coupling keygen, sign, verify, signature randomizer, and the future general `d`-layer construction.
An independent probe confirmed that always-accepting verification and an arbitrary replacement
randomizer still elaborate; this is now evidence for the stated abstraction boundary rather than a
construction claim. F-079 and PO-003 remain open for S08/S09. No active declaration, matrix,
specification, blueprint, architecture note, or report passage treats the bare bundle as a general
SLH-DSA witness.

### S02-R6-002 / F-082 — repaired

D-006 and D-009 remain `proposed` with `approver=unassigned`. PO-006 and PO-008 are provisional,
PO-003 is open, and the checklist leaves the affected items unchecked. The plan, blueprint,
specification, security architecture, assumptions, coverage, findings, declaration rationales, and
rendered report consistently use candidate/proposed language and say that D-009 does not supersede
the earlier contract without named approval. No technical review approval is inferred.

### S02-R6-003 / F-083 — repaired

The manifest's `globs_in_order`, `original_command`, and `deterministic_command` name exactly:

```text
HashSig/SLHDSA/*.lean
HashSig/SLHDSA/C13/*.lean
HashSig/SLHDSA/Concrete/*.lean
HashSig/SLHDSA/Security/*.lean
```

The checker requires exact equality with the fixed recipe before computing the 26-line manifest.
The independently reproduced active digest is
`09d340f611f600f9cd9a81e47ee2df06f9a9a3bbdd86fff439741cf09142625b`.
The normal gate copies the selected tree to a temporary fixture, appends one byte-changing line to
`Security/Architecture.lean`, and accepts only the exact composite-mismatch rejection. That focused
mutation passed.

### S02-R6-004 / F-084 — repaired

The repository entry has the exact field `repair_base_revision`, exact semantics
`exact-repair-base`, and no generic `revision` field. The checker requires the literal reviewed
repair base `7b77e700b3d24a6ab94ed741a650954bbd90859a`, requires the active S02 session to contain
that exact marker once, and additionally checks ancestry. Replacing it merely with another ancestor
cannot pass without changing reviewed harness code. The source ledger correctly calls the commit an
invalidated S02 implementation retained only as repair input, not an accepted S03 predecessor.

### S02-R6-005 / F-085 — repaired

The declaration rows use `CollectionDisjoint`, `SPprobSuccess`, and
`sampledTargetRealImpl` at the corrected sites. Eighteen exact full spans are pinned from each
declaration keyword through its final nonblank line, and the compiled inventory probe resolves all
eighteen roots plus the three corrected dependency names. The inventory remains honestly
`bootstrap-manual`, with F-018 open and no completeness/export claim. The S02 session now says the
r5/r6 repairs made narrow provenance/revision/declaration checks and no longer denies the actual
harness edit.

## New finding

### S02-R7-001 — the retained S03 bootstrap points at a completed failed round and no accepted predecessor

Severity: **HIGH**.

The exact reviewed tree correctly says everywhere else that r6 failed, r7 is pending, and S03 is
blocked. `sessions/S03-data-widths-parameters-adrs-codecs.md` contradicts that active state:

- line 3 says the bootstrap is “blocked by S02 r5 pending repaired r6 review”;
- lines 7-9 name only former commit `7b77e700`, explicitly say r4 acceptance was invalidated, and
  promise to name the repaired accepted predecessor “after r6”;
- lines 15-16 and 24 call the S02 interfaces accepted despite no current PASS; and
- line 76 instructs implementation to begin at “the accepted predecessor above,” although the only
  predecessor above is the invalidated former commit.

This is not harmless future tense. R6 is an immutable FAIL already present in the exact tree, and
the handoff has no valid referent for the commit from which S03 should start. It directly conflicts
with `README.md:13-27`, `plan.md:52-54,76-89`, `reviews/README.md`, `sessions/README.md`, and the S02
session. It also defeats the user's requested exact accepted-predecessor bootstrap if followed
literally.

Required repair: update the S03 record to the current failed-review state, remove every instruction
that can resolve “accepted predecessor” to `7b77e700`, and state that no S03 implementation may
begin until a new exact S02 repair commit receives independent PASS. The next repair must register
this finding and preserve this immutable artifact. After that PASS, the first S03 implementation
record must bind its input to the exact accepted S02 commit; it must not infer acceptance from an
earlier failed round.

## Reproduced commands and evidence

Commands are classified as static audit, elaboration, runtime, or report rendering.

```text
git show -s --format='%H%n%P%n%s' 2d7cc753
git diff --name-status 00634296..2d7cc753
git diff --check 00634296..2d7cc753
git diff --check c5d6cb03..2d7cc753
  PASS (static identity, cumulative scope, and whitespace audits).

./scripts/slhdsa/validate.sh --docs-only
  PASS (runtime documentation/provenance gate): exact repair base, matrices, 18 declaration spans,
  four-glob source composite, controlled Security-byte mutation, local source hashes, and S01
  authority/profile checks.

lake env lean HashSig/SLHDSA/Security/Notions.lean
lake env lean HashSig/SLHDSA/Security/OracleSurface.lean
lake env lean HashSig/SLHDSA/Security/Transcript.lean
lake env lean HashSig/SLHDSA/Security/Architecture.lean
lake env lean scripts/slhdsa/S02InventoryProbe.lean
  PASS (focused elaboration): all modules and inventory/dependency roots resolve.

lake build HashSig
  PASS (elaboration): 2,748 jobs; only the frozen legacy Security.lean:150 admission warning.

lake env lean scripts/slhdsa/PolicyAudit.lean
  PASS (authoritative compiled static audit): 27 HashSig modules, 1,629 owned constants, exact seven
  permitted generated `_unsafe_rec` helpers, and axiom union exactly
  [propext, Classical.choice, Quot.sound, sorryAx], with sorryAx confined to the legacy placeholder.

lake env lean /tmp/S02R6IndependentProbe.lean
  PASS (independently inspected focused probe replay): interface noncoupling examples, empty/invalid/
  duplicate/overlap events, role cards, six FIPS tuples, and all load-bearing axiom prints.

./scripts/slhdsa/validate.sh
  PASS (full runtime/elaboration gate): 3,007-job repository build, 2,748-job HashSig build,
  2,743-job HashSigTest build, exact fresh parser and 68 cases, compiled ordinary/IR initializer
  fixtures with absent sentinel, generated umbrella, extern/interop isolation, and both KATs.

latexmk -pdf -interaction=nonstopmode -halt-on-error \
  -outdir=/tmp/slhdsa-s02-r7-tex slhdsa-formalization-audit.tex
  PASS (report rendering): seven pages, 323,900 bytes; only box-layout warnings.
```

The cumulative S02 source introduces no unallowlisted `sorry`/`admit`, axiom declaration, explicit
`unsafe`, `extern`, source `partial`/`partial_fixpoint`, initializer, runtime override, linter
suppression, false-elimination helper, Interop import, Extern import, or legacy-security-file edit.
The twelve `noncomputable` declarations are the explicit ENNReal probability/master expressions.
The eight earlier source-recursive projections compile through total list combinators and introduce
no generated helper beyond the accepted seven.

No vector or executable conformance artifact changed. The full gate replays the legacy
SHA2-128-24 and C13 positive/tamper KATs, but those remain C-reference regression evidence rather
than FIPS/ACVP implementation-conformance evidence.

## Axiom replay

The focused probe printed axioms for the parameter restrictions and positivity roots; digest and
ITSR roots; `GeneratedKeyPair` and `SchemeInterface`; query handlers and structural bounds;
transcript coherence and distributions; role cards; target and collection handlers/events; all
component probabilities; `componentTerm`; `eufAdvantage`; `repairedRHS`;
`RepairedMasterStatement`; and budget independence.

Every completed root was axiom-free or used a subset of exactly:

```text
[propext, Classical.choice, Quot.sound]
```

No completed S02 root reported `sorryAx` or another nonstandard axiom.

## Quantitative evaluation

Role cards evaluate to `construction / primitive / master / target = 8 / 6 / 12 / 8`.
The six unique parameter tuples cover both SHA2 and SHAKE variants of all twelve FIPS sets. Columns
are FORS F, FORS H, FORS Tl, WOTS F UD-C, WOTS F TCR-C, WOTS F PRE-C, WOTS Tl, and XMSS H:

```text
128s len=35:
528905046081400263933952, 528775918872884297072640, 9223372036854775808,
323449759100660631040, 5175196145610570096640, 323449759100660631040,
9241421688590303744, 9223372036854775807

128f len=35:
155838093934698292051968, 153403123716968631238656, 73786976294838206464,
2951479051793528258520, 47223664828696452136320, 2951479051793528258520,
84327972908386521672, 73786976294838206463

192s len=51:
2568967366681086996250624, 2568810569356460465061888, 9223372036854775808,
471312506118105490944, 7541000097889687855104, 471312506118105490944,
9241421688590303744, 9223372036854775807

192f len=51:
623352375738793168207872, 620917405521063507394560, 73786976294838206464,
4300726618327712605272, 68811625893243401684352, 4300726618327712605272,
84327972908386521672, 73786976294838206463

256s len=67:
6649092007880460460883968, 6648686179510838850748416, 18446744073709551616,
1240778644518691095296, 19852458312299057524736, 1240778644518691095296,
18519084246547628288, 18446744073709551615

256f len=67:
5289050460814002639339520, 5278720284132725290434560, 295147905179352825856,
21093236956817748621104, 337491791309083977937664, 21093236956817748621104,
314824432191309680912, 295147905179352825855
```

All caps are positive natural numbers. Empty logs satisfy the cap but every selected-target event
fails; duplicate tweaks, over-cap traces, invalid indices, and target/collection overlap are
rejected. No denominator, finite-range, coefficient, role-order, or invented scalar-loss defect was
found.

## Immutable final decision

Final verdict: **FAIL with one blocking finding and zero nonblocking findings**.

The five r6 blockers are repaired, and the Lean/provenance/policy/report evidence otherwise passes.
S02 is not accepted at `2d7cc7532d0fce4e0a312ac9cc4b41d81f2f9863` because its retained S03
handoff can still direct implementation to an invalidated predecessor and describes a completed
failed review as pending. S03 and every later successor remain blocked. Repair the successor-state
record, register S02-R7-001 with evidence, produce an exact new repair commit, rerun the complete
gates, and obtain a fresh independent r8 PASS before S03 begins.
