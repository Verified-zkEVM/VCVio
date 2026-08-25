# S02 independent security-architecture review r8

Verdict: **PASS**

Blocking findings: **0**
Nonblocking findings: **0**

Reviewer: fresh independent S02 r8 reviewer; not the S02 implementer.
Review date: 2026-08-26.
Reviewed repair commit: `a80e4d336276cd86fb80be64e82d9d57e7dfc8b3`, parent
`2d7cc7532d0fce4e0a312ac9cc4b41d81f2f9863`, relative to accepted S01 commit
`c5d6cb03d11126e6290bec58ef8824f36fc3a73b` and exact invalidated S02 repair input
`7b77e700b3d24a6ab94ed741a650954bbd90859a`.

Independence and write-scope statement: I began read-only from `AGENTS.md`, the review protocol,
the accepted S01 state, the exact candidate and cumulative S02 diff, every S02 source module,
primary sources, matrices, generated inventory, compiled policy, failed review artifacts, active
session records, and the S03 bootstrap. I did not implement or alter the repair. This r8 artifact is
my only repository edit; commands otherwise read the worktree or wrote disposable output under
`/tmp`.

## Decision summary

The exact candidate repairs S02-R7-001. The S03 bootstrap now states that no accepted predecessor
exists, classifies `7b77e700b3d24a6ab94ed741a650954bbd90859a` only as invalidated historical
repair evidence, forbids using it as a start target, and blocks implementation until an exact S02
repair commit receives independent r8 PASS. The active indexes, plan, report, findings, S02 session,
security-architecture note, TCB row, and review index all agree with that pre-review state. The r7
FAIL artifact is preserved byte-for-byte and registered by its exact SHA-256.

I also independently replayed the cumulative S02 review rather than limiting the audit to the
routing diff. All r5 and r6 technical repairs remain effective: the signature-scheme bundle is
honestly arbitrary; general-construction coupling remains open; D-006 and D-009 remain proposed;
their dependent obligations are not treated as approved; the source composite covers the exact four
globs and rejects a Security-source mutation; the repository entry names the exact session-linked
repair input; declaration names and full spans are checked and elaborated; and the compiled policy
retains exactly seven generated helpers.

The documentation/provenance gate, all four focused modules, the inventory probe, the authoritative
compiled-policy audit, completed-root axiom prints, quantitative counterexamples and target counts,
full repository/HashSig/HashSigTest builds, fresh parser execution, isolation checks, both legacy
runtime KATs, and the report render pass. No admission, TCB, source-correspondence, quantitative,
traceability, scope, or overclaim defect remains in S02.

## Exact reviewed state and immutable history

The commit identity reproduced as:

```text
HEAD    a80e4d336276cd86fb80be64e82d9d57e7dfc8b3
parent  2d7cc7532d0fce4e0a312ac9cc4b41d81f2f9863
subject fix(slhdsa): correct S03 successor routing
status  clean before reviewer authorship
```

The candidate changes only S02/S03 documentation and traceability, the TCB matrix pin, the narrow
review-hash registry, and the new immutable r7 artifact. It does not change any S02 Lean module,
the rejected legacy `Security.lean`, construction or primitive code, parser source, vector, or Lake
target. `git diff --check` passed for both `2d7cc753..a80e4d33` and the cumulative
`c5d6cb03..a80e4d33` ranges.

All earlier S02 review artifacts are preserved at their introducing revisions. Their current
SHA-256 values are:

```text
978b186b35763091f3b72a91b0ada9880ae79f101065c026edb0fea71ee51bc4  r1 FAIL
e409eb70c43c8d95d2ac453cf576f112e9fbd030df321c2ba041c05ca2a8529d  r2 FAIL
b58147303d0874d899301050a1266c727bb1639b105f4793d7bd22001d6ca3bc  r3 FAIL
8c213d893913cc1614137501125f83bd610922b0d73be19d9b3ae6da35fe2ab9  r4 invalidated PASS
0c1ea5b29c49d7fc6640509bb974aefd73c1cab6587e2052e34ba57e91b55bb6  r5 FAIL
39328910948604a1920b6956d33885ebca0520eaff7af7b66088c3a30f1f219d  r6 FAIL
30753d77ffd190c63f0c90e132dfa800835eb712e06f7f026afcc5c48cf74c23  r7 FAIL
```

The harness exact-hash registry contains r5, r6, and r7, whose historical prose is excluded from
active-state mutation scans only when byte-identical. Direct `git show` comparisons confirmed r1
through r4 are unchanged from `7b77e700`, r5 is unchanged from `00634296`, r6 is unchanged from
`2d7cc753`, and r7 at the candidate matches the registered hash, 16,996-byte size, and 323 lines.

The four current S02 source hashes remain:

```text
f927253bf39108b4471a1cf50a043fde534116325510fb3ac64dee8918e30164  Notions.lean
64e2d767e0d16e2cddb2506156690610f0a099ce679717274a760fc028e1bac4  OracleSurface.lean
7b02ea5eb79a51805a4ae727c993be71a3670f58fd4d655afd272cc99aead71a  Transcript.lean
3fefd8776594b36b74590e3767a73d203cfea663f5b8106d6663ba6153596cee  Architecture.lean
```

## R7 finding disposition

### S02-R7-001 / F-086 — fixed

`sessions/S03-data-widths-parameters-adrs-codecs.md` now has no ambiguous predecessor reference:

- its status is blocked by r7 pending repaired r8 review;
- it says no accepted predecessor currently exists;
- it identifies `7b77e700` as invalidated evidence that must never be used as an S03 predecessor or
  start target;
- candidate S02 types become accepted inputs only after independent r8 PASS; and
- its handoff forbids implementation before this verdict and requires binding S03 to the exact
  accepted repair commit.

The active README, plan, S02 session, security-architecture note, session/review indexes, findings
register, rendered report, and TCB-010 note all say r7 failed and r8 is the pending acceptance gate.
F-086 is `REMEDIATED-PENDING-REVIEW` in the reviewed prestate, which is the correct implementer-side
status before this independent verdict. No active surface calls `7b77e700` accepted or directs S03
to it.

## R5 and R6 repair replay

### Generated helpers and admission policy

The cumulative source introduces no unallowlisted `sorry`/`admit`, axiom declaration, explicit
`unsafe`, `extern`, source `partial`/`partial_fixpoint`, initializer, `implemented_by` override,
linter suppression, Interop import, Extern import, or edit to the legacy security placeholder. The
twelve `noncomputable` declarations are explicit ENNReal probability and master expressions.
Source-recursive projections use total list combinators. The compiled audit reports exactly the
seven Lean 4.32.2 `._unsafe_rec` helpers already permitted by the frozen policy and no addition,
removal, or rename.

### Scheme boundary and decisions

`SchemeInterface` supplies a shared signature carrier, randomizer projection, key generation,
signing, and verification, but no law couples those fields to one another or to the future general
SLH-DSA construction. Code, specification, blueprint, architecture, matrices, report, and session
all classify it as an arbitrary signature-scheme experiment boundary. Always-accepting verification
and replacement-randomizer examples elaborate, confirming the limitation. F-079 and PO-003 remain
open for S08/S09.

D-006 and D-009 are `proposed` with `approver=unassigned`. PO-006 and PO-008 remain provisional;
PO-003 remains open. The standalone source-shaped component games are therefore a candidate design,
not an accepted supersession of the earlier transcript-derived-target contract. F-080 remains open,
and no prose infers decision approval from this technical review.

### Provenance, revision, and declaration inventory

The active source composite has the exact ordered globs and command recipe:

```text
HashSig/SLHDSA/*.lean
HashSig/SLHDSA/C13/*.lean
HashSig/SLHDSA/Concrete/*.lean
HashSig/SLHDSA/Security/*.lean
```

Its independently reproduced digest is
`09d340f611f600f9cd9a81e47ee2df06f9a9a3bbdd86fff439741cf09142625b`. The gate
copies the selected tree, changes `Security/Architecture.lean`, and succeeds only when that change
causes the exact composite-mismatch rejection.

The repository authority record has only `repair_base_revision`, with
`revision_semantics=exact-repair-base`; it equals the exact invalidated S02 implementation input
`7b77e700b3d24a6ab94ed741a650954bbd90859a`. The checker hard-codes that identity,
cross-checks the one exact S02 session marker, and then checks ancestry as an additional consistency
condition. The source ledger does not call it an accepted successor base.

All eighteen S02 declaration rows have exact full spans from declaration keyword through final
nonblank line. The corrected dependencies `CollectionDisjoint`, `SPprobSuccess`, and
`sampledTargetRealImpl` occur at their actual load-bearing sites, and `S02InventoryProbe.lean`
elaborates all eighteen roots plus those three dependencies. The inventory is explicitly
`bootstrap-manual`; F-018 remains open, so no completeness or kernel-export claim is made.

## Primary-source and semantic correspondence

The EasyCrypt checkout was clean at exactly
`a28e4c53897a4bb57b575a177225862d48f824b7`. The checked hashes were:

```text
3bb1ce65aec7af6ea91dc65be066ca2e7a1e7110e126acc02cd1886271372741  proofs/SPHINCS_PLUS.ec
67b0031db0fbd8c335b8008fe3c00fb5bc109d4902591fabfdbaf99c60a130d1  proofs/KeyedHashFunctions.eca
ac5e354b298bbb8760c483e0bd214c2f6bd78597fde5756f6428ef2bab043f7f  proofs/FORS_ES.ec
1e1f5c82fa6dcfd9a8b83004ea8df408fda8c7f87f03ae65d565dcd2ad904c92  proofs/TweakableHashFunctions.eca
d1ca5fff2e7544c3591d665cd04a2e0f7454c0a2971388911eb6f6303c026001  SPHINCS_EC.pdf
9b49545b61bc194f0d7793556b04ca8f2257990057e229f51164ce2aafe89aa6  CCS 2019 paper
8ef34228276f3386d23cb0da8c14592b8cfb0db3358016bba64df7a004f8d13d  NIST FIPS 205
```

`proofs/SPHINCS_PLUS.ec:4338-4370` gives, in order, the two PRF differences, Hmsg ITSR,
truncated DSPR-minus-SPprob, coefficient-three FORS-F TCR, FORS-H TCR-C, FORS-Tl TCR-C,
coefficient-`w-2` WOTS-F UD-C, WOTS-F TCR-C, WOTS-F PRE-C, WOTS-Tl TCR-C, and XMSS-H TCR-C.
`componentTerm` and `repairedRHS` retain those twelve roles, the source order, the two coefficients,
and the one truncated subtraction. There is no birthday/interleaving scalar or additive qS/qH loss.

Inspection of every changed load-bearing declaration confirms:

- generated key pairs package public/secret seed and root coherence, while the outer experiment
  remains explicitly abstract;
- public queries cannot represent PRF or PRFmsg, and qS/qH are structural bounds on the actual
  public program for every public key;
- TCR and DSPR choose `(tweak,input)` through a two-phase target oracle and validate the program's
  selected natural index;
- SPprob reruns the same DSPR program and selected-index interface, ignoring only its Boolean guess;
- PRE and real UD sample one fresh hidden input per target query and expose only its hash output;
- ideal UD samples a fresh output per target query;
- every `-C` program places target and collection queries in one execution log and checks target
  distinctness and cross-collection disjointness there; and
- ITSR gives the program its post-hop/NPRF setup while the challenger supplies only fresh randomizer
  queries; no full generated SLH secret key is injected into that component world.

No impossible provider, arbitrary target sampler, free public seed, secret public-query constructor,
unbounded target slack, empty target requirement, false-elimination dependency, QROM claim, or master
theorem proof is present. `QROMClaim` has no constructors and is only a boundary marker.

## Axiom and quantitative replay

The focused probe printed axioms for the parameter restrictions and positivity roots; digest and
ITSR roots; generated keys and the scheme boundary; public/full query handlers and structural
bounds; transcript coherence and distributions; role-card theorems; target and collection handlers,
events, and trace predicates; all component probabilities; `componentTerm`; `eufAdvantage`;
`repairedRHS`; `RepairedMasterStatement`; and budget independence.

Every completed root was axiom-free or used a subset of exactly:

```text
[propext, Classical.choice, Quot.sound]
```

No completed S02 root reported `sorryAx` or any other axiom. The authoritative aggregate audit saw
the one legacy `sorryAx` only at the exact frozen `SLHDSA.slhdsa_euf_cma_security` placeholder.

Role cardinalities evaluate to `construction / primitive / master / target = 8 / 6 / 12 / 8`.
The six unique parameter tuples cover the SHA2/SHAKE pairs of all twelve FIPS parameter sets. Their
computed `len` and target counts, ordered FORS F, FORS H, FORS Tl, WOTS F UD-C, WOTS F TCR-C,
WOTS F PRE-C, WOTS Tl, XMSS H, are:

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

All formula caps are positive. Empty traces satisfy the cap but every selected-target event fails;
invalid indices, duplicate target tweaks, target/collection overlap, and zero direct qS/qH budgets
are rejected. The old `17 * (17 + 0) / 256` interleaving expression is witnessed above one by the
compiled `256 < 17 * (17 + 0)` regression and is absent from the candidate RHS.

## Reproduced commands and results

Commands are classified as static audit, elaboration, runtime, or report rendering.

```text
git show -s --format='%H%n%P%n%s' a80e4d33
git diff --name-status 2d7cc753..a80e4d33
git diff --name-status c5d6cb03..a80e4d33
git diff --check 2d7cc753..a80e4d33
git diff --check c5d6cb03..a80e4d33
  PASS (static exact identity, repair scope, cumulative scope, and whitespace).

sha256sum docs/slhdsa/reviews/S02-security-architecture-review-r5.md \
  docs/slhdsa/reviews/S02-security-architecture-review-r6.md \
  docs/slhdsa/reviews/S02-security-architecture-review-r7.md
git show <introducing-commit>:<review-path> | sha256sum
  PASS (static immutable history and exact r5/r6/r7 registry values).

./scripts/slhdsa/validate.sh --docs-only
  PASS (runtime documentation/provenance gate): exact repair input, matrix pins, 18 complete
  declaration spans, five dependency sets, four-glob composite, controlled Security-byte mutation,
  local authority hashes, and S01 frozen-profile/descriptor mutation suites.

lake env lean HashSig/SLHDSA/Security/Notions.lean
lake env lean HashSig/SLHDSA/Security/OracleSurface.lean
lake env lean HashSig/SLHDSA/Security/Transcript.lean
lake env lean HashSig/SLHDSA/Security/Architecture.lean
lake env lean scripts/slhdsa/S02InventoryProbe.lean
  PASS (focused elaboration): all four modules and all inventory/dependency roots resolve.

lake env lean scripts/slhdsa/PolicyAudit.lean
  PASS (authoritative compiled static audit): 27 HashSig modules; 1,629 owned constants; exact
  seven generated helpers; union exactly [propext, Classical.choice, Quot.sound, sorryAx], with
  sorryAx confined to the legacy placeholder.

lake env lean /tmp/S02R6IndependentProbe.lean
  PASS (reviewer-inspected focused elaboration replay): interface noncoupling, target/event
  counterexamples, exact role cards, six parameter tuples, and all completed-root axiom prints.

./scripts/slhdsa/validate.sh
  PASS (full runtime/elaboration gate): 3,007-job repository build, 2,748-job HashSig build,
  2,743-job HashSigTest build, exact fresh parser with 68 runtime cases, ordinary/IR initializer
  rejection with absent sentinel, generated umbrella, extern/interop isolation, authoritative
  policy audit, and both legacy positive/tamper KATs.

latexmk -pdf -interaction=nonstopmode -halt-on-error \
  -outdir=/tmp/slhdsa-s02-r8-tex slhdsa-formalization-audit.tex
  PASS (report rendering): seven pages, 324,157 bytes; box-layout warnings only.
```

The full wrapper distinguishes elaboration from runtime execution. The SHA2-128-24 and C13 KATs
remain C-reference regression vectors with their pinned licenses/hashes and positive/tamper expected
results; they are not FIPS/ACVP conformance evidence. No vector, interface mode, or expected-result
record changed in S02.

## Findings and successor eligibility

Reviewer findings: **none**.

S02 is accepted at exact commit
`a80e4d336276cd86fb80be64e82d9d57e7dfc8b3`. This verdict accepts the implemented candidate
architecture and its accurately stated boundaries; it does not approve D-006 or D-009, prove the
master inequality, close F-079/F-080, refine `SchemeInterface` to the general construction, replace
the legacy `sorry`, establish QROM/asymptotic security, or claim FIPS/ACVP implementation
conformance.

S03 is eligible to begin only from exact accepted predecessor
`a80e4d336276cd86fb80be64e82d9d57e7dfc8b3`. The first S03 implementation record must bind to that
commit and must never use invalidated `7b77e700b3d24a6ab94ed741a650954bbd90859a` as its
predecessor.

## Final decision

Final result: **PASS with zero blocking and zero nonblocking findings**. The r7 routing defect is
fixed, every earlier S02 repair remains effective, all required gates pass, and the exact candidate
is eligible as the S03 predecessor under the scope limitations above.
