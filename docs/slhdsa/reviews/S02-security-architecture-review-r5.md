# S02 independent security-architecture review r5

Verdict: **FAIL**

Blocking findings: **6**
Nonblocking findings: **0**

Reviewer: fresh independent S02 r5 reviewer; not the S02 implementer.
Review date: 2026-08-25.
Reviewed implementation commit: `7b77e700b3d24a6ab94ed741a650954bbd90859a`, relative to
accepted predecessor `c5d6cb03d11126e6290bec58ef8824f36fc3a73b`.

Independence and write-scope statement: I began from the session inputs, review protocol, pinned
primary sources, exact S02 diff, four Lean modules, matrices, report, and session contract rather
than the implementer's acceptance narrative. I made no implementation or documentation repair.
This immutable r5 artifact is my only repository edit. Temporary Lean probes under `/tmp` and
read-only build/audit commands were the only other actions.

## Decision summary

The four S02 modules elaborate, their completed load-bearing roots have only the accepted standard
axioms, their target-count formulas are positive at all twelve FIPS parameter sets, and the twelve
RHS roles and coefficients follow the pinned EasyCrypt theorem. Those local successes do not
permit acceptance under the adversarial protocol.

The authoritative compiled policy audit rejects eight new generated partial runtime helpers. The
accepted commit also cannot pass its own repository-revision provenance check, while the source-tree
composite omits every new S02 module. Mandatory matrices, declaration/TCB inventory, findings,
decisions, report, and source-ledger traceability remain stale or contradictory. At the semantic
level, the supposedly generic repaired statement connects general-`d` target formulas to the
existing explicitly `d = 1` signing and verification implementation. Finally, the accepted
standalone-game design contradicts the still-authoritative S02 requirement for nonempty exact
honest-transcript-derived targets and leaves obsolete claims in `Transcript.lean`.

Under `review-protocol.md`, any one of these issues requires FAIL. S02 is reopened and every
successor, including S03, is blocked pending a fixed commit and independent re-review.

## Primary-source correspondence

The authority checkout was clean at exactly
`a28e4c53897a4bb57b575a177225862d48f824b7`. The reviewed hashes were:

```text
3bb1ce65aec7af6ea91dc65be066ca2e7a1e7110e126acc02cd1886271372741  proofs/SPHINCS_PLUS.ec
67b0031db0fbd8c335b8008fe3c00fb5bc109d4902591fabfdbaf99c60a130d1  proofs/KeyedHashFunctions.eca
ac5e354b298bbb8760c483e0bd214c2f6bd78597fde5756f6428ef2bab043f7f  proofs/FORS_ES.ec
1e1f5c82fa6dcfd9a8b83004ea8df408fda8c7f87f03ae65d565dcd2ad904c92  proofs/TweakableHashFunctions.eca
d1ca5fff2e7544c3591d665cd04a2e0f7454c0a2971388911eb6f6303c026001  SPHINCS_EC.pdf
9b49545b61bc194f0d7793556b04ca8f2257990057e229f51164ce2aafe89aa6  sphincsplus-framework-CCS2019.pdf
```

`SPHINCS_PLUS.ec:4338-4370` gives, in exact order, SKG PRF, MKG PRFmsg, Hmsg ITSR,
truncated DSPR-minus-SPprob, `3 *` FORS-F TCR, FORS-H TCR-C, FORS-Tl TCR-C,
`(w - 2) *` WOTS-F UD-C, WOTS-F TCR-C, WOTS-F PRE-C, WOTS-Tl TCR-C, and XMSS-H
TCR-C. `Architecture.lean:505-571` preserves that order and those coefficients.

The standalone target-game mechanics also match the primary game shapes in the respects sampled
here: `TweakableHashFunctions.eca:57-134` samples a fresh hidden PRE input; lines 261-335 define
chosen-input TCR; lines 341-453 give DSPR/SPprob; lines 470-542 sample a fresh real input or ideal
output per UD query; and lines 610-872 run target and collection oracles within the same `pick`
phase. `KeyedHashFunctions.eca:1486-1567` supplies the ITSR fresh-key oracle, while
`FORS_ES.ec:2175-2239` puts concrete post-hop setup and caching inside the reduction.

These source checks support the local game definitions. They do not cure the Lean LHS/profile
mismatch or the session-contract defects below.

## Findings

### S02-R5-001 — the authoritative compiled policy rejects eight new partial helpers

Severity: **CRITICAL**.

`review-protocol.md` and `validation.md` permit exactly seven Lean 4.32.2 compiler-generated
`._unsafe_rec` helpers under `HashSig/**`. Any addition, removal, or rename fails unless an accepted
decision, TCB row, focused validator change, tests, and independent review deliberately change the
policy. S02 did none of those things.

After the successful HashSig build, the authoritative audit reported 27 imported HashSig modules
and rejected this 15-element partial set. The eight additions and their safe source parents are:

| generated helper | source parent |
| --- | --- |
| `SLHDSA.Security.itsrHistoryTargets._unsafe_rec` | `Notions.lean:147-150` |
| `SLHDSA.Security.signedRequests._unsafe_rec` | `Transcript.lean:37-41` |
| `SLHDSA.Security.signingITSRHistory._unsafe_rec` | `Transcript.lean:46-55` |
| `SLHDSA.Security.chosenTargets._unsafe_rec` | `Architecture.lean:239-243` |
| `SLHDSA.Security.chosenTargetsC._unsafe_rec` | `Architecture.lean:245-250` |
| `SLHDSA.Security.sampledTargets._unsafe_rec` | `Architecture.lean:252-256` |
| `SLHDSA.Security.collectionTweaks._unsafe_rec` | `Architecture.lean:258-266` |
| `SLHDSA.Security.itsrOracleHistory._unsafe_rec` | `Architecture.lean:325-333` |

R4 source-scanned for the spellings `partial` and `unsafe`, but did not run the compiled semantic
gate and therefore missed these generated entries. This is exactly the lexer-versus-elaborated-
environment failure mode the S00 policy was designed to prevent.

Required repair: keep the seven-helper policy and make these definitions compile without new
source-recursion helpers. The direct total rewrites are `List.foldr` for `itsrHistoryTargets`,
`List.map` for `chosenTargets` and `itsrOracleHistory`, and `List.filterMap` for the remaining five.
Then rerun the complete compiled audit and confirm the exact original seven-helper set.

### S02-R5-002 — the accepted commit was not the reviewed tree and fails its own revision gate

Severity: **CRITICAL**.

The r4 artifact records only predecessor commit `c5d6cb03` plus an uncommitted S02 worktree
(`S02-security-architecture-review-r4.md:8-19`). Its command record says that, before writing r4,
the scope contained the four modules, umbrella import, two S02 documents, and r1-r3. Its reviewed
hash list covers only those four modules and two documents, and its final decision says no commit
was created. The final S02 commit subsequently added the r4 artifact and changed acceptance/index
state in `README.md`, `findings.md`, `plan.md`, `reference-manifest.json`, both review/session
indexes, and the session record. Those final bytes were not part of the independently reviewed
tree.

The resulting commit is also unreproducible under its own docs gate. At `7b77e700`, the manifest's
repo-local `vcvio` record pins predecessor `c5d6cb03`, while
`scripts/slhdsa/check-harness.py:5198-5201` requires `git rev-parse HEAD` to equal the recorded
revision. Therefore an exact checkout of `7b77e700` deterministically fails. The S03 bootstrap
repeats the same self-pin cycle: its manifest records `7b77e700` while HEAD is `7c5117bd`; the
live reproduction failed with:

```text
SLH-DSA harness check: FAIL: reference-manifest.json: revision mismatch for vcvio
```

Required repair: define the manifest field as an input/predecessor pin and validate that semantics
without requiring equality to the containing commit, or otherwise use a non-self-referential
reviewed-tree mechanism. Commit the fixed implementation first; r6 must identify and review that
exact commit. Acceptance/index changes made after a verdict must themselves receive independent
review.

### S02-R5-003 — the source provenance composite excludes all four S02 modules

Severity: **HIGH**.

`reference-manifest.json.source_tree_composite.globs_in_order` contains only:

```text
HashSig/SLHDSA/*.lean
HashSig/SLHDSA/C13/*.lean
HashSig/SLHDSA/Concrete/*.lean
```

It does not contain `HashSig/SLHDSA/Security/*.lean`. The validator reproduces exactly those globs,
so the successful composite check is blind to arbitrary changes in every new S02 implementation
file. `source-ledger.md:37-50` likewise still describes the S00 `f1853af4` baseline and old 22-line
composite as the VCVio source pin.

Required repair: add the Security subtree to the deterministic recipe, update the composite and
source ledger, and add a mutation regression proving that a changed S02 module invalidates the
provenance gate.

### S02-R5-004 — mandatory session traceability is absent and materially contradictory

Severity: **HIGH**.

The universal contract at `plan.md:3-14` requires every session to update coverage, obligations,
assumptions, TCB, declaration inventory, findings, decisions, report traceability, and the session
record. S02 changed none of `docs/slhdsa/matrices/**`, `docs/slhdsa/report/**`,
`proof-obligations.md`, `decisions.md`, `lean-blueprint.md`, or `source-ledger.md`.

The omissions are load-bearing, not editorial:

- `coverage.csv:7-9` still calls the architecture disputed, ITSR missing, and `qS/qH` absent.
- `proof-obligations.csv:3-9` still says target naturals admit zero, `pkSeed` is free, actual query
  bounds are absent, Hmsg/Tl are absent, and challenge samplers are arbitrary.
- `assumptions.csv:3-5` still says the PRF, TCR/DSPR, and ITSR models are pending S02.
- `decisions.csv:7` and `decisions.md:13` leave the exact theorem/notion/classical-model selection
  proposed with no named approver, while the session calls that architecture accepted and frozen.
- `tcb.csv:11` says the exact seven-helper policy passes, contradicted by the compiled 15-helper set.
- `declarations.jsonl` has no row for any S02 load-bearing root or any of its twelve
  `noncomputable` experiment/master definitions.
- `findings.md` contains no canonical rows for the twelve r1-r3 findings; it only appends a prose
  assertion that r4 passed.
- `slhdsa-formalization-audit.tex:104-107` retains the S00 observation of 23 HashSig modules and
  680 owned declarations and later says only that S02 is eligible. An independent static import of
  the S02 environment observed **27 modules and 1,646 owned constants**.

Required repair: reconcile every mandatory surface with separate rows for the rejected legacy
theorem and the proposed replacement architecture; inventory the new load-bearing declarations,
noncomputable boundaries, and generated-runtime policy; register every historical finding and
disposition; and obtain the approval required by the decision policy rather than inferring it from
a technical review.

### S02-R5-005 — the generic master statement is connected to the known `d = 1` scheme

Severity: **CRITICAL**.

`RepairedMasterStatement` at `Architecture.lean:573-580` is generic over `p`.
`ParameterConditions` at `Notions.lean:51-60` requires positive `d` and `h = hp*d` but does not
restrict `d = 1`. Its RHS target formulas at `Architecture.lean:78-97` explicitly count all layers
for general `d`.

The LHS does not describe that general construction:

- `eufAdvantage` at `Architecture.lean:545-551` runs `honestTranscriptDistribution`;
- `honestTranscriptDistribution` at `Transcript.lean:135-146` calls current `slhSign` and
  `slhVerify` through `queryImpl`;
- `Scheme.lean:14-21,64-72` explicitly implements only the `d = 1` parameter set, omits the tree
  index from its digest split, and fixes it to zero;
- `Hypertree.lean:10-20` states that the general `d > 1` hypertree is future work, and its `HtSig`
  is one XMSS signature rather than `d` layers.

This mismatch is already recorded globally as open `F-010`, `COV-003`, and `PO-012`, but r4 did not
apply it to the supposedly exact generic S02 master boundary. For every approved FIPS set, where
`d` is 7, 8, 17, or 22, the LHS and the general RHS target counts refer to different constructions.

Required repair: parameterize the S02 experiment over a scheme interface capable of receiving the
future general hypertree implementation, with explicit coupling laws, or restrict and label the
current statement as only the legacy `d = 1` profile. The current declaration cannot be accepted as
the frozen general SPX-TW master interface.

### S02-R5-006 — the accepted standalone games contradict the authoritative S02 contract

Severity: **HIGH**.

The accepted code deliberately switched to source-shaped standalone component games, but the
controlling contract was never amended or decided:

- `plan.md:65-69` requires honest-transcript-derived distributions;
- `lean-blueprint.md:47-51` requires a nonempty exact-cardinality target family derived from honest
  key/sign transcripts;
- `proof-obligations.csv:9` retains the same critical S12 obligation;
- `Architecture.lean:268-274` instead accepts an actual trace of any length at most the formula cap,
  including zero, and all component probabilities run standalone;
- `security-architecture.md` and the S02 session record explicitly say standalone games may issue
  zero target queries;
- `Transcript.lean:13-17` still says target data is consumed by component programs after the honest
  distribution and refers to certified target packages proving exact occurrence. Those packages
  were removed before r4 and do not exist in the accepted tree.

The primary EasyCrypt game definitions support the standalone-game choice and allow zero queries
at the generic game level. That makes this a required contract/decision repair, not a reason to
silently ignore the inconsistency.

Required repair: record and approve the source-driven change from exact honest-transcript packages
to independently run capped games; update the plan, blueprint, proof obligations, matrices, report,
and Transcript module docstring; and state separately that future concrete reductions must prove
their generated target traces and correspondence.

## Build, semantic-policy, axiom, and source-scan evidence

Commands were classified as elaboration, runtime, or static audit rather than conflated.

```text
git diff --name-status c5d6cb03..7b77e700
  PASS (static scope inventory): four new Security modules, umbrella import, and S02 docs/reviews.

git diff --check c5d6cb03..7b77e700
  PASS (static whitespace check).

lake build HashSig.SLHDSA.Security.Architecture
  PASS (elaboration): 2732 jobs.

lake build HashSig
  PASS (elaboration): 2748 jobs; only the frozen legacy Security.lean:150 sorry warning.

lake env lean scripts/slhdsa/PolicyAudit.lean
  FAIL (authoritative compiled static audit): 27 HashSig modules; eight unallowlisted
  SLHDSA.Security.*._unsafe_rec helpers in the 15-element observed set.

./scripts/slhdsa/validate.sh --docs-only
  FAIL (documentation/provenance runtime gate on the current successor tree):
  reference-manifest.json: revision mismatch for vcvio.

lake env lean /tmp/S02R4IndependentProbe.lean
  PASS (focused elaboration/evaluation after independently inspecting the probe contents).

lake env lean /tmp/S02InventoryProbe.lean
  PASS (static import probe): HashSig modules=27; owned constants=1646.

lake env lean /tmp/S02FipsCounts.lean
  PASS (runtime evaluation): six unique FIPS tuples, representing all twelve sets.
```

The source diff contains twelve `noncomputable` definitions, all probability/ENNReal experiments or
master expressions. No new source `sorry`, `admit`, axiom declaration, explicit `unsafe`, `extern`,
source `partial`, initializer, implementation override, linter suppression, false-elimination
helper, interop import, or `HashSig/SLHDSA/Security.lean` edit was found. The compiled audit,
however, is authoritative over generated partial declarations and fails as recorded above.

The independent axiom replay covered parameter restrictions and positivity; digest/ITSR roots;
generated-key coherence; public/internal query handlers; signing history; EUF/transcript
distributions; all role cards and query-bound lemmas; target/collection handlers and validity
events; every standalone component probability; `componentTerm`; `eufAdvantage`; `repairedRHS`;
`RepairedMasterStatement`; and budget independence. Every print was either axiom-free or a subset
of exactly:

```text
[propext, Classical.choice, Quot.sound]
```

No completed S02 root reported `sorryAx` or a nonstandard axiom.

No vector or executable-conformance artifact changed in S02. Vector hash, license, interface/mode,
expected-result, and positive-coverage review is therefore not applicable to this diff; existing
legacy/C13 KATs remain regression evidence only.

## Quantitative evaluation

Role-card evaluation was `construction / primitive / master / target = 8 / 6 / 12 / 8`.
The legacy reduced tuple reproduced r4's values. I additionally evaluated the six unique FIPS
parameter tuples, which represent all twelve SHA2/SHAKE sets. Columns are FORS F, FORS H, FORS Tl,
WOTS F UD-C, WOTS F TCR-C, WOTS F PRE-C, WOTS Tl, and XMSS H:

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

All values are positive natural numbers; there is no denominator or finite-range failure in these
symbolic counts. Their positivity does not repair the general-`d` LHS mismatch in S02-R5-005.

## Earlier-review disposition

R5 does not reopen the local r1-r3 game-timing repairs: the accepted code removes the impossible
provider, uses in-game target oracles, samples fresh PRE/UD values, runs target and collection calls
together, and keeps post-hop ITSR setup inside the reduction program. The six findings above are
new failures in the compiled policy, accepted-tree provenance, mandatory traceability, construction
profile, and governing contract. They were outside or contradicted the narrower r4 review scope.

## Immutable final decision

Final verdict: **FAIL with six blocking findings and zero nonblocking findings**.

S02 is not accepted at commit `7b77e700`. The S03 bootstrap must not be treated as an eligible
successor. A repair iteration must preserve this artifact, register and dispose all six findings
with evidence, produce a fixed implementation commit, rerun the complete docs/provenance,
elaboration, compiled-policy, axiom, quantitative, and report gates, and receive a fresh independent
`S02-security-architecture-review-r6.md` PASS before successor work resumes.
