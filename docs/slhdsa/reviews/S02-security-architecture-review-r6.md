# S02 independent security-architecture review r6

Verdict: **FAIL**

Blocking findings: **5**
Nonblocking findings: **0**

Reviewer: fresh independent S02 r6 reviewer; not the S02 implementer.
Review date: 2026-08-25.
Reviewed repair commit: `00634296d3f03a409fa3c39c6592ceb8cc73b1f7`, relative to repair
predecessor `7c5117bdaf8f9f62ffec6220c1f6669f5c6caa4e` and the reopened S02 commit
`7b77e700b3d24a6ab94ed741a650954bbd90859a`.

Independence and write-scope statement: I began read-only from `AGENTS.md`, the review protocol,
the immutable r5 FAIL artifact, the exact commit diff, the four Lean modules, primary sources,
matrices, report, provenance records, and generated/compiled inventories. I did not implement the
repair. This immutable r6 artifact is my only repository edit. A temporary independent Lean probe
under `/tmp` and read-only validation, build, source, and Git commands were the only other actions.

## Decision summary

The repair restores the exact seven-helper compiled policy, removes the direct call from the generic
EUF experiment to the known `d = 1` implementation, expands the active source composite to include
the four S02 modules, and updates substantial traceability. The focused modules, HashSig build,
docs/provenance gate, full baseline gate, axiom replay, formula evaluation, and primary-source game
comparison all succeed.

Those successes are insufficient under the zero-finding review protocol. The new scheme function
bundle has no law tying its algorithms or randomizer projection to one general SLH-DSA
construction. The standalone-game decision remains unapproved while authoritative obligations
treat it as a superseding decision. The manifest records stale commands that omit the Security
subtree and adds no required mutation regression. Its repository revision check accepts any
ancestor rather than the declared exact session input and calls an invalidated commit the S03
predecessor. Finally, the mandatory declaration inventory contains nonexistent dependencies and
incorrect source spans, while the S02 scope record denies the harness edit present in the reviewed
commit.

Any one issue requires FAIL. All successors, including S03, remain blocked pending a fixed commit
and a fresh independent r7 review.

## Primary-source correspondence

The EasyCrypt authority checkout was clean at exactly
`a28e4c53897a4bb57b575a177225862d48f824b7`. The source hashes matched the canonical ledger:

```text
3bb1ce65aec7af6ea91dc65be066ca2e7a1e7110e126acc02cd1886271372741  proofs/SPHINCS_PLUS.ec
67b0031db0fbd8c335b8008fe3c00fb5bc109d4902591fabfdbaf99c60a130d1  proofs/KeyedHashFunctions.eca
ac5e354b298bbb8760c483e0bd214c2f6bd78597fde5756f6428ef2bab043f7f  proofs/FORS_ES.ec
1e1f5c82fa6dcfd9a8b83004ea8df408fda8c7f87f03ae65d565dcd2ad904c92  proofs/TweakableHashFunctions.eca
d1ca5fff2e7544c3591d665cd04a2e0f7454c0a2971388911eb6f6303c026001  SPHINCS_EC.pdf
9b49545b61bc194f0d7793556b04ca8f2257990057e229f51164ce2aafe89aa6  sphincsplus-framework-CCS2019.pdf
```

`proofs/SPHINCS_PLUS.ec:4338-4370` gives, in order, SKG PRF, MKG PRFmsg, Hmsg
ITSR, truncated DSPR-minus-SPprob, `3 *` FORS-F TCR, FORS-H TCR-C, FORS-Tl
TCR-C, `(w - 2) *` WOTS-F UD-C, WOTS-F TCR-C, WOTS-F PRE-C, WOTS-Tl TCR-C,
and XMSS-H TCR-C. `Architecture.lean:504-575` retains that order and those coefficients.

The independently inspected component interfaces also retain their source shape:

- `TweakableHashFunctions.eca:57-134` samples a fresh hidden input on each PRE target query;
- lines 261-335 give the chosen-input TCR target oracle and selected-index event;
- lines 341-453 run the same DSPR adversary interface for DSPR and SPprob;
- lines 470-542 sample a fresh real input or ideal output on each UD target query;
- lines 610-872 run target and collection calls together in the same `pick` phase; and
- `KeyedHashFunctions.eca:1486-1567` supplies the fresh-key ITSR oracle and freshness/target-union
  event.

The repaired list-combinator projections preserve the prior trace order and selected events. No new
source-formula, game-timing, coefficient, or role-count discrepancy was found. The five failures
below concern the claimed general-scheme coupling, decision state, provenance semantics, and
mandatory audit data.

## Findings

### S02-R6-001 — `SchemeInterface` has no law coupling its fields to one general construction

Severity: **CRITICAL**.

R5-005 required an experiment parameterized by a scheme interface capable of receiving the future
general hypertree implementation, with explicit coupling laws. `SchemeInterface` at
`OracleSurface.lean:62-67` contains only five unconstrained fields:

```text
Signature
randomizer
keygen
sign
verify
```

Indexing the structure by `Primitives p` removes the previous syntactic call to `slhSign` and
`slhVerify`, and `keygen` returns a `GeneratedKeyPair` whose public/secret seed and root agree. It
does not establish that `sign`, `verify`, `randomizer`, and `keygen` implement one general
`p`/`d`-layer construction or even agree with each other.

The independent compiled probe defined `alwaysAcceptingScheme`, preserving `Signature`,
`randomizer`, `keygen`, and `sign` while replacing `verify` by `fun _ _ _ => true`. It also defined
`replaceRandomizer`, preserving every algorithm while accepting an arbitrary replacement projection.
Both definitions elaborated. Thus a context can change EUF success or transcript ITSR extraction
independently of all other scheme fields without providing any witness.

This contradicts the disposition claimed by F-079 and overstates:

- `security-architecture.md:90-104`, which describes one attacked scheme and the signature's `R`;
- DECL-016's rationale that the structure resolves the general-construction defect; and
- PO-003's discharged coupling status.

Required repair: either add a reviewed construction/refinement witness tying `keygen`, `sign`,
`verify`, the signature representation, and `randomizer` to the same general `p`/`d`-indexed
construction—including that `randomizer` is the signature `R` used by digest/verification—or
classify this honestly as an arbitrary signature-scheme experiment boundary and leave F-079/PO-003
open until S08/S09 supplies that witness. S02 need not prove perfect completeness, but a bare
function bundle is not itself evidence of construction coupling.

### S02-R6-002 — the standalone-game contract is treated as superseded without approval

Severity: **HIGH**.

R5-006 required the source-driven change from exact outer-transcript targets to standalone capped
games to be recorded **and approved**. The decision is recorded as D-009, but
`matrices/decisions.csv` leaves it `proposed` with `approver=unassigned`. The decision policy says an
accepted decision requires a named approver.

Despite that state:

- PO-008 is `discharged` and says D-009 supersedes the old requirement;
- `proof-obligations.md:22-24` checks the replacement obligation;
- plan, blueprint, specification, and security-architecture prose use the replacement contract as
  their operative boundary; and
- D-006 similarly remains proposed while `specification.md` says the theorem/model selection follows
  it.

A technical review cannot silently supply the missing owner approval, and a proposed decision
cannot supersede the authoritative contract under the repository's own policy.

Required repair: obtain and record a named approval for D-009, and for D-006 if its selection is
load-bearing. Otherwise retain proposed status and keep the affected obligations and claims pending,
without saying the proposal supersedes or discharges the prior requirement.

### S02-R6-003 — the source-composite record is internally inconsistent and lacks its required mutation regression

Severity: **HIGH**.

The active `source_tree_composite.globs_in_order` now includes
`HashSig/SLHDSA/Security/*.lean`, and the recorded digest matches the resulting 26-file manifest.
However, both command records in the same object still give the old three-glob recipe:

```text
original_command:      ... HashSig/SLHDSA/Concrete/*.lean | sha256sum
deterministic_command: ... HashSig/SLHDSA/Concrete/*.lean | sha256sum
```

Those commands omit every S02 module and do not reproduce the recorded digest. The validator ignores
the two stale fields and trusts only `globs_in_order`, so the normal PASS does not detect the internal
contradiction.

R5-003 also explicitly required a mutation regression proving that changing an S02 module invalidates
the provenance gate. No focused Security-source mutation test was added. Existing mutation suites
cover the frozen S01 parser/authority machinery, not this new composite boundary.

Required repair: update both command fields to the exact 26-file recipe, validate their declared
recipe against the configured glob list, and add a controlled temporary mutation regression that
changes a Security-module byte and observes rejection.

### S02-R6-004 — repository revision validation accepts an arbitrary ancestor and contradicts the session records

Severity: **HIGH**.

R5-002 required a non-self-referential but reproducible input/predecessor pin. The new
`git_revision_is_ancestor` gate only asks whether an arbitrary 40-hex revision is an ancestor of
`HEAD`. It does not bind that revision to the accepted input named by the active session. Replacing
the value with an unrelated older repository ancestor would still pass.

The manifest currently records invalidated commit `7b77e700` as the ancestor session base.
`source-ledger.md` calls that value the “S03 predecessor,” while the S03 session record correctly
calls it a former predecessor whose r4 acceptance was invalidated. Exact active Lean bytes are
separately hashed, but that does not repair the meaning or fail-closed identity of the revision
record, nor does it bind documentation and harness bytes.

Required repair: define an unambiguous field such as `accepted_input_revision` or
`repair_base_revision`, cross-check it with the active session record, and validate the exact expected
revision rather than arbitrary ancestry. Correct the ledger so `7b77e700` is not described as S03's
accepted predecessor.

### S02-R6-005 — mandatory traceability contains false declaration data and contradictory scope prose

Severity: **HIGH**.

R5-004 required synchronized and accurate declaration, matrix, report, findings, decisions, TCB,
and session traceability. The new declaration rows contain dependency names that do not exist in the
reviewed Lean environment:

| rows | recorded dependency | actual declaration |
| --- | --- | --- |
| DECL-022, DECL-025, DECL-026, DECL-027 | `SLHDSA.Security.CollectionSeparated` | `SLHDSA.Security.CollectionDisjoint` |
| DECL-024 | `SLHDSA.Security.SPSuccess` | `SLHDSA.Security.SPprobSuccess` |
| DECL-026 | `SLHDSA.Security.sampledTargetImpl` | `SLHDSA.Security.sampledTargetRealImpl` |

The new source spans also commonly end on the declaration header instead of the declaration end.
For example, DECL-015 ends on line 35 although `GeneratedKeyPair` ends on line 39; DECL-016 ends on
line 62 although `SchemeInterface` ends on line 67; and DECL-019 ends on line 118 although
`targetCount_pos` ends on line 140. These are exact structured fields, not informal prose.

The S02 session record adds another direct contradiction. Lines 11-12 say S02 did not reopen or edit
the frozen harness, while the exact reviewed commit modifies `scripts/slhdsa/check-harness.py`.
Lines 135-138 later acknowledge that manifest-semantic harness repair.

Required repair: correct every dependency identity and full source span, check the new rows against
the current source/elaborated declarations, and describe the narrow harness change accurately in the
session scope. The inventory may remain explicitly manual/incomplete under F-018; its populated
facts still must be true.

## Reproduced command and gate evidence

Commands are classified as static audit, elaboration, or runtime rather than conflated.

```text
git show -s --format='%H%n%P%n%s' 00634296
  PASS (static identity): exact reviewed commit and predecessor recorded above.

git diff --name-status 7c5117bd..00634296
  PASS (static scope inventory): four S02 Lean modules, S02 documentation/matrices/report,
  immutable r5 artifact, manifest, and the narrow harness validator change.

git diff --check 7c5117bd..00634296
  PASS (static whitespace audit).

lake env lean HashSig/SLHDSA/Security/Notions.lean
lake env lean HashSig/SLHDSA/Security/OracleSurface.lean
lake env lean HashSig/SLHDSA/Security/Transcript.lean
lake env lean HashSig/SLHDSA/Security/Architecture.lean
  PASS (focused elaboration).

lake build HashSig
  PASS (elaboration): 2748 jobs; only the frozen legacy Security.lean:150 warning.

lake env lean scripts/slhdsa/PolicyAudit.lean
  PASS (compiled semantic audit): 27 HashSig modules, 1,629 owned constants, exact original
  seven compiler `_unsafe_rec` helpers, and transitive axiom union exactly
  [propext, Classical.choice, Quot.sound, sorryAx], with sorryAx confined to the legacy placeholder.

./scripts/slhdsa/validate.sh --docs-only
  PASS (documentation/provenance runtime gate): local sources and active 26-file digest verified.
  This successful execution does not detect findings 003-005 because the relevant stale command,
  arbitrary-ancestor, and manual-inventory facts are not semantically checked.

./scripts/slhdsa/validate.sh
  PASS (full build/runtime gate): full build, HashSig build, HashSigTest build, private fresh parser,
  68 parser cases, policy fixtures, isolation gates, legacy KAT, and C13 KAT all passed.

lake env lean /tmp/S02R6IndependentProbe.lean
  PASS (focused elaboration/evaluation): adversarial scheme transformations, trace-event regressions,
  role cards, all FIPS formula values, and load-bearing `#print axioms` replay.
```

The reviewed diff introduces no new source `sorry`, `admit`, axiom declaration, explicit `unsafe`,
`extern`, source `partial`, initializer, implementation override, linter suppression, false
elimination, Interop import, Extern import, or edit to the rejected
`HashSig/SLHDSA/Security.lean`. The twelve `noncomputable` definitions are the ENNReal probability
experiments and master expressions already intended by the architecture. The total `List.foldr`,
`List.map`, and `List.filterMap` rewrites remove all eight S02-generated partial helpers.

The full validation also replayed the two existing embedded KATs. Their status remains unchanged:
they are C-reference regression evidence for the legacy SHA2-128-24 and C13 profiles, not FIPS/ACVP
implementation-conformance evidence. S02 changes no vector, interface mode, expected result, or
conformance claim.

## Axiom replay

The independent probe covered parameter restrictions and positivity; digest/ITSR roots;
generated-key coherence; `SchemeInterface`; public/internal query handlers; structural query bounds;
signing history; EUF/transcript predicates and distributions; all role-card and target-count roots;
target/collection handlers and events; every standalone component probability; `componentTerm`;
`eufAdvantage`; `repairedRHS`; `RepairedMasterStatement`; and budget independence.

Every completed root was axiom-free or used a subset of exactly:

```text
[propext, Classical.choice, Quot.sound]
```

No completed S02 root reported `sorryAx` or another nonstandard axiom.

## Quantitative evaluation

Role-card evaluation was `construction / primitive / master / target = 8 / 6 / 12 / 8`.
The six unique FIPS parameter tuples represent all twelve SHA2/SHAKE sets. Columns below are FORS F,
FORS H, FORS Tl, WOTS F UD-C, WOTS F TCR-C, WOTS F PRE-C, WOTS Tl, and XMSS H:

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

All values are positive natural numbers, and no range, denominator, truncation-coefficient, or
role-order defect was found. These evaluations do not supply the missing general-scheme coupling or
repair the audit-data findings.

## R5 disposition audit

| r5 finding | r6 result |
| --- | --- |
| S02-R5-001 generated partial helpers | Local repair confirmed: exact original seven-helper policy passes. |
| S02-R5-002 unreproducible acceptance revision | Not fully repaired: arbitrary-ancestor semantics and predecessor contradiction; S02-R6-004. |
| S02-R5-003 omitted S02 source provenance | Not fully repaired: active hash includes S02, but command records and mutation regression do not; S02-R6-003. |
| S02-R5-004 absent traceability | Not fully repaired: false declaration dependencies/spans and session-scope contradiction; S02-R6-005. |
| S02-R5-005 generic LHS hardwired to d=1 | Direct d=1 call removed, but construction/randomizer coupling remains unproved and unrepresented; S02-R6-001. |
| S02-R5-006 stale transcript-derived target contract | Prose updated, but the governing decision remains unapproved while treated as superseding; S02-R6-002. |

The earlier r1-r3 timing and source-game repairs remain intact. R6 does not reopen their local
two-phase, selected-index, fresh-input/output, same-execution collection, or post-hop ITSR mechanics.

## Immutable final decision

Final verdict: **FAIL with five blocking findings and zero nonblocking findings**.

S02 is not accepted at commit `00634296`. S03 and every later successor remain blocked. A repair
iteration must preserve r5 and this r6 artifact, register and dispose all five findings with exact
evidence, produce a fixed implementation commit, rerun the full documentation/provenance,
elaboration, compiled-policy, axiom, quantitative, and traceability gates, and receive a fresh
independent r7 PASS before successor work resumes.
