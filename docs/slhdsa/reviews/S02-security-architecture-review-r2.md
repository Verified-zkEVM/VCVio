# S02 independent security-architecture review r2

Verdict: **FAIL**

Blocking findings: **4**
Nonblocking findings: **0**

Reviewer: fresh independent S02 r2 reviewer; not the S02 implementer.
Review date: 2026-08-25.
Reviewed tree: VCVio commit `c5d6cb03d11126e6290bec58ef8824f36fc3a73b` on branch
`codex/sphincsplus-formalization`, plus the remediated uncommitted S02 worktree.

Independence and write-scope statement: I read r1 for its counterexamples and dispositions, then
independently inspected every current S02 Lean declaration and both current S02 documents against
the pinned EasyCrypt sources. Read-only commands and a `/tmp` Lean probe were the only actions before
this verdict. This file is my only repository edit. I did not change the Lean implementation,
`HashSig.lean`, either S02 design/session document, the accepted S00/S01 infrastructure or harness,
or the rejected legacy `HashSig/SLHDSA/Security.lean`.

## Decision summary

R2 contains substantial and useful remediation. `signingITSRHistory` now derives `(R, request)`
records from signing answers and rejects explicit `Hmsg` entries. `ParameterConditions` contains the
exact `lgw = 2 ∨ 4 ∨ 8` hypothesis. Target families have positive exact `Fin` cardinalities and
injective tweaks. The target provider has an exact erased honest-transcript marginal. Raw component
probability fields are gone; SKG/MKG use genuine VCVio PRF real/ideal experiments; TCR/DSPR/PRE
success outputs are recomputed in challenger-owned attempts; and the RHS retains the correct role
order, coefficients, and absence of birthday or budget slack.

The new experiment layer nevertheless fails primary-source correspondence in three independent
places. The ITSR summand is an event in the original PRFmsg-based EUF transcript, not the standalone
ITSR reduction game after the random-function hop. The FORS `SPprob` experiment discards the DSPR
reduction's chosen index and samples a uniform index instead. The WOTS UD real oracle returns the
hidden preimage, while the source returns a function output, and the Lean event omits the source
game's query-count, distinctness, and collection-separation checks.

The target-provider repair also introduces a hidden vacuity. It demands collection separation as a
certificate for every role and every exact-marginal adversary outcome, although the public interface
allows arbitrary hash queries at any `Adrs` and the master antecedent imposes no separation
condition. An overlapping public query therefore prevents a certified outcome instead of making the
relevant component event false. Binary construction/adversary origin tags also do not establish the
claimed subconstruction provenance: the current definitions make FORS-F and every WOTS-F role
definitionally indistinguishable, and likewise FORS-H and XMSS-H.

These are semantic defects in the proposed statement, not missing proofs of a correct set of games.
S02 remains unaccepted.

## Blocking findings

### S02-R2-001 — the ITSR summand is not the authoritative ITSR reduction experiment

The local ITSR predicate and history are repaired. The then-current definition takes `R` from `.sign`
answers, `Transcript.lean:68-72` excludes explicit `.hmsg` entries, and
`TranscriptITSRBreak` uses that signing history at `Transcript.lean:123-128`.

The quantitative term is different. `itsrComponentProbability` at
`HashSig/SLHDSA/Security/Architecture.lean:523-529` evaluates `TranscriptITSRBreak` directly over
`honestTranscriptDistribution`. That distribution signs with the actual `prims.PRFmsg` at
`Transcript.lean:135-146`. `componentTerm .hmsgItsr` ignores `ReductionSystem` and reduces
definitionally to this original-transcript event (`Architecture.lean:548`). The focused probe
compiled that equality by `rfl`.

The pinned third term is instead
`MCO_ITSR.ITSR(R_ITSR_EUFCMA(...A), O_ITSR_Default)` at
`/home/alh/SPHINCS/FV-SPHINCSPLUS-EC/proofs/SPHINCS_PLUS.ec:4347`. The ITSR challenger samples a
fresh key, records `(key,input)`, and returns it at
`proofs/KeyedHashFunctions.eca:1486-1505`. The concrete reduction's signing oracle obtains its
message key from `O.query(m)` at `proofs/FORS_ES.ec:2188-2212`. This occurs after the MKG
random-function hop represented separately by the preceding PRF advantage.

Therefore the current RHS term still uses pseudorandom signing randomizers from the attacked scheme
rather than ITSR-challenger keys. It has no ITSR reduction program, ITSR oracle, or hybrid
distribution. A correct architecture needs a role-specific ITSR adversary constructed from `A` and
interpreted by the challenger, or an explicitly modeled ideal-PRF transcript plus a proved
equivalence to that standalone game. The “ITSR advantage” and “concrete ... ITSR ... experiment”
claims at `docs/slhdsa/security-architecture.md:31-48` and
`docs/slhdsa/sessions/S02-security-architecture.md:48-49` currently overstate the type.

### S02-R2-002 — FORS `SPprob` does not run the same DSPR reduction or use its selected target

`dsprComponentProbability` correctly runs `system.forsFDspr adversary`, obtaining the reduction's
selected index and guess (`Architecture.lean:433-447`). But `forsFSPprobability` at
`Architecture.lean:449-466` has no reduction-program argument. It samples a uniform
`Fin targetCount` index at lines 458-466 and tests second-preimage existence there. The focused
`#check` confirms that its complete signature ends with only `adversary` and `provider`.

The authoritative baseline is not uniform target selection. `SM_DT_SPprob` runs the same adversary's
`pick` and `guess`, receives `(i,b)`, retrieves target `i`, and ignores only `b` before testing
second-preimage existence at
`/home/alh/SPHINCS/FV-SPHINCSPLUS-EC/proofs/TweakableHashFunctions.eca:402-426`. The DSPR game runs
the same interaction and uses the same adversary-selected `i` at lines 429-454. The master theorem
then subtracts those two probabilities for the identical named reduction at
`SPHINCS_PLUS.ec:4349-4352`.

“Challenger-defined” means that the challenger defines the SP-existence event; it does not mean that
the challenger replaces the reduction's target selection with a uniform index. The current
`Pr[DSPR(program)] - Pr[SPprob(uniform)]` is not the sourced term. Pass
`system.forsFDspr adversary` to both experiments, run the same public-view interaction independently
in each world, and have the baseline ignore only the returned guess.

### S02-R2-003 — the WOTS UD experiment reveals target preimages and omits the sourced validity event

`TargetPublicView` itself omits target inputs, but the real UD handler immediately re-exposes them:

```lean
example (targets : CertifiedTargetPackage prims conditions sample .wotsFUd)
    (i : Fin (positiveTargetCount p conditions .wotsFUd).value) :
    wotsUDRealImpl targets i = pure (targets.family.target i).input := rfl
```

This compiled independently and follows directly from `Architecture.lean:485-490`. The ideal world
returns a cached uniform `prims.Y` per index at lines 506-520. Consequently the two worlds compare
“honest preimage versus random value,” not “hash of a fresh input versus random output.” This also
contradicts the information-flow claim at `security-architecture.md:52-54` and session lines 50-52:
the reduction can learn every hidden preimage merely by querying its real oracle.

The authoritative SM-DT-UD oracle never returns `x`. In the real branch it samples `x` and returns
`f pp tw x`; in the ideal branch it samples an output, at
`/home/alh/SPHINCS/FV-SPHINCSPLUS-EC/proofs/TweakableHashFunctions.eca:483-507`. The game also records
queried tweaks and accepts only when the number of target queries is bounded and the tweaks are
distinct (`TweakableHashFunctions.eca:523-542`). The collection version additionally checks
disjointness from collection-oracle queries at lines 844-870.

The Lean reduction program can repeat an index or make unbounded target-oracle queries; neither
`wotsUDRealProbability` nor `wotsUDIdealProbability` logs or checks those queries. Injectivity of the
preloaded family does not constrain the program's query trace. A correct UD-C interface must keep
inputs hidden, return the recomputed `F` output in the real world and a uniform output in the ideal
world, and make the count/distinctness/collection conditions part of the experiment event. The same
oracle program should then be interpreted in both worlds, as the current code already attempts.

### S02-R2-004 — provider certification is vacuous for overlapping public queries and does not identify subconstruction roles

The marginal field itself is strong and correctly ties
`CertifiedHonestOutcome.sample <$> distribution A` to the exact
`honestTranscriptDistribution ... A` (`Architecture.lean:352-362`). The problem lies in what every
value of that distribution must certify.

`CertifiedTargetPackage.collectionSeparated` requires every target tweak to be absent from all
adversary-origin `F/H/Tl` queries in the same log (`Architecture.lean:247-254`). This certificate is
required for every target role in every `CertifiedHonestOutcome` at lines 256-260. Yet
`AdversaryQuery` accepts an arbitrary `Adrs` for each public primitive (`OracleSurface.lean:112-118`),
and `AdversaryBounds` imposes only a numeric pathwise bound, not address separation
(`OracleSurface.lean:195-209`). An adversary may therefore issue a bounded query at a construction
target address.

For such an honest outcome, an exact construction target family containing that address cannot
satisfy `collectionSeparated`. Because the provider marginal may not drop or replace that outcome,
the required provider cannot exist. This is not how the source collection games handle overlap:
disjointness is part of the component game's success event, so overlap makes that event false
(`TweakableHashFunctions.eca:742-745,866-870`); it does not make the target distribution impossible.
The problem is even stronger for non-collection roles such as FORS `F`, for which the current package
imposes separation although the authoritative term is plain SM-DT-TCR/DSPR.

The binary origin tag also leaves the advertised role provenance underdetermined. These independent
compiled equalities are both `Iff.rfl`:

```lean
TargetObserved sample .forsF target ↔ TargetObserved sample .wotsFUd target
TargetObserved sample .forsH target ↔ TargetObserved sample .xmssH target
```

All four WOTS/FORS `F` roles accept the same `.f .construction` entry, and the two `H` roles accept
the same `.h .construction` entry (`Architecture.lean:191-235`). `Fin` size and address injectivity do
not show that an index denotes the formula-prescribed FORS leaf, WOTS chain position, or XMSS node.
The provider can choose certificates conditionally after seeing the sample; its erased marginal says
nothing about a canonical role/coordinate extraction.

The candid non-claim at `security-architecture.md:108-111,166-176` is preferable to asserting a
provider inhabitant, but “refine the signing event” alone cannot repair this interface. The current
honest log has no construction entries at all, key generation is outside the logging handler, and
collection overlap remains possible after trace refinement. Use role/coordinate-indexed construction
events or a canonical extraction theorem, and move collection disjointness into precisely the `-C`
experiment events unless the public query type itself enforces a proved disjoint address namespace.

## R1 disposition

| r1 finding | r2 disposition |
| --- | --- |
| S02-R1-001 | **Local history fixed.** Signing entries supply `(R,request)` and explicit Hmsg entries are excluded. R2-001 is a separate quantitative-game mismatch. |
| S02-R1-002 | **Partially fixed.** Raw scalars were removed and PRF/TCR/PRE program types are meaningful, but ITSR, SPprob, and UD do not match the authoritative experiments (R2-001 through R2-003). |
| S02-R1-003 | **Not fully fixed.** Exact sizes, injective tweaks, observation, and the erased marginal are real improvements; provider separation/provenance still admits vacuity and role substitution (R2-004). |
| S02-R1-004 | **Fixed.** `lgw_approved` exactly requires 2, 4, or 8; the compiled `lgw_ne_one` theorem closes the counterexample. |

## Gates that passed

- Authority: `/home/alh/SPHINCS/FV-SPHINCSPLUS-EC` remains exactly commit
  `a28e4c53897a4bb57b575a177225862d48f824b7`; the repaired report is the 34-page, 745834-byte
  `SPHINCS_EC.pdf`.
- RHS syntax: roles and coefficients at `Architecture.lean:603-615` match
  `SPHINCS_PLUS.ec:4338-4370`: two PRF terms, ITSR, truncated DSPR minus SPprob, `3*FORS-F-TCR`,
  the two remaining FORS terms, `(w-2)*WOTS-F-UD-C`, the three remaining WOTS terms, and XMSS-H.
  No birthday or additive `qS`/`qH` term occurs.
- Formula evaluation: the eight target counts at `slhdsaSha2_128_24` remain
  `422212465065984`, `422212439900160`, `4194304`, `285212672`, `1140850688`,
  `285212672`, `4194304`, and `4194303`, agreeing with the pinned formulas.
- Positivity and roles: exact index types are nonempty; the role cards evaluate to `6`, `12`, and
  `8`; the rejected loss regression proves `256 < 17*(17+0)`.
- PRF surfaces: SKG has key `SkSeed`, domain `PkSeed × Adrs`, and evaluation
  `PRF pkSeed skSeed address`; MKG/PRFmsg has key `SkPrf`, domain
  `Y × List Byte`, and evaluation `PRFmsg skPrf optionalRandomness message`. Real and ideal terms run
  the same named PRF oracle program and use an absolute ENNReal difference.
- Public/internal separation and current seed coupling remain intact. Query-origin tagging prevents a
  public query from masquerading syntactically as `.construction`; the finer provenance defect is
  recorded in R2-004.
- TCR/DSPR/PRE attempts select an inhabited exact index, keep target inputs in the challenger, and
  recompute outputs under the generated public seed. FORS/WOTS `Tl` inputs retain separate `k` and
  `len` vector types.
- `SigningBound` and `HashQueryBound` remain structural `IsQueryBoundP` predicates on the actual
  adversary program, with compiled zero-budget regressions and no numeric RHS loss.
- The architecture remains explicitly classical. `QROMClaim` has no constructor, and no QROM theorem
  or cast was found.
- The S02 modules contain no new `sorry`, `axiom`, `unsafe`, `extern`, `partial`, initializer,
  implementation override, or linter suppression. The eleven `noncomputable` definitions are
  probability/ENNReal experiment evaluations, not admissions.
- The rejected legacy file remains untouched. Its warning is still visible, and neither current S02
  document claims its findings globally closed.

The explicit request encoder remains a disclosed future API boundary. As in r1, the current EUF
probability is exact only relative to that supplied encoder; this is not counted as a new finding.

## Independent command and axiom evidence

```text
git status --short --branch; git rev-parse HEAD; git diff -- HashSig.lean
  PASS: branch/commit and allowed S02 scope confirmed; generated imports are the same four modules.

git -C /home/alh/SPHINCS/FV-SPHINCSPLUS-EC rev-parse HEAD
sed -n '4338,4370p' .../proofs/SPHINCS_PLUS.ec
nl/rg over KeyedHashFunctions.eca, TweakableHashFunctions.eca, FORS_ES.ec, and current S02 sources
  PASS: source pin and the exact ITSR, SPprob/DSPR, UD/UD-C, role, coefficient, and count boundaries
        independently inspected.

lake build HashSig
  PASS: 2748 jobs; only the pre-existing rejected
        HashSig/SLHDSA/Security.lean:150 sorry warning was replayed.

lake env lean /tmp/S02R2Probe.lean
  PASS: r1 positive regressions, all role/count evaluations, the role-equivalence counterexamples,
        WOTS preimage-return equality, ITSR/system-independence equality, and API signatures compiled.
```

The focused probe ran `#print axioms` on the lgw and signing-ITSR regressions; target observation,
public-view erasure, all exact attempt predicates, both PRF schemes, certified component runner,
SPprob, both UD worlds, ITSR probability, `componentTerm`, `eufAdvantage`, `repairedRHS`,
`RepairedMasterStatement`, all role-card/count/nonemptiness/loss theorems, and budget independence.
Every declaration was axiom-free or depended only on the accepted `propext`, `Classical.choice`, and
`Quot.sound`; no `sorryAx` or other axiom occurred.

Source-token scans and `git diff --check` passed. No accepted S00/S01 file changed.

## Final decision

Final verdict: **FAIL with four blocking findings**. R2 closes the narrow lgw and signing-history
counterexamples and materially improves the type surface, but the RHS experiments and provider
boundary still do not enforce the pinned theorem. Re-review should wait for a standalone/hybrid-correct
ITSR game, same-program DSPR/SPprob experiments, a non-leaking validity-checked WOTS UD-C game, and a
nonvacuous role-precise honest target provider.
