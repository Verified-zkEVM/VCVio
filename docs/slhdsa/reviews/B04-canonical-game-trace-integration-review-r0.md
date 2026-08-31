# B04 canonical-game and construction-trace integration review r0

Date: 2026-08-31

Verdict: **PASS**

Blocking findings: **0**

Nonblocking findings: **0**

## Reviewed boundary

- candidate: `ea3e3a0baa2f4e3b6aaf323f65ba6a3eccbfd170`
- candidate tree: `fa88f6cd9f22e929aa0d2d112757b207f244fa98`
- candidate parent: `92a4c63ea920b80cd057b2b902f1125a1203973e`
- immutable-review restore tree: `80b6554c4ee7295d2beef83992001efedf62d92a`
- integration merge: `aca369d1050fdaa0f70389db94bb2d341eac6772`
- integration merge tree: `c6b3bd84ec88abf543cdb52d815196bcafa2b906`
- merge first parent, accepted B03 review:
  `e6ad65272816dfe78e0f2f5e6a0dccf5f3032cd1`
- merge second parent, exact shared head:
  `c149dc23d2545aa4afab2705c7247af4608021ad`

The worktree was clean at review start. The graph contains the exact normal two-parent merge, the
bounded immutable-artifact restoration, and the final documentation/inventory adaptation in that
order. The merge's sole textual conflict was `scripts/slhdsa/PolicyAudit.lean`.

## Merge and immutability review

All remote-owned generic-game, SLH-DSA adapter, test, aggregate-import, and workflow files in the
candidate are byte-identical to exact shared head `c149dc23...`. The candidate-versus-remote delta
is explained entirely by the newer accepted local B02/B03 construction, probes, sessions, reviews,
and their B04 documentation adaptation; no Quang game, trace, address, concrete, or test hunk was
dropped or rewritten.

The shared head had whitespace-normalized the immutable S00 r5 review from blob
`aede719995060c1bf38659ffc74f44a821612678` to
`2946e1fa2b8d1356538324f58b8ec243816933cc`. Commit `92a4c63e...` restores the exact predecessor
blob `aede7199...`. Comparing accepted B03 review head to the B04 candidate under
`docs/slhdsa/reviews` changes only the active `README.md`; every S00--B03 review artifact, including
B03 r0/r1/r2, is byte-identical.

The PolicyAudit resolution equals the incoming `c149dc23...` file and preserves exactly seventeen
unique `(generated _unsafe_rec helper, safe parent)` pairs. It retains exact observed-set equality,
Lean's generated-name/parent relation, common HashSig module ownership, partial-but-kernel-safe
helper status, safe nonpartial parent status, and absence of extern, initializer, implemented-by,
axiom, and `sorryAx` surfaces. The conflict changed only ordering/line wrapping relative to the
accepted local file; it did not add a duplicate or weaken any validation predicate.

## Technical semantics

### Canonical generic games

The imported PR #594/#596 surface implements source-final-validity games with an exact sticky
monitor: target and collection queries are always answered and recorded, while the final condition
checks the target cap, target-tweak `Nodup`, and target/collection disjointness. The accompanying
tests discriminate cap overflow, duplicate targets, both clash orders, legal repeated
collection-only tweaks, response orientation, DSPR baseline subtraction, prefix truncation, and
ITSR pair freshness/subset behavior.

`CanonicalGames` is a thin and correctly typed instantiation:

- FORS `F` uses standalone DSPR and TCR; FORS `H`, FORS `T_l`, WOTS `F`, WOTS `T_l`, and XMSS `H`
  use the shared variable-arity `Thash` collection.
- Attacked input types fix arity exactly: one node for `F`, an ordered pair for `H`, a
  `Vector _ p.k` for FORS compression, and a `Vector _ p.len` for WOTS compression.
- Every tweak is `Primitives.AdrsKey`. The evaluation bridges reduce to the same
  `adrsToKey`-based `F`/`H`/`T_l` calls used by construction.
- WOTS UD-C uses explicit uniform input and ideal-output generators and exposes the symmetric
  absolute advantage; WOTS PRE embeds the full node space by the injective identity.
- `H_msg` ITSR samples the message randomizer as its key, retains public seed/root and full request
  in the input, and maps each digest to the exact semantic FORS target set. Freshness remains pair
  freshness, as required by the imported ITSR game.
- Formula target caps are carried into the problems without being mislabeled as exact
  message-dependent query counts.

`ReductionAdversaries` is only a structure of ten future transformations and its named advantage
projections. There is no inhabitant, reduction program, or master inequality in this module, and no
theorem equates the canonical problems with the older architecture experiments.

The new compressed-address inverse proves injectivity only under the exact one-byte layer/type,
eight-byte tree, and four-byte word bounds. The concrete SHA2 corollary requires both addresses to
be canonical and in the narrowed SHA2 domain, so the fail-closed zero key cannot prove a false
global injectivity claim. `EncodedTargetLedgerConditions` remains an explicit obligation rather
than an inferred consequence of `ValidatedParams`.

### Construction traces

`TraceTargets` forms the union of the six structural ledgers—FORS leaf/tree/root, WOTS steps/public
keys, and XMSS nodes—and maps it through the actual `CorePrimitives.adrsToKey`. Its
`IsQueryBound`-based predicate is pathwise over every oracle answer, not a single-run observation.
`H_msg` is admitted separately because it has no address.

The WOTS proofs follow the operational programs. Each chain step is indexed by a
`Fin (w - 1)` obtained from the checked interval; key generation covers all `w - 1` steps, signing
uses `chainStepsCore`, recovery uses the residual `w - 1 - chainStepsCore`, and only key generation
and recovery add the final WOTS public-key-compression query. The paired contracts reuse the
existing exact/message-dependent structural query bounds.

The deterministic `withLogging` theorem transports the pathwise predicate to each logged public
hash query for a supplied answer function. It does not splice these queries into the outer CMA
transcript. The active README, plan, specification, security architecture, session, coverage, and
obligation records consistently keep the following open:

- the selected proof's `CountingInterface` and an inhabitant of `ReductionAdversaries`;
- outer-CMA signing-log refinement and target-input pairing;
- FORS, XMSS, and hypertree program-level trace bridges;
- concrete encoded injectivity and nonempty distinct target batches;
- canonical-to-bespoke experiment equivalences;
- the repaired master inequality and the same-message SUF residual;
- callback parity, conformance, external codecs/APIs, and all component reductions.

No S07 construction or security completion is claimed.

## Scanner, inventory, and provenance

The scanner change qualifies only the generic `run_*` fallback: an identifier is rejected by that
fallback only when the full token is its unqualified leaf. Explicit dangerous leaves such as
`run_cmd`, `addDecl`, registration, initialization, runtime overrides, and `run_tac` remain rejected
even when qualified.

Independent adversarial calls to `policy_findings` produced:

```text
unqualified-custom: ['environment-mutation']
unqualified-elab: ['environment-mutation']
qualified-proof: []
root-qualified: []
qualified-danger: ['environment-mutation']
unqualified-danger: ['environment-mutation']
comment-string: []
```

Thus actual unqualified `run_custom`/`run_elab` commands remain rejected, qualified theorem names
such as `Foo.run_custom` and `WriterT.run_bind'` are accepted, and qualification does not hide the
explicit `run_cmd` surface. The committed fixture adds the same positive qualified-proof case while
retaining the existing negative command case.

The unchanged five-glob recipe produces exactly 45 manifest lines and independently reproduces:

```text
6ae29b5b4d7c96fb8b6189d42a01c26391ee8c27a5875c450567c8825a65050c  -
```

The three edited inventory files reproduce their exact harness pins:

```text
9016    c53c5e1d51cb7cff6bec4f7c4d7284790bb25aa11460ba796729791611e5de54  coverage.csv
121435  9ca06d827e2cb6910e08f33cd6c8e8f99aaafbceaa328714761e9904bf0632c9  declarations.jsonl
9273    5a9926eea73b1b56b518a6612d10556666b132e95580d63529ebb912f338b92b  proof-obligations.csv
```

DECL-135--DECL-140 describe only the encoded primitive bridge, the uninhabited reduction-interface
shape, three WOTS address/budget contracts, and the deterministic logged-query consequence. COV-006,
COV-022, PO-006, PO-008, and PO-026 remain provisional/partial/open as appropriate; no row upgrades
conditional infrastructure into a reduction or conformance result.

## Independent validation

```text
git diff --exit-code c149dc23..ea3e3a0b -- <all remote-owned game/test/source paths>
# no output

git diff --name-only e6ad6527..ea3e3a0b -- 'docs/slhdsa/reviews/*review*.md'
# no output

git diff --check e6ad6527..ea3e3a0b
# no output

lake build HashSig.SLHDSA.Security.CanonicalGames \
  HashSig.SLHDSA.Security.TraceTargets \
  VCVioTest.ITSR VCVioTest.SMDTDSPR VCVioTest.SMDTOpenPRE \
  VCVioTest.SMDTPREFinalValidity VCVioTest.SMDTTCRFinalValidity VCVioTest.SMDTUDC
Build completed successfully (2734 jobs).

lake env lean /tmp/B04ReviewProbe.lean
B04 review declaration/axiom probe: PASS (6 exact load-bearing roots)
```

The exact probe covered `wotsFPreCProblem_eval_adrsToKey`, `ReductionAdversaries`, all three WOTS
trace contracts, and `mem_logged_query_isConstructionReachable`; every root's exact axiom set was
`{propext, Classical.choice, Quot.sound}`.

The implementation handoff supplied two completed PASS runs of the full compiled PolicyAudit and
reported 46 HashSig modules, 3,612 owned constants, the exact seventeen-helper set, and the exact
standard axiom union. I started an additional independent replay. It emitted only the audit's
expected internal mutation-fixture `sorry` warnings and no production finding, but remained silent
for approximately twelve minutes; after a final poll it was interrupted rather than delaying this
proportionate review. This interrupted redundant replay is not reported as PASS. The independent
source-level conflict audit, exact helper-set inspection, successful focused elaboration, and exact
root probe found no trust regression.

Per the review direction, the long authoritative wrapper was not repeated. The candidate handoff's
reported wrapper/aggregate evidence was checked against the actual command surface, while this
review independently replayed the changed modules/tests, exact axiom roots, scanner adversaries,
source composite, matrix pins, merge/source identity, and immutable artifacts.

## Final assessment

The integration preserves the complete shared canonical-game and construction-trace delta, keeps
the trust policy exact, fixes the source scanner narrowly, and describes the new Lean surface at its
actual conditional strength. With zero blocking and zero nonblocking findings, exact candidate
`ea3e3a0baa2f4e3b6aaf323f65ba6a3eccbfd170` **PASSes** independent B04 review.
