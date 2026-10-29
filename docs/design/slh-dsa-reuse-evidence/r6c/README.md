# Finite reuse completion evidence

The [completion manifest](../../slh-dsa-reuse-completion-manifest.md) fixes five
extraction/use families and six canonical delegation units. Its 52 named source
anchors are a change-impact inventory, not permanent intermediate APIs. A unit
states its proposed security/functional claims, relevant maps and actual consumers,
and documents retained, strengthened, replaced or retired intermediates. Independent
review checks the implementation and evidence that each required end security
guarantee remains available or is dominated over its original scope. Search
existing owners before adding generic mechanisms. This evidence list is not
implementation acceptance.

- [source-map.json](source-map.json) binds the finite 52 source locations and six
  delegation units. First-line headers are location anchors, not full contracts.
- [target-shapes.md](target-shapes.md) states quantified requirements for future
  contracts; it contains no new Lean declarations or claimed proofs.
- [proof-route-map.json](proof-route-map.json) and
  [proof-route-notes.md](proof-route-notes.md) distinguish shared mechanisms from
  complementary specialized quantitative arguments.
- [provenance.json](provenance.json) binds historical inventories to accepted
  implementation source and separately reviewed documentation candidates.
- [p6-checkpoint.json](p6-checkpoint.json) records the exact implementation head,
  validation/source/log hashes, active Lean/manifest/all 11pins and gate scope.

The source-map, proof-route and provenance artifacts remain byte-exact historical inventories:
their original author base ed014 plus held D candidate is not rewritten into a
later history. All 43 selected source anchors independently match accepted ae235.
All 52 listed names are absent from RAW1242; that archive does not claim complete
coverage of those intermediates. Historical documentation hashes describe their
recorded versions, not later revisions of this guidance. Use the captures as
comparison evidence and review deliberate guard/API changes rather than requiring
identical internal proof values, owners or ASTs. The
[R0 archive](../r0/README.md) and [R0b bindings](../r0b/README.md) remain unchanged.

The root full command and independent P6 acceptance at ae235 passed. This closes
the structural/effectful P6 gate only; full P5, broad migration and R6c/R8 remain
open. The checkpoint records the independent receipt hash.
The gate ran 37 executable actions plus the CSV checker and R0b tail: 39 non-build
driver actions. CSV has 18 rows; R0b checked 40 equations / 11 groups / 77 contracts and
invoked R0a's 1242 records / 509-name boundary once. Counts are distinct. Inherited
baselines remained 215 lint entries, 6 sorry-tainted declarations, 0 nonstandard-axiom
taint, and 6 proof-root plus 2 test-root flagged initializers. These are whole-gate
baseline counts, not new P6 debt.

## Reproduction discipline

Use an owned build environment at the recorded committed head and exact lock.
Use the pinned installed Lean/Lake/Python tools and ordinary owned Lake caches;
the repository's [cache policy](../../../../AGENTS.md) relies on normal source/import
content-hash invalidation. Routine builds and prototyping do not require recursive
Python cache/import-path or whole-Lean-reader custody audits, or per-compile
permission. Keep one builder per writable cache. Record actual tool/source/lock
identities and relevant test/provider inputs; do not claim hostile-host or full
supply-chain certification. Preserve historical audit failures honestly.

Before an accepted semantic commit, independently review its actual patch, retained
or improved end guarantees and meaningful ordinary consumers. Run appropriate
targeted builds, axiom/signature checks and runtime/negative controls. Negative
tests need successful setup, correct shadow/provider selection and the intended
genuine failure; timeout/import/build/cleanup errors are not a passing control.
An explicitly identified dirty trial patch may supply precommit evidence; it does
not establish clean recorded-head acceptance.

Prepare cache/import generation before validation; commit any generated changes.
Immediately before the final command record clean head/tree/index/source and all
11 clean dependency revisions, plus the full Lean version/commit and manifest
hash. Run `/usr/bin/time -v ./scripts/validate.sh --lint --test --axioms` with
`LEAN_NUM_THREADS=4`. Do not regenerate imports, edit source, repin dependencies,
or share a writable project cache during that command. Require exit0 and exactly
identical clean head/tree/index/source/dependency snapshots afterward. The
ordinary `lake test` tail already invokes R0b/R0a once; do not add a duplicate R0
chain. Retain logs and independent review bound to those snapshots. A whitespace
check alone does not establish validation of the recorded commit.
