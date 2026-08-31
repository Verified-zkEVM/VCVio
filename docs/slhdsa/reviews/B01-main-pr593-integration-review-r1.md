# B01 upstream architecture and parameter boundary integration review r1

Verdict: **PASS**

Date: 2026-08-31  
Reviewer: independent successor reviewer (not the integration implementer or r0 reviewer)  
Reviewed candidate: `1f3cfa89882af79755e87d90659edd7150186416`  
Candidate tree: `aca02cc3fab97a5f72d3c41e695116aa3f6d1c72`  
Required parent / immutable r0 FAIL artifact: `1fc92ddabdf045c8108a1fd00f250de497e0da7d`  
Parent tree: `c6bcf2882c5614b4bd63580808de189f01d9301c`  
Integration parent of r0: `ef750c13f085a343637a05bbad91b25dc04a469c`

## Scope and repository state

I read `AGENTS.md`, the independent review protocol, the complete B01 session record, the active B01
plan handoff, and `B01-main-pr593-integration-review-r0.md`. I reviewed the r0 findings from their
evidence and the repair diff, not from the repair commit message. The worktree was clean at review
start. Both required ancestry checks succeeded, and the repair changes exactly these three paths:

- `scripts/slhdsa/check-harness.py`;
- `docs/slhdsa/plan.md`; and
- `docs/slhdsa/sessions/B01-upstream-boundary-integration.md`.

`git diff --check` passed. The immutable r0 artifact remains blob
`4672c4a87d37f093c458264001542e13aad6e7e5` in both parent and candidate, with SHA-256
`bf8c4ef881ed93bc8e0c650853a568d566983dd8394956bbddc3b0d84ebe02b4`.

## B01-R0-001 closure: version-pinned parser trace validation

The repair closes the blocking finding without weakening parser ownership checks.

The checker admits exactly two Lean identities as direct structured trace keys: Lean 4.32.2 commit
`f3b06c705e6c85f5314019d5d3baab0fec5b580c` and Lean 4.33.1 commit
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`. It requires one such identity with a 16-lowercase-hex
trace token. For 4.32.2 it selects one top-level `linkObjs` array. For 4.33.1 it selects one exact
`HashSigTest.SLHDSA.ACVP.ParserTests:linkInfo` group and one direct nested
`Module.moreLinkObjs` array. It does not recurse, match substrings or suffixes, or search arbitrary
groups. Mixed identities, duplicate outer groups, and duplicate nested groups are rejected.

The selected array must contain unique, well-formed records whose path set is exactly the three
frozen ACVP export objects plus the four specifically permitted native stub libraries. Every module
source path and frozen source SHA-256, module identity, generated-C token, export-object token, and
executable-link token remains cross-bound. Thus an unrelated object, missing/duplicate object, or
dependency substitution is rejected rather than merely ignored.

Per-module grammar is likewise version-specific. Lean 4.33.1 uses one top-level `deps` group and
requires exactly `o/m/i/c/rs/r` when `m = true` (including the `.ir.sig` grammar and the public,
server, and private `.olean` outputs); Lean 4.32.2 retains the exact
`<module>:deps -> deps -> imports` path and its legacy output grammar. Both paths require exactly the
two named direct-import artifacts for each intended parser edge. Cached trace inspection
independently exhibited the legacy top-level executable `linkObjs` layout and current top-level
module `deps` plus `rs`/`r` layout.

I loaded the checker without invoking its main entry point and ran reviewer-owned fixtures from
`/tmp/b01_trace_probe.py`. The probe passed two positive link-layout fixtures, two positive
dependency-layout fixtures, a full legacy validator projection using the real cached trace
inventory, and fourteen negative structural fixtures. The negatives covered a mixed/duplicate or
wrong-pinned identity, duplicate outer/nested groups, substring keys, recursive placement,
unrelated groups, ambiguous current/legacy dependency groups, and recursive dependency placement.

The authoritative wrapper then performed a genuinely fresh no-cache 4.33.1 parser build. Its log
showed the three ACVP modules and C export objects, the exact four native stub archives, and the
parser executable. The fresh trace validator and its 234-case mutation partition passed, followed
by the parser positive 16/16, negative 52/52, and combined runtime 68/68 gates. This is direct
evidence that the repaired checker accepts the actual 4.33.1 nested link schema while retaining the
intended target/module/dependency boundary.

## B01-R0-002 closure: PR #595 ownership

Both active handoff statements now reserve exact PR #595 head
`be823fbb6745e95412efe2bf49e0e46055953413` across **S07--S09**: S07 owns digest splitting and FORS
addressing; S08/S09 own typed hypertree positions. They continue to prohibit S05 duplication.

The PR head is not an ancestor of the candidate. Relative to its PR #593 base, its two commits add
the unmerged `HashSig/SLHDSA/Position.lean` and `HashSigTest/SLHDSA/Position.lean` payload and related
imports/tests; both files are absent here, and searches found no candidate `DigestParts` or PR #595
position import. The integration therefore retains PR #593 as intended but neither merges nor
duplicates PR #595.

## Commands and gate evidence

Representative review commands, all run from the repository root:

```text
git status --short --untracked-files=all
git show -s --format='%H %P %T %s' 1f3cfa89882af79755e87d90659edd7150186416
git merge-base --is-ancestor ef750c13f085a343637a05bbad91b25dc04a469c 1fc92ddabdf045c8108a1fd00f250de497e0da7d
git merge-base --is-ancestor 1fc92ddabdf045c8108a1fd00f250de497e0da7d 1f3cfa89882af79755e87d90659edd7150186416
git diff --name-status 1fc92ddabdf045c8108a1fd00f250de497e0da7d..1f3cfa89882af79755e87d90659edd7150186416
git diff --check 1fc92ddabdf045c8108a1fd00f250de497e0da7d..1f3cfa89882af79755e87d90659edd7150186416
git ls-tree 1fc92ddabdf045c8108a1fd00f250de497e0da7d docs/slhdsa/reviews/B01-main-pr593-integration-review-r0.md
git ls-tree 1f3cfa89882af79755e87d90659edd7150186416 docs/slhdsa/reviews/B01-main-pr593-integration-review-r0.md
sha256sum docs/slhdsa/reviews/B01-main-pr593-integration-review-r0.md
lean --version
lake --version
jq '{inputs,outputs}' .lake/build/bin/slhdsa_acvp_parser.trace
jq '{inputs,outputs}' .lake/build/lib/lean/HashSigTest/SLHDSA/ACVP/ParserTests.trace
python3 -B /tmp/b01_trace_probe.py
git merge-base --is-ancestor be823fbb6745e95412efe2bf49e0e46055953413 HEAD  # exit 1
git diff --name-status 0caf09ca831ba0686db549b596ddfeb121de69ac..be823fbb6745e95412efe2bf49e0e46055953413
rg -n -i 'PR #595|be823fbb|DigestParts|Position.*S0[789]|S0[789].*Position' docs/slhdsa HashSig HashSigTest
./scripts/slhdsa/validate.sh
```

Installed versions were Lean 4.33.1 at the exact pinned commit and Lake 5.0.0. The full wrapper was
run once and exited zero with `SLH-DSA full baseline validation: PASS`. In addition to the fresh
parser evidence above, it passed the harness/provenance checks, all relevant builds, S03/S04
declaration and axiom probes, the exact five-helper PolicyAudit over 2,561 HashSig-owned constants
with transitive axiom union exactly `propext`, `Classical.choice`, and `Quot.sound`, the SHA2/C13
KATs, S03 codecs, and S04 primitive/vector tests. Expected warnings described absent optional native
submodules and policy-fixture/upstream `sorry` locations; no gate failed and no HashSig `sorryAx` was
admitted.

## Findings and verdict

Blocking findings: **0**.  
Nonblocking findings: **0**.

Both r0 findings are fixed with direct evidence, the repair remains within its declared scope, and
all authoritative gates pass. **B01 review r1: PASS.** This verdict reviews only the exact candidate
above; it does not merge PR #595, start S05, or authorize any unreviewed descendant.
