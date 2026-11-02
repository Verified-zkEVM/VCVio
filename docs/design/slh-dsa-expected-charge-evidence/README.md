# Expected terminal charge

The exact generic theorem proves `Pr[bad_final] + Phi_initial <= E[Phi_final]`
from existing `IsPotentialStep` and an initially good state. It needs neither
bad-predicate persistence nor finite potential, an invariant or a query budget.
A direct finite-program induction uses one private monotonicity helper; it does
not infer an expectation from a truncated-CDF bound or cancel infinite terms.

This research archive preserves the accepted 126-line source byte-for-byte.
Its theorem uses only `propext`, `Classical.choice` and `Quot.sound` (including
the private helper transitively). The manifest pins the original fresh proof,
independent review, frozen header and dependency revisions. No SLH result,
stopped-handler corollary, relative-kernel bridge or full127 claim is made.

## Replay at the reviewed archive commit

Use the pinned, already-built immutable canonical checkout; all outputs are external.
Set RECORDED_HEAD to the full reviewed research commit containing this archive.

```bash
set -euo pipefail
export GIT_OPTIONAL_LOCKS=0 LEAN_NUM_THREADS=4
research=$(git rev-parse --show-toplevel)
artifact=/tmp/vcvio-slhdsa-integration
evidence="$research/docs/design/slh-dsa-expected-charge-evidence"
recorded_head="${RECORDED_HEAD:?set the full reviewed research commit}"
out=$(mktemp -d /tmp/slhdsa-expected-charge-replay.XXXXXX)
context() {
python3 - "$research" "$artifact" "$evidence" "$recorded_head" <<'PYCONTEXT'
from pathlib import Path
import hashlib, json, subprocess, sys
r, a, e = map(Path, sys.argv[1:4]); expected = sys.argv[4]
git = lambda root,*args: subprocess.check_output(['git','-C',str(root),*args])
sha = lambda data: hashlib.sha256(data).hexdigest()
m = json.loads((e/'manifest.json').read_text())
assert len(expected)==40 and git(r,'rev-parse','HEAD').decode().strip()==expected
assert git(a,'rev-parse','HEAD').decode().strip()==m['canonicalBase']
assert not git(r,'status','--porcelain') and not git(a,'status','--porcelain')
assert sha((e/m['sourceFile']).read_bytes())==m['sourceSha256']
assert sha(git(r,'show',expected+':docs/design/slh-dsa-expected-charge-evidence/ExpectedCharge.lean'))==m['sourceSha256']
assert sha((a/'lake-manifest.json').read_bytes())==m['lakeManifestSha256']
assert (a/'lean-toolchain').read_text().strip()==m['toolchain']
pins = {}
for name,rev in m['dependencyRevisions'].items():
    root=a/'.lake/packages'/name
    assert git(root,'rev-parse','HEAD').decode().strip()==rev
    assert not git(root,'status','--porcelain'); pins[name]=rev
print(json.dumps({'researchHead':expected,'researchTree':git(r,'rev-parse','HEAD^{tree}').decode().strip(),
 'canonicalHead':m['canonicalBase'],'sourceSha256':m['sourceSha256'],'dependencies':pins,
 'manifestSha256':sha((e/'manifest.json').read_bytes()),
 'researchIndexSha256':sha(git(r,'ls-files','--stage','-z')),
 'canonicalIndexSha256':sha(git(a,'ls-files','--stage','-z'))},sort_keys=True))
PYCONTEXT
}
context > "$out/before.json"
lean --version > "$out/compiler-version.txt"
export LEAN_PATH="$out:$artifact/.lake/build/lib/lean"
for lib in "$artifact"/.lake/packages/*/.lake/build/lib/lean; do LEAN_PATH="$LEAN_PATH:$lib"; done
lean -j4 -DautoImplicit=false -DrelaxedAutoImplicit=false \
  -Dweak.linter.mathlibStandardSet=true -Dweak.linter.redundantVisibility=true \
  "--root=$evidence" -o "$out/ExpectedCharge.olean" "$evidence/ExpectedCharge.lean" > "$out/check.log" 2>&1
context > "$out/after.json"
cmp "$out/before.json" "$out/after.json"
cat "$out/check.log"
```

Require compiler exit zero, no warnings/errors and exactly the stated axiom root
with only the three allowed names. Retain the context files, raw log and output
hashes. Reuse only the pinned existing library artifacts; do not run a cache fetch,
Lake build, native execution or any source-changing command as part of this replay.
