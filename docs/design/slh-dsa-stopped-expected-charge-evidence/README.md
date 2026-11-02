# Independent stopping and expected potential charge

The existing charge certificate for hazard `P` survives freezing the handler at any
predicate `Q`. In that stopped run, `Pr[P(final)] + Φ(initial) ≤ E[Φ(final)]` from
an initially non-`P` state. Only `Q` needs the constructor's auxiliary decider;
no relation between predicates, initially-not-`Q`, persistence or finite-`Φ` premise.

The 64-line source and 44-line text audit are exact accepted bytes. The audit's two
private closed proofs recover `Q = P`; it is a non-module test, outside the active
API. There is no new guard, kernel, SLH/full127 result or production saving claim.

Replay needs built immutable b63 libraries and the manifest-pinned accepted
`CostTail`/`ExpectedCharge` artifacts at the paths below. They remain read-only.
Run after committing this archive; record the actual clean research commit.

```bash
set -euo pipefail
export GIT_OPTIONAL_LOCKS=0 LEAN_NUM_THREADS=2
research=$(git rev-parse --show-toplevel)
artifact=/tmp/vcvio-slhdsa-integration
evidence="$research/docs/design/slh-dsa-stopped-expected-charge-evidence"
cost_out=/tmp/slhdsa-joint-budget-prototype-20261102/packaged/out
charge_out=/tmp/slhdsa-expected-charge-pilot-20261102/final-checks-01/out
out=$(mktemp -d /tmp/slhdsa-generalized-stop-replay.XXXXXX)
recorded_head=$(git -C "$research" rev-parse HEAD)
printf '%s\n' "$recorded_head" > "$out/research-head.txt"
sha256sum "$evidence/manifest.json" > "$out/manifest-sha256.txt"
check_evidence() {
  test -z "$(git -C "$research" status --porcelain)"
  test -z "$(git -C "$artifact" status --porcelain)"
  test "$(git -C "$research" rev-parse HEAD)" = "$recorded_head"
  test "$(git -C "$artifact" rev-parse HEAD)" = b63fede77cfcf9e23fda94c28e951e4520fdeb91
  python3 - "$research" "$artifact" "$evidence/manifest.json" "$recorded_head" "$out" <<'PY'
from pathlib import Path
import hashlib, json, subprocess, sys
r, b, mf = map(Path, sys.argv[1:4]); head, out = sys.argv[4], Path(sys.argv[5])
m = json.loads(mf.read_text()); sha = lambda data: hashlib.sha256(data).hexdigest()
assert sha((b/'lake-manifest.json').read_bytes()) == m['lakeManifestSha256']
assert (b/'lean-toolchain').read_text().strip() == m['toolchain']
refs = {}
for rel, want in m['replaySourceSha256'].items():
    blob = subprocess.check_output(['git','-C',str(r),'show',head+':'+rel])
    assert sha((r/rel).read_bytes()) == sha(blob) == want
    refs[rel] = subprocess.check_output(['git','-C',str(r),'rev-parse',head+':'+rel]).decode().strip()
for entry in m['inheritedArtifacts']:
    assert sha(Path(entry['path']).read_bytes()) == entry['sha256']
assert len(m['dependencyRevisions']) == 12
for name, rev in m['dependencyRevisions'].items():
    pkg = b/'.lake/packages'/name
    assert subprocess.check_output(['git','-C',str(pkg),'rev-parse','HEAD']).decode().strip() == rev
    assert not subprocess.check_output(['git','-C',str(pkg),'status','--porcelain'])
(out/'source-gitblobs.json').write_text(json.dumps(refs, indent=2)+'\n')
PY
}
check_evidence
cp "$evidence/StoppedExpectedCharge.lean" "$out/StoppedExpectedCharge.lean"
cp "$evidence/ImportAudit03.lean.txt" "$out/ImportAudit03.lean"
cmp "$evidence/StoppedExpectedCharge.lean" "$out/StoppedExpectedCharge.lean"
cmp "$evidence/ImportAudit03.lean.txt" "$out/ImportAudit03.lean"
export LEAN_PATH="$out:$cost_out:$charge_out:$artifact/.lake/build/lib/lean"
for lib in "$artifact"/.lake/packages/*/.lake/build/lib/lean; do LEAN_PATH="$LEAN_PATH:$lib"; done
args=(-j2 -DautoImplicit=false -DrelaxedAutoImplicit=false
  -Dweak.linter.mathlibStandardSet=true -Dweak.linter.redundantVisibility=true "--root=$out")
lean "${args[@]}" -o "$out/StoppedExpectedCharge.olean" "$out/StoppedExpectedCharge.lean"
lean "${args[@]}" -o "$out/ImportAudit03.olean" "$out/ImportAudit03.lean"
check_evidence
```

Require both exits zero, no warnings, and all four printed roots within `propext`,
`Classical.choice`, `Quot.sound`. Default proof limits apply. Keep the recorded HEAD,
manifest/source Git-blob identities, artifact pins and before/after checks with the
replay result. Imported dependencies are not fresh proof checks in this replay.
