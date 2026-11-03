# Uniform FORS load primitives

The laws give tail bound `1/(8·2^128)` at cap `9·2^99` and fixed-first-view symmetry.
Source (185 lines) and closed ordinary-import text audit (44 lines) are accepted bytes.
No exported security-bound claim; signer/coverage/byte/seed/fill obligations remain open.

Replay after committing this archive, using immutable b63 and its 12 normal libraries.
The manifest pins packet/review and the 221-module closure. Two scoped
`exponentiation.threshold 1024` annotations remain; other proof limits/linters stay unchanged.

```bash
set -euo pipefail
export GIT_OPTIONAL_LOCKS=0 LEAN_NUM_THREADS=2
research=$(git rev-parse --show-toplevel)
base=/tmp/vcvio-slhdsa-integration
compiler=/home/alh/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean
evidence="$research/docs/design/slh-dsa-coverage-primitives-evidence"
out=$(mktemp -d /tmp/slhdsa-coverage-primitives-replay.XXXXXX)
recorded_head=$(git -C "$research" rev-parse HEAD)
check_evidence() { python3 - "$research" "$base" "$evidence" "$recorded_head" "$out" "$1" "$compiler" <<'PYCODE'
from pathlib import Path
import hashlib, json, subprocess, sys
r,b,e=map(Path,sys.argv[1:4]); head,out,stage=sys.argv[4],Path(sys.argv[5]),sys.argv[6]
sha=lambda v:hashlib.sha256(v).hexdigest()
git=lambda p,*args:subprocess.check_output(['git','-C',str(p),*args])
m=json.loads((e/'manifest.json').read_text())
def frame(p):
    assert not git(p,'status','--porcelain')
    return {'head':git(p,'rev-parse','HEAD').decode().strip(),'index':sha(git(p,'ls-files','-s','-z'))}
f={'research':frame(r),'canonical':frame(b),'sourceGitBlobs':{},'deps':{}}
compiler=Path(sys.argv[7]); assert str(compiler)==m['compilerExecutable']['path']
f['compiler']={'path':str(compiler),'sha256':sha(compiler.read_bytes())}
assert f['compiler']==m['compilerExecutable']
f['stdRoots']={str(p):sha(p.read_bytes()) for p in sorted((compiler.parent.parent/'lib/lean').glob('Std.*')) if p.is_file()}
assert len(f['stdRoots'])==6 and f['stdRoots']==m['stdRootSha256']
assert f['research']['head']==head and f['canonical']['head']==m['canonicalBase']
assert sha((b/'lake-manifest.json').read_bytes())==m['lakeManifestSha256']
assert (b/'lean-toolchain').read_text().strip()==m['toolchain']
for path in sorted(e.iterdir()):
    rel=str(path.relative_to(r)); blob=git(r,'show',head+':'+rel)
    assert sha(path.read_bytes())==sha(blob)
    if path.name in m['sourceFiles']: assert sha(blob)==m['sourceFiles'][path.name]['sha256']
    f['sourceGitBlobs'][rel]=git(r,'rev-parse',head+':'+rel).decode().strip()
assert len(m['dependencyRevisions'])==12
for name,rev in m['dependencyRevisions'].items():
    f['deps'][name]=frame(b/'.lake/packages'/name); assert f['deps'][name]['head']==rev
c=Path(m['sourceClosureEvidence']['path']); assert sha(c.read_bytes())==m['sourceClosureEvidence']['sha256']
for name,pin in json.loads(c.read_text())['canonicalModules'].items():
    rel=name.replace('.','/'); assert sha((b/(rel+'.lean')).read_bytes())==pin['sourceSHA256']
    assert sha((b/'.lake/build/lib/lean'/(rel+'.olean')).read_bytes())==pin['oleanSHA256']
(out/(stage+'.json')).write_text(json.dumps(f,sort_keys=True,indent=2)+'\n')
PYCODE
}
check_evidence before
cp "$evidence/RouteBPrimitives.lean" "$out/RouteBPrimitives.lean"
cp "$evidence/ImportAudit.lean.txt" "$out/ImportAudit.lean"
export LEAN_PATH="$out:$base/.lake/build/lib/lean"
for lib in "$base"/.lake/packages/*/.lake/build/lib/lean; do LEAN_PATH="$LEAN_PATH:$lib"; done
args=(-j2 -DautoImplicit=false -DrelaxedAutoImplicit=false
  -Dweak.linter.mathlibStandardSet=true -Dweak.linter.redundantVisibility=true "--root=$out")
"$compiler" --version > "$out/compiler.txt"
for unit in RouteBPrimitives ImportAudit; do
  timeout 240 "$compiler" "${args[@]}" -o "$out/$unit.olean" "$out/$unit.lean" > "$out/$unit.log" 2>&1
  printf '0\n' > "$out/$unit.exit"
done
check_evidence after
cmp "$out/before.json" "$out/after.json"
sha256sum "$out"/*.lean "$out"/*.log "$out"/*.olean > "$out/source-log-output-sha256.txt"
```

Require both exits zero, no warnings and four roots using only `propext`,
`Classical.choice`, `Quot.sound`. Retain the recorded clean commit, source Git blobs,
12 actual pins, pinned compiler/six Std roots, closure and source/log/NEW-output joins.
