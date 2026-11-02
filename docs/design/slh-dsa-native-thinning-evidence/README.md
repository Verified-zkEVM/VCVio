# Native actual-key thinning

`prEvent_roleRun_firedAtActualKey_le` proves, for each index `i`,
`Pr[reached i ∧ fired at actual key i] ≤ |Y|⁻¹ Pr[reached i]`.
The exact reviewed statement uses the original adversary, the generated public key,
pure deterministic `kappa`, and arbitrary fixed tapes with `L.other = []`.
No budget, good-walk, signer-history or extra class assumption is added.

The potential banks reciprocal-cardinality credit before assignment and while the
one deterministic nonce cell is uncached; a hit has value one and a dead cell zero.
The native step bound uses a uniform fresh nonce draw and pre-cache hit semantics.
Existing expected-query-count composition, actual signing discipline, signer-role
keygen's zero forger counter, and finite-credit cancellation yield the statement.

This is research evidence, outside active libraries: 1,001 physical Lean lines,
including proofs, comments, whitespace and checks; no production or LOC saving claim.
The four copied sources are byte-identical to the accepted external proof.
The 34 printed axiom roots include the initial proposition definition; all use only
`propext`, `Classical.choice` and `Quot.sound`. The external replay had no warnings.
The manifest pins sources, base, dependencies, accepted evidence and independent review.

Pair thinning, overwrite causality, occupation/adaptive coverage, actual-joint
budget transport and the full `q / 2^127` endpoint remain open. This archive neither
replaces the existing security proof nor establishes independence of proof methods.

## Replay

Use an immutable, already built checkout at the manifest's `baseCommit` (`b63fede7…`)
and the recorded twelve clean dependency revisions; no cache download or build is needed.
Run from the clean research checkout after committing the archive. All outputs go to `/tmp`.

```bash
export GIT_OPTIONAL_LOCKS=0 LEAN_NUM_THREADS=4
research=$(git rev-parse --show-toplevel)
artifact=/tmp/vcvio-slhdsa-integration
evidence="$research/docs/design/slh-dsa-native-thinning-evidence"
out=$(mktemp -d /tmp/slhdsa-native-thinning-replay.XXXXXX)
test -z "$(git -C "$research" status --porcelain)"
test -z "$(git -C "$artifact" status --porcelain)"
test "$(git -C "$artifact" rev-parse HEAD)" = b63fede77cfcf9e23fda94c28e951e4520fdeb91
python3 - "$evidence" "$artifact" <<'PYCHECK'
from pathlib import Path
import hashlib, json, subprocess, sys
source, base = map(Path, sys.argv[1:])
m = json.loads((source / 'manifest.json').read_text())
for name, entry in m['sourceFiles'].items():
    assert hashlib.sha256((source / name).read_bytes()).hexdigest() == entry['sha256']
for name, rev in m['dependencyRevisions'].items():
    root = base / '.lake/packages' / name
    assert subprocess.check_output(['git','-C',str(root),'rev-parse','HEAD']).decode().strip() == rev
    assert not subprocess.check_output(['git','-C',str(root),'status','--porcelain'])
PYCHECK
export LEAN_PATH="$out:$artifact/.lake/build/lib/lean"
for lib in "$artifact"/.lake/packages/*/.lake/build/lib/lean; do
  LEAN_PATH="$LEAN_PATH:$lib"
done
args=(-j4 -DautoImplicit=false -DrelaxedAutoImplicit=false
  -Dweak.linter.mathlibStandardSet=true -Dweak.linter.redundantVisibility=true
  "--root=$evidence")
lean "${args[@]}" -o "$out/Thin1Header.olean" "$evidence/Thin1Header.lean"
lean "${args[@]}" -o "$out/NativePotential.olean" "$evidence/NativePotential.lean"
lean "${args[@]}" -o "$out/NativeSuffix.olean" "$evidence/NativeSuffix.lean"
lean "${args[@]}" -o "$out/NativeThin1.olean" "$evidence/NativeThin1.lean"
test -z "$(git -C "$research" status --porcelain)"
test -z "$(git -C "$artifact" status --porcelain)"
```

Require all four exits zero and all printed axioms within the stated three-name set.
Record the actual research HEAD, source/manifest hashes and dependency revisions;
repeat the dependency check afterward. The first LEAN_PATH directory must be fresh.
