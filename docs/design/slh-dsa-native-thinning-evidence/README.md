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

`prEvent_roleRun_pair_firedAtActualKey_le` proves, for `first < second`,
`Pr[reached second ∧ fired first ∧ fired second] ≤ |Y|⁻² Pr[reached first]`.
It uses the same native experiment and hypotheses. One watch's pointwise decrease
pays for the other's expected step; when both share a fresh nonce cell, distinct
actual-key slots require distinct randomizers, so their singleton outcomes are
disjoint. The proof does not multiply expectation bounds or assume independence.
The four pair modules import the existing thin1 support without copying it.

This is research evidence outside active libraries. The four unchanged thin1
sources contain 1,001 physical Lean lines and the four pair sources add 463;
the archive totals 1,464 lines including proofs, comments, whitespace and checks.
All sources are byte-identical to their accepted external proofs. The 34 original
printed axiom roots and nine pair roots use only `propext`, `Classical.choice` and
`Quot.sound`; the accepted replays had no warnings. The manifest retains the
original thin1 hashes and pins both accepted packets and independent reviews.
There is no production or LOC saving claim.

Causality is not yet included in this archive unit. Occupation/adaptive coverage,
same-measure actual-joint budget transport, byte/weak-seed assembly and the full
`q / 2^127` endpoint remain open. This archive neither replaces the existing
security proof nor establishes independence of proof methods.

## Replay

Use an immutable, already built checkout at the manifest's `baseCommit` (`b63fede7…`)
and the recorded twelve clean dependency revisions; no cache download or build is needed.
Run from the clean research checkout after committing this archive. Record that
actual commit at replay time; the accepted external packets record their earlier
research heads. All new outputs go to one fresh `/tmp` directory placed first.

```bash
set -euo pipefail
export GIT_OPTIONAL_LOCKS=0 LEAN_NUM_THREADS=4
research=$(git rev-parse --show-toplevel)
artifact=/tmp/vcvio-slhdsa-integration
evidence="$research/docs/design/slh-dsa-native-thinning-evidence"
out=$(mktemp -d /tmp/slhdsa-native-thinning-replay.XXXXXX)
recorded_head=$(git -C "$research" rev-parse HEAD)
printf '%s\n' "$recorded_head" > "$out/research-head.txt"
sha256sum "$evidence/manifest.json" > "$out/manifest-sha256.txt"
check_evidence() {
  test -z "$(git -C "$research" status --porcelain)"
  test -z "$(git -C "$artifact" status --porcelain)"
  test "$(git -C "$research" rev-parse HEAD)" = "$recorded_head"
  test "$(git -C "$artifact" rev-parse HEAD)" = b63fede77cfcf9e23fda94c28e951e4520fdeb91
  python3 - "$evidence" "$artifact" <<'PYCHECK'
from pathlib import Path
import hashlib, json, subprocess, sys
source, base = map(Path, sys.argv[1:])
m = json.loads((source / 'manifest.json').read_text())
assert hashlib.sha256((base / 'lake-manifest.json').read_bytes()).hexdigest() == m['lakeManifestSha256']
assert (base / 'lean-toolchain').read_text().strip() == m['toolchain']
for name, entry in m['sourceFiles'].items():
    assert hashlib.sha256((source / name).read_bytes()).hexdigest() == entry['sha256']
assert len(m['dependencyRevisions']) == 12
for name, rev in m['dependencyRevisions'].items():
    root = base / '.lake/packages' / name
    assert subprocess.check_output(['git','-C',str(root),'rev-parse','HEAD']).decode().strip() == rev
    assert not subprocess.check_output(['git','-C',str(root),'status','--porcelain'])
PYCHECK
}
check_evidence
export LEAN_PATH="$out:$artifact/.lake/build/lib/lean"
for lib in "$artifact"/.lake/packages/*/.lake/build/lib/lean; do
  LEAN_PATH="$LEAN_PATH:$lib"
done
args=(-DautoImplicit=false -DrelaxedAutoImplicit=false
  -Dweak.linter.mathlibStandardSet=true -Dweak.linter.redundantVisibility=true
  "--root=$evidence")
lean -j4 "${args[@]}" -o "$out/Thin1Header.olean" "$evidence/Thin1Header.lean"
lean -j4 "${args[@]}" -o "$out/NativePotential.olean" "$evidence/NativePotential.lean"
lean -j4 "${args[@]}" -o "$out/NativeSuffix.olean" "$evidence/NativeSuffix.lean"
lean -j4 "${args[@]}" -o "$out/NativeThin1.olean" "$evidence/NativeThin1.lean"
lean -j4 "${args[@]}" -o "$out/PairHeader.olean" "$evidence/PairHeader.lean"
lean -j4 "${args[@]}" -o "$out/PairPotential.olean" "$evidence/PairPotential.lean"
lean -j4 "${args[@]}" -o "$out/PairRun.olean" "$evidence/PairRun.lean"
lean -j4 "${args[@]}" -o "$out/NativeThin2.olean" "$evidence/NativeThin2.lean"
check_evidence
```

Require every exit zero, no warnings, and every printed axiom within the stated
three-name set. Keep the actual research HEAD, manifest hash and recorded twelve
dependency revisions with the replay result. Default proof limits apply.
