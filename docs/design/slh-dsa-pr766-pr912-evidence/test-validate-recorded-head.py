#!/usr/bin/env python3
"""Exercise validation identity and cleanliness gates in isolated temporary repositories."""
from pathlib import Path
import json, os, subprocess, sys, tempfile
helper = Path(__file__).with_name('validate-recorded-head.py').resolve()

def git(root, *args):
    return subprocess.check_output(['git', '-C', str(root), *args], text=True, stderr=subprocess.DEVNULL).strip()
with tempfile.TemporaryDirectory(prefix='slhdsa-validation-gate-fixtures-') as td:
    base = Path(td)
    fakebin = base / 'bin'
    fakebin.mkdir()
    lake = fakebin / 'lake'
    lake.write_text('#!/usr/bin/env python3\nprint("Lean (version 4.35.0, fixture)")\n')
    lake.chmod(493)
    env = os.environ.copy()
    env['PATH'] = str(fakebin) + os.pathsep + env['PATH']

    def setup(label):
        root = base / label
        root.mkdir()
        git(root, 'init', '-q')
        git(root, 'config', 'user.name', 'Validation Fixture')
        git(root, 'config', 'user.email', 'fixture@example.invalid')
        dep = root / '.lake/packages/PolyFun'
        dep.mkdir(parents=True)
        git(dep, 'init', '-q')
        git(dep, 'config', 'user.name', 'Validation Fixture')
        git(dep, 'config', 'user.email', 'fixture@example.invalid')
        (dep / 'Source.lean').write_text('-- dependency\n')
        git(dep, 'add', '.')
        git(dep, 'commit', '-qm', 'fixture dependency')
        rev = git(dep, 'rev-parse', 'HEAD')
        (root / '.gitignore').write_text('.lake/\n')
        (root / 'Generated.lean').write_text('-- generated imports\n')
        (root / 'lean-toolchain').write_text('leanprover/lean4:v4.35.0\n')
        (root / 'lake-manifest.json').write_text(json.dumps({'packagesDir': '.lake/packages', 'packages': [{'type': 'git', 'name': 'PolyFun', 'rev': rev}]}))
        git(root, 'add', '.')
        git(root, 'commit', '-qm', 'fixture source')
        return (root, dep)

    def run(label, setup_change=None, body='pass', want=0, version_change=None, error=None):
        root, dep = setup(label)
        if setup_change:
            setup_change(root, dep)
        report = base / (label + '-report')
        run_env = env.copy()
        if version_change:
            invocation, mutation = version_change
            counter = base / (label + '-version-calls')
            run_env['FIXTURE_VERSION_COUNTER'] = str(counter)
            lake.write_text(
                '#!/usr/bin/env python3\n'
                'from pathlib import Path\n'
                'import os, subprocess\n'
                'counter = Path(os.environ["FIXTURE_VERSION_COUNTER"])\n'
                'invocation = int(counter.read_text()) + 1 if counter.exists() else 1\n'
                'counter.write_text(str(invocation))\n'
                f'if invocation == {invocation}:\n'
                + ''.join('    ' + line + '\n' for line in mutation.splitlines())
                + 'print("Lean (version 4.35.0, fixture)")\n'
            )
        r = subprocess.run([sys.executable, str(helper), '--report-dir', str(report), '--', sys.executable, '-c', body], cwd=root, env=run_env, text=True, capture_output=True)
        assert r.returncode == want, (label, r.stdout, r.stderr)
        rec = json.loads((report / 'validation.json').read_text())
        assert rec['status'] == ('passed' if want == 0 else 'failed')
        if error:
            assert error in rec.get('error', ''), (label, rec)
        if version_change:
            assert counter.read_text() == str(invocation), (label, counter.read_text())
            assert ('commandExitCode' in rec) == (invocation == 2), (label, rec)
        if want == 0:
            assert rec['before'] == rec['after'] and rec['before']['dependencyRevisions']['PolyFun'] == git(dep, 'rev-parse', 'HEAD')
        print(label + ': PASS')
    run('clean')
    run('ignored-build-output', body="from pathlib import Path; Path('.lake/build').mkdir(); Path('.lake/build/output').write_text('artifact')")
    run('dirty-tracked-before', lambda r, d: (r / 'Generated.lean').write_text('-- dirty\n'), want=1)

    def stage(r, d):
        (r / 'Generated.lean').write_text('-- staged\n')
        git(r, 'add', 'Generated.lean')
    run('dirty-index-before', stage, want=1)
    run('untracked-before', lambda r, d: (r / 'New.lean').write_text('-- untracked\n'), want=1)
    run('generated-import-mutation-after', body="from pathlib import Path; import subprocess; Path('Generated.lean').write_text('-- regenerated imports\\n'); subprocess.run(['git','diff','--check'],check=True)", want=1)
    run('untracked-after', body="from pathlib import Path; Path('New.lean').write_text('-- untracked\\n')", want=1)
    run('head-changed-with-clean-tree', body="import subprocess; subprocess.run(['git','commit','--allow-empty','-qm','changed head'],check=True)", want=1)

    def mismatch(r, d):
        (d / 'Source.lean').write_text('-- different dependency\n')
        git(d, 'add', '.')
        git(d, 'commit', '-qm', 'wrong revision')
    run('dependency-lock-mismatch', mismatch, want=1)
    run('dirty-dependency-before', lambda r, d: (d / 'Source.lean').write_text('-- dirty dependency\n'), want=1)
    run('dirty-dependency-after', body="from pathlib import Path; Path('.lake/packages/PolyFun/Source.lean').write_text('-- dirty dependency\\n')", want=1)
    run('command-failed', body='raise SystemExit(7)', want=1)
    lake.write_text('#!/usr/bin/env python3\nprint("Lean (version 4.36.0, fixture)")\n')
    run('wrong-active-lean', want=1)
    version_mutations = {
        'tracked-source-mutation': (
            "Path('Generated.lean').write_text('-- dirty during version query\\n')",
            'source tree is dirty',
        ),
        'clean-source-commit': (
            "Path('Generated.lean').write_text('-- committed during version query\\n')\n"
            "subprocess.run(['git', 'add', 'Generated.lean'], check=True)\n"
            "subprocess.run(['git', 'commit', '-qm', 'version source mutation'], check=True)",
            'inputs changed during Lean version query',
        ),
        'dirty-dependency': (
            "Path('.lake/packages/PolyFun/Source.lean').write_text('-- dirty dependency\\n')",
            'dependency source tree is dirty',
        ),
        'clean-dependency-commit': (
            "dep = '.lake/packages/PolyFun'\n"
            "Path(dep, 'Source.lean').write_text('-- committed dependency mutation\\n')\n"
            "subprocess.run(['git', '-C', dep, 'add', '.'], check=True)\n"
            "subprocess.run(['git', '-C', dep, 'commit', '-qm', 'version dependency mutation'], check=True)",
            'dependency revision differs from lock',
        ),
        'clean-manifest-commit': (
            "Path('lake-manifest.json').write_text(Path('lake-manifest.json').read_text() + '\\n')\n"
            "subprocess.run(['git', 'add', 'lake-manifest.json'], check=True)\n"
            "subprocess.run(['git', 'commit', '-qm', 'version manifest mutation'], check=True)",
            'inputs changed during Lean version query',
        ),
        'clean-toolchain-commit': (
            "Path('lean-toolchain').write_text('leanprover/lean4:v4.36.0\\n')\n"
            "subprocess.run(['git', 'add', 'lean-toolchain'], check=True)\n"
            "subprocess.run(['git', 'commit', '-qm', 'version toolchain mutation'], check=True)",
            'inputs changed during Lean version query',
        ),
    }
    for invocation, phase in [(1, 'initial'), (2, 'final')]:
        for name, (mutation, error) in version_mutations.items():
            run(f'{phase}-version-{name}', want=1,
                version_change=(invocation, mutation), error=error)
print('25 validation-gate fixtures: PASS')
