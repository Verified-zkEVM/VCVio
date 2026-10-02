#!/usr/bin/env bash
# Dry-run the migration of open pull requests onto the current commit.
#
# usage: scripts/migration-dry-run.sh --worktree DIR --out DIR PR...
#
# DIR is a worktree of this repository with a built `.lake` (a copy of this checkout's
# `.lake/build`, with `.lake/packages` linked), so that a build only recompiles what a pull request
# touches. For each pull request the script
#
#   1. resets DIR to the current commit and fetches the pull request's head;
#   2. merges it, preferring the pull request's side of a conflicting hunk, keeps the files this
#      branch deleted deleted, and keeps this branch's toolchain, manifest, lakefile and baselines;
#   3. regenerates the umbrella modules;
#   4. runs `scripts/migrate-native-probability.py` over the pull request's Lean files, recording
#      its diff and the sites it leaves to finish by hand;
#   5. builds the modules of those files.
#
# OUT/pr-N/ receives the merge record, the codemod's output, the build log and the lists of files
# the pull request touched and the ones this branch also touched since `main`, which tell an error
# of the migration from an error of the automatic merge. `scripts/classify-migration-errors.py OUT`
# turns the logs into OUT/migration-dry-run.csv and OUT/summary.md. Each result is committed in DIR
# on the local branch `dryrun/pr-N`; nothing is pushed.
set -euo pipefail

usage() {
  echo "usage: $0 --worktree DIR --out DIR PR..." >&2
  exit 2
}

worktree=""
out=""
prs=()
while [ "$#" -gt 0 ]; do
  case "$1" in
    --worktree) worktree="$2"; shift 2 ;;
    --out) out="$2"; shift 2 ;;
    -h|--help) usage ;;
    *) prs+=("$1"); shift ;;
  esac
done
[ -n "$worktree" ] && [ -n "$out" ] && [ "${#prs[@]}" -gt 0 ] || usage
[ -d "$worktree/.lake/build" ] || { echo "$worktree has no built .lake" >&2; exit 2; }

repo="$(git rev-parse --show-toplevel)"
base="$(git -C "$repo" rev-parse HEAD)"
git -C "$repo" fetch -q origin main
main_base="$(git -C "$repo" merge-base origin/main "$base")"
# Files this branch changed since it left `main`: an error in a file both sides touched may come
# from the automatic merge rather than from the migration.
ours_changed="$(git -C "$repo" diff --name-only "$main_base" "$base")"
kept=(lean-toolchain lake-manifest.json lakefile.lean scripts/axiom_baseline.json
  scripts/nolints.json scripts/init_sweep_baseline.json scripts/expose_boundary_baseline.tsv
  scripts/spec_coverage_baseline.json scripts/lifted_law_parity_baseline.json)
library_roots='^(ToMathlib|VCVio|VCVioCslib|LatticeCrypto|HashSig|Examples|Extern|VCVioWidgets|VCVioTest|LatticeCryptoTest|HashSigTest)/'

mkdir -p "$out"
for pr in "${prs[@]}"; do
  dir="$out/pr-$pr"
  rm -rf "$dir"
  mkdir -p "$dir"
  echo "== pr $pr: $(date +%T)"

  # Outside `refs/heads/dryrun/`, so the result branch `dryrun/pr-N` stays an unambiguous name.
  git -C "$repo" fetch -q -f origin "pull/$pr/head:refs/dryrun-heads/pr-$pr"
  head="$(git -C "$repo" rev-parse "refs/dryrun-heads/pr-$pr")"
  pr_base="$(git -C "$repo" merge-base origin/main "$head")"
  git -C "$repo" diff --name-only --diff-filter=d "$pr_base" "$head" > "$dir/pr-files.txt"
  grep -Fxf <(printf '%s\n' "$ours_changed") "$dir/pr-files.txt" > "$dir/shared-files.txt" || true
  printf 'base %s\nhead %s\npr-base %s\n' "$base" "$head" "$pr_base" > "$dir/commits.txt"

  git -C "$worktree" merge --abort > /dev/null 2>&1 || true
  git -C "$worktree" reset -q --hard "$base"
  git -C "$worktree" clean -qfd
  git -C "$worktree" merge --no-commit --no-ff -X theirs "$head" > "$dir/merge.txt" 2>&1 || true
  # What `-X theirs` cannot settle: a file one side deleted, or added on both sides.
  git -C "$worktree" status --porcelain | grep -E '^(DD|AU|UD|UA|DU|AA|UU) ' > "$dir/unmerged.txt" || true
  while read -r code path; do
    case "$code" in
      DU|DD) git -C "$worktree" rm -q -- "$path" ;;
      UD) git -C "$worktree" add -- "$path" ;;
      *)
        if git -C "$worktree" cat-file -e ":3:$path" 2> /dev/null; then
          git -C "$worktree" show ":3:$path" > "$worktree/$path"
        fi
        git -C "$worktree" add -- "$path"
        ;;
    esac
  done < "$dir/unmerged.txt"
  for path in "${kept[@]}"; do
    if git -C "$repo" cat-file -e "$base:$path" 2> /dev/null; then
      git -C "$repo" show "$base:$path" > "$worktree/$path"
    fi
  done
  (cd "$worktree" && ./scripts/update-lib.sh > "$dir/update-lib.txt" 2>&1) || true

  lean_files=()
  while read -r path; do
    case "$path" in
      *.lean) [ -f "$worktree/$path" ] && lean_files+=("$path") ;;
    esac
  done < "$dir/pr-files.txt"
  if [ "${#lean_files[@]}" -gt 0 ]; then
    (cd "$worktree" && python3 scripts/migrate-native-probability.py --dry-run "${lean_files[@]}" \
      > "$dir/codemod.diff" 2> "$dir/codemod-sites.txt") || true
    (cd "$worktree" && python3 scripts/migrate-native-probability.py "${lean_files[@]}" \
      > /dev/null 2> "$dir/codemod.txt") || true
  fi

  modules=()
  for path in "${lean_files[@]}"; do
    if [[ "$path" =~ $library_roots ]]; then
      module="${path%.lean}"
      modules+=("${module//\//.}")
    fi
  done
  printf '%s\n' "${modules[@]}" > "$dir/modules.txt"
  if [ "${#modules[@]}" -gt 0 ]; then
    (cd "$worktree" && nice -n 19 lake build "${modules[@]}" > "$dir/build.log" 2>&1) \
      && echo "ok" > "$dir/status.txt" || echo "failed" > "$dir/status.txt"
  else
    echo "no modules" > "$dir/status.txt"
  fi

  git -C "$worktree" add -A
  git -C "$worktree" commit -q --no-verify \
    -m "Migration dry run of #$pr onto $(git -C "$repo" rev-parse --short "$base")" \
    -m "Automatic: merge preferring #$pr's side of conflicting hunks, this branch's toolchain, manifest, lakefile and baselines, regenerated umbrellas, and the probability codemod over the pull request's Lean files. Build: $(cat "$dir/status.txt")." \
    || true
  git -C "$worktree" branch -q -f "dryrun/pr-$pr" HEAD
  errors="$(grep -c '^error: .*\.lean:' "$dir/build.log" 2> /dev/null || true)"
  echo "   $(cat "$dir/status.txt"); ${errors:-0} errors"
done
