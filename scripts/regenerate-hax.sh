#!/usr/bin/env bash
# Regenerate the Lean extractions of the hax examples with the hax CLI.
#
# Each example's Rust crate is `Interop/Hax/<Name>/`, next to the Lean file `Interop/Hax/<Name>.lean`
# that proves it correct, and extracts into the modules `Interop.Hax.<Name>.Extraction.*`. The
# extracted modules are committed, so building `Interop/` needs no Rust toolchain.
#
#   scripts/regenerate-hax.sh          regenerate in place
#   scripts/regenerate-hax.sh --check  extract into a temporary copy and fail if the committed
#                                      modules differ (CI's `hax-extraction` job)
#
# After extraction, each `Extraction/` directory keeps aeneas's `Types`, `Funs` and `Specs`
# modules. `ProofObligations.lean` holds `sorry` stubs for the contracts, which the proofs in
# `Interop/Hax/<Name>.lean` discharge instead, so it is removed. The `*_Template.lean` models of
# external definitions seed `FunsExternal.lean` and `TypesExternal.lean` when those are absent (none
# of the examples has external definitions) and are then removed.
#
# Requires `cargo-hax` at the hax release that `Interop/lakefile.toml` requires.
set -euo pipefail

root="$(git rev-parse --show-toplevel)"
cd "$root"

check=0
case "${1:-}" in
  --check) check=1 ;;
  "") ;;
  *) echo "usage: $0 [--check]" >&2; exit 2 ;;
esac

# The hax release `Interop/lakefile.toml` requires (the only full-commit `rev` there).
pin="$(sed -n 's/^rev = "\([0-9a-f]\{40\}\)"$/\1/p' Interop/lakefile.toml)"
if [[ -z "$pin" || "$(wc -l <<<"$pin")" -ne 1 ]]; then
  echo "regenerate-hax: cannot find the hax rev in Interop/lakefile.toml" >&2
  exit 1
fi
have="$(cargo hax --version 2>/dev/null | sed -n 's/^commit=\([0-9a-f]*\)$/\1/p')"
if [[ "$have" != "$pin" ]]; then
  echo "regenerate-hax: cargo-hax is at '${have:-none}', but Interop/lakefile.toml pins $pin." >&2
  echo "Install it with: cargo install --locked --git https://github.com/cryspen/hax --rev $pin cargo-hax" >&2
  exit 1
fi

# Extract every crate under `$1/Interop/Hax`, then tidy each `Extraction/` directory.
extract_all() {
  local base="$1" dir scenario ext
  for dir in "$base"/Interop/Hax/*/; do
    [[ -f "$dir/hax.toml" ]] || continue
    scenario="$(sed -n 's/^\[scenario\.\([a-z0-9-]*\)\]$/\1/p' "$dir/hax.toml")"
    ( cd "$dir" && cargo hax extract "$scenario" ) >/dev/null
    ext="$dir/Extraction"
    rm -f "$ext/ProofObligations.lean"
    for template in "$ext"/*_Template.lean; do
      [[ -e "$template" ]] || continue
      local target="${template%_Template.lean}.lean"
      [[ -e "$target" ]] || cp "$template" "$target"
      rm "$template"
    done
  done
}

if [[ "$check" -eq 0 ]]; then
  extract_all "$root"
  echo "regenerate-hax: regenerated Interop/Hax/*/Extraction"
  exit 0
fi

# `--check`: extract into a copy of the crates and their committed extractions, then compare.
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
mkdir -p "$tmp/Interop"
cp -R Interop/Hax "$tmp/Interop/Hax"
rm -rf "$tmp"/Interop/Hax/*/Extraction "$tmp"/Interop/Hax/*/proofs
# Seeded models of external definitions are hand-maintained once present: keep the committed ones.
for ext in Interop/Hax/*/Extraction; do
  mkdir -p "$tmp/$ext"
  for kept in "$ext"/FunsExternal.lean "$ext"/TypesExternal.lean; do
    [[ -e "$kept" ]] && cp "$kept" "$tmp/$kept"
  done
done
export CARGO_TARGET_DIR="${CARGO_TARGET_DIR:-$root/Interop/Hax/target}"
extract_all "$tmp"

status=0
for ext in "$tmp"/Interop/Hax/*/Extraction; do
  rel="${ext#"$tmp"/}"
  if ! diff -r "$rel" "$ext" >/dev/null 2>&1; then
    echo "regenerate-hax: $rel differs from a fresh extraction:" >&2
    diff -r "$rel" "$ext" >&2 || true
    status=1
  fi
done
if [[ "$status" -eq 0 ]]; then
  echo "regenerate-hax: committed extractions match a fresh extraction"
else
  echo "regenerate-hax: run scripts/regenerate-hax.sh and commit the result" >&2
fi
exit "$status"
