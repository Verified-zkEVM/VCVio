#!/usr/bin/env bash
# Make room for Lean on disposable GitHub-hosted Linux runners.
set -euo pipefail

if [[ "${GITHUB_ACTIONS:-}" != "true" ||
      "${RUNNER_ENVIRONMENT:-}" != "github-hosted" || "${RUNNER_OS:-}" != "Linux" ]]; then
  echo "SDK cleanup requires GitHub-hosted Linux environment flags." >&2
  exit 1
fi

# These preinstalled SDKs are unused by the Lean and Linux native-backend builds.
# Keep repository sources, build caches and host C/C++ compiler/Python/Rust toolchains intact.
df -h /
sudo rm -rf -- /usr/share/dotnet /usr/local/lib/android
df -h /
