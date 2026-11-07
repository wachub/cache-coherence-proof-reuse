#!/usr/bin/env bash
set -euo pipefail

repo_name="${1:-cache-coherence-proof-reuse}"
if [[ "$repo_name" == *'/'* ]]; then
  echo 'Pass a GitHub repository NAME only, not owner/name. gh uses your authenticated account.' >&2
  exit 2
fi
if [[ ! "$repo_name" =~ ^[A-Za-z0-9_.-]+$ ]]; then
  echo 'Invalid repository name.' >&2
  exit 2
fi

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"

command -v git >/dev/null || { echo 'Install git first.' >&2; exit 1; }
command -v gh >/dev/null || { echo 'Install GitHub CLI (gh) first.' >&2; exit 1; }
gh auth status >/dev/null || { echo 'Run: gh auth login' >&2; exit 1; }

if [[ -n "$(git status --porcelain)" ]]; then
  echo 'Working tree is not clean. Review and commit/discard local changes before publishing.' >&2
  git status --short
  exit 1
fi
if [[ "$(git branch --show-current)" != 'main' ]]; then
  echo 'Switch to the packaged main branch before first publish: git switch main' >&2
  exit 1
fi
if git remote get-url origin >/dev/null 2>&1; then
  echo 'An origin remote already exists. Refusing to create or overwrite anything.' >&2
  git remote -v
  exit 1
fi

owner="$(gh api user --jq '.login')"
echo "About to create PRIVATE GitHub repository: ${owner}/${repo_name}"
echo 'It will receive main, historical experiment branches, and Git tags.'
read -r -p 'Type PUBLISH to continue: ' confirmation
[[ "$confirmation" == 'PUBLISH' ]] || { echo 'Cancelled.'; exit 1; }

gh repo create "${owner}/${repo_name}" --private --source=. --remote=origin --push

# Preserve significant experiments as separate remote branches.
for branch in \
  'experiment/hierarchical-cache-width-v2.1' \
  'feature/mesi-moesi-composable' \
  'proof/minimized-invariant-progress-v1.9'; do
  if git show-ref --verify --quiet "refs/heads/${branch}"; then
    git push -u origin "$branch"
  fi
done
git push origin --tags

echo
printf 'Repository: https://github.com/%s/%s\n' "$owner" "$repo_name"
echo 'Note: the GitHub repository was created PRIVATE.'
