# Start here — ChatGPT Desktop / Work and GitHub

This is a complete local Git repository, including `.git/` history, not a source-only snapshot.

## A. Start a local project

1. Extract the repository archive into a durable workspace directory (not a temporary Downloads extraction). Open that directory with ChatGPT Desktop's available local-file or Work workflow, or with your editor/Codex terminal.
2. If using a ChatGPT **Project**, create one named **Proof-Carrying Cache Verification**, upload `CHATGPT_PROJECT_INSTRUCTIONS.md` as a reference file, and paste its text into the Project's instructions if custom instructions are supported. Also attach `docs/PROOF_STATUS.md` and `HIERARCHICAL_COHERENCE_v2_1.md` for easy context. A ChatGPT Project is not itself a Git checkout; code edits/pushes require working in the local repository or a connected development environment.
3. For the initial conversation, paste the contents of `PROJECT_FIRST_MESSAGE.md`.
4. Check `git status` and `git log --oneline -5`. This export starts on `main`. The historical v2.0/v2.1 and v1.9 branches and tags are retained.

## B. Publish to a NEW GitHub repository (PRIVATE by default)

On the computer that holds the extracted repo, install Git and the GitHub CLI (`gh`), then:

```bash
cd /path/to/cache-proof-evolution-desktop
# Authenticate once; choose your GitHub account and preferred browser/SSH flow.
gh auth login

# Creates a NEW PRIVATE repo named cache-coherence-proof-reuse,
# pushes main and all preserved local historical branches and tags:
bash scripts/publish_github.sh cache-coherence-proof-reuse
```

If you prefer a different repo name, pass it as the argument. The script refuses to overwrite an existing origin and refuses to publish with uncommitted changes. It does not require putting an access token in source code.

After creation:

```bash
git remote -v
git branch -a
git log --oneline --decorate -5
```

Future changes:

```bash
git switch -c research/semantic-proof-reuse
git add -A
git commit -m "Experiment: semantic reuse for MSI-to-MESI"
git push -u origin research/semantic-proof-reuse
```

To share the new GitHub URL with ChatGPT, paste the `https://github.com/<account>/<repo>` URL. If the GitHub connector is available, ChatGPT can inspect the remote repository, but local filesystem changes still need a Git push to appear remotely.

## C. What *not* to claim

- Do not say the repository proves full concrete temporal liveness or complete SC refinement.
- Do not say v2.1 has verified asynchronous interlevel messages; it uses atomic service steps.
- Do not say proof certificates transfer semantically across MSI→MESI: that algorithm remains to be developed.
- The reported counts are historical recorded checks and should be rerun before making new claims.

## D. Project file map

- `AGENTS.md` — instructions for coding/verification agents.
- `CHATGPT_PROJECT_INSTRUCTIONS.md` — paste into ChatGPT Project instructions.
- `PROJECT_FIRST_MESSAGE.md` — initial message for a new desktop chat.
- `docs/RESEARCH_ROADMAP.md` — focused paper hypothesis and benchmark plan.
- `docs/PROOF_STATUS.md` — precise evidence and limitations by milestone.
- `HIERARCHICAL_COHERENCE_v2_1.md` — latest configuration and solver checks.
- `MESI_MOESI_EXTENSION_v2_0.md` — asynchronous protocol variant work.
- `scripts/publish_github.sh` — private GitHub repository creation and push.
