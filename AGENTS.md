# Agent Instructions

Read `.agents/rules/project-summary.md` before changing code.

## Project Roots

- The main Lean project is `projects/LCS`. Run `lake` commands there, not at repo root.
- The toolchain is pinned to `leanprover/lean4:v4.28.0` in `projects/LCS`, `projects/docs_LCS`, and `projects/LCS/docbuild`.
- `projects/docs_LCS` is a separate Verso docs project.
- `projects/LCS/docbuild` is a separate `doc-gen4` project used only for API docs.

## Verified Commands

- Full library build: `lake build` from `projects/LCS`
- Single-module check: `lake build LCS.WinningCondition` from `projects/LCS`
- The umbrella target is `LCS` via `projects/LCS/LCS.lean`; it imports the strategy modules, `WinningCondition`, and `Games/MagicSquare`.

## Code Layout

- Core types live in `projects/LCS/LCS/Basic.lean` (`LCSLayout`, `Assignment`, `LCSGame`).
- The two strategy formalisms are split between `LCS/Strategy/ObservableStrategy.lean` and `LCS/Strategy/ProjectorStrategy.lean`.
- The bridge from observable strategies to projector strategies is in `LCS/Strategy/Equivalence.lean`.
- The concrete example is `LCS/Games/MagicSquare.lean`.

## Docs Flow

- Manual docs live in `projects/docs_LCS`; `MainManual.lean` is the manual entrypoint and includes `DocsLCS/*.lean`.
- Build the manual with `lake exe generate-docs` from `projects/docs_LCS`.
- The docs project points examples at `../LCS` via `set_option verso.exampleProject "../LCS"`; if library code changes, verify the library build before debugging docs output.
- Root `update-docs.sh` is the full docs pipeline. It is interactive and does more than one thing: builds manual HTML, optionally builds literate output from `projects/LCS`, optionally builds `doc-gen4` output from `projects/LCS/docbuild`, runs `postprocess_docs/.venv/bin/python3 main.py`, compiles `typst/status.typ`, and copies artifacts into `docs/`.

## Gotchas

- Prefer focused `lake build <Module>` checks for Lean changes; the docs pipeline is much heavier and interactive.
- `projects/LCS/lakefile.toml` enables `weak.linter.mathlibStandardSet = true`. `lake build` currently succeeds with existing linter warnings, so warnings alone are not a regression.
- Treat `docs/` and generated doc outputs as build artifacts unless the task is explicitly about documentation generation or published HTML.
