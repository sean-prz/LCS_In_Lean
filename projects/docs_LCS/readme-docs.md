Docs Plan

The manual now has a clearer structure, but the remaining work is to complete the later mathematical chapters so that the exposition matches the current library.

Current State

- `projects/docs_LCS/MainManual.lean`
  Builds the manual from `DocsLCS.Docs`.
- `projects/docs_LCS/DocsLCS/Docs.lean`
  Now acts as a compact homepage with a short summary, verified results, and links.
- `projects/docs_LCS/DocsLCS/Section1.lean`
  Now serves as `About This Project`, with motivation, milestones, a codebase map, and a manual overview.
- `projects/docs_LCS/DocsLCS/Section2.lean`
  Now gives the conceptual introduction to LCS games, their historical role, the Alice/Bob game picture, and the place of Magic Square as the main running example.
- `projects/docs_LCS/DocsLCS/Section3.lean`
  Now focuses on the formalisation of LCS games themselves: `LCSLayout`, `Assignment`, and `LCSGame`.
- `projects/docs_LCS/DocsLCS/Section4.lean`
  Now focuses on measurement systems, projector strategies, observable strategies, and the observable-to-projector bridge.
- The main remaining manual gaps are the chapter on winning conditions and SOS, and the chapter on the Magic Square case study.

The library now has enough real content to document:

- `LCS.Basic`
- `LCS.Measurement`
- `LCS.Observable`
- `LCS.Strategy.ObservableStrategy`
- `LCS.Strategy.ObservableToProjector`
- `LCS.Strategy.Equivalence`
- `LCS.Strategy.ProjectorStrategy`
- `LCS.WinningCondition`
- `LCS.Games.MagicSquare`

Goal

Turn `DocsLCS` into a coherent short manual that explains:

1. What problem the project formalizes.
2. How the code is organized mathematically.
3. What Milestone 1 achieved.
4. What Milestone 2 achieved.
5. How the abstract formalism is instantiated on Magic Square.
6. What remains open.

Recommended Structure

Use the manual as a short research companion, not as a full API reference. Let `doc-gen4` handle exhaustive API docs.

Suggested chapter structure:

1. Landing page
2. About the project
3. Introduction to LCS games
4. Formalising LCS games
5. Strategy formalisms and equivalence
6. Winning condition, local loss, and SOS decomposition
7. Magic Square case study
8. Current results and next steps

File-by-File Plan

1. `projects/docs_LCS/DocsLCS/Docs.lean`
   Keep as the homepage.
   Current role:
   - one-paragraph project summary
   - `Main Verified Results`
   - links to:
     - Magic Square strategy page
     - Winning condition page
     - strategy equivalence page
     - status report PDF
   Keep it short and avoid turning it back into a chapter overview page.

2. `projects/docs_LCS/DocsLCS/Section1.lean`
   Keep as `About This Project`.
   Current role:
   - motivation: why LCS games
   - exact scope of the project
   - precise statement of Milestones 1 and 2 in prose
   - accurate codebase map using current module names
   - manual overview

3. `projects/docs_LCS/DocsLCS/Section2.lean`
   Keep as the conceptual introduction.
   Current role:
   - why LCS games matter historically
   - Alice/Bob roles in the nonlocal game
   - why projector strategies are the target formalism
   - how observables enter the picture
   - why Magic Square is the main case study

4. `projects/docs_LCS/DocsLCS/Section3.lean`
   Keep focused on the formalisation of the game data.
   Explain:
   - `LCSLayout`
   - `Assignment`
   - `LCSGame`
   - why the layout/game split matters

5. `projects/docs_LCS/DocsLCS/Section4.lean`
   Keep focused on measurements and strategies.
   Explain:
   - `IsMeasurementSystem`
   - projector-based strategy: `LCSStrategy`
   - observable-based strategy: `ObservableStrategyData`
   - derived observables `Alice_A` and `Bob_B`
   - why two formalisms are useful
   - what the observable-to-projector construction accomplishes
   Reference modules:
   - `LCS.Measurement`
   - `LCS.Observable`
   - `LCS.Strategy.ProjectorStrategy`
   - `LCS.Strategy.ObservableStrategy`
   - `LCS.Strategy.ObservableToProjector`
   - `LCS.Strategy.Equivalence`

6. Add `projects/docs_LCS/DocsLCS/Section5.lean`
   This should become the chapter on winning conditions and SOS.
   Explain:
   - winning assignments
   - local winning operator
   - local loss operator
   - the role of the projector identities
   - the theorem `local_loss_sos`
   Keep the theorem central, and describe the proof structure at a high level:
   - rewrite local loss
   - use the key identities
   - rearrange into a sum of squares

7. Add `projects/docs_LCS/DocsLCS/Section6.lean`
   This should become the concrete Magic Square chapter.
   Explain:
   - the layout
   - the Pauli-grid observables
   - local commutativity checks
   - the construction of the Magic Square strategy
   - why this is Milestone 1
   This should read like a worked example instantiating the abstract framework.

8. Update `Docs.lean`
   Include `Section5` and `Section6` once they exist.

Writing Style Guidelines

Use the docs for three layers only:

1. Intuition
2. Formal statement
3. Pointer to source/API page

Avoid:

- week-by-week diary language
- placeholder remnants
- long proof scripts copied into prose
- outdated implementation history unless it matters mathematically

Prefer:

- timeless phrasing
- one theorem or definition per subsection
- one short Lean snippet only when it clarifies the interface

Execution Order

1. Keep `Docs.lean` as the compact homepage.
2. Keep `Section1.lean` as `About This Project`.
3. Keep `Section2.lean` as the conceptual introduction.
4. Keep `Section3.lean` focused on `LCSLayout`, `Assignment`, and `LCSGame`.
5. Keep `Section4.lean` focused on measurements, strategies, observables, and equivalence.
6. Add `Section5.lean` for winning conditions and SOS.
7. Add `Section6.lean` for Magic Square.
8. Update includes in `Docs.lean`.
9. Build the manual with `lake exe generate-docs` in `projects/docs_LCS`.
10. Fix broken links, anchor mismatches, and stale references.

Content Outline You Can Reuse

For the manual intro:

- Project goal:
  Formalize part of the theory of Linear Constraint System games in Lean 4, focusing on two milestones: a concrete Magic Square strategy and the general sum-of-squares decomposition of the local loss operator.
- Milestone 1:
  Formalize the Mermin-Peres Magic Square grid and prove it defines a valid observable strategy.
- Milestone 2:
  Formalize the local winning and local loss operators and prove the SOS decomposition theorem for a general LCS game and projector strategy.
- Remaining direction:
  package the results more cleanly, instantiate the general theorem on concrete games, and strengthen the documentation.

Risks To Watch

- stale module names in prose
- broken links to API docs if paths changed
- mixing manual exposition with generated API documentation
- over-documenting proof details instead of theorem meaning

Suggested End State

After this pass, the manual should be understandable to a reader who:

- knows basic Lean and linear algebra,
- has not followed the weekly project history,
- wants to see exactly what is formalized and where.
