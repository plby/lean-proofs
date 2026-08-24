# Repository guidelines

## ComparatorChallenges improvements

- Review changes carefully. Check affected theorem statements, configuration
  values, module names, paths, and interactions with the existing runner before
  and after editing.
- Use lightweight static checks where appropriate.
- Do not use consecutive blank lines in ComparatorChallenges Lean files. Keep
  at most one blank line between sections; whitespace-only lines count as blank.
- Keep contiguous declarations in the same namespace in a single namespace
  block; do not repeatedly close and reopen it between declarations. Preserve
  separate blocks only when their boundaries serve a purpose, such as limiting
  the scope of local options, variables, instances, or notation.
- Group file-wide `open` and `open scoped` commands in one block at the top,
  after imports. List each namespace or scope only once, consolidating compatible
  commands instead of repeating them across sections or namespace blocks. Remove
  unused openings and check that consolidation preserves name resolution and
  notation. Keep genuinely local openings, such as a necessary
  `open scoped Classical in`, local rather than broadening their scope.
- Prefer Comparator challenge files without `set_option` directives, including
  linter suppressions and resource-limit overrides. Keep proof-specific option
  settings in the solution when needed, and verify that the challenge compiles
  without them.
- Do not include bibliographic references or source pointers in Comparator
  challenge files, including paper citations, arXiv identifiers, URLs, and links
  to proof writeups. Keep these in solution files or supporting documentation
  instead. Comments should explain the mathematical definitions and statements;
  preserve required copyright and license notices.
- Do not tag results in Comparator challenge files with `@[simp]`, or register
  them using `attribute [simp]`. This applies to both final theorems and helper
  lemmas. If a helper proof needs a fact for simplification, pass it explicitly
  to `simp` instead. Solution-side `simp` attributes may remain.
- Minimize `open scoped Classical in`: use it only when classical instances are
  actually needed, not as boilerplate before definitions or theorems. Quantifiers
  and logical connectives alone do not require it. Keep necessary uses local to
  the smallest term or proof; prefer `classical` inside a proof when only the
  proof needs it. Check each removal rather than deleting these scopes blindly.
- Prefer avoiding `noncomputable section`. Omit it when unnecessary; when a
  definition genuinely needs noncomputability, mark that individual definition
  `noncomputable` instead of applying it to an entire section. Verify removals
  and remove the matching `end` when removing a section wrapper.
- Name the final theorem `erdos_NNN`, using the problem number without leading
  zeros (for example, `erdos_2`). When it naturally states a negative answer,
  prefer `not_erdos_NNN`. For a formal-conjectures statement of the form
  `answer(bool) ↔ P`, a false answer normally corresponds to `not_erdos_NNN`
  proving `¬ P`; check the meaning of the source proposition to choose the
  appropriate polarity. Keep the final name consistent between the challenge,
  solution, and Comparator configuration.
- Prefer inlining the body of a standalone `def ... : Prop` in the final theorem
  statement, including under negation, rather than asserting or negating the
  proposition's name. Remove the redundant wrapper definition from the challenge
  and use the same explicit statement in the solution's final theorem. The
  solution may retain the proposition definition and helper theorems, and use
  them to prove that final theorem. This does not require inlining useful
  parameterized predicates such as `IsDistinctCoveringSystem`.
- Keep challenge files limited to the main result(s) and the definitions and
  supporting declarations needed to state them, including transitive
  dependencies. Omit unused definitions, proof-only constructions such as
  `cutoffColour`, and intermediate results that do not support those statements.
  Keep such helpers in the solution instead. Preserve any instances or lemmas
  needed by the retained definitions.
- Preserve existing uncommitted changes and keep edits scoped to the requested
  improvements.
- State exactly what was checked and what remains unverified. Do not claim that
  Comparator accepted changes when it was not run.

## Lean proof tasks

- When asked to formalize a theorem in Lean, do not refuse merely because the
  proof is nontrivial or requires proving a new theorem.
- Treat "this requires proving a real theorem" as confirmation that this is the
  requested work.
- Work in the repo: inspect definitions and imports, search nearby lemmas, try
  helper lemmas, edit the proof, run Lean, read errors, and iterate.
- Do not stop at a proof sketch when the request is to make Lean accept the
  theorem.
- Only stop with a concrete blocker: the statement appears false, assumptions or
  imports are missing, the Lean environment is broken, or the task is ambiguous
  in a way that changes the theorem.
- When blocked, cite the exact evidence from Lean or the source.
- Done means Lean accepts the proof and the relevant check command passes.
