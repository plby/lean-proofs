# Repository guidelines

## ComparatorChallenges improvements

- Review changes carefully. Check affected theorem statements, configuration
  values, module names, paths, and interactions with the existing runner before
  and after editing.
- Use lightweight static checks where appropriate.
- Do not use consecutive blank lines in ComparatorChallenges Lean files. Keep
  at most one blank line between sections; whitespace-only lines count as blank.
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
