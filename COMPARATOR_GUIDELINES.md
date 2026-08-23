# Repository guidelines

## ComparatorChallenges improvements

- Do not rerun Comparator setup or invoke its validation runner while making
  improvements, unless the user explicitly asks. These operations may take too
  long. Do not install or rebuild Comparator or its supporting tooling as part
  of this work.
- Compensate for the lack of a Comparator run with careful source review. Check
  affected theorem statements, configuration values, module names, paths, and
  interactions with the existing runner before and after editing.
- Use lightweight static checks where appropriate, without triggering setup,
  dependency builds, or Comparator validation.
- Do not use consecutive blank lines in ComparatorChallenges Lean files. Keep
  at most one blank line between sections; whitespace-only lines count as blank.
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
  This does not authorize rerunning Comparator for ComparatorChallenges
  improvements; follow the restriction above and report that validation as
  unverified.
