# Erdős Problem 884

[EPC](https://www.erdosproblems.com/884) ·
[formalization comment](https://www.erdosproblems.com/884#post-7362) ·
[pinned formalization](https://github.com/honicky/erdos884/tree/323e9a01306df1e094b434beaa48c018370fe258)

## Statement and authorship

`Erdos884.not_erdos_884` disproves the proposed absolute bound on the sum
of reciprocal pairwise divisor gaps by one plus the sum of reciprocal
consecutive divisor gaps. It proves the negation of the corresponding
`IsBigO Filter.atTop` statement, using the original formal-conjectures
definitions with `Nat.nth (· ∣ n)` enumerating the divisors.
The additive `1` is retained. The construction gives arbitrarily large
counterexamples, so this is a disproof of the eventual bound as well.

The informal proof is **Daniel Larsen**'s
[*A question of Erdős on reciprocals of gaps between divisors*](https://github.com/Larsen-Daniel/Erdos-884/blob/main/884.pdf),
building on **Terence Tao**'s
[*On the sum of reciprocals of gaps between divisors*](https://terrytao.wordpress.com/wp-content/uploads/2025/09/erdos-884.pdf).
Larsen's multiscale argument removes Tao's prime-tuples assumption.

The source README explicitly credits **Claude Fable 5**, with minor guidance
from **R. J. Honicky** (`honicky`). Git history confirms this attribution
through Claude Fable 5 coauthor trailers and the final two credit updates.
The source describes Honicky's role as orchestrating proof attempts against
the Axle verification API. The metadata preserves the human name as supplied,
without guessing expansions of the initials.

The statement definitions are credited to the **Formal Conjectures authors**.
The underlying Selberg sieve is due to **Arend Mellendijk**; this foundational
library credit is distinct from authorship of the problem-specific proof.

## Version and license

The selected source is commit `323e9a01306df1e094b434beaa48c018370fe258`
of `honicky/erdos884` (4 July 2026). Its checked-in toolchain explicitly
specifies `leanprover/lean4:v4.31.0`, and the Mathlib dependency is pinned to
`fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`, with input revision `v4.31.0`.
The July 5 EPC comment points to this repository.

The Apache 2.0 license is copied to `Erdos884/LICENSE`; modified source
files carry notices. The source's bundled Selberg sieve is not copied:
the port imports the existing, tracked
`ErdosProblems.Erdos896.PNT.Mathlib.NumberTheory.Sieve.SelbergBounds`
module, preserving that library's existing attribution and license notices.
No sieve-library files are modified.

## Port and Comparator

The upstream `modules/ORDER` supplies the dependency order for the original
amalgamation. The port makes those components real Lean modules, extracts
the two statement definitions into `Definitions`, and exposes the one
previously private helper needed across module boundaries.
The final theorem is named `not_erdos_884` and directly states the negative
answer; the redundant `False ↔ …` wrapper is omitted.

The independent Comparator challenge imports only Mathlib and repeats just
the two divisor-sum definitions and the final negative statement. It imports
neither the solution nor the sieve library.

The compatibility changes update finite-set partition counting and the
`Set.ofPred` API, make conditional sieve sums explicit, and keep classical
instances local to proofs. Unused helper hypotheses are removed rather than
renamed. The mathematical statement and multiscale argument are preserved.

## Verification

- `lake build ErdosProblems.Erdos884 Erdos884` passes on Lean/Mathlib 4.33.0.
  The new solution modules emit no warnings. The independent challenge has
  its expected placeholder warning; the existing sieve library replays its
  pre-existing style warnings.
- `not_erdos_884` depends only on `propext`, `Classical.choice`, and `Quot.sound`.
- Independent exports pass `Comparator.compareAt` and `Comparator.checkAxioms`;
  a fresh Lean environment accepts kernel replay of the exported solution.
  These checks were rerun after the last cleanup.
- The full Linux sandbox/Nanoda runner was not run because this macOS
  environment lacks `landrun`. Nanoda remains enabled in the configuration.
- Metadata, unique registrations, license preservation, configuration
  consistency, and the absence of solution placeholders, `native_decide`,
  custom axioms, unsafe declarations, `run_cmd`, and file/process IO were checked.
