# Erdős Problem 49 progress

- Phase: complete (mathematical writeup and Lean formalization).
- Verified mathematics: Tao's stronger weak-monotonicity theorem is reconstructed
  in `tex/49.tex`, including the anatomy partition, primary and secondary
  packing bounds, six exceptional-set estimates, prime-number-theorem conversion,
  finite-prefix absorption, and a lemma-by-lemma Leanization plan.
- Source audit: the statement and numbered ingredients were rechecked against
  Tao's open-access 2024 article (Theorem 1.1, Proposition 1.4, Lemmas 1.5--1.7
  and 2.1, and Propositions 3.2--3.4) and against the current Erdős Problems
  page for Problem 49.
- Verified Lean result: `erdos_49_quantitative : QuantitativeResolution` proves
  uniformly for every `N ≥ 10` and every weakly totient-monotone
  `A ⊆ [1,N]` that
  `|A| ≤ (1 + C (log log N)^5 / log N) π(N)` for one nonnegative constant `C`.
  The strict Erdős formulation and the prime lower-bound example are also formalized.
- Validation: `/tmp/lean-4.33.0-linux/bin/lake build ErdosProblems.Erdos49`
  completed successfully (8769 jobs) at the default computational limits.
- Analytic dependency audit: the pinned `PrimeNumberTheoremAndUpstream` checkout
  is at `7715064f690d0689f30889846f4e2c5e7ec0c47e`; its three current Lean 4.33
  compatibility edits (`Fourier.lean`, `MediumPNT.lean`, and `IEANTN/Mertens.lean`)
  were inspected in full.  They contain no assumptions or proof placeholders,
  and the build rechecks `MediumPNT` with only the standard three axioms.
- Axiom audit: `#print axioms erdos_49_quantitative` reports exactly
  `propext`, `Classical.choice`, and `Quot.sound`; there are no project-local
  or newly introduced axioms.
- Final status: direct public-module checking and the full target build both pass;
  the final forbidden-placeholder and computational-limit scan is clean.
