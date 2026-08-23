/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean development toward Erdős Problem 587.
https://www.erdosproblems.com/forum/thread/587

Informal authors:
- H. H. Nguyen
- V. H. Vu

Statement authors:
- Formal Conjectures authors

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos587.md
- https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/587.lean
-/
/- Copyright 2026. Released under Apache 2.0 license. -/

import ErdosProblems.Erdos587.NguyenVuCompletion

/-!
# Erdős Problem 587

For `A ⊆ {1, ..., N}`, require every nonempty subset sum of `A` to be a
non-square.  Nguyen and Vu proved that the largest possible cardinality is
at most

`N^(1/3) * (log N)^(O(1))`.

The exact finite quantity `MaxNotSqSum` and the square-subset-sum-free
predicate are defined in `ErdosProblems.Erdos587.NVDevelopment`.  The checked
development imported here proves the stopped-sumset construction, divisor
descent, rank-zero/rank-one cases, and the asymptotic conversion.  The
remaining mathematical obligation is the unconditional quantitative
balanced rank-two locator isolated by
`configured_nguyen_vu_one_step_of_balanced_rank_two_locator`.
-/

open Filter

namespace Erdos587

/-- The corrected Formal Conjectures target for Erdős Problem 587. -/
def NguyenVuBound : Prop :=
  ∃ᵉ (O > 0) (O' > 0), ∀ᶠ N : ℕ in atTop,
    (MaxNotSqSum N : ℝ) ≤
      O' * Real.nthRoot 3 N * (N : ℝ).log ^ O

/-- The target is equivalent to the uniform bound for every admissible
finite set; this is the interface used by the Nguyen--Vu development. -/
theorem nguyenVuBound_iff_eventual_uniform_card_bound :
    NguyenVuBound ↔
      (∃ᵉ (O > 0) (O' > 0), ∀ᶠ N : ℕ in atTop,
        ∀ A ⊆ Finset.Icc 1 N, SquareSubsetSumFree A →
          (A.card : ℝ) ≤
            O' * Real.nthRoot 3 N * (N : ℝ).log ^ O) := by
  exact nguyen_vu_iff_eventual_uniform_card_bound

end Erdos587
