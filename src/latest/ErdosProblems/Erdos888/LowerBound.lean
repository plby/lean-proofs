import ErdosProblems.Erdos888.LowerCount

/-!
# Erdős Problem 888: asymptotic lower bound

This file packages the counted prime--semiprime construction as a lower
Big-O estimate for the exact extremal function.
-/

open Filter Asymptotics

namespace Erdos888

/-- The cardinality of the explicit construction is dominated by the exact
extremal cardinality. -/
theorem lowerBoundSet_card_isBigO_extremalSize :
    (fun n : ℕ ↦ ((lowerBoundSet n).card : ℝ)) =O[atTop]
      (fun n : ℕ ↦ (extremalSize n : ℝ)) := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards with n
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _),
    Real.norm_of_nonneg (Nat.cast_nonneg _), one_mul]
  exact_mod_cast card_lowerBoundSet_le_extremalSize n

/-- The resolved lower estimate for Erdős Problem 888. -/
theorem scale_isBigO_extremalSize :
    scale =O[atTop] (fun n : ℕ ↦ (extremalSize n : ℝ)) :=
  lowerBoundSet_isOmega_scale.trans lowerBoundSet_card_isBigO_extremalSize

end Erdos888
