import ErdosProblems.Erdos964.SievePolynomial

/-!
# Comparing a weighted sum with and without a cut
-/

namespace Erdos964

theorem weighted_cut_sum_error {ι : Type*} (s : Finset ι) (w A B : ι → ℝ)
    (cut : ι → Prop) [DecidablePred cut] (E U : ℝ) (hE : 0 ≤ E)
    (hw : ∀ r ∈ s, 0 ≤ w r)
    (hkeep : ∀ r ∈ s, ¬cut r → |w r * A r - w r * B r| ≤ E * w r)
    (hremove : ∀ r ∈ s, cut r → |w r * B r| ≤ U * w r) :
    |(∑ r ∈ s, if cut r then 0 else w r * A r) - (∑ r ∈ s, w r * B r)| ≤
      E * (∑ r ∈ s, w r) + U * (∑ r ∈ s, if cut r then w r else 0) := by
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ r ∈ s, |(if cut r then 0 else w r * A r) - w r * B r| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ r ∈ s, (E * w r + U * (if cut r then w r else 0)) := by
      apply Finset.sum_le_sum
      intro r hr
      by_cases hcut : cut r
      · rw [if_pos hcut, zero_sub, abs_neg, if_pos hcut]
        exact (hremove r hr hcut).trans (le_add_of_nonneg_left (mul_nonneg hE (hw r hr)))
      · rw [if_neg hcut, if_neg hcut, mul_zero, add_zero]
        exact hkeep r hr hcut
    _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

end Erdos964
