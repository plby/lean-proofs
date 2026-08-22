/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZConditionalTruncatedRandomTotalProductBound
import ErdosProblems.Erdos1165.HLOZSharpWindowProductClosure

/-!
# Sharp adjacent-window comparison after an accepted cutoff

The same-rank accepted creation screen truncates an away total by a strict
upper cutoff.  Since the lower sharp window lies entirely to the left of the
upper sharp window, truncating both windows at that cutoff can only improve
their upper-to-lower mass comparison.
-/

open scoped BigOperators

namespace Erdos1165.HLOZTruncatedSharpWindowRatio

open HLOZProposition48Candidates HLOZSharpWindowProductClosure
open ScreeningInstantiation

noncomputable section

/-- Restricting two consecutive sharp windows to the same initial segment
preserves every nonnegative upper-to-lower mass comparison. -/
theorem activeFailureWindow_inter_Iio_ratio
    (m i upper cut : ℕ) (weight : Fin upper → ℝ)
    (hweight : ∀ v, 0 ≤ weight v) {C : ℝ} (hC : 0 ≤ C)
    (hratio :
      (∑ v : Fin upper,
        if (v : ℕ) ∈ activeUpperFailureWindow m i then weight v else 0) ≤
      C * ∑ v : Fin upper,
        if (v : ℕ) ∈ activeLowerFailureWindow m i then weight v else 0) :
    (∑ v : Fin upper,
        if (v : ℕ) ∈ activeUpperFailureWindow m i ∧ (v : ℕ) < cut
        then weight v else 0) ≤
      C * ∑ v : Fin upper,
        if (v : ℕ) ∈ activeLowerFailureWindow m i ∧ (v : ℕ) < cut
        then weight v else 0 := by
  classical
  by_cases hactive : m / 2 ≤ i
  · rw [activeUpperFailureWindow_eq_of_active hactive,
      activeLowerFailureWindow_eq_of_active hactive] at hratio ⊢
    by_cases hcut : cut ≤ i / 15 + shellWidth48 m
    · have hleft :
          (∑ v : Fin upper,
            if (v : ℕ) ∈ upperFailureWindow i (shellWidth48 m) ∧
                (v : ℕ) < cut then weight v else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro v _hv
        rw [if_neg]
        rintro ⟨hvUpper, hvCut⟩
        rw [upperFailureWindow, Finset.mem_Ico] at hvUpper
        omega
      rw [hleft]
      exact mul_nonneg hC
        (Finset.sum_nonneg fun v _hv ↦ by
          split
          · exact hweight v
          · exact le_rfl)
    · have hlowerEq :
          (∑ v : Fin upper,
            if (v : ℕ) ∈ lowerFailureWindow i (shellWidth48 m) ∧
                (v : ℕ) < cut then weight v else 0) =
          ∑ v : Fin upper,
            if (v : ℕ) ∈ lowerFailureWindow i (shellWidth48 m)
            then weight v else 0 := by
        apply Finset.sum_congr rfl
        intro v _hv
        by_cases hvLower :
            (v : ℕ) ∈ lowerFailureWindow i (shellWidth48 m)
        · have hvCut : (v : ℕ) < cut := by
            rw [lowerFailureWindow, Finset.mem_Ico] at hvLower
            omega
          simp [hvLower, hvCut]
        · simp [hvLower]
      rw [hlowerEq]
      calc
        (∑ v : Fin upper,
            if (v : ℕ) ∈ upperFailureWindow i (shellWidth48 m) ∧
                (v : ℕ) < cut then weight v else 0) ≤
            ∑ v : Fin upper,
              if (v : ℕ) ∈ upperFailureWindow i (shellWidth48 m)
              then weight v else 0 := by
          apply Finset.sum_le_sum
          intro v _hv
          by_cases hvBoth :
              (v : ℕ) ∈ upperFailureWindow i (shellWidth48 m) ∧
                (v : ℕ) < cut
          · simp [hvBoth]
          · rw [if_neg hvBoth]
            split
            · exact hweight v
            · exact le_rfl
        _ ≤ C * ∑ v : Fin upper,
              if (v : ℕ) ∈ lowerFailureWindow i (shellWidth48 m)
              then weight v else 0 := hratio
  · rw [activeUpperFailureWindow_eq_empty_of_inactive hactive,
      activeLowerFailureWindow_eq_empty_of_inactive hactive]
    simp

end

end Erdos1165.HLOZTruncatedSharpWindowRatio
