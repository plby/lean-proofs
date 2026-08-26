import ErdosProblems.Erdos547.ResidualBudgets

/-!
# Identities for the two parts of a fixed-ratio budget
-/

namespace Erdos547.DPRS

theorem skew_parts_of_sum (a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b) :
    (a + b) / (1 + b / a) = a ∧ (b / a) * ((a + b) / (1 + b / a)) = b := by
  have he : (a + b) / (1 + b / a) = a := by
    have hab : a + b ≠ 0 := by linarith
    field_simp [ne_of_gt ha, hab]
  exact ⟨he, by rw [he, div_mul_cancel₀ _ (ne_of_gt ha)]⟩

theorem min_skew_parts_of_one_le (r γ : ℝ) (hr : 0 ≤ r) (hγ : 1 ≤ γ) :
    min (r / (1 + γ)) (γ * (r / (1 + γ))) = r / (1 + γ) := by
  have hden : 0 < 1 + γ := by linarith
  exact min_eq_left (le_mul_of_one_le_left (div_nonneg hr hden.le) hγ)

end Erdos547.DPRS

#print axioms Erdos547.DPRS.skew_parts_of_sum
