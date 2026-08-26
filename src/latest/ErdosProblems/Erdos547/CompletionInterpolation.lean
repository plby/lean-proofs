import ErdosProblems.Erdos547.ResidualNumbers

/-!
# Interpolating full and one-sided residual allocations
-/

namespace Erdos547.DPRS

theorem interpolated_endpoint_le (a M γ x y z t : ℝ) (hM : 0 < M)
    (ht : t ≤ 1) (he : x + γ * y = M - a) (hz : γ * z ≤ M - a) :
    a / M + (t * x + γ * (t * y + (1 - t) * z)) / M ≤ 1 := by
  have hrewrite : t * x + γ * (t * y + (1 - t) * z) =
      t * (M - a) + (1 - t) * (γ * z) := by
    rw [← he]
    ring
  rw [hrewrite, ← add_div]
  apply (div_le_one hM).mpr
  have hh := mul_le_mul_of_nonneg_left hz (sub_nonneg.mpr ht)
  nlinarith only [hh]

theorem interpolated_reverse_endpoint_le (a M γ x y z t : ℝ) (hM : 0 < M)
    (ht : t ≤ 1) (he : γ * x + y = M - a) (hz : z ≤ M - a) :
    a / M + (t * y + (1 - t) * z + γ * (t * x)) / M ≤ 1 := by
  have hrewrite : t * y + (1 - t) * z + γ * (t * x) =
      t * (M - a) + (1 - t) * z := by
    rw [← he]
    ring
  rw [hrewrite, ← add_div]
  apply (div_le_one hM).mpr
  have hh := mul_le_mul_of_nonneg_left hz (sub_nonneg.mpr ht)
  nlinarith only [hh]

theorem interpolated_reverse_endpoint_eq (a M γ x y z t : ℝ) (hM : 0 < M)
    (he : γ * x + y = M - a) (hz : z = M - a) :
    a / M + (t * y + (1 - t) * z + γ * (t * x)) / M = 1 := by
  rw [← add_div]
  apply (div_eq_one_iff_eq (ne_of_gt hM)).mpr
  rw [hz]
  nlinarith only [congrArg (fun r : ℝ ↦ t * r) he]

theorem interpolated_total_lower (a b M γ x y z t : ℝ) (hM : 0 < M)
    (ht : t ≤ 1) (he₁ : x + γ * y = M - a) (he₂ : γ * x + y = M - b)
    (hz : M - (a + b) ≤ (1 + γ) * z) :
    t + 1 - (a + b) / M ≤
      ((1 + γ) * (t * x) + (1 + γ) * (t * y + (1 - t) * z)) / M := by
  have he : (1 + γ) * (x + y) = 2 * M - (a + b) := by nlinarith only [he₁, he₂]
  have hrewrite : (1 + γ) * (t * x) + (1 + γ) * (t * y + (1 - t) * z) =
      t * (2 * M - (a + b)) + (1 - t) * ((1 + γ) * z) := by
    rw [← he]
    ring
  rw [hrewrite, le_div_iff₀ hM]
  have hh := mul_le_mul_of_nonneg_left hz (sub_nonneg.mpr ht)
  have hc : (a + b) / M * M = a + b := div_mul_cancel₀ _ (ne_of_gt hM)
  nlinarith only [hh, hc]

end Erdos547.DPRS

#print axioms Erdos547.DPRS.interpolated_total_lower
