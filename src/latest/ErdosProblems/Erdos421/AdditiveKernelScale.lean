import ErdosProblems.Erdos421.LogarithmicIntegerWeights

/-! # Stability of an additive kernel under a small change of scale -/

namespace Erdos421

open scoped SchwartzMap

theorem rescaled_kernel_difference_le (φ : 𝓢(ℝ, ℂ)) {C r η t : ℝ} (hC : 0 ≤ C)
    (hnorm : ∀ s : ℝ, ‖φ s‖ ≤ C)
    (hlip : ∀ s t : ℝ, ‖φ s - φ t‖ ≤ C * |s - t|)
    (hr : 1 ≤ r) (hrη : r ≤ 1 + η) (ht : |t| ≤ 1) :
    ‖r • φ (r * t) - φ t‖ ≤ 2 * C * η := by
  have he : r • φ (r * t) - φ t = (r - 1) • φ (r * t) + (φ (r * t) - φ t) := by
    rw [sub_smul, one_smul]
    abel
  have harg : |r * t - t| ≤ η := by
    rw [show r * t - t = (r - 1) * t by ring, abs_mul, abs_of_nonneg (by linarith)]
    have hb := mul_le_mul_of_nonneg_left ht (by linarith : 0 ≤ r - 1)
    nlinarith
  rw [he]
  calc
    _ ≤ ‖(r - 1) • φ (r * t)‖ + ‖φ (r * t) - φ t‖ := norm_add_le _ _
    _ ≤ (r - 1) * C + C * |r * t - t| := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
      exact add_le_add (mul_le_mul_of_nonneg_left (hnorm _) (by linarith)) (hlip _ _)
    _ ≤ η * C + C * η := add_le_add (mul_le_mul_of_nonneg_right (by linarith) hC)
      (mul_le_mul_of_nonneg_left harg hC)
    _ = _ := by ring

theorem additive_weight_scale_support {Y Z x : ℝ} (hY : 0 < Y) (hYZ : Y ≤ Z) (n : ℕ)
    (hne : additiveIntegerWeight Y x n - additiveIntegerWeight Z x n ≠ 0) :
    x < n ∧ (n : ℝ) ≤ x + Z := by
  by_cases hleft : additiveIntegerWeight Y x n = 0
  · have hright : additiveIntegerWeight Z x n ≠ 0 := by
      intro hzero
      exact hne (by rw [hleft, hzero, sub_self])
    have hb := additiveIntegerWeight_nonzero (hY.trans_le hYZ) hright
    exact ⟨hb.1, hb.2.le⟩
  · have hb := additiveIntegerWeight_nonzero hY hleft
    exact ⟨hb.1, hb.2.le.trans (add_le_add_right hYZ x)⟩

theorem additive_weight_scale_difference {C Y Z η x : ℝ} (hC : 0 ≤ C)
    (hnorm : ∀ t : ℝ, ‖oneSidedSchwartzWindow t‖ ≤ C)
    (hlip : ∀ s t : ℝ,
      ‖oneSidedSchwartzWindow s - oneSidedSchwartzWindow t‖ ≤ C * |s - t|)
    (hY : 0 < Y) (hYZ : Y ≤ Z) (hZη : Z ≤ (1 + η) * Y) (hη : 0 ≤ η) (n : ℕ) :
    ‖additiveIntegerWeight Y x n - additiveIntegerWeight Z x n‖ ≤ 2 * C * η / Z := by
  have hZ : 0 < Z := hY.trans_le hYZ
  by_cases hzero : additiveIntegerWeight Y x n - additiveIntegerWeight Z x n = 0
  · rw [hzero, norm_zero]
    positivity
  have hspan := additive_weight_scale_support hY hYZ n hzero
  have ht : |(x - (n : ℝ)) / Z| ≤ 1 := by
    rw [abs_div, abs_of_pos hZ, abs_of_nonpos (by linarith)]
    exact (div_le_one hZ).mpr (by linarith)
  have hr : 1 ≤ Z / Y := (le_div_iff₀ hY).mpr (by simpa using hYZ)
  have hrη : Z / Y ≤ 1 + η := (div_le_iff₀ hY).mpr hZη
  have he : additiveIntegerWeight Y x n - additiveIntegerWeight Z x n =
      (Z⁻¹ : ℝ) • ((Z / Y) • oneSidedSchwartzWindow ((Z / Y) * ((x - (n : ℝ)) / Z)) -
        oneSidedSchwartzWindow ((x - (n : ℝ)) / Z)) := by
    rw [additiveIntegerWeight, additiveIntegerWeight, smul_sub, smul_smul]
    have harg : (Z / Y) * ((x - (n : ℝ)) / Z) = (x - n) / Y := by field_simp
    have hscalar : Z⁻¹ * (Z / Y) = Y⁻¹ := by field_simp
    rw [harg, hscalar]
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hZ)]
  calc
    _ ≤ Z⁻¹ * (2 * C * η) := mul_le_mul_of_nonneg_left
      (rescaled_kernel_difference_le _ hC hnorm hlip hr hrη ht) (by positivity)
    _ = _ := by ring

end Erdos421
