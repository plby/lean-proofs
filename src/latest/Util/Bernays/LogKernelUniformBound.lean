import Util.Bernays.LogKernelSmallPart

/-!
# The uniform weighted bound used to remove frequency truncation
-/

open Filter Topology

namespace Bernays

theorem smallLogKernel_scaled_le {y : ℝ} (hy : 1 ≤ y) :
    Real.sqrt y * ((1 + y) * (1 + (y / (4 * Real.pi)) ^ 2)⁻¹) ≤ 32 * Real.pi ^ 2 := by
  have hroot : Real.sqrt y ≤ y := Real.sqrt_le_self_iff.mpr (Or.inr hy)
  have hden : 0 < 1 + (y / (4 * Real.pi)) ^ 2 := by positivity
  rw [← mul_assoc, ← div_eq_mul_inv, div_le_iff₀ hden]
  have hnum : Real.sqrt y * (1 + y) ≤ 2 * y ^ 2 := by
    have := mul_le_mul_of_nonneg_right hroot (by linarith : 0 ≤ 1 + y)
    nlinarith
  have hid : 32 * Real.pi ^ 2 * (y / (4 * Real.pi)) ^ 2 = 2 * y ^ 2 := by
    field_simp
    ring
  nlinarith [Real.pi_pos, sq_nonneg Real.pi]

theorem logarithmicKernelMass_scaled_bound {a : ℕ → ℂ} (ha : ∀ n : ℕ, ‖a n‖ ≤ 1)
    (hcheby : cheby a) {C : ℝ} (hC : 0 ≤ C)
    (hcount : ∀ N : ℕ, cumsum (fun n => ‖a n‖) N ≤
      C * N / (1 + Real.sqrt (Real.log (N : ℝ))))
    {δ : ℝ} (hδ : 0 < δ) (hδ₁ : δ ≤ 1) :
    logarithmicKernelMass a (Real.exp (1 / δ)) / Real.sqrt δ ≤
      32 * Real.pi ^ 2 + 2 * C * (1 + 2 * Real.pi ^ 2) := by
  have hy : 1 ≤ (1 : ℝ) / δ := (le_div_iff₀ hδ).mpr (by simpa using hδ₁)
  have hx : 1 < Real.exp (1 / δ) := Real.one_lt_exp_iff.mpr (by positivity)
  have hbound := logarithmicKernelMass_le ha hcheby hC hcount hx
  rw [Real.log_exp] at hbound
  have hmul := mul_le_mul_of_nonneg_left hbound (Real.sqrt_nonneg (1 / δ))
  have hs : Real.sqrt (1 / δ) = (Real.sqrt δ)⁻¹ := by
    rw [one_div, Real.sqrt_inv]
  have hsp : Real.sqrt (1 / δ) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  have hcancel : Real.sqrt (1 / δ) *
      ((2 * C / Real.sqrt (1 / δ)) * (1 + 2 * Real.pi ^ 2)) =
      2 * C * (1 + 2 * Real.pi ^ 2) := by field_simp
  rw [mul_add, hcancel] at hmul
  have hfinal := hmul.trans (add_le_add (smallLogKernel_scaled_le hy) le_rfl)
  simpa only [hs, inv_mul_eq_div] using hfinal

theorem logarithmicKernelMass_eventually_scaled_bound {a : ℕ → ℂ}
    (ha : ∀ n : ℕ, ‖a n‖ ≤ 1) (hcheby : cheby a) {C : ℝ} (hC : 0 ≤ C)
    (hcount : ∀ N : ℕ, cumsum (fun n => ‖a n‖) N ≤
      C * N / (1 + Real.sqrt (Real.log (N : ℝ)))) :
    ∀ᶠ δ : ℝ in 𝓝[>] 0, logarithmicKernelMass a (Real.exp (1 / δ)) / Real.sqrt δ ≤
      32 * Real.pi ^ 2 + 2 * C * (1 + 2 * Real.pi ^ 2) := by
  filter_upwards [self_mem_nhdsWithin, (eventually_le_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono
    nhdsWithin_le_nhds] with δ hδ hδ₁
  exact logarithmicKernelMass_scaled_bound ha hcheby hC hcount hδ hδ₁

end Bernays
