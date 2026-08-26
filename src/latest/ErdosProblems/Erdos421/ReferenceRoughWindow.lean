import ErdosProblems.Erdos421.ReferenceWindowError

/-! # Uniform rough-window asymptotics at the logarithmic reference scale -/

namespace Erdos421

open Filter Topology

theorem logarithmicRoughWindow_reference_asymptotic (n : ℕ) {β L η : ℝ}
    (hβ : 0 < β) (hL : 2 ≤ L) (hη : 0 < η) :
    ∀ᶠ X : ℝ in atTop, 0 < (Real.log X) ^ (-L) ∧ (Real.log X) ^ (-L) ≤ 1 / 2 ∧
      ∀ x : ℝ, X ^ β ≤ x → ∀ N z : ℕ, 2 ≤ z → (z : ℝ) ^ 2 ≤ x →
        (1 + (Real.log X) ^ (-L)) * x ≤ (z : ℝ) ^ (n + 3) →
        (1 + (Real.log X) ^ (-L)) * x ≤ (N : ℝ) + 1 →
        |logarithmicRoughWindow N z ((Real.log X) ^ (-L)) (Real.log x) -
          finiteBuchstab (n + 1) (Real.log x / Real.log z) / Real.log z| ≤
          η / Real.log X := by
  obtain ⟨C, hC, K, hK, hrough⟩ := exists_logarithmicRoughWindow_asymptotic
  obtain ⟨X₀, hX₀, hwindow⟩ := hrough n (L + 2) 1 (by linarith) (by norm_num)
  let D : ℝ := roughCountErrorConstant (n + 1) + ((n : ℝ) + 3) ^ 2
  have hD : 0 ≤ D := add_nonneg (roughCountErrorConstant_nonneg _) (sq_nonneg _)
  let J : ℝ := K + C / β ^ (L + 2) + C * D / β ^ (2 : ℕ)
  have hlim₁ := Real.tendsto_log_atTop.const_div_atTop J
  have hlim₂ := ((isLittleO_log_rpow_rpow_atTop 1 hβ).tendsto_div_nhds_zero).const_mul K
  norm_num only [Real.rpow_one, mul_zero] at hlim₂
  have hlim := hlim₁.add hlim₂
  norm_num only [add_zero] at hlim
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop 2,
    (tendsto_rpow_atTop hβ).eventually_ge_atTop X₀,
    hlim.eventually (gt_mem_nhds hη)] with X hX hlog hlarge hsmall
  have hXp : 0 < X := by linarith
  have hLX : 0 < Real.log X := by linarith
  have hpower : 0 < X ^ β := Real.rpow_pos_of_pos hXp β
  obtain ⟨hδ, hδsmall, _⟩ := reference_delta_bounds (by linarith : 1 ≤ Real.log X) hL
  have hδhi : (Real.log X) ^ (-L) ≤ 1 / 2 := hδsmall.trans
    ((div_le_iff₀ (sq_pos_of_pos hLX)).mpr (by nlinarith))
  refine ⟨hδ, hδhi, ?_⟩
  intro x hxx N z hz hzsq hpow hN
  have hxp : 0 < x := hpower.trans_le hxx
  have hlogs : β * Real.log X ≤ Real.log x := by
    have h := Real.log_le_log hpower hxx
    rwa [Real.log_rpow hXp] at h
  have hw := hwindow x (hlarge.trans hxx) ((Real.log X) ^ (-L)) hδ hδhi N z hz hzsq hpow hN
  simp only [mul_one] at hw
  have hfirst : K * ((Real.log X) ^ (-L) + x⁻¹) ≤
      K / (Real.log X) ^ (2 : ℕ) + K / X ^ β := by
    have h := mul_le_mul_of_nonneg_left (add_le_add hδsmall (inv_anti₀ hpower hxx)) hK.le
    exact h.trans_eq (by ring)
  have hpart := reference_log_error_le (by linarith : 1 ≤ Real.log X) hL hβ hlogs hC.le hD
  calc
    _ ≤ _ := hw
    _ = K * ((Real.log X) ^ (-L) + x⁻¹) +
        (C / ((Real.log X) ^ (-L) * (Real.log x) ^ (L + 2)) +
          C * D * (Real.log X) ^ (-L) / (Real.log x) ^ (2 : ℕ)) := by dsimp only [D]; ring
    _ ≤ (K / (Real.log X) ^ (2 : ℕ) + K / X ^ β) +
        (C / β ^ (L + 2) + C * D / β ^ (2 : ℕ)) / (Real.log X) ^ (2 : ℕ) :=
      add_le_add hfirst hpart
    _ = (J / Real.log X + K * (Real.log X / X ^ β)) / Real.log X := by
      dsimp only [J]
      field_simp
      ring
    _ ≤ _ := div_le_div_of_nonneg_right hsmall.le hLX.le

end Erdos421
