import ErdosProblems.Erdos67b.MRSmoothPrimePowerBounds

/-! # Uniform polynomial-height estimate for the actual prime kernel -/

open Filter

namespace Erdos67b

noncomputable section

open LogWeylParameters ResidueLogPhase

theorem mrExists_smoothPrime_powerCutoff_kernel_bound (R : ℕ) (hR : 2 ≤ R)
    {h : ℝ} (hhR : 2 * h ≤ (R : ℝ)) :
    ∃ P₀ : ℝ, 1 < P₀ ∧ ∀ P ≥ P₀,
      2 ≤ mrPrimePowerCutoff R P ∧
      ∀ hD : 1 ≤ mrPrimePowerCutoff R P, ∀ t : ℝ, |t| ≤ P ^ h →
        ‖mrSmoothPrimeSelbergKernel (mrPrimePowerCutoff R P) hD P t‖ ≤
          4000 * P / (mrPrimeSieveExponent R * Real.log P * (1 + t ^ 2)) +
            mrPrimeKernelErrorConstant R * P ^ (1 - mrPrimeKernelSaving R) := by
  obtain ⟨A₀, _, hA₀⟩ := mrExists_smoothPrimeSelberg_oscillation R hR
  obtain ⟨P₁, hP₁⟩ := eventually_atTop.1 (mrEventually_primePowerCutoff_geometry R hR A₀)
  refine ⟨max 2 P₁, lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_⟩
  intro P hP
  have hgeom := hP₁ P ((le_max_right 2 P₁).trans hP)
  obtain ⟨hPone, hDtwo, _hupper, hlog, hDP, hscale, hcomp⟩ := hgeom
  refine ⟨hDtwo, ?_⟩
  intro hD t ht
  have hPpos : 0 < P := by linarith
  have hmain : 0 ≤ 4000 * P /
      (mrPrimeSieveExponent R * Real.log P * (1 + t ^ 2)) := by
    have := mrPrimeSieveExponent_pos R
    have := Real.log_pos hPone
    positivity
  have hpower : 0 ≤ P ^ (1 - mrPrimeKernelSaving R) := Real.rpow_nonneg hPpos.le _
  have hC := mrPrimeWeylConstant_pos R
  have hpi := Real.pi_pos
  by_cases hlow : |t| ≤ P ^ (savingExponent R / 4)
  · have hb := mrSmoothPrime_kernel_low_power_bound hR hPone hDtwo hlog hDP hlow
    apply hb.trans
    apply add_le_add le_rfl
    apply mul_le_mul_of_nonneg_right _ hpower
    unfold mrPrimeKernelErrorConstant
    linarith
  · have htlarge : P ^ (savingExponent R / 4) < |t| := lt_of_not_ge hlow
    have htne : t ≠ 0 := by
      intro hz
      rw [hz, abs_zero] at htlarge
      exact (Real.rpow_pos_of_pos hPpos _).not_gt htlarge
    have hheight := mrPrimePowerCutoff_height hPone hhR hcomp ht
    have hb := mrSmoothPrime_kernel_high_power_bound hPone.le hD htlarge
      (hA₀ hPpos _ hD hDP hscale htne hheight)
    apply hb.trans
    unfold mrPrimeKernelErrorConstant
    nlinarith

end

end Erdos67b
