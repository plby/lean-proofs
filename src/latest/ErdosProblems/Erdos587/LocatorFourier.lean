import ErdosProblems.Erdos587.FractionalFourier

/-! Finite periodization counts and their one-sixth Fourier error. -/

open scoped BigOperators SchwartzMap

namespace Erdos587

lemma summable_scaledFourierCoeff_phase (g : 𝓢(ℝ, ℂ)) {σ : ℝ} (hσ : 0 < σ)
    (t : ℝ) : Summable (fun m : ℤ => scaledFourierCoeff g σ m * phase ((m : ℝ) * t)) := by
  apply Summable.of_norm
  simpa only [norm_mul, norm_phase, mul_one] using (summable_scaledFourierCoeff g hσ).norm

theorem finite_periodization_fourier_identity (g : 𝓢(ℝ, ℂ)) {σ : ℝ} (hσ : 0 < σ)
    (θ : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ Finset.range N, periodizedSchwartz g σ (θ n)) =
      ∑' m : ℤ, scaledFourierCoeff g σ m *
        ∑ n ∈ Finset.range N, phase ((m : ℝ) * θ n) := by
  simp_rw [periodizedSchwartz_eq_fourier g hσ]
  rw [← Summable.tsum_finsetSum (s := Finset.range N)
    (fun n _ => summable_scaledFourierCoeff_phase g hσ (θ n))]
  apply tsum_congr
  intro m
  exact (Finset.mul_sum _ _ _).symm

lemma summable_finite_fourier_count (g : 𝓢(ℝ, ℂ)) {σ : ℝ} (hσ : 0 < σ)
    (θ : ℕ → ℝ) (N : ℕ) :
    Summable (fun m : ℤ => scaledFourierCoeff g σ m *
      ∑ n ∈ Finset.range N, phase ((m : ℝ) * θ n)) := by
  apply Summable.of_norm
  apply ((summable_scaledFourierCoeff g hσ).norm.mul_right (N : ℝ)).of_nonneg_of_le
  · intro m
    exact norm_nonneg _
  · intro m
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    calc
      _ ≤ ∑ n ∈ Finset.range N, ‖phase ((m : ℝ) * θ n)‖ := norm_sum_le _ _
      _ = (N : ℝ) := by simp only [norm_phase, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]

theorem finite_periodization_error_bound (g : 𝓢(ℝ, ℂ)) {σ E D : ℝ}
    (hσ : 0 < σ) (hE : 0 ≤ E) (θ : ℕ → ℝ) (N : ℕ)
    (hharmonic : ∀ m : ℤ, m ≠ 0 →
      ‖∑ n ∈ Finset.range N, phase ((m : ℝ) * θ n)‖ ≤ E * |(m : ℝ)| ^ (1 / 6 : ℝ))
    (hmoment : Summable (fun m : ℤ => ‖scaledFourierCoeff g σ m‖ * |(m : ℝ)| ^ (1 / 6 : ℝ)))
    (hbudget : (∑' m : ℤ, ‖scaledFourierCoeff g σ m‖ * |(m : ℝ)| ^ (1 / 6 : ℝ)) ≤ D) :
    ‖(∑ n ∈ Finset.range N, periodizedSchwartz g σ (θ n)) -
      (N : ℂ) * scaledFourierCoeff g σ 0‖ ≤ E * D := by
  classical
  let R (m : ℤ) := if m = 0 then (0 : ℂ) else
    scaledFourierCoeff g σ m * ∑ n ∈ Finset.range N, phase ((m : ℝ) * θ n)
  have hpoint (m : ℤ) : ‖R m‖ ≤ E * (‖scaledFourierCoeff g σ m‖ * |(m : ℝ)| ^ (1 / 6 : ℝ)) := by
    by_cases hm : m = 0
    · subst m
      simp only [R, if_pos rfl, norm_zero]
      positivity
    · simp only [R, if_neg hm, norm_mul]
      calc
        _ ≤ ‖scaledFourierCoeff g σ m‖ * (E * |(m : ℝ)| ^ (1 / 6 : ℝ)) :=
          mul_le_mul_of_nonneg_left (hharmonic m hm) (norm_nonneg _)
        _ = _ := by ring
  have hRnorm : Summable (fun m => ‖R m‖) :=
    (hmoment.mul_left E).of_nonneg_of_le (fun m => norm_nonneg _) hpoint
  have hidentity : (∑ n ∈ Finset.range N, periodizedSchwartz g σ (θ n)) -
      (N : ℂ) * scaledFourierCoeff g σ 0 = ∑' m : ℤ, R m := by
    rw [finite_periodization_fourier_identity g hσ θ N,
      (summable_finite_fourier_count g hσ θ N).tsum_eq_add_tsum_ite (0 : ℤ)]
    have hzero : scaledFourierCoeff g σ 0 *
        ∑ n ∈ Finset.range N, phase (((0 : ℤ) : ℝ) * θ n) =
        (N : ℂ) * scaledFourierCoeff g σ 0 := by
      simp [phase_zero, mul_comm]
    rw [hzero, add_sub_cancel_left]
  rw [hidentity]
  calc
    _ ≤ ∑' m : ℤ, ‖R m‖ := norm_tsum_le_tsum_norm hRnorm
    _ ≤ ∑' m : ℤ, E * (‖scaledFourierCoeff g σ m‖ * |(m : ℝ)| ^ (1 / 6 : ℝ)) :=
      hRnorm.tsum_le_tsum hpoint (hmoment.mul_left E)
    _ = E * ∑' m : ℤ, ‖scaledFourierCoeff g σ m‖ * |(m : ℝ)| ^ (1 / 6 : ℝ) := tsum_mul_left
    _ ≤ E * D := mul_le_mul_of_nonneg_left hbudget hE

end Erdos587
