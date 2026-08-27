import ErdosProblems.Erdos587.HooleyUniformMajorArc

/-! # Smooth quadratic sums and their exact zero-mode mean -/

open scoped FourierTransform SchwartzMap

namespace Erdos587

noncomputable def deltaSmoothQuadraticSum (f : 𝓢(ℝ, ℂ)) (K α θ : ℝ) : ℂ :=
  ∑' n : ℤ, phase (α * (n : ℝ) ^ 2 + θ * n) * f (K⁻¹ * n)

noncomputable def deltaSmoothQuadraticMean (f : 𝓢(ℝ, ℂ)) (K : ℝ) (q : ℕ) (a : ℤ) : ℂ :=
  (K : ℂ) / q * completeQuadraticGaussSum q a 0 * 𝓕 f 0

noncomputable def deltaSmoothCenteredQuadratic (f : 𝓢(ℝ, ℂ)) (K : ℝ) (q : ℕ) (a : ℤ) : ℂ :=
  deltaSmoothQuadraticSum f K ((a : ℝ) / q) 0 - deltaSmoothQuadraticMean f K q a

lemma delta_smooth_sum_eq_quadratic_weight (f : 𝓢(ℝ, ℂ)) {K : ℝ} (hK : 0 < K)
    (q : ℕ) (a : ℤ) :
    deltaSmoothQuadraticSum f K ((a : ℝ) / q) 0 =
      ∑' n : ℤ, quadraticResiduePhase q a n *
        dilateSchwartz f K⁻¹ (inv_ne_zero hK.ne') n := by
  apply tsum_congr
  intro n
  simp only [quadraticResiduePhase, dilateSchwartz_apply, zero_mul, add_zero]
  congr 2
  push_cast
  ring

lemma delta_fourier_dilate_inverse (f : 𝓢(ℝ, ℂ)) {K : ℝ} (hK : 0 < K) (ξ : ℝ) :
    𝓕 (dilateSchwartz f K⁻¹ (inv_ne_zero hK.ne')) ξ = (K : ℂ) * 𝓕 f (K * ξ) := by
  rw [fourier_dilateSchwartz]
  simp only [abs_inv, abs_of_pos hK, Complex.ofReal_inv, inv_inv, div_inv_eq_mul, mul_comm K]

theorem delta_smooth_centered_poisson (f : 𝓢(ℝ, ℂ)) {K : ℝ} (hK : 0 < K)
    {q : ℕ} (hq : 0 < q) (a : ℤ) :
    deltaSmoothCenteredQuadratic f K q a =
      (q : ℂ)⁻¹ * ∑' n : ℤ, if n = 0 then 0 else
        completeQuadraticGaussSum q a n *
          𝓕 (dilateSchwartz f K⁻¹ (inv_ne_zero hK.ne')) ((n : ℝ) / q) := by
  let w := dilateSchwartz f K⁻¹ (inv_ne_zero hK.ne')
  have hzero : (∫ x : ℝ, w x) = (K : ℂ) * 𝓕 f 0 := by
    rw [← fourier_zero_eq_integral]
    change 𝓕 w 0 = _
    rw [delta_fourier_dilate_inverse f hK, mul_zero]
  have h := poisson_quadratic_weight_centered w hq a
  rw [hzero] at h
  rw [deltaSmoothCenteredQuadratic, delta_smooth_sum_eq_quadratic_weight f hK]
  apply Eq.trans _ h
  dsimp only [deltaSmoothQuadraticMean]
  ring

theorem exists_delta_family_fourier_decay {W : Set 𝓢(ℝ, ℂ)}
    (hW : Bornology.IsVonNBounded ℝ W) :
    ∃ C : ℝ, 0 < C ∧ ∀ f ∈ W, ∀ ξ : ℝ,
      ‖𝓕 f ξ‖ ≤ C / (1 + |ξ|) ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := exists_delta_family_small_chirp_fourier_decay hW
  refine ⟨C + 1, by positivity, ?_⟩
  intro f hf ξ
  have hzero : quadraticChirpMul 0 f = f := by
    ext x
    simp only [quadraticChirpMul_apply, zero_mul, phase_zero, one_mul]
  have h := hbound f hf 0 (by norm_num) ξ
  rw [hzero] at h
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < (1 + |ξ|) ^ 2)).mpr
  nlinarith

end Erdos587
