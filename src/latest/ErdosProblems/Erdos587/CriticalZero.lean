import ErdosProblems.Erdos587.SignedNearby

/-! The zero-frequency nearby error is a Schwartz quadrature error. -/

open MeasureTheory
open scoped BigOperators SchwartzMap

namespace Erdos587

lemma completeQuadraticGaussSum_zero_zero (q : ℕ) :
    completeQuadraticGaussSum q 0 0 = (q : ℂ) := by
  simp [completeQuadraticGaussSum, phase_zero]

lemma signedNearbyQuadraticRemainder_zero (f : 𝓢(ℝ, ℂ)) {q : ℕ} (hq : 0 < q)
    (v : ℕ) (b : ℤ) (L : ℝ) :
    signedNearbyQuadraticRemainder f q 0 v b L =
      (∑' z : ℤ, f (L⁻¹ * z)) - ∫ x : ℝ, f (L⁻¹ * x) := by
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  simp only [signedNearbyQuadraticRemainder, zero_mul, quadraticResiduePhase, Int.cast_zero,
    zero_div, phase_zero, one_mul, completeQuadraticGaussSum_zero_zero,
    inv_mul_cancel₀ hqC]

theorem exists_signed_nearby_zero_bound (f : 𝓢(ℝ, ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q : ℕ, 0 < q → ∀ v : ℕ, ∀ b : ℤ, ∀ L : ℝ, 0 < L →
      ‖signedNearbyQuadraticRemainder f q 0 v b L‖ ≤ C / L := by
  obtain ⟨C, hC, hquad⟩ := exists_uniform_chirp_quadrature_bound f
  refine ⟨C, hC, ?_⟩
  intro q hq v b L hL
  rw [signedNearbyQuadraticRemainder_zero f hq]
  simpa only [quadraticChirpMul_apply, zero_mul, phase_zero, one_mul, div_eq_mul_inv] using
    hquad 0 (by norm_num) L⁻¹ (inv_pos.mpr hL)

theorem exists_weighted_nearby_zero_bound (f g : 𝓢(ℝ, ℂ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℕ, 0 < q → ∀ v : ℕ, ∀ b : ℤ, ∀ L σ : ℝ,
      1 ≤ L → 0 ≤ σ → σ ≤ 1 →
      ‖((σ : ℂ) * g 0) * signedNearbyQuadraticRemainder f q 0 v b L‖ ≤ C := by
  obtain ⟨C, hC, hzero⟩ := exists_signed_nearby_zero_bound f
  refine ⟨C * ‖g 0‖ + 1, by positivity, ?_⟩
  intro q hq v b L σ hL hσ hσ1
  have hLpos : 0 < L := by linarith
  have hh : C / L ≤ C := div_le_self hC hL
  calc
    _ = (σ * ‖g 0‖) * ‖signedNearbyQuadraticRemainder f q 0 v b L‖ := by
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hσ]
    _ ≤ (1 * ‖g 0‖) * C :=
      mul_le_mul (mul_le_mul_of_nonneg_right hσ1 (norm_nonneg _))
        ((hzero q hq v b L hLpos).trans hh) (norm_nonneg _) (by positivity)
    _ ≤ C * ‖g 0‖ + 1 := by nlinarith

end Erdos587
