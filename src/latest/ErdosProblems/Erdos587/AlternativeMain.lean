import ErdosProblems.Erdos587.NearbyCounting
import ErdosProblems.Erdos587.IntegralPeriodization

/-!
# Exact Fourier expansion of the alternative main term

Every complete Gauss mean is retained. The periodized integral form will
provide positivity, while its Fourier form matches the nearby remainder.
-/

open MeasureTheory
open scoped BigOperators SchwartzMap FourierTransform

namespace Erdos587

noncomputable def alternativeRootArgument (a u b v t : ℕ) (r : ℤ) (x : ℝ) : ℝ :=
  (b : ℝ) * (r : ℝ) ^ 2 / u + x ^ 2 / (u * v) - (a : ℝ) * t / v

lemma continuous_alternativeRootArgument (a u b v t : ℕ) (r : ℤ) :
    Continuous (alternativeRootArgument a u b v t r) := by
  change Continuous (fun x : ℝ =>
    (b : ℝ) * (r : ℝ) ^ 2 / u + x ^ 2 / (u * v) - (a : ℝ) * t / v)
  fun_prop

noncomputable def alternativeSquareMain (f g : 𝓢(ℝ, ℂ))
    (a u b v t : ℕ) (L σ : ℝ) : ℂ :=
  (u : ℂ)⁻¹ * ∑ r : Fin u, ∫ x : ℝ, f (L⁻¹ * x) *
    periodizedSchwartz g σ (alternativeRootArgument a u b v t (r : ℕ) x)

noncomputable def nearbyMainFrequency (f : 𝓢(ℝ, ℂ))
    (u : ℕ) (m : ℤ) (v : ℕ) (b : ℤ) (L : ℝ) : ℂ :=
  (u : ℂ)⁻¹ * completeQuadraticGaussSum u (m * b) 0 * nearbyQuadraticIntegral f u m v L

lemma alternative_quadratic_phase (a u b v t : ℕ) (m r : ℤ) (x : ℝ) :
    phase ((m : ℝ) * alternativeRootArgument a u b v t r x) =
      phase (-(m : ℝ) * a * t / v) * quadraticResiduePhase u (m * b) r *
        phase (((m : ℝ) / (u * v)) * x ^ 2) := by
  unfold alternativeRootArgument quadraticResiduePhase
  rw [← phase_add, ← phase_add]
  congr 1
  push_cast
  ring

lemma alternative_quadratic_integral_factor (f : 𝓢(ℝ, ℂ))
    (a u b v t : ℕ) (m r : ℤ) (L : ℝ) :
    (∫ x : ℝ, phase ((m : ℝ) * alternativeRootArgument a u b v t r x) * f (L⁻¹ * x)) =
      (phase (-(m : ℝ) * a * t / v) * quadraticResiduePhase u (m * b) r) *
        nearbyQuadraticIntegral f u m v L := by
  rw [nearbyQuadraticIntegral, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [alternative_quadratic_phase]
  ring

lemma sum_residue_quadratic_phase (u : ℕ) (a : ℤ) :
    (∑ r : Fin u, quadraticResiduePhase u a (r : ℕ)) = completeQuadraticGaussSum u a 0 := by
  simp only [quadraticResiduePhase, completeQuadraticGaussSum, zero_mul, add_zero]

lemma alternative_frequency_factor (f g : 𝓢(ℝ, ℂ))
    (a u b v t : ℕ) (m : ℤ) (L σ : ℝ) :
    (u : ℂ)⁻¹ * (∑ r : Fin u, scaledFourierCoeff g σ m *
      ∫ x : ℝ, phase ((m : ℝ) * alternativeRootArgument a u b v t (r : ℕ) x) * f (L⁻¹ * x)) =
      (scaledFourierCoeff g σ m * phase (-(m : ℝ) * a * t / v)) *
        nearbyMainFrequency f u m v b L := by
  simp_rw [alternative_quadratic_integral_factor]
  have hfactor : (∑ r : Fin u, scaledFourierCoeff g σ m *
      ((phase (-(m : ℝ) * a * t / v) * quadraticResiduePhase u (m * b) (r : ℕ)) *
        nearbyQuadraticIntegral f u m v L)) =
      (scaledFourierCoeff g σ m * phase (-(m : ℝ) * a * t / v)) *
        ((∑ r : Fin u, quadraticResiduePhase u (m * b) (r : ℕ)) * nearbyQuadraticIntegral f u m v L) := by
    rw [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    ring
  rw [hfactor, sum_residue_quadratic_phase]
  unfold nearbyMainFrequency
  ring

theorem alternativeSquareMain_fourier (f g : 𝓢(ℝ, ℂ)) (a u b v t : ℕ)
    {L σ : ℝ} (hL : 0 < L) (hσ : 0 < σ) :
    alternativeSquareMain f g a u b v t L σ =
      ∑' m : ℤ, (scaledFourierCoeff g σ m * phase (-(m : ℝ) * a * t / v)) *
        nearbyMainFrequency f u m v b L := by
  let θ : Fin u → ℝ → ℝ := fun r => alternativeRootArgument a u b v t (r : ℕ)
  have hθ (r : Fin u) : Continuous (θ r) := continuous_alternativeRootArgument a u b v t (r : ℕ)
  have hs (r : Fin u) := summable_integral_periodization_fourier f g
    (inv_pos.mpr hL) hσ (θ r) (hθ r)
  unfold alternativeSquareMain
  have hrows : (∑ r : Fin u, ∫ x : ℝ, f (L⁻¹ * x) * periodizedSchwartz g σ (θ r x)) =
      ∑ r : Fin u, ∑' m : ℤ, scaledFourierCoeff g σ m *
        ∫ x : ℝ, phase ((m : ℝ) * θ r x) * f (L⁻¹ * x) := by
    apply Finset.sum_congr rfl
    intro r hr
    exact integral_periodization_fourier_identity f g (inv_pos.mpr hL) hσ (θ r) (hθ r)
  rw [hrows, ← Summable.tsum_finsetSum (s := Finset.univ) (fun r hr => hs r), ← tsum_mul_left]
  apply tsum_congr
  intro m
  exact alternative_frequency_factor f g a u b v t m L σ

lemma norm_nearbyMainFrequency_le (f : 𝓢(ℝ, ℂ)) {u : ℕ} (hu : 0 < u)
    (m : ℤ) (v : ℕ) (b : ℤ) {L : ℝ} (hL : 0 < L) :
    ‖nearbyMainFrequency f u m v b L‖ ≤ L * ∫ x : ℝ, ‖f x‖ := by
  have hgauss : ‖(u : ℂ)⁻¹ * completeQuadraticGaussSum u (m * b) 0‖ ≤ 1 := by
    simpa only [div_eq_mul_inv, mul_comm] using norm_complete_quadratic_mean_le_one hu (m * b)
  have hint := norm_chirp_integral_le_scaled_l1 f hL ((m : ℝ) / (u * v))
  unfold nearbyMainFrequency
  rw [norm_mul]
  exact (mul_le_mul hgauss hint (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)

lemma summable_alternativeSquareMain_fourier (f g : 𝓢(ℝ, ℂ))
    (a u b v t : ℕ) (hu : 0 < u) {L σ : ℝ} (hL : 0 < L) (hσ : 0 < σ) :
    Summable (fun m : ℤ => (scaledFourierCoeff g σ m * phase (-(m : ℝ) * a * t / v)) *
      nearbyMainFrequency f u m v b L) := by
  apply ((summable_scaledFourierCoeff g hσ).norm.mul_left (L * ∫ x : ℝ, ‖f x‖)).of_norm_bounded
  intro m
  simp only [norm_mul, norm_phase, mul_one]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left
    (norm_nearbyMainFrequency_le f hu m v b hL) (norm_nonneg (scaledFourierCoeff g σ m))

lemma signedNearbyQuadraticRemainder_eq_lattice_sub_main (f : 𝓢(ℝ, ℂ))
    (u : ℕ) (m : ℤ) (v : ℕ) (b : ℤ) (L : ℝ) :
    signedNearbyQuadraticRemainder f u m v b L =
      nearbyQuadraticLattice f u m v b L - nearbyMainFrequency f u m v b L := rfl

end Erdos587
