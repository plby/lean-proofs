import ErdosProblems.Erdos587.HooleySmoothQuadratic
import ErdosProblems.Erdos587.AlternativeMain

/-!
# The complete-period main term for the power-separated branch

Its residue form is nonnegative for nonnegative physical weights. Its
Fourier form retains exactly the zero mode of each quadratic Poisson sum.
-/

open scoped BigOperators SchwartzMap FourierTransform

namespace Erdos587

noncomputable def deltaPeriodicSquareDensity (g : 𝓢(ℝ, ℂ))
    (a q t : ℕ) (σ : ℝ) : ℂ :=
  (q : ℂ)⁻¹ * ∑ r : Fin q, periodizedSchwartz g σ
    ((a : ℝ) * (((r : ℕ) : ℝ) ^ 2 - t) / q)

noncomputable def deltaPeriodicSquareMain (f g : 𝓢(ℝ, ℂ))
    (a q t : ℕ) (L σ : ℝ) : ℂ :=
  (L : ℂ) * 𝓕 f 0 * deltaPeriodicSquareDensity g a q t σ

lemma delta_periodic_quadratic_phase (a q t : ℕ) (m z : ℤ) :
    phase ((m : ℝ) * ((a : ℝ) * ((z : ℝ) ^ 2 - t) / q)) =
      phase (-(m : ℝ) * a * t / q) * quadraticResiduePhase q (m * a) z := by
  rw [quadraticResiduePhase, ← phase_add]
  congr 1
  push_cast
  ring

lemma delta_periodic_main_frequency_factor (f g : 𝓢(ℝ, ℂ))
    (a q t : ℕ) (L σ : ℝ) (m : ℤ) :
    ((L : ℂ) * 𝓕 f 0 * (q : ℂ)⁻¹) *
      (∑ r : Fin q, scaledFourierCoeff g σ m *
        phase ((m : ℝ) * ((a : ℝ) * (((r : ℕ) : ℝ) ^ 2 - t) / q))) =
      (scaledFourierCoeff g σ m * phase (-(m : ℝ) * a * t / q)) *
        deltaSmoothQuadraticMean f L q (m * a) := by
  have heq (r : Fin q) := delta_periodic_quadratic_phase a q t m (r : ℕ)
  simp only [Int.cast_natCast] at heq
  simp_rw [heq, ← mul_assoc]
  rw [← Finset.mul_sum, sum_residue_quadratic_phase]
  unfold deltaSmoothQuadraticMean
  ring

theorem deltaPeriodicSquareMain_fourier (f g : 𝓢(ℝ, ℂ))
    (a q t : ℕ) (L : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    deltaPeriodicSquareMain f g a q t L σ =
      ∑' m : ℤ, (scaledFourierCoeff g σ m * phase (-(m : ℝ) * a * t / q)) *
        deltaSmoothQuadraticMean f L q (m * a) := by
  have hs (r : Fin q) : Summable (fun m : ℤ => scaledFourierCoeff g σ m *
      phase ((m : ℝ) * ((a : ℝ) * (((r : ℕ) : ℝ) ^ 2 - t) / q))) := by
    apply Summable.of_norm
    simpa only [norm_mul, norm_phase, mul_one] using (summable_scaledFourierCoeff g hσ).norm
  unfold deltaPeriodicSquareMain deltaPeriodicSquareDensity
  rw [← mul_assoc]
  simp_rw [periodizedSchwartz_eq_fourier g hσ]
  rw [← Summable.tsum_finsetSum (s := Finset.univ) (fun r _ => hs r), ← tsum_mul_left]
  apply tsum_congr
  intro m
  exact delta_periodic_main_frequency_factor f g a q t L σ m

lemma summable_deltaPeriodicSquareMain_fourier (f g : 𝓢(ℝ, ℂ))
    (a q t : ℕ) (L : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    Summable (fun m : ℤ => (scaledFourierCoeff g σ m * phase (-(m : ℝ) * a * t / q)) *
      deltaSmoothQuadraticMean f L q (m * a)) := by
  have hs (r : Fin q) : Summable (fun m : ℤ => scaledFourierCoeff g σ m *
      phase ((m : ℝ) * ((a : ℝ) * (((r : ℕ) : ℝ) ^ 2 - t) / q))) := by
    apply Summable.of_norm
    simpa only [norm_mul, norm_phase, mul_one] using (summable_scaledFourierCoeff g hσ).norm
  have hsum := (summable_sum (s := (Finset.univ : Finset (Fin q))) (fun r _ => hs r)).mul_left
    ((L : ℂ) * 𝓕 f 0 * (q : ℂ)⁻¹)
  exact hsum.congr (fun m => delta_periodic_main_frequency_factor f g a q t L σ m)

lemma delta_periodic_quadratic_lattice_factor (f : 𝓢(ℝ, ℂ))
    (a q t : ℕ) (m : ℤ) (L : ℝ) :
    (∑' z : ℤ, phase ((m : ℝ) * ((a : ℝ) * ((z : ℝ) ^ 2 - t) / q)) * f (L⁻¹ * z)) =
      phase (-(m : ℝ) * a * t / q) *
        deltaSmoothQuadraticSum f L (((m * a : ℤ) : ℝ) / q) 0 := by
  unfold deltaSmoothQuadraticSum
  rw [← tsum_mul_left]
  apply tsum_congr
  intro z
  rw [delta_periodic_quadratic_phase]
  simp only [quadraticResiduePhase, zero_mul, add_zero]
  have hphase : phase ((((m * a) * z ^ 2 : ℤ) : ℝ) / q) =
      phase ((((m * a : ℤ) : ℝ) / q) * (z : ℝ) ^ 2) := by
    congr 1
    push_cast
    ring
  rw [hphase]
  ring

theorem delta_weightedSquareCount_fourier (f g : 𝓢(ℝ, ℂ))
    (a q t : ℕ) {L σ : ℝ} (hL : 0 < L) (hσ : 0 < σ) :
    weightedSquareCount f g a q t L σ =
      ∑' m : ℤ, (scaledFourierCoeff g σ m * phase (-(m : ℝ) * a * t / q)) *
        deltaSmoothQuadraticSum f L (((m * a : ℤ) : ℝ) / q) 0 := by
  rw [weightedSquareCount, weighted_periodization_fourier_identity f g (inv_pos.mpr hL) hσ]
  apply tsum_congr
  intro m
  rw [delta_periodic_quadratic_lattice_factor]
  ring

lemma summable_delta_weightedSquareCount_fourier (f g : 𝓢(ℝ, ℂ))
    (a q t : ℕ) {L σ : ℝ} (hL : 0 < L) (hσ : 0 < σ) :
    Summable (fun m : ℤ => (scaledFourierCoeff g σ m * phase (-(m : ℝ) * a * t / q)) *
      deltaSmoothQuadraticSum f L (((m * a : ℤ) : ℝ) / q) 0) := by
  have hh := (summable_weighted_fourier_roots f g (inv_pos.mpr hL) hσ
    (fun z => (a : ℝ) * ((z : ℝ) ^ 2 - t) / q)).prod
  apply hh.congr
  intro m
  calc
    _ = scaledFourierCoeff g σ m *
        ∑' z : ℤ, phase ((m : ℝ) * ((a : ℝ) * ((z : ℝ) ^ 2 - t) / q)) * f (L⁻¹ * z) := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro z
      ring
    _ = _ := by rw [delta_periodic_quadratic_lattice_factor]; ring

theorem delta_weightedSquareCount_sub_periodicMain (f g : 𝓢(ℝ, ℂ))
    (a q t : ℕ) {L σ : ℝ} (hL : 0 < L) (hσ : 0 < σ) :
    weightedSquareCount f g a q t L σ - deltaPeriodicSquareMain f g a q t L σ =
      ∑' m : ℤ, (scaledFourierCoeff g σ m * phase (-(m : ℝ) * a * t / q)) *
        deltaSmoothCenteredQuadratic f L q (m * a) := by
  rw [delta_weightedSquareCount_fourier f g a q t hL hσ,
    deltaPeriodicSquareMain_fourier f g a q t L hσ,
    ← Summable.tsum_sub (summable_delta_weightedSquareCount_fourier f g a q t hL hσ)
      (summable_deltaPeriodicSquareMain_fourier f g a q t L hσ)]
  apply tsum_congr
  intro m
  rw [deltaSmoothCenteredQuadratic, mul_sub]

end Erdos587
