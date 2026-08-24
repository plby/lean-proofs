import ErdosProblems.Erdos587.Periodization
import ErdosProblems.Erdos587.SignedNearby

/-!
# The smoothed square count in nearby rational coordinates

The Bezout identity splits the quadratic phase exactly into a rational
phase modulo the small coefficient and a slowly varying chirp.
-/

open MeasureTheory
open scoped BigOperators SchwartzMap FourierTransform

namespace Erdos587

noncomputable def weightedSquareCount (f g : 𝓢(ℝ, ℂ))
    (a v t : ℕ) (L σ : ℝ) : ℂ :=
  ∑' z : ℤ, f (L⁻¹ * z) * periodizedSchwartz g σ
    ((a : ℝ) * ((z : ℝ) ^ 2 - t) / v)

noncomputable def nearbyQuadraticLattice (f : 𝓢(ℝ, ℂ))
    (u : ℕ) (m : ℤ) (v : ℕ) (b : ℤ) (L : ℝ) : ℂ :=
  ∑' z : ℤ, quadraticResiduePhase u (m * b) z *
    (phase (((m : ℝ) / (u * v)) * (z : ℝ) ^ 2) * f (L⁻¹ * z))

noncomputable def nearbyQuadraticIntegral (f : 𝓢(ℝ, ℂ))
    (u : ℕ) (m : ℤ) (v : ℕ) (L : ℝ) : ℂ :=
  ∫ x : ℝ, phase (((m : ℝ) / (u * v)) * x ^ 2) * f (L⁻¹ * x)

lemma bezout_quadratic_phase {a u b v : ℕ} (hu : 0 < u) (hv : 0 < v)
    (hab : a * u = b * v + 1) (t : ℕ) (m z : ℤ) :
    phase ((m : ℝ) * ((a : ℝ) * ((z : ℝ) ^ 2 - t) / v)) =
      phase (-(m : ℝ) * a * t / v) * quadraticResiduePhase u (m * b) z *
        phase (((m : ℝ) / (u * v)) * (z : ℝ) ^ 2) := by
  have huR : (u : ℝ) ≠ 0 := by exact_mod_cast hu.ne'
  have hvR : (v : ℝ) ≠ 0 := by exact_mod_cast hv.ne'
  have habR : (a : ℝ) * u = b * v + 1 := by exact_mod_cast hab
  unfold quadraticResiduePhase
  rw [← phase_add, ← phase_add]
  congr 1
  push_cast
  field_simp
  linear_combination (m : ℝ) * (z : ℝ) ^ 2 * habR

lemma bezout_quadratic_lattice_factor (f : 𝓢(ℝ, ℂ))
    {a u b v : ℕ} (hu : 0 < u) (hv : 0 < v) (hab : a * u = b * v + 1)
    (t : ℕ) (m : ℤ) (L : ℝ) :
    (∑' z : ℤ, phase ((m : ℝ) * ((a : ℝ) * ((z : ℝ) ^ 2 - t) / v)) * f (L⁻¹ * z)) =
      phase (-(m : ℝ) * a * t / v) * nearbyQuadraticLattice f u m v b L := by
  rw [nearbyQuadraticLattice, ← tsum_mul_left]
  apply tsum_congr
  intro z
  rw [bezout_quadratic_phase hu hv hab]
  ring

theorem weightedSquareCount_fourier (f g : 𝓢(ℝ, ℂ))
    {a u b v : ℕ} (hu : 0 < u) (hv : 0 < v) (hab : a * u = b * v + 1)
    (t : ℕ) {L σ : ℝ} (hL : 0 < L) (hσ : 0 < σ) :
    weightedSquareCount f g a v t L σ =
      ∑' m : ℤ, (scaledFourierCoeff g σ m * phase (-(m : ℝ) * a * t / v)) *
        nearbyQuadraticLattice f u m v b L := by
  rw [weightedSquareCount, weighted_periodization_fourier_identity f g (inv_pos.mpr hL) hσ]
  apply tsum_congr
  intro m
  rw [bezout_quadratic_lattice_factor f hu hv hab]
  exact (mul_assoc _ _ _).symm

lemma summable_weightedSquareCount_fourier (f g : 𝓢(ℝ, ℂ))
    {a u b v : ℕ} (hu : 0 < u) (hv : 0 < v) (hab : a * u = b * v + 1)
    (t : ℕ) {L σ : ℝ} (hL : 0 < L) (hσ : 0 < σ) :
    Summable (fun m : ℤ => (scaledFourierCoeff g σ m * phase (-(m : ℝ) * a * t / v)) *
      nearbyQuadraticLattice f u m v b L) := by
  have hh := (summable_weighted_fourier_roots f g (inv_pos.mpr hL) hσ
    (fun z => (a : ℝ) * ((z : ℝ) ^ 2 - t) / v)).prod
  apply hh.congr
  intro m
  calc
    _ = scaledFourierCoeff g σ m *
        ∑' z : ℤ, phase ((m : ℝ) * ((a : ℝ) * ((z : ℝ) ^ 2 - t) / v)) * f (L⁻¹ * z) := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro z
      exact mul_assoc _ _ _
    _ = _ := by rw [bezout_quadratic_lattice_factor f hu hv hab]; exact (mul_assoc _ _ _).symm

end Erdos587
