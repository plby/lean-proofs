import ErdosProblems.Erdos421.FiniteLatticeSpectrum
import ErdosProblems.Erdos421.DivisorWindowSpectrum
import ErdosProblems.Erdos421.RationalFrequencyMean

/-! # A mean-square bound for finite smoothed lattice sums -/

namespace Erdos421

open MeasureTheory FourierTransform
open scoped SchwartzMap

theorem finite_lattice_mean_square (φ : 𝓢(ℝ, ℂ)) {C : ℝ}
    (hφ : ∀ t : ℝ, ‖𝓕 φ t‖ ≤ C / (1 + |t|))
    (T : Finset (ℕ × ℤ)) (a : ℕ → ℂ) {M : ℕ} (hM : 0 < M)
    (hT : ∀ v ∈ T, 0 < v.1 ∧ v.1 ≤ M) (ha : ∀ v ∈ T, ‖a v.1‖ ≤ 1)
    (hzero : ∀ v ∈ T, v.2 ≠ 0) {R Y : ℝ} (hR : 0 ≤ R) (hY : 0 < Y)
    (hspan : ∀ v ∈ T, |(v.2 : ℝ) / v.1| ≤ R) {u v : ℝ} (huv : u ≤ v) :
    (∫ x in u..v, ‖∑ w ∈ T, ((a w.1 / (w.1 : ℂ)) * 𝓕 φ (Y * (w.2 : ℝ) / w.1)) *
        oscillatoryPhase (2 * Real.pi * ((w.2 : ℝ) / w.1)) x‖ ^ 2) ≤
      (v - u + 16 * M ^ 2 * Real.log (4 * Real.pi * R * M ^ 2 + 2)) *
        (2 * C ^ 2 * (harmonic M : ℝ) ^ 3 / Y) := by
  classical
  let F := T.image (fun w ↦ (w.2 : ℚ) / w.1)
  let c : ℚ → ℂ := fun q ↦ groupedLatticeCoefficient T a q * 𝓕 φ (Y * q)
  have hFden : ∀ q ∈ F, q.den ≤ M := by
    intro q hq
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hq
    exact (Nat.le_of_dvd (hT w hw).1 (lattice_frequency_den_dvd w.2 w.1)).trans (hT w hw).2
  have hFzero : ∀ q ∈ F, q ≠ 0 := by
    intro q hq
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hq
    exact div_ne_zero (by exact_mod_cast hzero w hw) (by exact_mod_cast (hT w hw).1.ne')
  have hFspan : ∀ q ∈ F, |(q : ℝ)| ≤ R := by
    intro q hq
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hq
    simpa only [Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast] using hspan w hw
  have hh : (0 : ℝ) ≤ harmonic M := by
    simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    positivity
  have hc : ∀ q ∈ F, ‖c q‖ ≤
      C * (harmonic M : ℝ) / ((q.den : ℝ) + Y * |(q.num : ℝ)|) := by
    intro q hq
    exact rational_window_coefficient_bound φ hφ hh hY q
      (groupedLatticeCoefficient_norm_le T a hT ha q)
  have henergy := rational_coefficient_square_energy F c hFden hFzero hY hc
  have heR : 2 * (C * (harmonic M : ℝ)) ^ 2 * (harmonic M : ℝ) / Y =
      2 * C ^ 2 * (harmonic M : ℝ) ^ 3 / Y := by ring
  rw [heR] at henergy
  have hlog : 0 ≤ Real.log (4 * Real.pi * R * (M : ℝ) ^ 2 + 2) := by
    apply Real.log_nonneg
    have hh' : 0 ≤ 4 * Real.pi * R * (M : ℝ) ^ 2 := by positivity
    linarith
  have hfactor : 0 ≤ v - u + 16 * (M : ℝ) ^ 2 *
      Real.log (4 * Real.pi * R * (M : ℝ) ^ 2 + 2) := by positivity
  have hb := (rational_frequency_mean_square_bound F c hM hFden hFspan u v).trans
    (mul_le_mul_of_nonneg_left henergy hfactor)
  have heq (x : ℝ) :
      (∑ w ∈ T, ((a w.1 / (w.1 : ℂ)) * 𝓕 φ (Y * (w.2 : ℝ) / w.1)) *
        oscillatoryPhase (2 * Real.pi * ((w.2 : ℝ) / w.1)) x) =
        ∑ q ∈ F, c q * oscillatoryPhase (2 * Real.pi * q) x := by
    have he := finite_lattice_spectrum_grouping T a
      (fun q ↦ 𝓕 φ (Y * q) * oscillatoryPhase (2 * Real.pi * q) x)
    simpa only [Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast, mul_div_assoc,
      ← mul_assoc, F, c] using he
  simpa only [heq] using hb

end Erdos421
