import ErdosProblems.Erdos421.DivisibilityWindows
import Mathlib.NumberTheory.Harmonic.Bounds

/-! # Coefficients obtained by grouping equal rational frequencies -/

namespace Erdos421

/-- The arithmetic coefficient of a reduced rational Fourier frequency. -/
noncomputable def divisorFourierCoefficient (S : Finset ℕ) (a : ℕ → ℂ) (q : ℚ) : ℂ :=
  ∑ m ∈ S.filter (fun m ↦ q.den ∣ m), a m / (m : ℂ)

theorem sum_reciprocal_multiples_le (S : Finset ℕ) {M d : ℕ} (hd : 0 < d)
    (hS : ∀ m ∈ S, 0 < m ∧ m ≤ M ∧ d ∣ m) :
    (∑ m ∈ S, 1 / (m : ℝ)) ≤ (harmonic M : ℝ) / d := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hmul (m : ℕ) (hm : m ∈ S) : d * (m / d) = m := Nat.mul_div_cancel' (hS m hm).2.2
  have hinj : Set.InjOn (fun m ↦ m / d) S := by
    intro m hm n hn heq
    change m / d = n / d at heq
    rw [← hmul m hm, ← hmul n hn, heq]
  have hsub : S.image (fun m ↦ m / d) ⊆ Finset.Icc 1 M := by
    intro n hn
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hn
    have hpos : 0 < m / d :=
      Nat.div_pos (Nat.le_of_dvd (hS m hm).1 (hS m hm).2.2) hd
    exact Finset.mem_Icc.mpr ⟨hpos, (Nat.div_le_self m d).trans (hS m hm).2.1⟩
  have hterm (m : ℕ) (hm : m ∈ S) : 1 / (m : ℝ) = (1 / (d : ℝ)) * (1 / (m / d : ℕ)) := by
    have he : (d : ℝ) * (m / d : ℕ) = m := by exact_mod_cast hmul m hm
    rw [one_div_mul_one_div, he]
  calc
    _ = (1 / (d : ℝ)) * ∑ m ∈ S, (1 : ℝ) / (m / d : ℕ) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl hterm
    _ = (1 / (d : ℝ)) * ∑ n ∈ S.image (fun m ↦ m / d), 1 / (n : ℝ) := by
      rw [Finset.sum_image hinj]
    _ ≤ (1 / (d : ℝ)) * ∑ n ∈ Finset.Icc 1 M, 1 / (n : ℝ) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ ↦ by positivity)
    _ = _ := by
      simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, one_div]
      ring

theorem divisorFourierCoefficient_norm_le (S : Finset ℕ) (a : ℕ → ℂ) {M : ℕ}
    (hS : ∀ m ∈ S, 0 < m ∧ m ≤ M) (ha : ∀ m ∈ S, ‖a m‖ ≤ 1) (q : ℚ) :
    ‖divisorFourierCoefficient S a q‖ ≤ (harmonic M : ℝ) / q.den := by
  classical
  let T := S.filter (fun m ↦ q.den ∣ m)
  have hT : ∀ m ∈ T, 0 < m ∧ m ≤ M ∧ q.den ∣ m := by
    intro m hm
    obtain ⟨hmS, hdiv⟩ := Finset.mem_filter.mp hm
    exact ⟨(hS m hmS).1, (hS m hmS).2, hdiv⟩
  calc
    _ ≤ ∑ m ∈ T, ‖a m / (m : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ m ∈ T, 1 / (m : ℝ) := by
      apply Finset.sum_le_sum
      intro m hm
      rw [norm_div, Complex.norm_natCast]
      exact div_le_div_of_nonneg_right (ha m (Finset.mem_filter.mp hm).1) (Nat.cast_nonneg m)
    _ ≤ _ := sum_reciprocal_multiples_le T q.den_pos hT

end Erdos421
