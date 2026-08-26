import ErdosProblems.Erdos67.StationaryIrrationalAtoms

/-!
# Boundary estimates for translating a modulated average

Only two endpoint terms remain when a modulated average is shifted once.
These explicit estimates will make conditional residue masses converge to the
ordinary spectral atom mass, without an ergodicity assumption.
-/

open scoped BigOperators ComplexConjugate
open Finset MeasureTheory

namespace Erdos67.StationaryModel

theorem modulatedAverage_eq_weightedSum (N d : ℕ) (η : FrequencyCircle) (ω : Configuration) :
    modulatedAverage N d η ω =
      (∑ j ∈ range (N + 1), conj (fourier 1 η) ^ j * (coordinate ((d * j : ℕ) : ℤ) ω : ℂ)) /
        ((N + 1 : ℕ) : ℂ) := by
  simp only [modulatedAverage, coordinatePolynomial, modulationCoefficients,
    div_mul_eq_mul_div, fourier_nat_eq_pow, map_pow, ← sum_div]
  exact congrArg (fun z : ℂ ↦ z / ((N + 1 : ℕ) : ℂ))
    (Fin.sum_univ_eq_sum_range
      (fun j ↦ conj (fourier 1 η) ^ j * (coordinate ((d * j : ℕ) : ℤ) ω : ℂ)) (N + 1))

theorem weightedSum_shift_identity (zeta : ℂ) (x : ℕ → ℂ) (M : ℕ) :
    zeta * (∑ j ∈ range M, zeta ^ j * x (j + 1)) - (∑ j ∈ range M, zeta ^ j * x j) =
      zeta ^ M * x M - x 0 := by
  have h₁ := sum_range_succ (fun j ↦ zeta ^ j * x j) M
  have h₂ := sum_range_succ' (fun j ↦ zeta ^ j * x j) M
  have he : zeta * (∑ j ∈ range M, zeta ^ j * x (j + 1)) =
      ∑ j ∈ range M, zeta ^ (j + 1) * x (j + 1) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro j _
    rw [pow_succ]
    ring
  rw [he]
  simp only [pow_zero, one_mul] at h₂
  linear_combination h₁ - h₂

theorem norm_modulatedAverage_le (N d : ℕ) (η : FrequencyCircle) (ω : Configuration) :
    ‖modulatedAverage N d η ω‖ ≤ 1 := by
  rw [modulatedAverage_eq_weightedSum, norm_div, Complex.norm_natCast]
  apply (div_le_iff₀ (Nat.cast_pos.mpr (Nat.succ_pos N))).2
  rw [one_mul]
  calc
    _ ≤ ∑ j ∈ range (N + 1),
        ‖conj (fourier 1 η) ^ j * (coordinate ((d * j : ℕ) : ℤ) ω : ℂ)‖ := norm_sum_le _ _
    _ = _ := by
      simp only [norm_mul, norm_pow, RCLike.norm_conj, norm_fourier_frequency,
        one_pow, Complex.norm_real, Real.norm_eq_abs, abs_coordinate,
        sum_const, card_range, nsmul_eq_mul, mul_one]

theorem modulatedAverage_shift_identity (N : ℕ) (η : FrequencyCircle) (ω : Configuration) :
    conj (fourier 1 η) * modulatedAverage N 1 η (shift 1 ω) - modulatedAverage N 1 η ω =
      (conj (fourier 1 η) ^ (N + 1) * (coordinate ((N + 1 : ℕ) : ℤ) ω : ℂ) -
        (coordinate 0 ω : ℂ)) / ((N + 1 : ℕ) : ℂ) := by
  rw [modulatedAverage_eq_weightedSum, modulatedAverage_eq_weightedSum]
  simp only [one_mul, coordinate_shift]
  rw [← mul_div_assoc, ← sub_div]
  have hshift (j : ℕ) : coordinate ((j : ℤ) + 1) ω = coordinate ((j + 1 : ℕ) : ℤ) ω := by
    rw [Nat.cast_add, Nat.cast_one]
  simp_rw [hshift]
  exact congrArg (fun z : ℂ ↦ z / ((N + 1 : ℕ) : ℂ))
    (weightedSum_shift_identity (conj (fourier 1 η))
      (fun j ↦ (coordinate (j : ℤ) ω : ℂ)) (N + 1))

theorem norm_modulatedAverage_shift_sub_le (N : ℕ) (η : FrequencyCircle) (ω : Configuration) :
    ‖conj (fourier 1 η) * modulatedAverage N 1 η (shift 1 ω) - modulatedAverage N 1 η ω‖ ≤
      2 / ((N + 1 : ℕ) : ℝ) := by
  rw [modulatedAverage_shift_identity, norm_div, Complex.norm_natCast]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  calc
    _ ≤ ‖conj (fourier 1 η) ^ (N + 1) * (coordinate ((N + 1 : ℕ) : ℤ) ω : ℂ)‖ +
        ‖(coordinate 0 ω : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by
      simp only [norm_mul, norm_pow, RCLike.norm_conj, norm_fourier_frequency,
        one_pow, Complex.norm_real, Real.norm_eq_abs, abs_coordinate, one_mul]
      norm_num

theorem abs_normSq_sub_le_twice_norm_sub {z w : ℂ} (hz : ‖z‖ ≤ 1) (hw : ‖w‖ ≤ 1) :
    |Complex.normSq z - Complex.normSq w| ≤ 2 * ‖z - w‖ := by
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq,
    sq_sub_sq, abs_mul, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
  have hnorm := abs_norm_sub_norm_le z w
  calc
    _ ≤ 2 * |‖z‖ - ‖w‖| := by
      apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
      linarith
    _ ≤ _ := mul_le_mul_of_nonneg_left hnorm (by norm_num)

theorem abs_modulatedAverage_normSq_shift_sub_le (N : ℕ) (η : FrequencyCircle)
    (ω : Configuration) :
    |Complex.normSq (modulatedAverage N 1 η (shift 1 ω)) -
      Complex.normSq (modulatedAverage N 1 η ω)| ≤ 4 / ((N + 1 : ℕ) : ℝ) := by
  have hz : ‖conj (fourier 1 η) * modulatedAverage N 1 η (shift 1 ω)‖ ≤ 1 := by
    simpa only [norm_mul, RCLike.norm_conj, norm_fourier_frequency, one_mul] using
      norm_modulatedAverage_le N 1 η (shift 1 ω)
  have he := abs_normSq_sub_le_twice_norm_sub hz (norm_modulatedAverage_le N 1 η ω)
  have hm : Complex.normSq (conj (fourier 1 η)) = 1 := by
    rw [Complex.normSq_eq_norm_sq, RCLike.norm_conj, norm_fourier_frequency, one_pow]
  rw [Complex.normSq_mul, hm, one_mul] at he
  have hb := norm_modulatedAverage_shift_sub_le N η ω
  calc
    _ ≤ 2 * (2 / ((N + 1 : ℕ) : ℝ)) :=
      he.trans (mul_le_mul_of_nonneg_left hb (by norm_num))
    _ = _ := by ring

end Erdos67.StationaryModel
