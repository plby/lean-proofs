import ErdosProblems.Erdos421.IntegerReciprocalSquares
import Mathlib.NumberTheory.Harmonic.Bounds

/-! # Square energy of the reduced rational Fourier coefficients -/

namespace Erdos421

theorem rational_reciprocal_square_sum_le (S : Finset ℚ) {M : ℕ}
    (hden : ∀ q ∈ S, q.den ≤ M) (hzero : ∀ q ∈ S, q ≠ 0)
    {Y : ℝ} (hY : 0 < Y) :
    (∑ q ∈ S, 1 / ((q.den : ℝ) + Y * |(q.num : ℝ)|) ^ 2) ≤
      2 * (harmonic M : ℝ) / Y := by
  classical
  have hmap : ∀ q ∈ S, q.den ∈ Finset.Icc 1 M := by
    intro q hq
    exact Finset.mem_Icc.mpr ⟨q.den_pos, hden q hq⟩
  have hfiber (d : ℕ) (hd : d ∈ Finset.Icc 1 M) :
      (∑ q ∈ S.filter (fun q ↦ q.den = d),
        1 / ((q.den : ℝ) + Y * |(q.num : ℝ)|) ^ 2) ≤ 2 / (Y * d) := by
    let T := S.filter (fun q ↦ q.den = d)
    have hinj : Set.InjOn Rat.num T := by
      intro r hr s hs he
      have hdr := (Finset.mem_filter.mp hr).2
      have hds := (Finset.mem_filter.mp hs).2
      rw [← Rat.num_div_den r, ← Rat.num_div_den s, he, hdr, hds]
    have hT : ∀ n ∈ T.image Rat.num, n ≠ 0 := by
      intro n hn
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hn
      exact Rat.num_ne_zero.mpr (hzero q (Finset.mem_filter.mp hq).1)
    have hdR : (0 : ℝ) < d := by exact_mod_cast (Finset.mem_Icc.mp hd).1
    have hb := sum_integer_arithmetic_inverse_squares_le (T.image Rat.num) hT hdR hY
    rw [Finset.sum_image hinj] at hb
    calc
      _ = ∑ q ∈ T, 1 / ((d : ℝ) + Y * |(q.num : ℝ)|) ^ 2 := by
        apply Finset.sum_congr rfl
        intro q hq
        rw [(Finset.mem_filter.mp hq).2]
      _ ≤ _ := hb
  calc
    _ = ∑ d ∈ Finset.Icc 1 M, ∑ q ∈ S.filter (fun q ↦ q.den = d),
        1 / ((q.den : ℝ) + Y * |(q.num : ℝ)|) ^ 2 :=
      (Finset.sum_fiberwise_of_maps_to hmap _).symm
    _ ≤ ∑ d ∈ Finset.Icc 1 M, 2 / (Y * d) := Finset.sum_le_sum hfiber
    _ = _ := by
      simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
      simp_rw [div_mul_eq_div_mul_one_div, ← Finset.mul_sum]
      ring_nf

theorem rational_coefficient_square_energy (S : Finset ℚ) (c : ℚ → ℂ) {M : ℕ}
    (hden : ∀ q ∈ S, q.den ≤ M) (hzero : ∀ q ∈ S, q ≠ 0)
    {Y C : ℝ} (hY : 0 < Y)
    (hc : ∀ q ∈ S, ‖c q‖ ≤ C / ((q.den : ℝ) + Y * |(q.num : ℝ)|)) :
    (∑ q ∈ S, ‖c q‖ ^ 2) ≤ 2 * C ^ 2 * (harmonic M : ℝ) / Y := by
  calc
    _ ≤ ∑ q ∈ S, (C / ((q.den : ℝ) + Y * |(q.num : ℝ)|)) ^ 2 :=
      Finset.sum_le_sum (fun q hq ↦ pow_le_pow_left₀ (norm_nonneg _) (hc q hq) 2)
    _ = C ^ 2 * ∑ q ∈ S, 1 / ((q.den : ℝ) + Y * |(q.num : ℝ)|) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      rw [div_pow]
      ring
    _ ≤ C ^ 2 * (2 * (harmonic M : ℝ) / Y) :=
      mul_le_mul_of_nonneg_left (rational_reciprocal_square_sum_le S hden hzero hY) (sq_nonneg C)
    _ = _ := by ring

end Erdos421
