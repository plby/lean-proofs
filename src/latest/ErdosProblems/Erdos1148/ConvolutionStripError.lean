import ErdosProblems.Erdos1148.WeightedDivisorSum
import ErdosProblems.Erdos1148.CharacterConvolutionCutoff
import ErdosProblems.Erdos1148.ZetaCharacterCutoff

/-! # Summing the strip errors for a convolution of two character convolutions -/

namespace Erdos1148.DukeArithmetic

open Finset

lemma rpow_hyperbola_half_error_weight {x m : ℝ} (hx : 0 ≤ x) (hm : 0 < m) (s : ℝ) :
    m ^ (-s) * (x / m) ^ (1 / 2 - s) = x ^ (1 / 2 - s) * m ^ (-(1 / 2) : ℝ) := by
  calc
    _ = x ^ (1 / 2 - s) * (m ^ (-s) / m ^ (1 / 2 - s)) := by
      rw [Real.div_rpow hx hm.le]
      ring
    _ = _ := by rw [← Real.rpow_sub hm, show -s - (1 / 2 - s) = -(1 / 2) by ring]

theorem norm_weighted_hyperbola_error_sum_le (f : ArithmeticFunction ℝ) (E : ℕ → ℝ)
    (s : ℝ) (N X : ℕ) {C D : ℝ} (hC : 0 ≤ C)
    (hE : ∀ n ∈ Ioc 0 N, ‖E n‖ ≤ C * ((X : ℝ) / n) ^ (1 / 2 - s))
    (hweight : (∑ n ∈ Ioc 0 N, (n : ℝ) ^ (-(1 / 2) : ℝ) * ‖f n‖) ≤
      D * (N : ℝ) ^ (5 / 8 : ℝ)) :
    ‖∑ n ∈ Ioc 0 N, (n : ℝ) ^ (-s) * f n * E n‖ ≤
      C * D * (X : ℝ) ^ (1 / 2 - s) * (N : ℝ) ^ (5 / 8 : ℝ) := by
  calc
    _ ≤ ∑ n ∈ Ioc 0 N, ‖(n : ℝ) ^ (-s) * f n * E n‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Ioc 0 N,
        (C * (X : ℝ) ^ (1 / 2 - s)) * ((n : ℝ) ^ (-(1 / 2) : ℝ) * ‖f n‖) := by
      apply sum_le_sum
      intro n hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Ioc.mp hn).1
      rw [norm_mul, norm_mul, Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)]
      calc
        _ ≤ (n : ℝ) ^ (-s) * ‖f n‖ * (C * ((X : ℝ) / n) ^ (1 / 2 - s)) :=
          mul_le_mul_of_nonneg_left (hE n hn) (by positivity)
        _ = _ := by
          rw [show (n : ℝ) ^ (-s) * ‖f n‖ * (C * ((X : ℝ) / n) ^ (1 / 2 - s)) =
            C * ((n : ℝ) ^ (-s) * ((X : ℝ) / n) ^ (1 / 2 - s)) * ‖f n‖ by ring,
            rpow_hyperbola_half_error_weight (Nat.cast_nonneg X) hn0]
          ring
    _ = (C * (X : ℝ) ^ (1 / 2 - s)) *
        (∑ n ∈ Ioc 0 N, (n : ℝ) ^ (-(1 / 2) : ℝ) * ‖f n‖) := by rw [mul_sum]
    _ ≤ (C * (X : ℝ) ^ (1 / 2 - s)) * (D * (N : ℝ) ^ (5 / 8 : ℝ)) :=
      mul_le_mul_of_nonneg_left hweight (mul_nonneg hC (by positivity))
    _ = _ := by ring

theorem norm_hyperbola_constant_strip_error_le (f : ArithmeticFunction ℝ) (P : ℕ → ℝ)
    (s L : ℝ) {N X : ℕ} (hNX : N ≤ X) {C D : ℝ} (hC : 0 ≤ C)
    (hP : ∀ y : ℝ, 1 ≤ y → ‖P ⌊y⌋₊ - L‖ ≤ C * y ^ (1 / 2 - s))
    (hweight : (∑ n ∈ Ioc 0 N, (n : ℝ) ^ (-(1 / 2) : ℝ) * ‖f n‖) ≤
      D * (N : ℝ) ^ (5 / 8 : ℝ)) :
    ‖(∑ n ∈ Ioc 0 N, (n : ℝ) ^ (-s) * f n * P (X / n)) -
        weightedArithmeticPartialSum f s N * L‖ ≤
      C * D * (X : ℝ) ^ (1 / 2 - s) * (N : ℝ) ^ (5 / 8 : ℝ) := by
  rw [weightedArithmeticPartialSum, sum_mul, ← sum_sub_distrib]
  simp_rw [← mul_sub]
  apply norm_weighted_hyperbola_error_sum_le f (fun n => P (X / n) - L) s N X hC ?_ hweight
  intro n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Ioc.mp hn).1
  have hx : (1 : ℝ) ≤ (X : ℝ) / n := (le_div_iff₀ hn0).mpr
    (by simpa only [one_mul] using (Nat.cast_le.mpr ((mem_Ioc.mp hn).2.trans hNX) : (n : ℝ) ≤ X))
  simpa only [Nat.floor_div_eq_div] using hP ((X : ℝ) / n) hx

theorem norm_hyperbola_residue_strip_error_le (f : ArithmeticFunction ℝ) (P : ℕ → ℝ)
    (s Z R : ℝ) {N X : ℕ} (hNX : N ≤ X) {C D : ℝ} (hC : 0 ≤ C)
    (hP : ∀ y : ℝ, 1 ≤ y →
      ‖P ⌊y⌋₊ - (Z + y ^ (1 - s) / (1 - s) * R)‖ ≤ C * y ^ (1 / 2 - s))
    (hweight : (∑ n ∈ Ioc 0 N, (n : ℝ) ^ (-(1 / 2) : ℝ) * ‖f n‖) ≤
      D * (N : ℝ) ^ (5 / 8 : ℝ)) :
    ‖(∑ n ∈ Ioc 0 N, (n : ℝ) ^ (-s) * f n * P (X / n)) -
        (Z * weightedArithmeticPartialSum f s N +
          (X : ℝ) ^ (1 - s) / (1 - s) * R * weightedArithmeticPartialSum f 1 N)‖ ≤
      C * D * (X : ℝ) ^ (1 / 2 - s) * (N : ℝ) ^ (5 / 8 : ℝ) := by
  have hmain : (∑ n ∈ Ioc 0 N, (n : ℝ) ^ (-s) * f n *
        (Z + ((X : ℝ) / n) ^ (1 - s) / (1 - s) * R)) =
      Z * weightedArithmeticPartialSum f s N +
        (X : ℝ) ^ (1 - s) / (1 - s) * R * weightedArithmeticPartialSum f 1 N := by
    simp only [weightedArithmeticPartialSum, mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Ioc.mp hn).1
    calc
      _ = Z * ((n : ℝ) ^ (-s) * f n) +
          ((n : ℝ) ^ (-s) * ((X : ℝ) / n) ^ (1 - s)) * f n / (1 - s) * R := by ring
      _ = _ := by rw [rpow_hyperbola_main_weight (Nat.cast_nonneg X) hn0]; ring
  rw [← hmain, ← sum_sub_distrib]
  simp_rw [← mul_sub]
  apply norm_weighted_hyperbola_error_sum_le f
    (fun n => P (X / n) - (Z + ((X : ℝ) / n) ^ (1 - s) / (1 - s) * R)) s N X hC ?_ hweight
  intro n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Ioc.mp hn).1
  have hx : (1 : ℝ) ≤ (X : ℝ) / n := (le_div_iff₀ hn0).mpr
    (by simpa only [one_mul] using (Nat.cast_le.mpr ((mem_Ioc.mp hn).2.trans hNX) : (n : ℝ) ≤ X))
  simpa only [Nat.floor_div_eq_div] using hP ((X : ℝ) / n) hx

end Erdos1148.DukeArithmetic
