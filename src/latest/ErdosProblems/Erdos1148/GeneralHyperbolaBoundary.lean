import ErdosProblems.Erdos1148.HyperbolaBoundaryEstimates

/-! # Zeta-character boundary terms without a square cutoff -/

namespace Erdos1148.DukeArithmetic

open Finset ArithmeticFunction

lemma realZetaConvolution_hyperbola_general {q : ℕ} (χ : DirichletCharacter ℝ q) (s : ℝ)
    {N X : ℕ} (hNX : N ≤ X) (hNN : N * N ≤ X) (hX : X < (N + 1) * (N + 1)) :
    weightedArithmeticPartialSum (realZetaConvolution χ) s X =
      (∑ m ∈ Ioc 0 N, (m : ℝ) ^ (-s) * χ m * realPowerPartialSum s (X / m)) +
      (∑ n ∈ Ioc 0 N, (n : ℝ) ^ (-s) * realDirichletPartialSum χ s (X / n)) -
      realDirichletPartialSum χ s N * realPowerPartialSum s N := by
  have h := weighted_convolution_hyperbola (realCharacterArithmetic χ)
    (zeta : ArithmeticFunction ℝ) s hNX hNX hNN hX
  rw [mul_comm (realCharacterArithmetic χ), ← realZetaConvolution] at h
  simp only [weighted_zeta_eq_realPowerPartialSum, weighted_realCharacter_eq_partialSum] at h
  rw [h]
  congr 2
  · apply sum_congr rfl
    intro m hm
    rw [realCharacterArithmetic, ← χ.apply_eq_toArithmeticFunction_apply
      (Nat.ne_zero_of_lt (mem_Ioc.mp hm).1)]
  · apply sum_congr rfl
    intro n hn
    have hn0 : n ≠ 0 := Nat.ne_zero_of_lt (mem_Ioc.mp hn).1
    simp only [natCoe_apply, zeta_apply, hn0, if_false, Nat.cast_one, mul_one]

lemma rpow_hyperbola_general_main_tail {N X : ℕ} (hN : 0 < N)
    (hX : X < (N + 1) * (N + 1)) {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    (X : ℝ) ^ (1 - s) * (N : ℝ) ^ (-1 : ℝ) ≤ 4 * (N : ℝ) ^ (1 - 2 * s) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hX4 : (X : ℝ) ≤ 4 * ((N : ℝ) * N) := by
    have h : (X : ℝ) < ((N : ℝ) + 1) * ((N : ℝ) + 1) := by exact_mod_cast hX
    nlinarith
  have hfour : (4 : ℝ) ^ (1 - s) ≤ 4 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : ℝ) ≤ 4) (by linarith : 1 - s ≤ 1)
  calc
    _ ≤ (4 * ((N : ℝ) * N)) ^ (1 - s) * (N : ℝ) ^ (-1 : ℝ) :=
      mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow (Nat.cast_nonneg X) hX4 (by linarith)) (by positivity)
    _ = (4 : ℝ) ^ (1 - s) * (((N : ℝ) * N) ^ (1 - s) * (N : ℝ) ^ (-1 : ℝ)) := by
      rw [Real.mul_rpow (by norm_num) (mul_nonneg hN0.le hN0.le)]
      ring
    _ = (4 : ℝ) ^ (1 - s) * (N : ℝ) ^ (1 - 2 * s) := by
      rw [rpow_hyperbola_square_main_tail hN0]
    _ ≤ _ := mul_le_mul_of_nonneg_right hfour (by positivity)

theorem hyperbola_general_residue_tail_error_le {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℝ q) (hχ : χ ≠ 1) {s : ℝ} (hs : 0 < s) (hs1 : s < 1)
    {N X : ℕ} (hN : 0 < N) (hX : X < (N + 1) * (N + 1)) :
    ‖(X : ℝ) ^ (1 - s) / (1 - s) *
        (realDirichletValue χ 1 - realDirichletPartialSum χ 1 N)‖ ≤
      8 * ((q : ℝ) / (1 - s)) * (N : ℝ) ^ (1 - 2 * s) := by
  have hd : 0 < 1 - s := by linarith
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc
    _ ≤ (X : ℝ) ^ (1 - s) / (1 - s) * (2 * q * (N : ℝ) ^ (-1 : ℝ)) :=
      mul_le_mul_of_nonneg_left
        (realDirichletValue_sub_partialSum_norm_le_nat χ hχ zero_lt_one hN) (by positivity)
    _ = 2 * ((q : ℝ) / (1 - s)) * ((X : ℝ) ^ (1 - s) * (N : ℝ) ^ (-1 : ℝ)) := by ring
    _ ≤ 2 * ((q : ℝ) / (1 - s)) * (4 * (N : ℝ) ^ (1 - 2 * s)) :=
      mul_le_mul_of_nonneg_left (rpow_hyperbola_general_main_tail hN hX hs hs1) (by positivity)
    _ = _ := by ring

end Erdos1148.DukeArithmetic
