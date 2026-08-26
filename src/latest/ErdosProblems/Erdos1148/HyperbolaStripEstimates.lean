import ErdosProblems.Erdos1148.RealZetaConvolution
import ErdosProblems.Erdos1148.HyperbolaRpow
import Mathlib.Algebra.Order.Floor.Semifield

/-! # Quantitative errors in the two strips of the Dirichlet hyperbola -/

namespace Erdos1148.DukeArithmetic

open Finset

lemma realPowerPartialSum_div_error_le {s : ℝ} (hs : 0 < s) (hs1 : s < 1)
    {X m : ℕ} (hm : 0 < m) (hmX : m ≤ X) :
    ‖realPowerPartialSum s (X / m) -
        (realZetaRegularized s + ((X : ℝ) / m) ^ (1 - s) / (1 - s))‖ ≤
      2 * ((X : ℝ) / m) ^ (-s) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hx : (1 : ℝ) ≤ (X : ℝ) / m :=
    (le_div_iff₀ hmR).mpr (by simpa only [one_mul] using (Nat.cast_le.mpr hmX : (m : ℝ) ≤ X))
  have h := power_sum_regularized_floor_error_le hs hs1 hx
  simpa only [Nat.floor_div_eq_div, Real.norm_eq_abs, realPowerPartialSum] using h

lemma realDirichletPartialSum_div_error_le {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℝ q) (hχ : χ ≠ 1) {s : ℝ} (hs : 0 < s)
    {X m : ℕ} (hm : 0 < m) (hX : 0 < X) :
    ‖realDirichletPartialSum χ s (X / m) - realDirichletValue χ s‖ ≤
      2 * q * ((X : ℝ) / m) ^ (-s) := by
  have h := realDirichletValue_sub_floor_partialSum_norm_le χ hχ hs
    (show (0 : ℝ) < (X : ℝ) / m by positivity)
  simpa only [Nat.floor_div_eq_div, norm_sub_rev] using h

theorem hyperbola_power_strip_error_le {q : ℕ} (χ : DirichletCharacter ℝ q)
    {s : ℝ} (hs : 0 < s) (hs1 : s < 1) {N X : ℕ} (hNX : N ≤ X) :
    ‖(∑ m ∈ Ioc 0 N, (m : ℝ) ^ (-s) * χ m * realPowerPartialSum s (X / m)) -
        (realZetaRegularized s * realDirichletPartialSum χ s N +
          (X : ℝ) ^ (1 - s) / (1 - s) * realDirichletPartialSum χ 1 N)‖ ≤
      2 * N * (X : ℝ) ^ (-s) := by
  have hmain : (∑ m ∈ Ioc 0 N, (m : ℝ) ^ (-s) * χ m *
        (realZetaRegularized s + ((X : ℝ) / m) ^ (1 - s) / (1 - s))) =
      realZetaRegularized s * realDirichletPartialSum χ s N +
        (X : ℝ) ^ (1 - s) / (1 - s) * realDirichletPartialSum χ 1 N := by
    rw [realDirichletPartialSum_eq_sum_Ioc, realDirichletPartialSum_eq_sum_Ioc,
      mul_sum, mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro m hm
    have hm0 : (0 : ℝ) < m := by exact_mod_cast (mem_Ioc.mp hm).1
    calc
      _ = realZetaRegularized s * ((m : ℝ) ^ (-s) * χ m) +
          ((m : ℝ) ^ (-s) * ((X : ℝ) / m) ^ (1 - s)) * χ m / (1 - s) := by ring
      _ = _ := by rw [rpow_hyperbola_main_weight (Nat.cast_nonneg X) hm0]; ring
  rw [← hmain, ← sum_sub_distrib]
  calc
    _ ≤ ∑ m ∈ Ioc 0 N,
        ‖(m : ℝ) ^ (-s) * χ m * realPowerPartialSum s (X / m) -
          (m : ℝ) ^ (-s) * χ m *
            (realZetaRegularized s + ((X : ℝ) / m) ^ (1 - s) / (1 - s))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _m ∈ Ioc 0 N, 2 * (X : ℝ) ^ (-s) := by
      apply sum_le_sum
      intro m hm
      have hmN := mem_Ioc.mp hm
      have hm0 : (0 : ℝ) < m := by exact_mod_cast hmN.1
      rw [← mul_sub, norm_mul, norm_mul, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg m) _)]
      calc
        _ ≤ (m : ℝ) ^ (-s) * 1 * (2 * ((X : ℝ) / m) ^ (-s)) := by
          gcongr
          · exact χ.norm_le_one _
          · exact realPowerPartialSum_div_error_le hs hs1 hmN.1 (hmN.2.trans hNX)
        _ = _ := by
          rw [show (m : ℝ) ^ (-s) * 1 * (2 * ((X : ℝ) / m) ^ (-s)) =
            2 * ((m : ℝ) ^ (-s) * ((X : ℝ) / m) ^ (-s)) by ring,
            rpow_hyperbola_error_weight (Nat.cast_nonneg X) hm0]
    _ = _ := by simp only [sum_const, Nat.card_Ioc, Nat.sub_zero, nsmul_eq_mul]; ring

theorem hyperbola_character_strip_error_le {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℝ q) (hχ : χ ≠ 1) {s : ℝ} (hs : 0 < s)
    (N : ℕ) {X : ℕ} (hX : 0 < X) :
    ‖(∑ n ∈ Ioc 0 N, (n : ℝ) ^ (-s) * realDirichletPartialSum χ s (X / n)) -
        realPowerPartialSum s N * realDirichletValue χ s‖ ≤
      2 * q * N * (X : ℝ) ^ (-s) := by
  rw [realPowerPartialSum_eq_sum_Ioc, sum_mul, ← sum_sub_distrib]
  calc
    _ ≤ ∑ n ∈ Ioc 0 N,
        ‖(n : ℝ) ^ (-s) * realDirichletPartialSum χ s (X / n) -
          (n : ℝ) ^ (-s) * realDirichletValue χ s‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Ioc 0 N, 2 * q * (X : ℝ) ^ (-s) := by
      apply sum_le_sum
      intro n hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Ioc.mp hn).1
      rw [← mul_sub, norm_mul, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)]
      calc
        _ ≤ (n : ℝ) ^ (-s) * (2 * q * ((X : ℝ) / n) ^ (-s)) :=
          mul_le_mul_of_nonneg_left
            (realDirichletPartialSum_div_error_le χ hχ hs (mem_Ioc.mp hn).1 hX)
            (Real.rpow_nonneg (Nat.cast_nonneg n) _)
        _ = _ := by
          rw [show (n : ℝ) ^ (-s) * (2 * q * ((X : ℝ) / n) ^ (-s)) =
            2 * q * ((n : ℝ) ^ (-s) * ((X : ℝ) / n) ^ (-s)) by ring,
            rpow_hyperbola_error_weight (Nat.cast_nonneg X) hn0]
    _ = _ := by simp only [sum_const, Nat.card_Ioc, Nat.sub_zero, nsmul_eq_mul]; ring

end Erdos1148.DukeArithmetic
