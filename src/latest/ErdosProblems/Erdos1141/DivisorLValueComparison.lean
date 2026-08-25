import ErdosProblems.Erdos1141.DivisorHyperbola
import ErdosProblems.Erdos1141.CharacterLValueApproximation

/-!
# Finite comparison of the divisor sum with its L-value main term
-/

namespace Pollack17

open scoped BigOperators

theorem divisorCoefficient_eq_sum {m : ℕ} (χ : DirichletCharacter ℂ m) (n : ℕ) :
    divisorCoefficient χ n = ∑ d ∈ n.divisors, (χ (d : ℕ)).re := by
  unfold divisorCoefficient
  have heq : χ.zetaMul n = ∑ d ∈ n.divisors, χ (d : ℕ) := by
    change (ArithmeticFunction.zeta * toArithmeticFunction (χ ·)) n = _
    rw [ArithmeticFunction.coe_zeta_mul_apply]
    apply Finset.sum_congr rfl
    intro d hd
    simp only [toArithmeticFunction, ArithmeticFunction.coe_mk,
      if_neg (Nat.pos_of_mem_divisors hd).ne']
  rw [heq, Complex.re_sum]

theorem abs_divisor_sum_sub_LFunction_main_le {m X Y R : ℕ} [NeZero m]
    (hm : 1 < m) (χ : DirichletCharacter ℂ m) (hχ : χ.IsQuadratic) (hχ1 : χ ≠ 1)
    (hY : 0 < Y) (hYX : Y ≤ X) (hYR : Y ≤ R) {b : ℝ} (hb : 0 ≤ b)
    (hprefix : ∀ n : ℕ, Y ≤ n →
      |∑ d ∈ Finset.Icc 1 n, (χ (d : ℕ)).re| ≤ (n : ℝ) * b) :
    |(∑ n ∈ Finset.Icc 1 X, divisorCoefficient χ n) -
        (X : ℝ) * (DirichletCharacter.LFunction χ 1).re| ≤
      (Y : ℝ) + (X : ℝ) * b * (5 + 2 * Real.log (X : ℝ) + Real.log (R : ℝ)) +
        4 * (X : ℝ) * Real.sqrt (m : ℝ) * Real.log (m : ℝ) / (R : ℝ) := by
  have hf (n : ℕ) : |(χ (n : ℕ)).re| ≤ 1 := by
    rcases hχ (n : ℕ) with h | h | h <;> rw [h] <;> norm_num
  have hhyp := abs_divisor_sum_sub_truncated_main_le (fun n => (χ (n : ℕ)).re)
    hf hY hYX hb hprefix
  have htail := abs_reciprocal_prefix_sub_LFunction_re_le hm χ hχ1 hY hYR hb
    (fun n hn _ => hprefix n hn)
  simp_rw [← divisorCoefficient_eq_sum χ] at hhyp
  let P : ℝ := ∑ d ∈ Finset.Icc 1 Y, (χ (d : ℕ)).re / (d : ℝ)
  let L : ℝ := (DirichletCharacter.LFunction χ 1).re
  let S : ℝ := ∑ n ∈ Finset.Icc 1 X, divisorCoefficient χ n
  have htri := abs_sub_le S ((X : ℝ) * P) ((X : ℝ) * L)
  have hscaled : |(X : ℝ) * P - (X : ℝ) * L| ≤
      (X : ℝ) * (b * (3 + Real.log (R : ℝ)) +
        4 * Real.sqrt (m : ℝ) * Real.log (m : ℝ) / (R : ℝ)) := by
    rw [← mul_sub, abs_mul, abs_of_nonneg (Nat.cast_nonneg X)]
    exact mul_le_mul_of_nonneg_left htail (Nat.cast_nonneg X)
  change |S - (X : ℝ) * L| ≤ _
  calc
    _ ≤ ((Y : ℝ) + 2 * (X : ℝ) * b * (1 + Real.log (X : ℝ))) +
        (X : ℝ) * (b * (3 + Real.log (R : ℝ)) +
          4 * Real.sqrt (m : ℝ) * Real.log (m : ℝ) / (R : ℝ)) :=
      htri.trans (add_le_add hhyp hscaled)
    _ = _ := by ring

end Pollack17
