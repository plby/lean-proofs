import ErdosProblems.Erdos421.FiniteCoefficients
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

/-! # A truncated Vaughan identity and its coefficient bounds -/

namespace Erdos421

def arithmeticTail {R : Type*} [AddGroup R] (f : ArithmeticFunction R) (A : ℕ) :
    ArithmeticFunction R := f - arithmeticTruncate f A

theorem arithmeticTail_apply {R : Type*} [AddGroup R] (f : ArithmeticFunction R) (A n : ℕ) :
    arithmeticTail f A n = if A < n then f n else 0 := by
  simp only [arithmeticTail, sub_eq_add_neg, ArithmeticFunction.add_apply,
    ArithmeticFunction.neg_apply]
  rw [arithmeticTruncate_apply]
  by_cases hn : n ≤ A
  · simp only [if_pos hn, if_neg (not_lt_of_ge hn), add_neg_cancel]
  · simp only [if_neg hn, if_pos (lt_of_not_ge hn), neg_zero, add_zero]

theorem norm_arithmeticTruncate_le (f : ArithmeticFunction ℝ) (A n : ℕ) :
    ‖arithmeticTruncate f A n‖ ≤ ‖f n‖ := by
  rw [arithmeticTruncate_apply]
  split_ifs
  · exact le_rfl
  · simpa only [norm_zero] using norm_nonneg (f n)

theorem truncated_inverse_identity {R : Type*} [CommRing R]
    (m z l a b : R) (hmz : m * z = 1) :
    l = a * (l * z) - a * b * z + b + (m - a) * (l - b) * z := by
  calc
    l = (m * z) * l := by rw [hmz, one_mul]
    _ = a * (l * z) - a * b * z + (m * z) * b + (m - a) * (l - b) * z := by ring
    _ = _ := by rw [hmz, one_mul]

open scoped ArithmeticFunction ArithmeticFunction.zeta ArithmeticFunction.Moebius

theorem vaughan_identity (U V : ℕ) :
    Λ = arithmeticTruncate (μ : ArithmeticFunction ℝ) U * ArithmeticFunction.log -
        arithmeticTruncate (μ : ArithmeticFunction ℝ) U * arithmeticTruncate Λ V *
          (ζ : ArithmeticFunction ℝ) + arithmeticTruncate Λ V +
        arithmeticTail (μ : ArithmeticFunction ℝ) U * arithmeticTail Λ V *
          (ζ : ArithmeticFunction ℝ) := by
  simpa only [ArithmeticFunction.vonMangoldt_mul_zeta, arithmeticTail] using
    truncated_inverse_identity (μ : ArithmeticFunction ℝ) (ζ : ArithmeticFunction ℝ) Λ
      (arithmeticTruncate (μ : ArithmeticFunction ℝ) U) (arithmeticTruncate Λ V)
      ArithmeticFunction.coe_moebius_mul_coe_zeta

theorem moebius_real_norm_le_one (n : ℕ) : ‖(μ n : ℝ)‖ ≤ 1 := by
  rw [Real.norm_eq_abs]
  exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := n))

theorem vonMangoldt_tail_nonneg (V n : ℕ) : 0 ≤ arithmeticTail Λ V n := by
  rw [arithmeticTail_apply]
  split_ifs <;> positivity

theorem vonMangoldt_tail_le (V n : ℕ) : arithmeticTail Λ V n ≤ Λ n := by
  rw [arithmeticTail_apply]
  split_ifs
  · exact le_rfl
  · exact ArithmeticFunction.vonMangoldt_nonneg

theorem vonMangoldt_tail_zeta_bounds (V n : ℕ) :
    0 ≤ (arithmeticTail Λ V * (ζ : ArithmeticFunction ℝ)) n ∧
      (arithmeticTail Λ V * (ζ : ArithmeticFunction ℝ)) n ≤ Real.log n := by
  rw [ArithmeticFunction.coe_mul_zeta_apply]
  constructor
  · exact Finset.sum_nonneg (fun d _ ↦ vonMangoldt_tail_nonneg V d)
  · calc
      _ ≤ ∑ d ∈ n.divisors, Λ d := Finset.sum_le_sum (fun d _ ↦ vonMangoldt_tail_le V d)
      _ = _ := ArithmeticFunction.vonMangoldt_sum

theorem arithmeticTail_mul_zeta_eq_zero_of_le {R : Type*} [Ring R]
    (f : ArithmeticFunction R) {A n : ℕ} (hn : n ≤ A) :
    (arithmeticTail f A * (ζ : ArithmeticFunction R)) n = 0 := by
  rw [ArithmeticFunction.coe_mul_zeta_apply]
  apply Finset.sum_eq_zero
  intro d hd
  obtain ⟨hdn, hn0⟩ := Nat.mem_divisors.mp hd
  have hdA : d ≤ A := (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hdn).trans hn
  rw [arithmeticTail_apply, if_neg (not_lt_of_ge hdA)]

theorem arithmeticTail_mul_apply {R : Type*} [Ring R] (f g : ArithmeticFunction R)
    (U n : ℕ) :
    (arithmeticTail f U * g) n =
      ∑ p ∈ n.divisorsAntidiagonal.filter (fun p ↦ U < p.1), f p.1 * g p.2 := by
  rw [ArithmeticFunction.mul_apply, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p _
  rw [arithmeticTail_apply]
  split_ifs <;> simp

theorem vaughan_typeII_apply (U V n : ℕ) :
    (arithmeticTail (μ : ArithmeticFunction ℝ) U * arithmeticTail Λ V *
      (ζ : ArithmeticFunction ℝ)) n =
      ∑ p ∈ n.divisorsAntidiagonal.filter (fun p ↦ U < p.1 ∧ V < p.2),
        (μ p.1 : ℝ) * (arithmeticTail Λ V * (ζ : ArithmeticFunction ℝ)) p.2 := by
  rw [mul_assoc, arithmeticTail_mul_apply, Finset.sum_filter, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp₁ : U < p.1
  · by_cases hp₂ : V < p.2
    · simp only [hp₁, hp₂, and_self, if_true, ArithmeticFunction.intCoe_apply]
    · rw [arithmeticTail_mul_zeta_eq_zero_of_le Λ (le_of_not_gt hp₂)]
      simp
  · simp only [hp₁, false_and, if_false]

theorem vaughan_short_coefficient_bound (U V n : ℕ) :
    ‖(arithmeticTruncate (μ : ArithmeticFunction ℝ) U * arithmeticTruncate Λ V) n‖ ≤
      Real.log n := by
  rw [ArithmeticFunction.mul_apply]
  calc
    _ ≤ ∑ p ∈ n.divisorsAntidiagonal,
        ‖arithmeticTruncate (μ : ArithmeticFunction ℝ) U p.1 * arithmeticTruncate Λ V p.2‖ :=
      norm_sum_le _ _
    _ ≤ ∑ p ∈ n.divisorsAntidiagonal, Λ p.2 := by
      apply Finset.sum_le_sum
      intro p _
      rw [norm_mul]
      have hμ : ‖arithmeticTruncate (μ : ArithmeticFunction ℝ) U p.1‖ ≤ 1 :=
        (norm_arithmeticTruncate_le _ _ _).trans (moebius_real_norm_le_one p.1)
      have hΛ : ‖arithmeticTruncate Λ V p.2‖ ≤ Λ p.2 := by
        simpa only [Real.norm_eq_abs, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg] using
          norm_arithmeticTruncate_le Λ V p.2
      simpa only [one_mul] using
        mul_le_mul hμ hΛ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    _ = ∑ d ∈ n.divisors, Λ d := Nat.sum_divisorsAntidiagonal' (fun _ d ↦ Λ d)
    _ = _ := ArithmeticFunction.vonMangoldt_sum

theorem vaughan_short_coefficient_supported (U V : ℕ) :
    SupportedThrough
      (arithmeticTruncate (μ : ArithmeticFunction ℝ) U * arithmeticTruncate Λ V) (U * V) :=
  (arithmeticTruncate_supported _ _).mul (arithmeticTruncate_supported _ _)

end Erdos421
