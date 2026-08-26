import ErdosProblems.Erdos941.LocalRootConvolution
import ErdosProblems.Erdos941.DirichletHyperbola
import Mathlib.Analysis.PSeries
import Mathlib.Algebra.Order.Chebyshev

/-! # Finite square convolutions and coarse reciprocal-sum bounds -/

namespace Erdos941

open ArithmeticFunction Finset Analytic

theorem allRootCount_eq_sum_Ioc_real (n X : ℕ) :
    (allRootCount n X : ℝ) =
      ∑ a ∈ Ioc 0 X, (allRootCoefficient n : ArithmeticFunction ℝ) a := by
  rw [allRootCount_eq_sum, Nat.cast_sum]
  have h := sum_range_add_sum_Ico
    (fun a => (allRootCoefficient n : ArithmeticFunction ℝ) a) (by omega : 1 ≤ X + 1)
  rw [sum_range_one, ArithmeticFunction.map_zero, zero_add] at h
  rw [show Ico 1 (X + 1) = Ioc 0 X by ext a; simp; omega] at h
  exact h.symm

theorem sum_squareIndicator_mul (F : ℕ → ℝ) (N : ℕ) :
    (∑ a ∈ Ioc 0 (N ^ 2), (squareIndicator : ArithmeticFunction ℝ) a * F a) =
      ∑ c ∈ Ioc 0 N, F (c ^ 2) := by
  classical
  have he : (∑ a ∈ Ioc 0 (N ^ 2), (squareIndicator : ArithmeticFunction ℝ) a * F a) =
      ∑ a ∈ (Ioc 0 (N ^ 2)).filter IsSquare, F a := by
    rw [sum_filter]
    apply sum_congr rfl
    intro a ha
    have ha0 : a ≠ 0 := (mem_Ioc.mp ha).1.ne'
    rw [intCoe_apply, squareIndicator_eq]
    by_cases hsq : IsSquare a <;> simp [ha0, hsq]
  rw [he]
  symm
  apply sum_nbij (fun c => c ^ 2)
  · intro c hc
    obtain ⟨hc0, hcN⟩ := mem_Ioc.mp hc
    exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨pow_pos hc0 _, Nat.pow_le_pow_left hcN 2⟩, IsSquare.sq c⟩
  · exact (Nat.pow_left_injective (by decide : 2 ≠ 0)).injOn
  · intro a ha
    obtain ⟨ha, c, hc⟩ := mem_filter.mp ha
    have hc' : a = c ^ 2 := by simpa only [pow_two] using hc
    refine ⟨c, mem_Ioc.mpr ?_, hc'.symm⟩
    obtain ⟨ha0, haN⟩ := mem_Ioc.mp ha
    constructor <;> nlinarith
  · intro c hc
    rfl

theorem sum_square_convolution (f : ArithmeticFunction ℝ) (N : ℕ) :
    (∑ a ∈ Ioc 0 (N ^ 2), (f * (squareIndicator : ArithmeticFunction ℝ)) a) =
      ∑ c ∈ Ioc 0 N, ∑ b ∈ Ioc 0 (N ^ 2 / c ^ 2), f b := by
  rw [mul_comm f, sum_Ioc_mul_eq_sum_prod_filter, sum_hyperbola_strip]
  exact sum_squareIndicator_mul _ N

theorem sum_inv_sq_Ioc_le_two (N : ℕ) :
    (∑ c ∈ Ioc 0 N, ((c : ℝ)⁻¹) ^ 2) ≤ 2 := by
  have h := sum_Ioo_inv_sq_le (α := ℝ) 0 (N + 1)
  simpa only [Ioo_add_one_right_eq_Ioc, Nat.cast_zero, zero_add, div_one, ← inv_pow] using h

theorem sum_inv_Ioc_le_sqrt (N : ℕ) :
    (∑ c ∈ Ioc 0 N, (c : ℝ)⁻¹) ≤ Real.sqrt (2 * N) := by
  have h : (∑ c ∈ Ioc 0 N, (c : ℝ)⁻¹) ^ 2 ≤
      (N : ℝ) * ∑ c ∈ Ioc 0 N, ((c : ℝ)⁻¹) ^ 2 := by
    simpa using (sq_sum_le_card_mul_sum_sq (s := Ioc 0 N) (f := fun c : ℕ => (c : ℝ)⁻¹))
  have hb := mul_le_mul_of_nonneg_left (sum_inv_sq_Ioc_le_two N) (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 * N by positivity)
  have hp := Real.sqrt_nonneg (2 * (N : ℝ))
  nlinarith

end Erdos941
