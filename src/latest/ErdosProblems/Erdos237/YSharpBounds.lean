import ErdosProblems.Erdos237.YWeightBounds
import BoundedGaps.Maynard.MaynardLambdaSharpBound

/-!
# Sharp logarithmic bounds for supported Y-coefficients

The quotient reindex in `BoundedGaps` is independent of smoothness. The
supported Y-version below retains that sharper bound for step weights.
-/

namespace Erdos237

open Finset BoundedGaps.Maynard
open scoped BigOperators

theorem abs_coefficientFromY_le_quotientWeightSum {H : Finset ℕ} {R W : ℕ}
    {y : (H → ℕ) → ℝ} {B : ℝ}
    (hy : IsSupportedMaynardY H R W y) (hB : 0 ≤ B) (hbound : ∀ r, |y r| ≤ B)
    {d : H → ℕ} (hd : d ∈ maynardDivisorTupleSupport H R W) :
    |maynardCoefficientFromY H R W y d| ≤ B * lambdaQuotientWeightSum H R d := by
  classical
  have hterm (r : H → ℕ) :
      |if divisorTupleProduct H r < R ∧ (∀ h : H, d h ∣ r h)
        then y r / ∏ h : H, (Nat.totient (r h) : ℝ) else 0| ≤
      if divisorTupleProduct H r < R ∧ (∀ h : H, d h ∣ r h) ∧
          Squarefree (divisorTupleProduct H r)
      then B * (Nat.totient (divisorTupleProduct H r) : ℝ)⁻¹ else 0 := by
    by_cases hz : y r = 0
    · simp only [hz, zero_div, ite_self, abs_zero]
      split_ifs <;> positivity
    have hr := hy r hz
    by_cases hdiv : ∀ h : H, d h ∣ r h
    · rw [if_pos ⟨hr.1, hdiv⟩, if_pos ⟨hr.1, hdiv, hr.2.2⟩]
      have hphi : (∏ h : H, (Nat.totient (r h) : ℝ)) =
          (Nat.totient (divisorTupleProduct H r) : ℝ) := by
        exact_mod_cast (totient_divisorTupleProduct_eq_prod hr.2.2).symm
      rw [hphi, abs_div,
        abs_of_nonneg (Nat.cast_nonneg (Nat.totient (divisorTupleProduct H r)) : (0 : ℝ) ≤ _),
        div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right (hbound r) (by positivity)
    · rw [if_neg (fun h => hdiv h.2), if_neg (fun h => hdiv h.2.1), abs_zero]
  have hinner :
      |∑ r ∈ maynardDivisorTupleBox H R,
        if divisorTupleProduct H r < R ∧ (∀ h : H, d h ∣ r h)
        then y r / ∏ h : H, (Nat.totient (r h) : ℝ) else 0| ≤
      B * ∑ r ∈ lambdaAuxiliaryTupleSupport H R d,
        (Nat.totient (divisorTupleProduct H r) : ℝ)⁻¹ := by
    calc
      _ ≤ _ := abs_sum_le_sum_abs _ _
      _ ≤ ∑ r ∈ maynardDivisorTupleBox H R,
          if divisorTupleProduct H r < R ∧ (∀ h : H, d h ∣ r h) ∧
              Squarefree (divisorTupleProduct H r)
          then B * (Nat.totient (divisorTupleProduct H r) : ℝ)⁻¹ else 0 :=
        sum_le_sum (fun r _ => hterm r)
      _ = _ := by rw [lambdaAuxiliaryTupleSupport, sum_filter, mul_sum]; simp
  rw [maynardCoefficientFromY, if_pos (isMaynardDivisorTuple_of_mem_support hd).2.1,
    abs_mul]
  calc
    _ ≤ (divisorTupleProduct H d : ℝ) *
        (B * ∑ r ∈ lambdaAuxiliaryTupleSupport H R d,
          (Nat.totient (divisorTupleProduct H r) : ℝ)⁻¹) :=
      mul_le_mul (abs_mobius_tuple_mul_le H d) hinner (abs_nonneg _) (by positivity)
    _ = _ := by rw [lambdaQuotientWeightSum_eq_auxiliary_sum]; ring

theorem abs_coefficientFromY_le_sharp_log {H : Finset ℕ} {R W : ℕ}
    {y : (H → ℕ) → ℝ} {B : ℝ}
    (hy : IsSupportedMaynardY H R W y) (hB : 0 ≤ B) (hbound : ∀ r, |y r| ≤ B)
    (hH : H.Nonempty) {d : H → ℕ} (hd : d ∈ maynardDivisorTupleSupport H R W) :
    |maynardCoefficientFromY H R W y d| ≤
      B * (1 + Real.log R) ^ (2 * Fintype.card H ^ 2) := by
  have hk : 1 ≤ Fintype.card H := by
    let : Nonempty H := hH.to_subtype
    exact Fintype.card_pos
  calc
    _ ≤ B * lambdaQuotientWeightSum H R d :=
      abs_coefficientFromY_le_quotientWeightSum hy hB hbound hd
    _ ≤ B * squarefreeTauFirstMean (Fintype.card H) R :=
      mul_le_mul_of_nonneg_left
        (lambdaQuotientWeightSum_le_squarefreeTauFirstMean hH
          (isMaynardDivisorTuple_of_mem_support hd)) hB
    _ ≤ _ := mul_le_mul_of_nonneg_left (squarefreeTauFirstMean_le_one_add_log hk) hB

end Erdos237
