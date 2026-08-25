import ErdosProblems.Erdos964.ScalarTransformSupport
import BoundedGaps.Maynard.AugmentedReciprocalTotientLocalData
import BoundedGaps.Maynard.WeightedSmoothAbel

/-!
# The transformed polynomial as a linear logarithmic weight

The exact scalar transform is placed in the generic Abel-summation interface.
The strict endpoint is retained as `(R-1)/r`.
-/

namespace Erdos964

open scoped BigOperators
open BoundedGaps.Maynard

noncomputable def scalarTransformCoefficient (M r n : ℕ) : ℝ :=
  ((r : ℝ) / r.totient) * squarefreeCoprimeInvTotientAF (M * r) n

theorem scalarTransformCoefficient_zero (M r : ℕ) : scalarTransformCoefficient M r 0 = 0 := by
  simp only [scalarTransformCoefficient, ArithmeticFunction.map_zero, mul_zero]

theorem scalarTransformCoefficient_cumulative (M r : ℕ) (t : ℝ) :
    abelCumulative (scalarTransformCoefficient M r) t =
      ((r : ℝ) / r.totient) * squarefreeCoprimeInvTotientMean (M * r) ⌊t⌋₊ := by
  unfold abelCumulative scalarTransformCoefficient
  rw [← Finset.mul_sum, sum_squarefreeCoprimeInvTotientAF_eq_mean]

theorem scalarLinearY_mul_eq_linear_log (R r n : ℕ) (hR : 1 ≤ R) (hr : 0 < r)
    (hn : n ∈ Finset.Icc 1 ((R - 1) / r)) :
    scalarLinearY R (r * n) =
      (7 - 6 * Real.log r / Real.log R) - (6 / Real.log R) * Real.log n := by
  have hn' := Finset.mem_Icc.mp hn
  have hprod := (Nat.le_div_iff_mul_le hr).mp hn'.2
  rw [Nat.mul_comm n r] at hprod
  have hcut : r * n < R := by omega
  have hpos : 1 ≤ r * n := Nat.mul_pos hr hn'.1
  rw [scalarLinearY, if_pos ⟨hpos, hcut⟩, linearSieveWeight, Nat.cast_mul,
    Real.log_mul (by exact_mod_cast hr.ne') (by exact_mod_cast (show n ≠ 0 by omega))]
  ring

theorem scalarSemiprimeTransform_eq_linear_log_sum (M R r : ℕ) (hR : 1 ≤ R)
    (hr : r ∣ scalarSievePrimeProduct M R) :
    scalarSemiprimeTransform (scalarSievePrimeProduct M R) (scalarLinearY R) r =
      ∑ n ∈ Finset.Icc 0 ((R - 1) / r),
        ((7 - 6 * Real.log r / Real.log R) - (6 / Real.log R) * Real.log n) *
          scalarTransformCoefficient M r n := by
  have hr0 : 0 < r := Nat.pos_of_ne_zero
    (ne_zero_of_dvd_ne_zero (scalarSievePrimeProduct_squarefree M R).ne_zero hr)
  rw [scalarSemiprimeTransform_eq_fixed_modulus_sum M R r hR hr]
  have hinterval (Q : ℕ) : Finset.Icc 0 Q = insert 0 (Finset.Icc 1 Q) := by
    ext n
    simp
    omega
  rw [hinterval ((R - 1) / r), Finset.sum_insert (by simp),
    scalarTransformCoefficient_zero, mul_zero, zero_add]
  rw [Finset.sum_filter, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hn0 : n ≠ 0 := by have := (Finset.mem_Icc.mp hn).1; omega
  unfold scalarTransformCoefficient
  rw [squarefreeCoprimeInvTotientAF_apply, if_neg hn0]
  by_cases hcond : Squarefree n ∧ n.Coprime (M * r)
  · rw [if_pos hcond, if_pos hcond, scalarLinearY_mul_eq_linear_log R r n hR hr0 hn]
    ring
  · rw [if_neg hcond, if_neg hcond]
    simp only [mul_zero]

end Erdos964
