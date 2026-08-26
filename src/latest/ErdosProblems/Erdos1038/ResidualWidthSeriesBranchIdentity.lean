import ErdosProblems.Erdos1038.ResidualWidthUniformComparison

/-!
# Odd inverse-width series as a difference of inverse branches

The existing residual-coordinate theorem is specialized to one atomic
configuration.  Canonical platform refinements change their coordinate type
at every mesh, so this file records the same identity for arbitrary positive
finite coordinates.
-/

set_option warningAsError false

open Set
open scoped BigOperators

namespace Erdos1038

noncomputable section

/-- At the natural evaluation scale, the full Lagrange inverse series is
the `tsum` of the scaled coefficients. -/
theorem lagrangeInverseValue_inverseMonomial_eq_tsum_scaled
    {iota : Type*} [Fintype iota]
    (a d : iota → ℝ) (hd : d ∈ positiveCoordinates iota) :
    lagrangeInverseValue a d (inverseMonomial a d) =
      ∑' n : ℕ, scaledLagrangeCoefficient a n d := by
  unfold lagrangeInverseValue
  apply tsum_congr
  intro n
  exact
    (scaledLagrangeCoefficient_eq_inverseCoeff_mul_pow a d hd n).symm

/-- The negative natural scale inserts the alternating sign into the
scaled coefficient series. -/
theorem lagrangeInverseValue_neg_inverseMonomial_eq_tsum_signed_scaled
    {iota : Type*} [Fintype iota]
    (a d : iota → ℝ) (hd : d ∈ positiveCoordinates iota) :
    lagrangeInverseValue a d (-inverseMonomial a d) =
      ∑' n : ℕ, (-1 : ℝ) ^ n * scaledLagrangeCoefficient a n d := by
  unfold lagrangeInverseValue
  apply tsum_congr
  intro n
  rw [show -inverseMonomial a d =
      (-1 : ℝ) * inverseMonomial a d by ring, mul_pow,
    scaledLagrangeCoefficient_eq_inverseCoeff_mul_pow a d hd n]
  ring

/-- Whenever the full scaled coefficient sequence is summable, its odd
width series is exactly the positive inverse branch minus the negative
inverse branch. -/
theorem inverseWidthSeries_eq_inverseValue_sub_neg
    {iota : Type*} [Fintype iota]
    (a d : iota → ℝ) (hd : d ∈ positiveCoordinates iota)
    (hsum : Summable (fun n : ℕ ↦ scaledLagrangeCoefficient a n d)) :
    inverseWidthSeries a d =
      lagrangeInverseValue a d (inverseMonomial a d) -
        lagrangeInverseValue a d (-inverseMonomial a d) := by
  let coefficient : ℕ → ℝ :=
    fun n ↦ scaledLagrangeCoefficient a n d
  have hsum' : Summable coefficient := by
    simpa only [coefficient] using! hsum
  have hinjEven : Function.Injective (fun j : ℕ ↦ 2 * j) := by
    intro m n hmn
    exact Nat.eq_of_mul_eq_mul_left (by omega) hmn
  have hinjOdd : Function.Injective (fun j : ℕ ↦ 2 * j + 1) := by
    intro m n hmn
    exact Nat.eq_of_mul_eq_mul_left (by omega) (Nat.add_right_cancel hmn)
  have hEven : Summable (fun j ↦ coefficient (2 * j)) := by
    simpa only [Function.comp_apply] using! hsum'.comp_injective hinjEven
  have hOdd : Summable (fun j ↦ coefficient (2 * j + 1)) := by
    simpa only [Function.comp_apply] using! hsum'.comp_injective hinjOdd
  let signed : ℕ → ℝ := fun n ↦ (-1 : ℝ) ^ n * coefficient n
  have hSignedEven : Summable (fun j ↦ signed (2 * j)) := by
    simpa only [signed, pow_mul, neg_one_sq, one_pow, one_mul] using! hEven
  have hSignedOdd : Summable (fun j ↦ signed (2 * j + 1)) := by
    simpa [signed, pow_add, pow_mul] using! hOdd.neg
  have hsplit :
      (∑' j, coefficient (2 * j)) + (∑' j, coefficient (2 * j + 1)) =
        ∑' n, coefficient n :=
    tsum_even_add_odd hEven hOdd
  have hsplitSigned :
      (∑' j, signed (2 * j)) + (∑' j, signed (2 * j + 1)) =
        ∑' n, signed n :=
    tsum_even_add_odd hSignedEven hSignedOdd
  have hsignedEven :
      (∑' j, signed (2 * j)) = ∑' j, coefficient (2 * j) := by
    apply tsum_congr
    intro j
    simp [signed, pow_mul]
  have hsignedOdd :
      (∑' j, signed (2 * j + 1)) =
        -∑' j, coefficient (2 * j + 1) := by
    rw [← tsum_neg]
    apply tsum_congr
    intro j
    simp [signed, pow_add, pow_mul]
  rw [inverseWidthSeries,
    lagrangeInverseValue_inverseMonomial_eq_tsum_scaled a d hd,
    lagrangeInverseValue_neg_inverseMonomial_eq_tsum_signed_scaled a d hd]
  change 2 * ∑' j, coefficient (2 * j + 1) =
    (∑' n, coefficient n) - ∑' n, signed n
  rw [← hsplit, ← hsplitSigned, hsignedEven, hsignedOdd]
  ring

end

end Erdos1038
