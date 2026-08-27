/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTCommonCoefficients
import ErdosProblems.Erdos4b.FGKMTPrimeUniverse

/-!
# The literal common presieved weight

The coefficient vector depends on the dimension, modulus and sieve
radius, not on the label prime. The weight is its finite divisibility
sum squared, with the original support and small-prime indicator.
-/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

open scoped Classical in
def commonDivisorWeight {α : Type*} [DecidableEq α] [Fintype α]
    (k R : ℕ) (p : α → ℕ) (forms : Fin k → ℤ) : ℝ :=
  (∑ d : α → Option (Fin k),
    if ∀ i, (assignmentPrimeTuple p d i : ℤ) ∣ forms i then commonSieveCoefficient k R p d
    else 0) ^ 2

theorem commonDivisorWeight_nonneg {α : Type*} [DecidableEq α] [Fintype α]
    (k R : ℕ) (p : α → ℕ) (forms : Fin k → ℤ) :
    0 ≤ commonDivisorWeight k R p forms := sq_nonneg _

theorem commonDivisorWeight_eq_quadratic {α : Type*} [DecidableEq α] [Fintype α]
    (k R : ℕ) (p : α → ℕ) (forms : Fin k → ℤ) :
    commonDivisorWeight k R p forms =
      ∑ d : α → Option (Fin k), ∑ e : α → Option (Fin k),
        if (∀ i, (assignmentPrimeTuple p d i : ℤ) ∣ forms i) ∧
            (∀ i, (assignmentPrimeTuple p e i : ℤ) ∣ forms i) then
          commonSieveCoefficient k R p d * commonSieveCoefficient k R p e
        else 0 := by
  classical
  unfold commonDivisorWeight
  rw [pow_two, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d _hd
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _he
  by_cases hd : ∀ i, (assignmentPrimeTuple p d i : ℤ) ∣ forms i <;>
    by_cases he : ∀ i, (assignmentPrimeTuple p e i : ℤ) ∣ forms i <;> simp [hd, he]

open scoped Classical in
def commonPrimeSieveWeight (k W M R : ℕ) (y : ℝ) (h : Fin k → ℕ) (p : ℕ) (n : ℤ) : ℝ :=
  if |(n : ℝ)| ≤ y ∧ (∏ i, (n + (h i : ℤ) * p).natAbs).Coprime W then
    commonDivisorWeight k R (fun q : commonPrimeUniverse M R => q.val)
      (fun i => n + (h i : ℤ) * p)
  else 0

theorem commonPrimeSieveWeight_nonneg (k W M R : ℕ) (y : ℝ) (h : Fin k → ℕ)
    (p : ℕ) (n : ℤ) : 0 ≤ commonPrimeSieveWeight k W M R y h p n := by
  unfold commonPrimeSieveWeight
  split_ifs
  · exact commonDivisorWeight_nonneg _ _ _ _
  · exact le_rfl

theorem commonPrimeSieveWeight_zero_of_outside (k W M R : ℕ) (y : ℝ) (h : Fin k → ℕ)
    (p : ℕ) (n : ℤ) (hn : y < |(n : ℝ)|) : commonPrimeSieveWeight k W M R y h p n = 0 := by
  unfold commonPrimeSieveWeight
  exact if_neg (fun hh => (not_le_of_gt hn) hh.1)

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.commonDivisorWeight_eq_quadratic
#print axioms Erdos4b.FGKMT.commonPrimeSieveWeight_nonneg
