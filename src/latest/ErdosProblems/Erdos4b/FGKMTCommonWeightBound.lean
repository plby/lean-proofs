/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTCommonCoefficientBound
import ErdosProblems.Erdos4b.FGKMTCommonWeights

/-!
# Pointwise bound for the literal presieved weight

No divisibility or small-prime indicator is discarded from the definition.
The absolute value of any selected coefficient sum is at most its full
l1 norm, giving the same uniform squared envelope for every integer.
-/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

theorem commonDivisorWeight_le_l1_sq {α : Type*} [DecidableEq α] [Fintype α]
    (k R : ℕ) (p : α → ℕ) (forms : Fin k → ℤ) :
    commonDivisorWeight k R p forms ≤ (∑ d, |commonSieveCoefficient k R p d|) ^ 2 := by
  classical
  let f := fun d : α → Option (Fin k) =>
    if ∀ i, (assignmentPrimeTuple p d i : ℤ) ∣ forms i then commonSieveCoefficient k R p d
    else 0
  have habs : |∑ d, f d| ≤ ∑ d, |commonSieveCoefficient k R p d| := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum ?_)
    intro d _hd
    dsimp only [f]
    split_ifs
    · exact le_rfl
    · simpa only [abs_zero] using abs_nonneg (commonSieveCoefficient k R p d)
  change (∑ d, f d) ^ 2 ≤ _
  rw [← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) habs 2

theorem commonDivisorWeight_le_radius_envelope {α : Type*} [DecidableEq α] [Fintype α]
    {k R : ℕ} {p : α → ℕ} (hk : 2 ≤ k) (hp : ∀ q, (p q).Prime)
    (hinj : Function.Injective p) (hlarge : ∀ q, 2 * k ^ 2 < p q) (hR : 1 < R)
    (forms : Fin k → ℤ) :
    commonDivisorWeight k R p forms ≤ (R : ℝ) ^ 3 * (1 + Real.log R) ^ (2 * k) :=
  (commonDivisorWeight_le_l1_sq k R p forms).trans
    (commonSieveCoefficient_l1_sq_le hk hp hinj hlarge hR)

theorem commonPrimeSieveWeight_le_radius_envelope {k W M R : ℕ}
    (hk : 2 ≤ k) (hR : 1 < R)
    (hsmall : ∀ q : ℕ, q.Prime → q ≤ 2 * k ^ 2 → q ∣ M)
    (y : ℝ) (h : Fin k → ℕ) (p : ℕ) (n : ℤ) :
    commonPrimeSieveWeight k W M R y h p n ≤
      (R : ℝ) ^ 3 * (1 + Real.log R) ^ (2 * k) := by
  unfold commonPrimeSieveWeight
  split_ifs
  · exact commonDivisorWeight_le_radius_envelope hk commonPrimeUniverse_prime
      Subtype.val_injective (commonPrimeUniverse_large hsmall) hR _
  · positivity

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.commonPrimeSieveWeight_le_radius_envelope
