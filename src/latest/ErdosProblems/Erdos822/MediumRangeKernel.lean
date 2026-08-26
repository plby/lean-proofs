/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos822.MediumRangeGcdMass
import ErdosProblems.Erdos822.WeightedCommonDivisorRanges

/-! # The unconditional medium-range weighted collision-kernel estimate -/

namespace Erdos822

open scoped BigOperators Classical
open Filter

theorem mediumGcdAnchorTerm_nonneg (N m m' : ℕ) : 0 ≤ mediumGcdAnchorTerm N m m' := by
  unfold mediumGcdAnchorTerm
  split_ifs <;> positivity

theorem exists_eventually_mediumWeightedCommonDivisorKernel_bound (S : ℕ) (C : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ N : ℕ in atTop, ∀ z y : ℕ, 2 ≤ z → z ≤ y →
      (Real.log (z : ℝ) / Real.log (y : ℝ)) ^ 2 *
        (∑ m ∈ gilCofactors N S C, ∑ m' ∈ (gilCofactors N S C).erase m,
          mediumWeightedCommonDivisorKernel N m m' z y) ≤ K * (N ^ 60 : ℕ) := by
  obtain ⟨D, hD, hbound⟩ := exists_logRatio_sq_mul_singularFactor_upper
  refine ⟨4 * D ^ 2, by positivity, ?_⟩
  filter_upwards [eventually_sum_mediumGcdAnchorTerm_le S C] with N hN
  intro z y hz hzy
  have hpoint (m m' : ℕ) :
      (Real.log (z : ℝ) / Real.log (y : ℝ)) ^ 2 *
        mediumWeightedCommonDivisorKernel N m m' z y ≤
      (N ^ 60 : ℕ) * D ^ 2 * (mediumGcdAnchorTerm N m m' / m') := by
    unfold mediumWeightedCommonDivisorKernel mediumGcdAnchorTerm
    split_ifs with h
    · calc
        _ = ((N ^ 60 : ℕ) * ((shiftedCoefficientGcd m m' : ℝ) / (m * m' : ℕ))) *
            ((Real.log (z : ℝ) / Real.log (y : ℝ)) ^ 2 *
              Erdos851.singularFactor (reducedTotientDet m m') z y) := by
          push_cast
          ring
        _ ≤ ((N ^ 60 : ℕ) * ((shiftedCoefficientGcd m m' : ℝ) / (m * m' : ℕ))) * D ^ 2 :=
          mul_le_mul_of_nonneg_left (hbound _ z y hz hzy) (by positivity)
        _ = _ := by push_cast; ring
    · simp
  have hsum : (∑ m ∈ gilCofactors N S C, ∑ m' ∈ (gilCofactors N S C).erase m,
      mediumGcdAnchorTerm N m m' / m') ≤ 4 := by
    calc
      _ ≤ ∑ m ∈ gilCofactors N S C, ∑ m' ∈ gilCofactors N S C,
          mediumGcdAnchorTerm N m m' / m' := by
        apply Finset.sum_le_sum
        intro m hm
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
          (fun m' hm' hnot ↦ div_nonneg (mediumGcdAnchorTerm_nonneg N m m') (by positivity))
      _ = ∑ m' ∈ gilCofactors N S C, ∑ m ∈ gilCofactors N S C,
          mediumGcdAnchorTerm N m m' / m' := Finset.sum_comm
      _ ≤ 4 := hN
  calc
    _ = ∑ m ∈ gilCofactors N S C, ∑ m' ∈ (gilCofactors N S C).erase m,
        (Real.log (z : ℝ) / Real.log (y : ℝ)) ^ 2 *
          mediumWeightedCommonDivisorKernel N m m' z y := by simp only [Finset.mul_sum]
    _ ≤ ∑ m ∈ gilCofactors N S C, ∑ m' ∈ (gilCofactors N S C).erase m,
        (N ^ 60 : ℕ) * D ^ 2 * (mediumGcdAnchorTerm N m m' / m') :=
      Finset.sum_le_sum fun m hm ↦ Finset.sum_le_sum fun m' hm' ↦ hpoint m m'
    _ = ((N ^ 60 : ℕ) * D ^ 2) *
        (∑ m ∈ gilCofactors N S C, ∑ m' ∈ (gilCofactors N S C).erase m,
          mediumGcdAnchorTerm N m m' / m') := by simp only [Finset.mul_sum]
    _ ≤ ((N ^ 60 : ℕ) * D ^ 2) * 4 := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by ring

#print axioms exists_eventually_mediumWeightedCommonDivisorKernel_bound

end Erdos822
