/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos822.LargeRangeGcdMass
import ErdosProblems.Erdos822.OrderedSymmetricSum
import ErdosProblems.Erdos822.WeightedCommonDivisorRanges

/-! # The unconditional large-range weighted collision-kernel estimate -/

namespace Erdos822

open scoped BigOperators Classical
open Filter

noncomputable def largeGcdMassKernel (N m m' : ℕ) : ℝ :=
  if (outerCollisionPairs (N ^ 60) m m').Nonempty ∧
      N ^ 20 < shiftedCoefficientGcd m m' then
    (shiftedCoefficientGcd m m' : ℝ) / (m * m' : ℕ)
  else 0

theorem outerCollisionPairs_nonempty_comm (x m m' : ℕ) :
    (outerCollisionPairs x m m').Nonempty ↔ (outerCollisionPairs x m' m).Nonempty := by
  rw [← Finset.card_pos, outerCollisionPairs_card_comm x m m', Finset.card_pos]

theorem largeGcdMassKernel_comm (N m m' : ℕ) :
    largeGcdMassKernel N m m' = largeGcdMassKernel N m' m := by
  unfold largeGcdMassKernel
  simp only [outerCollisionPairs_nonempty_comm (N ^ 60) m m',
    shiftedCoefficientGcd_comm m m', Nat.mul_comm m m']

theorem largeGcdMassKernel_nonneg (N m m' : ℕ) : 0 ≤ largeGcdMassKernel N m m' := by
  unfold largeGcdMassKernel
  split_ifs <;> positivity

theorem sum_largeGcdMassKernel_eq_twice_anchor (N S : ℕ) (C : ℝ) :
    (∑ m ∈ gilCofactors N S C, ∑ m' ∈ (gilCofactors N S C).erase m,
      largeGcdMassKernel N m m') =
      2 * ∑ m' ∈ gilCofactors N S C, ∑ m ∈ largeAboveAnchor N S C m',
        (shiftedCoefficientGcd m m' : ℝ) / (m * m' : ℕ) := by
  rw [sum_erase_symmetric_eq_twice_ordered _ _ (largeGcdMassKernel_comm N)]
  congr 1
  apply Finset.sum_congr rfl
  intro m' hm'
  rw [largeAboveAnchor, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro m hm
  rw [largeGcdMassKernel_comm N m' m]
  unfold largeGcdMassKernel
  by_cases hlt : m' < m <;>
    by_cases hne : (outerCollisionPairs (N ^ 60) m m').Nonempty <;>
    by_cases hg : N ^ 20 < shiftedCoefficientGcd m m' <;> simp [hlt, hne, hg]

theorem eventually_sum_largeGcdMassKernel_le (S : ℕ) (C : ℝ) :
    ∀ᶠ N : ℕ in atTop,
      (∑ m ∈ gilCofactors N S C, ∑ m' ∈ (gilCofactors N S C).erase m,
        largeGcdMassKernel N m m') ≤ 46 := by
  filter_upwards [eventually_sum_largeAboveAnchor_weight_le S C] with N hN
  rw [sum_largeGcdMassKernel_eq_twice_anchor]
  linarith

theorem exists_eventually_largeWeightedCommonDivisorKernel_bound (S : ℕ) (C : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ N : ℕ in atTop, ∀ z y : ℕ, 2 ≤ z → z ≤ y →
      (Real.log (z : ℝ) / Real.log (y : ℝ)) ^ 2 *
        (∑ m ∈ gilCofactors N S C, ∑ m' ∈ (gilCofactors N S C).erase m,
          largeWeightedCommonDivisorKernel N m m' z y) ≤ K * (N ^ 60 : ℕ) := by
  obtain ⟨D, hD, hbound⟩ := exists_logRatio_sq_mul_singularFactor_upper
  refine ⟨46 * D ^ 2, by positivity, ?_⟩
  filter_upwards [eventually_sum_largeGcdMassKernel_le S C] with N hN
  intro z y hz hzy
  have hpoint (m m' : ℕ) :
      (Real.log (z : ℝ) / Real.log (y : ℝ)) ^ 2 *
        largeWeightedCommonDivisorKernel N m m' z y ≤
      (N ^ 60 : ℕ) * D ^ 2 * largeGcdMassKernel N m m' := by
    unfold largeWeightedCommonDivisorKernel largeGcdMassKernel
    split_ifs with h
    · calc
        _ = ((N ^ 60 : ℕ) * ((shiftedCoefficientGcd m m' : ℝ) / (m * m' : ℕ))) *
            ((Real.log (z : ℝ) / Real.log (y : ℝ)) ^ 2 *
              Erdos851.singularFactor (reducedTotientDet m m') z y) := by
          push_cast
          ring
        _ ≤ ((N ^ 60 : ℕ) * ((shiftedCoefficientGcd m m' : ℝ) / (m * m' : ℕ))) * D ^ 2 :=
          mul_le_mul_of_nonneg_left (hbound _ z y hz hzy) (by positivity)
        _ = _ := by ring
    · simp
  calc
    _ = ∑ m ∈ gilCofactors N S C, ∑ m' ∈ (gilCofactors N S C).erase m,
        (Real.log (z : ℝ) / Real.log (y : ℝ)) ^ 2 *
          largeWeightedCommonDivisorKernel N m m' z y := by simp only [Finset.mul_sum]
    _ ≤ ∑ m ∈ gilCofactors N S C, ∑ m' ∈ (gilCofactors N S C).erase m,
        (N ^ 60 : ℕ) * D ^ 2 * largeGcdMassKernel N m m' :=
      Finset.sum_le_sum fun m hm ↦ Finset.sum_le_sum fun m' hm' ↦ hpoint m m'
    _ = ((N ^ 60 : ℕ) * D ^ 2) *
        (∑ m ∈ gilCofactors N S C, ∑ m' ∈ (gilCofactors N S C).erase m,
          largeGcdMassKernel N m m') := by simp only [Finset.mul_sum]
    _ ≤ ((N ^ 60 : ℕ) * D ^ 2) * 46 := mul_le_mul_of_nonneg_left hN (by positivity)
    _ = _ := by ring

#print axioms exists_eventually_largeWeightedCommonDivisorKernel_bound

end Erdos822
