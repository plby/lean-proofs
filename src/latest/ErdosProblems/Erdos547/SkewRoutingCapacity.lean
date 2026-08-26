import ErdosProblems.Erdos547.AllocationOperations

/-!
# Converting skew weights to routed far-class capacities
-/

namespace Erdos547.DPRS.SkewMatching

open Finset SimpleGraph
open scoped BigOperators

variable {I : Type*} [Fintype I] {G : SimpleGraph I} {γ : ℝ}

noncomputable def arcCapacity (σ : SkewMatching G γ) (M : ℝ) (i j : I) : ℝ :=
  M * γ * σ.weight i j / (1 + γ)

theorem arcCapacity_nonneg (σ : SkewMatching G γ) {M : ℝ} (hM : 0 ≤ M) (i j : I) :
    0 ≤ σ.arcCapacity M i j :=
  div_nonneg (mul_nonneg (mul_nonneg hM σ.skew_nonneg) (σ.nonnegative i j)) σ.denominator_pos.le

theorem arcCapacity_row (σ : SkewMatching G γ) (M : ℝ) (i : I) :
    (∑ j, σ.arcCapacity M i j) = M * γ * σ.outLoad i := by
  simp only [arcCapacity, outLoad, ← Finset.sum_div, ← Finset.mul_sum]
  ring

theorem arcCapacity_column (σ : SkewMatching G γ) (M : ℝ) (j : I) :
    (∑ i, σ.arcCapacity M i j) = M * σ.inLoad j := by
  simp only [arcCapacity, inLoad, ← Finset.sum_div, ← Finset.mul_sum]
  ring

theorem arcCapacity_supported (σ : SkewMatching G γ) (M : ℝ) (i j : I)
    (h : 0 < σ.arcCapacity M i j) : G.Adj i j := by
  by_contra hn
  have hz := σ.supported i j hn
  simp only [arcCapacity, hz, mul_zero, zero_div, lt_self_iff_false] at h

theorem arcCapacity_row_pos (σ : SkewMatching G γ) {M : ℝ} (hM : 0 < M)
    (hγ : 0 < γ) (i : I) (hi : 0 < σ.outLoad i) : 0 < ∑ j, σ.arcCapacity M i j := by
  rw [σ.arcCapacity_row]
  exact mul_pos (mul_pos hM hγ) hi

end Erdos547.DPRS.SkewMatching

namespace Erdos547.DPRS

open Finset SimpleGraph
open scoped BigOperators

variable {I C : Type*} [Fintype I] [Fintype C] {G : SimpleGraph I} {γ : C → ℝ}

noncomputable def familyCapacity (σ : ∀ c, SkewMatching G (γ c)) (M : ℝ) (a : C × I) (j : I) : ℝ :=
  (σ a.1).arcCapacity M a.2 j

theorem familyCapacity_column (σ : ∀ c, SkewMatching G (γ c)) (M : ℝ) (j : I) :
    (∑ a, familyCapacity σ M a j) = M * ∑ c, (σ c).inLoad j := by
  rw [Fintype.sum_prod_type]
  simp only [familyCapacity, SkewMatching.arcCapacity_column, Finset.mul_sum]

theorem familyCapacity_budget (σ : ∀ c, SkewMatching G (γ c)) (M demand : ℝ)
    (hM : 0 ≤ M) (j : I) (hload : (∑ c, (σ c).load j) ≤ 1)
    (hnear : demand ≤ M * ∑ c, (σ c).outLoad j) :
    demand + (∑ a, familyCapacity σ M a j) ≤ M := by
  rw [familyCapacity_column]
  have hh := mul_le_mul_of_nonneg_left hload hM
  simp only [SkewMatching.load, Finset.sum_add_distrib, mul_add, mul_one] at hh
  linarith only [hh, hnear]

end Erdos547.DPRS

#print axioms Erdos547.DPRS.familyCapacity_budget
