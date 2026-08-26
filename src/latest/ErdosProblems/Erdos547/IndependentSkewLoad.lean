import ErdosProblems.Erdos547.SkewBipartiteSupport

/-!
# Bounding the load of an allocation on a set with no internal supporting arcs
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] {G : SimpleGraph V} {γ : ℝ}

theorem SkewMatching.sum_load_independent_le (σ : SkewMatching G γ) (U : Finset V)
    (hzero : ∀ u ∈ U, ∀ v ∈ U, σ.weight u v = 0) :
    (∑ u ∈ U, σ.load u) ≤ max 1 γ * σ.total / (1 + γ) := by
  classical
  let A := ∑ u ∈ U, ∑ v, σ.weight u v
  let B := ∑ u ∈ U, ∑ v, σ.weight v u
  have hA : 0 ≤ A := Finset.sum_nonneg fun u _ ↦
    Finset.sum_nonneg fun v _ ↦ σ.nonnegative u v
  have hB : 0 ≤ B := Finset.sum_nonneg fun u _ ↦
    Finset.sum_nonneg fun v _ ↦ σ.nonnegative v u
  have hsum : A + B ≤ σ.total := by
    have heA : A = ∑ u, ∑ v, if u ∈ U then σ.weight u v else 0 := by
      simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_mem_eq, A]
    have heB : B = ∑ u, ∑ v, if v ∈ U then σ.weight u v else 0 := by
      rw [Finset.sum_comm]
      simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_mem_eq, B]
    rw [heA, heB, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro u _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro v _
    by_cases hu : u ∈ U <;> by_cases hv : v ∈ U
    · rw [if_pos hu, if_pos hv, hzero u hu v hv]
      norm_num
    · rw [if_pos hu, if_neg hv, add_zero]
    · rw [if_neg hu, if_pos hv, zero_add]
    · rw [if_neg hu, if_neg hv, add_zero]
      exact σ.nonnegative u v
  have hload : (∑ u ∈ U, σ.load u) = (A + γ * B) / (1 + γ) := by
    simp only [SkewMatching.load, SkewMatching.outLoad, SkewMatching.inLoad,
      Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.mul_sum, A, B, add_div]
  rw [hload]
  apply div_le_div_of_nonneg_right _ σ.denominator_pos.le
  have h₁ := mul_le_mul_of_nonneg_right (le_max_left (1 : ℝ) γ) hA
  have h₂ := mul_le_mul_of_nonneg_right (le_max_right (1 : ℝ) γ) hB
  have h₃ := mul_le_mul_of_nonneg_left hsum (le_trans zero_le_one (le_max_left (1 : ℝ) γ))
  nlinarith

end Erdos547.DPRS

#print axioms Erdos547.DPRS.SkewMatching.sum_load_independent_le
