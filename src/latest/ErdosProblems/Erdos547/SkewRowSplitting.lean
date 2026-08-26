import ErdosProblems.Erdos547.AllocationRestriction
import ErdosProblems.Erdos547.SeparatedRows

/-!
# Splitting a skew allocation by independently capping its outgoing rows
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] {G : SimpleGraph V} {γ : ℝ}

namespace SkewMatching

def scaleRows (σ : SkewMatching G γ) (t : V → ℝ)
    (ht : ∀ u, 0 ≤ t u) (ht1 : ∀ u, t u ≤ 1) : SkewMatching G γ :=
  σ.ofBoundedWeight (fun u v ↦ t u * σ.weight u v)
    (fun u v ↦ mul_nonneg (ht u) (σ.nonnegative u v))
    (fun u v ↦ (mul_le_mul_of_nonneg_right (ht1 u) (σ.nonnegative u v)).trans_eq (one_mul _))

theorem scaleRows_isSuballocation (σ : SkewMatching G γ) (t : V → ℝ)
    (ht : ∀ u, 0 ≤ t u) (ht1 : ∀ u, t u ≤ 1) :
    (σ.scaleRows t ht ht1).IsSuballocation σ := σ.ofBoundedWeight_isSuballocation _ _ _

theorem scaleRows_outLoad (σ : SkewMatching G γ) (t : V → ℝ)
    (ht : ∀ u, 0 ≤ t u) (ht1 : ∀ u, t u ≤ 1) (u : V) :
    (σ.scaleRows t ht ht1).outLoad u = t u * σ.outLoad u := by
  change (∑ v, t u * σ.weight u v) / (1 + γ) = _
  rw [← Finset.mul_sum]
  exact mul_div_assoc _ _ _

theorem load_sum_of_weight_sum (σ τ ρ : SkewMatching G γ)
    (h : ∀ u v, τ.weight u v + ρ.weight u v = σ.weight u v) (u : V) :
    τ.load u + ρ.load u = σ.load u := by
  have hout : τ.outLoad u + ρ.outLoad u = σ.outLoad u := by
    rw [outLoad, outLoad, ← add_div, ← Finset.sum_add_distrib]
    exact congrArg (fun r ↦ r / (1 + γ)) (Finset.sum_congr rfl fun v _ ↦ h u v)
  have hin : τ.inLoad u + ρ.inLoad u = σ.inLoad u := by
    rw [inLoad, inLoad, ← add_div, ← mul_add, ← Finset.sum_add_distrib]
    exact congrArg (fun r ↦ γ * r / (1 + γ)) (Finset.sum_congr rfl fun v _ ↦ h v u)
  change (τ.outLoad u + τ.inLoad u) + (ρ.outLoad u + ρ.inLoad u) = _
  change _ = σ.outLoad u + σ.inLoad u
  linarith

theorem exists_row_split (σ : SkewMatching G γ) (a : V → ℝ) (ha : ∀ u, 0 ≤ a u) :
    ∃ τ ρ : SkewMatching G γ, τ.IsSuballocation σ ∧ ρ.IsSuballocation σ ∧
      (∀ u, τ.outLoad u = min (a u) (σ.outLoad u)) ∧
      (∀ u v, τ.weight u v + ρ.weight u v = σ.weight u v) ∧
      ∀ u, τ.load u + ρ.load u = σ.load u := by
  let t := fun u ↦ min (a u) (σ.outLoad u) / σ.outLoad u
  have ht (u : V) : 0 ≤ t u := capped_ratio_nonneg (ha u) (σ.outLoad_nonneg u)
  have ht1 (u : V) : t u ≤ 1 := capped_ratio_le_one (σ.outLoad_nonneg u)
  let τ := σ.scaleRows t ht ht1
  let ρ := σ.scaleRows (fun u ↦ 1 - t u) (fun u ↦ by linarith [ht1 u])
    (fun u ↦ by linarith [ht u])
  have hweight (u v : V) : τ.weight u v + ρ.weight u v = σ.weight u v := by
    change t u * σ.weight u v + (1 - t u) * σ.weight u v = _
    ring
  refine ⟨τ, ρ, σ.scaleRows_isSuballocation t ht ht1,
    σ.scaleRows_isSuballocation (fun u ↦ 1 - t u) _ _, ?_, hweight,
    σ.load_sum_of_weight_sum τ ρ hweight⟩
  intro u
  rw [show τ.outLoad u = t u * σ.outLoad u from σ.scaleRows_outLoad t ht ht1 u]
  exact capped_ratio_mul (ha u) (σ.outLoad_nonneg u)

end SkewMatching

end Erdos547.DPRS

#print axioms Erdos547.DPRS.SkewMatching.exists_row_split
