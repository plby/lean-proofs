import ErdosProblems.Erdos547.AllocationComparison

/-!
# Extracting a fractional matching from an allocation of skew at least one
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] {G : SimpleGraph V} {γ : ℝ}

namespace SkewMatching

def extractFractional (σ : SkewMatching G γ) (hγ : 1 ≤ γ) : FractionalMatching G where
  weight u v := (σ.weight u v + σ.weight v u) / (1 + γ)
  symmetric u v := by rw [add_comm (σ.weight u v)]
  nonnegative u v := div_nonneg (add_nonneg (σ.nonnegative u v) (σ.nonnegative v u))
    σ.denominator_pos.le
  supported u v huv := by
    rw [σ.supported u v huv, σ.supported v u (fun hvu ↦ huv hvu.symm)]
    simp only [add_zero, zero_div]
  capacity u := by
    rw [← Finset.sum_div, Finset.sum_add_distrib]
    apply (div_le_one σ.denominator_pos).mpr
    have hcol : 0 ≤ ∑ v, σ.weight v u := Finset.sum_nonneg fun v _ ↦ σ.nonnegative v u
    have hh := mul_le_mul_of_nonneg_right hγ hcol
    linarith [σ.capacity u]

theorem extractFractional_dominated (σ : SkewMatching G γ) (hγ : 1 ≤ γ) :
    (σ.extractFractional hγ).DominatedBySkew σ := by
  intro u v
  apply div_le_div_of_nonneg_right _ σ.denominator_pos.le
  have hh := mul_le_mul_of_nonneg_right hγ (σ.nonnegative v u)
  change σ.weight u v + σ.weight v u ≤ σ.weight u v + γ * σ.weight v u
  linarith

theorem extractFractional_load (σ : SkewMatching G γ) (hγ : 1 ≤ γ) (u : V) :
    (σ.extractFractional hγ).load u = σ.outLoad u + (∑ v, σ.weight v u) / (1 + γ) := by
  simp only [FractionalMatching.load, extractFractional, ← Finset.sum_div,
    Finset.sum_add_distrib, outLoad, add_div]

theorem extractFractional_total (σ : SkewMatching G γ) (hγ : 1 ≤ γ) :
    (σ.extractFractional hγ).total = σ.total / (1 + γ) := by
  have hh := (σ.extractFractional hγ).sum_load
  simp only [extractFractional_load, Finset.sum_add_distrib, σ.sum_outLoad,
    ← Finset.sum_div] at hh
  have hrev : (∑ u, ∑ v, σ.weight v u) = σ.total := Finset.sum_comm
  rw [hrev] at hh
  linarith

theorem extractFractional_load_eq_outLoad (σ : SkewMatching G γ) (hγ : 1 ≤ γ)
    (u : V) (hzero : ∀ v, σ.weight v u = 0) :
    (σ.extractFractional hγ).load u = σ.outLoad u := by
  rw [extractFractional_load]
  simp only [hzero, Finset.sum_const_zero, zero_div, add_zero]

end SkewMatching

end Erdos547.DPRS

#print axioms Erdos547.DPRS.SkewMatching.extractFractional_total
