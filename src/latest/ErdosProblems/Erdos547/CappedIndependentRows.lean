import ErdosProblems.Erdos547.BipartiteDirected
import ErdosProblems.Erdos547.BoundedFractional

/-!
# Capping a fractional matching on independent rows

Edges with neither endpoint in the selected set are discarded. Every
selected row receives exactly its prescribed capped allowance.
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

namespace FractionalMatching

theorem directedWeight_self_symmetric (μ : FractionalMatching G) (U : Finset V)
    (t : V → ℝ) (u v : V) : μ.directedWeight U t t u v = μ.directedWeight U t t v u := by
  rw [directedWeight, directedWeight, μ.symmetric v u]
  exact add_comm _ _

theorem independent_directedWeight_le (μ : FractionalMatching G) (U : Finset V)
    (hU : ∀ u ∈ U, ∀ v ∈ U, μ.weight u v = 0) (t : V → ℝ) (ht : ∀ u, t u ≤ 1)
    (u v : V) : μ.directedWeight U t t u v ≤ μ.weight u v := by
  rw [directedWeight]
  by_cases hu : u ∈ U
  · rw [if_pos hu]
    by_cases hv : v ∈ U
    · rw [if_pos hv, hU u hu v hv, mul_zero, mul_zero, add_zero]
    · rw [if_neg hv, add_zero]
      exact (mul_le_mul_of_nonneg_right (ht u) (μ.nonnegative u v)).trans_eq (one_mul _)
  · rw [if_neg hu, zero_add]
    by_cases hv : v ∈ U
    · rw [if_pos hv]
      exact (mul_le_mul_of_nonneg_right (ht v) (μ.nonnegative u v)).trans_eq (one_mul _)
    · rw [if_neg hv]
      exact μ.nonnegative u v

def capIndependent (μ : FractionalMatching G) (U : Finset V)
    (hU : ∀ u ∈ U, ∀ v ∈ U, μ.weight u v = 0) (a : V → ℝ) (ha : ∀ u, 0 ≤ a u) :
    FractionalMatching G :=
  let t := fun u ↦ min (a u) (μ.load u) / μ.load u
  μ.ofBoundedWeight (μ.directedWeight U t t)
    (μ.directedWeight_self_symmetric U t)
    (μ.directedWeight_nonneg U t t
      (fun u ↦ capped_ratio_nonneg (ha u) (μ.load_nonneg u))
      (fun u ↦ capped_ratio_nonneg (ha u) (μ.load_nonneg u)))
    (μ.independent_directedWeight_le U hU t (fun u ↦ capped_ratio_le_one (μ.load_nonneg u)))

theorem capIndependent_weight_le (μ : FractionalMatching G) (U : Finset V)
    (hU : ∀ u ∈ U, ∀ v ∈ U, μ.weight u v = 0) (a : V → ℝ) (ha : ∀ u, 0 ≤ a u)
    (u v : V) : (μ.capIndependent U hU a ha).weight u v ≤ μ.weight u v :=
  μ.independent_directedWeight_le U hU _ (fun u ↦ capped_ratio_le_one (μ.load_nonneg u)) u v

theorem capIndependent_load (μ : FractionalMatching G) (U : Finset V)
    (hU : ∀ u ∈ U, ∀ v ∈ U, μ.weight u v = 0) (a : V → ℝ) (ha : ∀ u, 0 ≤ a u)
    {u : V} (hu : u ∈ U) : (μ.capIndependent U hU a ha).load u = min (a u) (μ.load u) := by
  let t := fun u ↦ min (a u) (μ.load u) / μ.load u
  have hrow (v : V) : μ.directedWeight U t t u v = t u * μ.weight u v := by
    rw [directedWeight, if_pos hu]
    by_cases hv : v ∈ U
    · rw [if_pos hv, hU u hu v hv, mul_zero, mul_zero, add_zero]
    · rw [if_neg hv, add_zero]
  change (∑ v, μ.directedWeight U t t u v) = _
  simp only [hrow, ← Finset.mul_sum]
  exact capped_ratio_mul (ha u) (μ.load_nonneg u)

theorem capIndependent_total (μ : FractionalMatching G) (U : Finset V)
    (hU : ∀ u ∈ U, ∀ v ∈ U, μ.weight u v = 0) (a : V → ℝ) (ha : ∀ u, 0 ≤ a u) :
    (μ.capIndependent U hU a ha).total = ∑ u ∈ U, min (a u) (μ.load u) := by
  let t := fun u ↦ min (a u) (μ.load u) / μ.load u
  change (∑ u, ∑ v, μ.directedWeight U t t u v) / 2 = _
  rw [μ.directedWeight_total, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro u _
  calc
    (t u + t u) * μ.load u / 2 = t u * μ.load u := by ring
    _ = _ := capped_ratio_mul (ha u) (μ.load_nonneg u)

theorem capIndependent_runsBetween (μ : FractionalMatching G) (U : Finset V)
    (hU : ∀ u ∈ U, ∀ v ∈ U, μ.weight u v = 0) (a : V → ℝ) (ha : ∀ u, 0 ≤ a u) :
    (μ.capIndependent U hU a ha).RunsBetween U Uᶜ := by
  intro u v hp
  have hpositive : 0 < μ.weight u v := hp.trans_le (μ.capIndependent_weight_le U hU a ha u v)
  by_cases hu : u ∈ U
  · left
    refine ⟨hu, Finset.mem_compl.mpr ?_⟩
    intro hv
    rw [hU u hu v hv] at hpositive
    exact (lt_irrefl 0) hpositive
  · right
    refine ⟨Finset.mem_compl.mpr hu, ?_⟩
    by_contra hv
    simp only [capIndependent, ofBoundedWeight, directedWeight,
      if_neg hu, if_neg hv, add_zero] at hp
    exact (lt_irrefl 0) hp

end FractionalMatching

end Erdos547.DPRS

#print axioms Erdos547.DPRS.FractionalMatching.capIndependent_load
#print axioms Erdos547.DPRS.FractionalMatching.capIndependent_total
