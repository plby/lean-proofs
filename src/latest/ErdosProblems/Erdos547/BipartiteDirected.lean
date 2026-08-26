import ErdosProblems.Erdos547.BipartiteFractional

/-!
# Vertex-dependent orientations of a bipartite fractional matching
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

namespace FractionalMatching

def directedWeight (μ : FractionalMatching G) (U : Finset V) (f g : V → ℝ) (u v : V) : ℝ :=
  (if u ∈ U then f u * μ.weight u v else 0) + (if v ∈ U then g v * μ.weight u v else 0)

theorem directedWeight_nonneg (μ : FractionalMatching G) (U : Finset V) (f g : V → ℝ)
    (hf : ∀ u, 0 ≤ f u) (hg : ∀ u, 0 ≤ g u) (u v : V) :
    0 ≤ μ.directedWeight U f g u v := by
  apply add_nonneg <;> split_ifs
  · exact mul_nonneg (hf u) (μ.nonnegative u v)
  · exact le_rfl
  · exact mul_nonneg (hg v) (μ.nonnegative u v)
  · exact le_rfl

theorem directedWeight_total (μ : FractionalMatching G) (U : Finset V) (f g : V → ℝ) :
    (∑ u, ∑ v, μ.directedWeight U f g u v) = ∑ u ∈ U, (f u + g u) * μ.load u := by
  change (∑ u, ∑ v, ((if u ∈ U then f u * μ.weight u v else 0) +
    (if v ∈ U then g v * μ.weight u v else 0))) = _
  simp only [Finset.sum_add_distrib]
  have hfirst : (∑ u, ∑ v, if u ∈ U then f u * μ.weight u v else 0) =
      ∑ u, if u ∈ U then f u * μ.load u else 0 := by
    apply Finset.sum_congr rfl
    intro u _
    by_cases hu : u ∈ U
    · simp only [if_pos hu, ← Finset.mul_sum, load]
    · simp only [if_neg hu, Finset.sum_const_zero]
  have hsecond : (∑ u, ∑ v, if v ∈ U then g v * μ.weight u v else 0) =
      ∑ v, if v ∈ U then g v * μ.load v else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro v _
    by_cases hv : v ∈ U
    · simp only [if_pos hv, μ.symmetric _ v, ← Finset.mul_sum, load]
    · simp only [if_neg hv, Finset.sum_const_zero]
  rw [hfirst, hsecond, Finset.sum_ite_mem_eq, Finset.sum_ite_mem_eq, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro u _
  ring

omit [DecidableEq V] in
theorem Crosses.weight_zero_same {μ : FractionalMatching G} {U : Finset V}
    (h : μ.Crosses U) {u v : V} (hu : u ∈ U) (hv : v ∈ U) : μ.weight u v = 0 := by
  apply le_antisymm _ (μ.nonnegative u v)
  exact le_of_not_gt fun hp ↦ ((h u v hp).mp hu) hv

theorem Crosses.directedWeight_of_mem {μ : FractionalMatching G} {U : Finset V}
    (h : μ.Crosses U) (f g : V → ℝ) {u : V} (hu : u ∈ U) (v : V) :
    μ.directedWeight U f g u v = f u * μ.weight u v := by
  rw [directedWeight, if_pos hu]
  by_cases hv : v ∈ U
  · rw [h.weight_zero_same hu hv, mul_zero, mul_zero, if_pos hv, add_zero]
  · rw [if_neg hv, add_zero]

theorem Crosses.directedWeight_reverse_of_mem {μ : FractionalMatching G} {U : Finset V}
    (h : μ.Crosses U) (f g : V → ℝ) {u : V} (hu : u ∈ U) (v : V) :
    μ.directedWeight U f g v u = g u * μ.weight v u := by
  rw [directedWeight, if_pos hu]
  by_cases hv : v ∈ U
  · rw [h.weight_zero_same hv hu, mul_zero, mul_zero, if_pos hv, add_zero]
  · rw [if_neg hv, zero_add]

theorem Crosses.directedWeight_endpoint {μ : FractionalMatching G} {U : Finset V}
    (h : μ.Crosses U) (f g : V → ℝ) (γ : ℝ) (u v : V) :
    (μ.directedWeight U f g u v + γ * μ.directedWeight U f g v u) / (1 + γ) =
      (if u ∈ U then (f u + γ * g u) / (1 + γ) else
        (g v + γ * f v) / (1 + γ)) * μ.weight u v := by
  by_cases hu : u ∈ U
  · rw [h.directedWeight_of_mem f g hu, h.directedWeight_reverse_of_mem f g hu,
      μ.symmetric v u, if_pos hu]
    ring
  · rw [if_neg hu]
    by_cases hv : v ∈ U
    · rw [h.directedWeight_of_mem f g hv, h.directedWeight_reverse_of_mem f g hv,
        μ.symmetric v u]
      ring
    · have hz : μ.weight u v = 0 := by
        apply le_antisymm _ (μ.nonnegative u v)
        exact le_of_not_gt fun hp ↦ hu ((h u v hp).mpr hv)
      simp only [directedWeight, if_neg hu, if_neg hv, add_zero, mul_zero, zero_div, hz]

end FractionalMatching

end Erdos547.DPRS

#print axioms Erdos547.DPRS.FractionalMatching.directedWeight_total
