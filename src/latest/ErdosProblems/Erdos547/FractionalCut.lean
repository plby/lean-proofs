import ErdosProblems.Erdos547.FractionalReplacement

/-!
# Load lost when a fractional matching is restricted to a vertex set
-/

noncomputable section

namespace Erdos547.DPRS.FractionalMatching

open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

omit [DecidableEq V] in
theorem inside_load_le (μ : FractionalMatching G) (U : Set V) (u : V) :
    (μ.inside U).load u ≤ μ.load u :=
  (μ.inside U).load_le_of_weight_le μ (μ.inside_weight_le U) u

omit [DecidableEq V] in
theorem inside_load_eq_sum (μ : FractionalMatching G) (U : Finset V) {u : V}
    (hu : u ∈ U) : (μ.inside (U : Set V)).load u = ∑ v ∈ U, μ.weight u v := by
  classical
  calc
    _ = ∑ v ∈ U, (μ.inside (U : Set V)).weight u v := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      exact fun v _ hv ↦ μ.inside_weight_of_notMem (Or.inr hv)
    _ = _ := Finset.sum_congr rfl fun v hv ↦ μ.inside_weight_of_mem hu hv

open scoped Classical in
theorem inside_load_add_boundary (μ : FractionalMatching G) (U : Finset V) {u : V}
    (hu : u ∈ U) :
    (μ.inside (U : Set V)).load u + (∑ v ∈ Uᶜ, μ.weight u v) = μ.load u := by
  rw [μ.inside_load_eq_sum U hu]
  exact Finset.sum_add_sum_compl U (μ.weight u)

omit [DecidableEq V] in
theorem inside_load_eq_of_no_cross (μ : FractionalMatching G) (U : Finset V) {u : V}
    (hu : u ∈ U) (hz : ∀ v ∉ U, μ.weight u v = 0) :
    (μ.inside (U : Set V)).load u = μ.load u := by
  classical
  have h := μ.inside_load_add_boundary U hu
  have hs : (∑ v ∈ Uᶜ, μ.weight u v) = 0 :=
    Finset.sum_eq_zero fun v hv ↦ hz v (Finset.mem_compl.mp hv)
  rwa [hs, add_zero] at h

open scoped Classical in
theorem sum_inside_loss_le_compl (μ : FractionalMatching G) (U : Finset V) :
    (∑ u ∈ U, (μ.load u - (μ.inside (U : Set V)).load u)) ≤
      ∑ v ∈ Uᶜ, μ.load v := by
  calc
    _ = ∑ u ∈ U, ∑ v ∈ Uᶜ, μ.weight u v := Finset.sum_congr rfl fun u hu ↦ by
      linarith [μ.inside_load_add_boundary U hu]
    _ = ∑ v ∈ Uᶜ, ∑ u ∈ U, μ.weight u v := Finset.sum_comm
    _ ≤ _ := Finset.sum_le_sum fun v _ ↦ by
      calc
        _ = ∑ u ∈ U, μ.weight v u := Finset.sum_congr rfl fun u _ ↦ μ.symmetric u v
        _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun u _ _ ↦ μ.nonnegative v u)

end Erdos547.DPRS.FractionalMatching

#print axioms Erdos547.DPRS.FractionalMatching.sum_inside_loss_le_compl
