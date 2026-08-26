import ErdosProblems.Erdos547.BipartiteFractional

/-!
# Saturation when one side of a fractional matching is fully accessible
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

namespace FractionalMatching

theorem RunsBetween.outside_load_le {μ : FractionalMatching G} {U W : Finset V}
    (h : μ.RunsBetween U W) (w : EdgeWeights G) (c : V)
    (hW : ∀ u ∈ W, μ.load u ≤ w.weight c u) {u : V} (hu : u ∉ U) :
    μ.load u ≤ w.weight c u := by
  classical
  by_cases huW : u ∈ W
  · exact hW u huW
  · rw [h.load_zero_outside (fun hp ↦ (Finset.mem_union.mp hp).elim hu huW)]
    exact w.nonnegative c u

theorem RunsBetween.saturation_eq {μ : FractionalMatching G} {U W : Finset V}
    (h : μ.RunsBetween U W) (hdis : Disjoint U W) (w : EdgeWeights G) (c : V)
    (hW : ∀ u ∈ W, μ.load u ≤ w.weight c u) :
    w.saturation μ.load c = (∑ u ∈ U, min (w.weight c u) (μ.load u)) + μ.total := by
  classical
  rw [EdgeWeights.saturation, ← Finset.sum_add_sum_compl U]
  congr 1
  calc
    _ = ∑ u ∈ Uᶜ, μ.load u := Finset.sum_congr rfl fun u hu ↦
      min_eq_right (h.outside_load_le w c hW (Finset.mem_compl.mp hu))
    _ = μ.total := (h.crosses hdis).swap.sum_load_side

end FractionalMatching

end Erdos547.DPRS

#print axioms Erdos547.DPRS.FractionalMatching.RunsBetween.saturation_eq
