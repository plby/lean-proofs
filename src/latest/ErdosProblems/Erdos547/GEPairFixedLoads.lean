import ErdosProblems.Erdos547.GEPairSupport
import ErdosProblems.Erdos547.TouchingLoad

/-!
# Loads away from the reachable cut of a GE pair
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {γ : ℝ}

namespace GallaiEdmondsPartition

theorem IsGEPair.fractional_load_fixed_outside {D : GallaiEdmondsPartition G}
    {w : EdgeWeights G} {c : V} {μ ν : FractionalMatching G} {σ : SkewMatching G γ}
    (h : D.IsGEPair w c μ σ ν) {u : V}
    (hu : u ∉ D.reachableVertices w c μ ∪ D.reachableNeighbours w c μ) :
    ν.load u = μ.load u := by
  apply Finset.sum_congr rfl
  intro v _
  by_cases hv : v ∈ D.reachableVertices w c μ ∪ D.reachableNeighbours w c μ
  · have hn : ¬ D.ReachableCross w c μ u v := by
      rintro (h | h)
      · exact hu (Finset.mem_union_left _ h.1)
      · exact hu (Finset.mem_union_right _ h.2)
    rw [h.fractional_cross u v (Or.inr hv) hn]
    symm
    apply le_antisymm _ (μ.nonnegative u v)
    exact le_of_not_gt fun hp ↦ hn (D.reachableCross_of_pos w c μ (Or.inr hv) hp)
  · exact h.fixed_outside u v hu hv

theorem IsGEPair.skew_load_zero_outside {D : GallaiEdmondsPartition G}
    {w : EdgeWeights G} {c : V} {μ ν : FractionalMatching G} {σ : SkewMatching G γ}
    (h : D.IsGEPair w c μ σ ν) {u : V}
    (hu : u ∉ D.reachableVertices w c μ ∪ D.reachableNeighbours w c μ) : σ.load u = 0 := by
  apply σ.load_eq_zero_of_weights u
  · exact fun v ↦ h.skew_supported u v (fun hh ↦ hu (Finset.mem_union_right _ hh.1))
  · exact fun v ↦ h.skew_supported v u (fun hh ↦ hu (Finset.mem_union_left _ hh.2))

theorem IsGEPair.covers_nontrivial {D : GallaiEdmondsPartition G}
    {w : EdgeWeights G} {c : V} {μ ν : FractionalMatching G} {σ : SkewMatching G γ}
    (h : D.IsGEPair w c μ σ ν) (hm : D.IsMaxSaturation w c μ)
    {u : V} (hu : u ∈ D.nontrivialVertices) : σ.load u + ν.load u = 1 := by
  have hout : u ∉ D.reachableVertices w c μ ∪ D.reachableNeighbours w c μ := by
    intro hh
    rcases Finset.mem_union.mp hh with hh | hh
    · exact D.singleton_not_nontrivial (hm.reachable_singleton hh) hu
    · exact D.nontrivial_not_separator hu (hm.reachable_neighbour_separator hh)
  rw [h.skew_load_zero_outside hout, h.fractional_load_fixed_outside hout, zero_add,
    hm.1.load_nontrivial hu]

theorem IsGEPair.covers_neighbours_of_not_separator {D : GallaiEdmondsPartition G}
    {w : EdgeWeights G} {c d : V} {μ ν : FractionalMatching G} {σ : SkewMatching G γ}
    (h : D.IsGEPair w c μ σ ν) (hm : D.IsMaxSaturation w c μ)
    (hd : d ∉ D.separator) {u : V} (hdu : G.Adj d u) : σ.load u + ν.load u = 1 := by
  rcases D.vertex_classes u with hu | hu | hu
  · exact h.covers_separator u hu
  · exact (hd (D.neighbour_of_singleton_mem_separator hu hdu.symm)).elim
  · exact h.covers_nontrivial hm hu

end GallaiEdmondsPartition

end Erdos547.DPRS

#print axioms Erdos547.DPRS.GallaiEdmondsPartition.IsGEPair.covers_neighbours_of_not_separator
