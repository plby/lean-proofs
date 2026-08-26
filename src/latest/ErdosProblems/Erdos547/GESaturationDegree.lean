import ErdosProblems.Erdos547.GEReachableSets
import ErdosProblems.Erdos547.WeightedNeighbourhood

/-!
# A maximum GE saturation is at least the minimum weighted degree

If the anchor is not fully saturated, a deficient singleton generates a
reachable set. Its load equals the size of its separator neighbourhood.
This neighbourhood contains every neighbour of the deficient singleton.
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

namespace GallaiEdmondsPartition

theorem IsFractionalGE.neighbour_load_of_not_separator {D : GallaiEdmondsPartition G}
    {μ : FractionalMatching G} (h : D.IsFractionalGE μ) {c v : V}
    (hc : c ∉ D.separator) (hcv : G.Adj c v) : μ.load v = 1 := by
  rcases D.vertex_classes v with hv | hv | hv
  · exact h.load_separator hv
  · exact (hc (D.neighbour_of_singleton_mem_separator hv hcv.symm)).elim
  · exact h.load_nontrivial hv

theorem IsFractionalGE.saturation_of_not_separator {D : GallaiEdmondsPartition G}
    {μ : FractionalMatching G} (h : D.IsFractionalGE μ) (w : EdgeWeights G) {c : V}
    (hc : c ∉ D.separator) : w.saturation μ.load c = w.degree c := by
  apply w.saturation_eq_of_covers_neighbours μ.load μ.load_nonneg c
  intro v hcv
  rw [h.neighbour_load_of_not_separator hc hcv]
  exact w.at_most_one c v

theorem IsFractionalGE.deficient_singleton {D : GallaiEdmondsPartition G}
    {μ : FractionalMatching G} (h : D.IsFractionalGE μ) {w : EdgeWeights G} {c v : V}
    (hdef : μ.load v < w.weight c v) : v ∈ D.singletonVertices := by
  rcases D.vertex_classes v with hv | hv | hv
  · rw [h.load_separator hv] at hdef
    exact (not_lt_of_ge (w.at_most_one c v) hdef).elim
  · exact hv
  · rw [h.load_nontrivial hv] at hdef
    exact (not_lt_of_ge (w.at_most_one c v) hdef).elim

theorem IsMaxSaturation.reachable_neighbours_card_le_saturation
    {D : GallaiEdmondsPartition G} {w : EdgeWeights G} {c : V} {μ : FractionalMatching G}
    (h : D.IsMaxSaturation w c μ) :
    ((D.reachableNeighbours w c μ).card : ℝ) ≤ w.saturation μ.load c := by
  classical
  calc
    _ = ∑ _y ∈ D.reachableNeighbours w c μ, (1 : ℝ) := by simp
    _ = ∑ y ∈ D.reachableNeighbours w c μ, μ.load y :=
      Finset.sum_congr rfl fun _ hy ↦
        (h.1.load_separator (h.reachable_neighbour_separator hy)).symm
    _ = ∑ x ∈ D.reachableVertices w c μ, μ.load x :=
      (D.reachable_load_sum_eq w c μ).symm
    _ = ∑ x ∈ D.reachableVertices w c μ, min (w.weight c x) (μ.load x) :=
      Finset.sum_congr rfl fun x hx ↦ (min_eq_right (h.reachable_load_le hx)).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun x _ _ ↦ le_min (w.nonnegative c x) (μ.load_nonneg x))

theorem IsMaxSaturation.saturation_ge_min_degree {D : GallaiEdmondsPartition G}
    {w : EdgeWeights G} {c : V} {μ : FractionalMatching G}
    (h : D.IsMaxSaturation w c μ) (k : ℝ) (hdeg : ∀ v, k ≤ w.degree v) :
    k ≤ w.saturation μ.load c := by
  classical
  by_contra hn
  have hlt : w.saturation μ.load c < w.degree c := (lt_of_not_ge hn).trans_le (hdeg c)
  obtain ⟨x, hdef⟩ := w.exists_deficient_of_saturation_lt_degree μ.load c hlt
  have hx : x ∈ D.reachableVertices w c μ := Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, x, h.1.deficient_singleton hdef, hdef, Relation.ReflTransGen.refl⟩
  have hN : w.degree x ≤ ((D.reachableNeighbours w c μ).card : ℝ) :=
    w.degree_le_card_of_neighbours_subset x _ (fun v hxv ↦
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, x, hx, hxv⟩)
  exact hn ((hdeg x).trans (hN.trans h.reachable_neighbours_card_le_saturation))

end GallaiEdmondsPartition

end Erdos547.DPRS

#print axioms Erdos547.DPRS.GallaiEdmondsPartition.IsMaxSaturation.saturation_ge_min_degree
