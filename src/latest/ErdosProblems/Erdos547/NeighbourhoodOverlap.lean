import ErdosProblems.Erdos547.WeightedNeighbourhood

/-!
# Restricting weighted degree to common graph neighbours
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

open scoped Classical in
theorem EdgeWeights.degreeOn_common_neighbours (w : EdgeWeights G) (d y : V) :
    w.degreeOn ((Finset.univ.filter (G.Adj d)).filter (G.Adj y)) d =
      w.degreeOn (Finset.univ.filter (G.Adj y)) d := by
  classical
  apply Finset.sum_subset
  · intro u hu
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hu).2⟩
  · intro u hu hn
    apply w.supported d u
    intro hdu
    exact hn (Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdu⟩, (Finset.mem_filter.mp hu).2⟩)

open scoped Classical in
theorem EdgeWeights.neighbourhood_overlap_card_bound (w : EdgeWeights G) (d e : V) :
    w.degreeOn (Finset.univ.filter (G.Adj e)) d + w.degree e -
      w.degreeOn (Finset.univ.filter (G.Adj d)) e ≤
        ((Finset.univ.filter (G.Adj e)).card : ℝ) := by
  classical
  let C := Finset.univ.filter (G.Adj e)
  have he : w.degree e = w.degreeOn C e := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro u _ hu
    exact w.supported e u (fun h ↦ hu (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩))
  have ho : w.degreeOn (Finset.univ.filter (G.Adj d)) e =
      ∑ u ∈ C, if G.Adj d u then w.weight e u else 0 := by
    rw [← w.degreeOn_common_neighbours e d]
    exact Finset.sum_filter _ _
  rw [he, ho]
  have hp : w.degreeOn C d + w.degreeOn C e ≤ (C.card : ℝ) +
      ∑ u ∈ C, if G.Adj d u then w.weight e u else 0 := by
    have hh : ∀ u ∈ C, w.weight d u + w.weight e u ≤
        1 + (if G.Adj d u then w.weight e u else 0) := by
      intro u _
      by_cases hdu : G.Adj d u
      · rw [if_pos hdu]
        linarith [w.at_most_one d u]
      · rw [if_neg hdu, w.supported d u hdu, zero_add, add_zero]
        exact w.at_most_one e u
    have hs := Finset.sum_le_sum hh
    simpa only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one,
      EdgeWeights.degreeOn] using hs
  linarith

end Erdos547.DPRS
