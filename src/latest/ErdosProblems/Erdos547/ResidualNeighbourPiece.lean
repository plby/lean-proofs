import ErdosProblems.Erdos547.CappedIndependentRows
import ErdosProblems.Erdos547.WeightedNeighbourhood

/-!
# Capturing a residual anchor neighbourhood on independent fractional rows
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

theorem FractionalMatching.exists_neighbour_piece (F : FractionalMatching G) (U : Finset V)
    (hU : ∀ u ∈ U, ∀ v ∈ U, F.weight u v = 0) (w : EdgeWeights G) (d : V)
    (hN : ∀ u, G.Adj d u → u ∈ U) (hbound : ∀ u ∈ U, w.weight d u ≤ F.load u) :
    ∃ P : FractionalMatching G, (∀ u v, P.weight u v ≤ F.weight u v) ∧
      P.RunsBetween U Uᶜ ∧ (∀ u ∈ U, P.load u = w.weight d u) ∧ P.total = w.degree d := by
  let P := F.capIndependent U hU (w.weight d) (w.nonnegative d)
  refine ⟨P, F.capIndependent_weight_le U hU _ _, F.capIndependent_runsBetween U hU _ _,
    ?_, ?_⟩
  · intro u hu
    rw [show P.load u = min (w.weight d u) (F.load u) from
      F.capIndependent_load U hU _ _ hu, min_eq_left (hbound u hu)]
  · rw [show P.total = ∑ u ∈ U, min (w.weight d u) (F.load u) from
      F.capIndependent_total U hU _ _]
    calc
      _ = ∑ u ∈ U, w.weight d u := Finset.sum_congr rfl fun u hu ↦ min_eq_left (hbound u hu)
      _ = _ := Finset.sum_subset (Finset.subset_univ _)
        (fun u _ hu ↦ w.supported d u (fun h ↦ hu (hN u h)))

theorem exists_residual_neighbour_piece (F : FractionalMatching G) (U : Finset V)
    (hU : ∀ u ∈ U, ∀ v ∈ U, F.weight u v = 0) (w : EdgeWeights G) (d : V)
    (l : V → ℝ) (hl : ∀ u, 0 ≤ l u) (hN : ∀ u, G.Adj d u → u ∈ U)
    (hcover : ∀ u ∈ U, F.load u + l u = 1) :
    ∃ P : FractionalMatching G, (∀ u v, P.weight u v ≤ F.weight u v) ∧
      P.RunsBetween U Uᶜ ∧ (∀ u ∈ U, P.load u ≤ max 0 (w.weight d u - l u)) ∧
      P.total = (w.truncate l hl).degree d := by
  let w' := w.truncate l hl
  let P := F.capIndependent U hU (w'.weight d) (w'.nonnegative d)
  have hbound (u : V) (hu : u ∈ U) : w'.weight d u ≤ F.load u := by
    change max 0 (w.weight d u - l u) ≤ F.load u
    apply max_le (F.load_nonneg u)
    linarith [hcover u hu, w.at_most_one d u]
  refine ⟨P, F.capIndependent_weight_le U hU _ _, F.capIndependent_runsBetween U hU _ _,
    ?_, ?_⟩
  · intro u hu
    rw [show P.load u = min (w'.weight d u) (F.load u) from
      F.capIndependent_load U hU _ _ hu]
    exact min_le_left _ _
  · rw [show P.total = ∑ u ∈ U, min (w'.weight d u) (F.load u) from
      F.capIndependent_total U hU _ _]
    calc
      _ = ∑ u ∈ U, w'.weight d u := Finset.sum_congr rfl fun u hu ↦ min_eq_left (hbound u hu)
      _ = _ := Finset.sum_subset (Finset.subset_univ _)
        (fun u _ hu ↦ w'.supported d u (fun h ↦ hu (hN u h)))

omit [DecidableEq V] in
theorem EdgeWeights.saturation_le_sum_of_neighbours_subset (w : EdgeWeights G)
    (l : V → ℝ) (hl : ∀ u, 0 ≤ l u) (d : V) (U : Finset V)
    (hN : ∀ u, G.Adj d u → u ∈ U) : w.saturation l d ≤ ∑ u ∈ U, l u := by
  have he : w.saturation l d = ∑ u ∈ U, min (w.weight d u) (l u) := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro u _ hu
    rw [w.supported d u (fun h ↦ hu (hN u h)), min_eq_left (hl u)]
  rw [he]
  exact Finset.sum_le_sum fun _ _ ↦ min_le_right _ _

end Erdos547.DPRS

#print axioms Erdos547.DPRS.exists_residual_neighbour_piece
