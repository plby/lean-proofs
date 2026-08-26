import ErdosProblems.Erdos547.GEReachableSets
import ErdosProblems.Erdos547.AllocationRestriction
import ErdosProblems.Erdos547.CappingLoss

/-!
# The fractional matching carried by all reachable vertices
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

namespace GallaiEdmondsPartition

def reachablePiece (D : GallaiEdmondsPartition G) (w : EdgeWeights G) (c : V)
    (μ : FractionalMatching G) : FractionalMatching G :=
  μ.touching (D.reachableVertices w c μ : Set V)

theorem reachablePiece_le (D : GallaiEdmondsPartition G) (w : EdgeWeights G) (c : V)
    (μ : FractionalMatching G) (u v : V) : (D.reachablePiece w c μ).weight u v ≤ μ.weight u v := by
  by_cases hu : u ∈ D.reachableVertices w c μ
  · rw [show (D.reachablePiece w c μ).weight u v = μ.weight u v from
      μ.touching_weight_of_mem (Or.inl hu)]
  · by_cases hv : v ∈ D.reachableVertices w c μ
    · rw [show (D.reachablePiece w c μ).weight u v = μ.weight u v from
        μ.touching_weight_of_mem (Or.inr hv)]
    · rw [show (D.reachablePiece w c μ).weight u v = 0 from μ.touching_weight_of_notMem hu hv]
      exact μ.nonnegative u v

theorem reachablePiece_load (D : GallaiEdmondsPartition G) (w : EdgeWeights G) (c : V)
    (μ : FractionalMatching G) {u : V} (hu : u ∈ D.reachableVertices w c μ) :
    (D.reachablePiece w c μ).load u = μ.load u :=
  Finset.sum_congr rfl fun _ _ ↦ μ.touching_weight_of_mem (Or.inl hu)

theorem reachablePiece_between (D : GallaiEdmondsPartition G) (w : EdgeWeights G) (c : V)
    (μ : FractionalMatching G) : (D.reachablePiece w c μ).RunsBetween
      (D.reachableVertices w c μ) (D.reachableNeighbours w c μ) := by
  intro u v hp
  have hμ := hp.trans_le (D.reachablePiece_le w c μ u v)
  by_cases hu : u ∈ D.reachableVertices w c μ
  · exact Or.inl ⟨hu, D.reachable_neighbour_mem w c μ hu hμ⟩
  · have hv : v ∈ D.reachableVertices w c μ := by
      by_contra hn
      rw [show (D.reachablePiece w c μ).weight u v = 0 from
        μ.touching_weight_of_notMem hu hn] at hp
      exact lt_irrefl 0 hp
    exact Or.inr ⟨D.reachable_neighbour_mem w c μ hv (by rwa [μ.symmetric v u]), hv⟩

theorem le_reachablePiece_of_between (D : GallaiEdmondsPartition G) (w : EdgeWeights G)
    (c : V) (μ Q : FractionalMatching G) (hQ : ∀ u v, Q.weight u v ≤ μ.weight u v)
    (U : Finset V) (hbetween : Q.RunsBetween U (D.reachableVertices w c μ)) (u v : V) :
    Q.weight u v ≤ (D.reachablePiece w c μ).weight u v := by
  by_cases hu : u ∈ D.reachableVertices w c μ
  · rw [show (D.reachablePiece w c μ).weight u v = μ.weight u v from
      μ.touching_weight_of_mem (Or.inl hu)]
    exact hQ u v
  · by_cases hv : v ∈ D.reachableVertices w c μ
    · rw [show (D.reachablePiece w c μ).weight u v = μ.weight u v from
        μ.touching_weight_of_mem (Or.inr hv)]
      exact hQ u v
    · apply le_trans _ (D.reachablePiece w c μ |>.nonnegative u v)
      apply le_of_not_gt
      intro hp
      rcases hbetween u v hp with hh | hh
      · exact hv hh.2
      · exact hu hh.1

theorem IsMaxSaturation.reachablePiece_total {D : GallaiEdmondsPartition G}
    {w : EdgeWeights G} {c : V} {μ : FractionalMatching G}
    (h : D.IsMaxSaturation w c μ) :
    (D.reachablePiece w c μ).total = ((D.reachableNeighbours w c μ).card : ℝ) := by
  have hdis : Disjoint (D.reachableVertices w c μ) (D.reachableNeighbours w c μ) :=
    Finset.disjoint_left.mpr fun _ hu hv ↦ D.singleton_not_separator (h.reachable_singleton hu)
      (h.reachable_neighbour_separator hv)
  calc
    _ = ∑ u ∈ D.reachableVertices w c μ, (D.reachablePiece w c μ).load u :=
      ((D.reachablePiece_between w c μ).crosses hdis).sum_load_side.symm
    _ = ∑ u ∈ D.reachableVertices w c μ, μ.load u :=
      Finset.sum_congr rfl fun _ hu ↦ D.reachablePiece_load w c μ hu
    _ = ∑ u ∈ D.reachableNeighbours w c μ, μ.load u := D.reachable_load_sum_eq w c μ
    _ = ∑ _u ∈ D.reachableNeighbours w c μ, (1 : ℝ) :=
      Finset.sum_congr rfl fun _ hu ↦ h.1.load_separator (h.reachable_neighbour_separator hu)
    _ = _ := by simp

end GallaiEdmondsPartition

end Erdos547.DPRS

#print axioms Erdos547.DPRS.GallaiEdmondsPartition.IsMaxSaturation.reachablePiece_total
