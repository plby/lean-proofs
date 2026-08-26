import ErdosProblems.Erdos547.CoveredRemainder
import ErdosProblems.Erdos547.GECoveredRegion
import ErdosProblems.Erdos547.GEPairFixedLoads

/-!
# The residual allocation for an avoiding anchor outside the separator

The location of the anchor is retained as an explicit hypothesis. The general
avoiding case still needs an argument for anchors in the separator.
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {δ : ℝ}

namespace GallaiEdmondsPartition

theorem IsGEPair.exists_avoiding_allocation_of_not_separator {D : GallaiEdmondsPartition G}
    {w : EdgeWeights G} {c d : V} {μ ν : FractionalMatching G} {σ : SkewMatching G δ}
    (h : D.IsGEPair w c μ σ ν) (hm : D.IsMaxSaturation w c μ)
    (C : Finset V) (hC : C ⊆ D.reachableNeighbours w c μ) (hd : d ∉ D.separator)
    (a b r γ : ℝ) (ha : 0 ≤ a) (hγ : 0 ≤ γ)
    (hdegree : (a + b) / 2 ≤ w.degree d)
    (hmass : w.degreeOn C d + (a + b) / 2 ≤ r + (σ.touching (C : Set V)).total)
    (hbudget : σ.total + r ≤ b) :
    ∃ α : SkewMatching G γ,
      α.DominatedByFractional (ν.sub (ν.touching (C : Set V)) (ν.touching_weight_le _)) ∧
      α.Fits (w.truncate
        (fun u ↦ σ.load u + (ν.touching (C : Set V)).load u)
        (fun u ↦ add_nonneg (σ.load_nonneg u) ((ν.touching (C : Set V)).load_nonneg u))) d ∧
      α.total = a := by
  classical
  let R := D.reachableVertices w c μ
  let W := D.coveredReachable w c μ σ ν C
  let F := ν.touching (C : Set V)
  let τ := σ.touching (C : Set V)
  let U := (C ∪ W)ᶜ
  have hr := h.restriction_runs_between hm C hC
  have hWR : W ⊆ R := Finset.filter_subset _ _
  have hdis : Disjoint C W := Finset.disjoint_left.mpr fun u hu hv ↦
    D.singleton_not_separator (hm.reachable_singleton (hWR hv))
      (hm.reachable_neighbour_separator (hC hu))
  have hzero (u : V) (hu : u ∈ U) : τ.load u = 0 ∧ F.load u = 0 := by
    have huC : u ∉ C := fun hh ↦ Finset.mem_compl.mp hu (Finset.mem_union_left _ hh)
    have huW : u ∉ W := fun hh ↦ Finset.mem_compl.mp hu (Finset.mem_union_right _ hh)
    by_cases huR : u ∈ R
    · have hp : τ.load u + F.load u ≤ 0 := le_of_not_gt fun hh ↦
        huW (Finset.mem_filter.mpr ⟨huR, hh⟩)
      constructor <;> linarith [τ.load_nonneg u, F.load_nonneg u]
    · exact ⟨hr.1.load_zero huC huR, hr.2.load_zero_outside
        (fun hh ↦ (Finset.mem_union.mp hh).elim huC huR)⟩
  have hWzero (u : V) (hu : u ∈ W) : w.weight d u = 0 := by
    apply w.supported d u
    intro hdu
    exact hd (D.neighbour_of_singleton_mem_separator (hm.reachable_singleton (hWR hu)) hdu.symm)
  have he : w.degreeOn U d + w.degreeOn C d = w.degree d := by
    have hsplit := Finset.sum_compl_add_sum (C ∪ W) (w.weight d)
    rw [Finset.sum_union hdis, Finset.sum_eq_zero (fun u hu ↦ hWzero u hu), add_zero] at hsplit
    exact hsplit
  have hcover (u : V) (_hu : u ∈ U) : w.weight d u ≤ σ.load u + ν.load u := by
    by_cases hdu : G.Adj d u
    · rw [h.covers_neighbours_of_not_separator hm hd hdu]
      exact w.at_most_one d u
    · rw [w.supported d u hdu]
      exact add_nonneg (σ.load_nonneg u) (ν.load_nonneg u)
  apply exists_skew_in_covered_remainder w d σ τ (σ.retain_isSuballocation _) ν F
    (ν.touching_weight_le _) U (fun u hu ↦ (hzero u hu).2) (fun u hu ↦ (hzero u hu).1)
    hcover a γ ha hγ
  change w.degreeOn C d + (a + b) / 2 ≤ r + τ.total at hmass
  linarith

end GallaiEdmondsPartition

end Erdos547.DPRS

namespace Erdos547.DPRS.GallaiEdmondsPartition
#print axioms IsGEPair.exists_avoiding_allocation_of_not_separator
end Erdos547.DPRS.GallaiEdmondsPartition
