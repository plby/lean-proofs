import ErdosProblems.Erdos547.GEPairSupport
import ErdosProblems.Erdos547.ResidualNeighbourPiece

/-!
# The residual neighbourhood piece in a mixed GE pair
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {γ : ℝ}

namespace GallaiEdmondsPartition

theorem IsGEPair.fractional_partner_reachable {D : GallaiEdmondsPartition G}
    {w : EdgeWeights G} {c : V} {μ ν : FractionalMatching G} {σ : SkewMatching G γ}
    (h : D.IsGEPair w c μ σ ν) (hm : D.IsMaxSaturation w c μ)
    {u v : V} (hu : u ∈ D.reachableNeighbours w c μ) (huv : 0 < ν.weight u v) :
    v ∈ D.reachableVertices w c μ := by
  have hcross : D.ReachableCross w c μ u v := by
    by_contra hn
    rw [h.fractional_cross u v (Or.inl (Finset.mem_union_right _ hu)) hn] at huv
    exact lt_irrefl 0 huv
  rcases hcross with hcross | hcross
  · exact (D.singleton_not_separator (hm.reachable_singleton hcross.1)
      (hm.reachable_neighbour_separator hu)).elim
  · exact hcross.1

theorem IsGEPair.selected_piece_fits_other_side {D : GallaiEdmondsPartition G}
    {w : EdgeWeights G} {c d : V} {μ ν : FractionalMatching G} {σ : SkewMatching G γ}
    (h : D.IsGEPair w c μ σ ν) (hm : D.IsMaxSaturation w c μ)
    (hd : d ∈ D.reachableVertices w c μ) (J : FractionalMatching G)
    (hJ : ∀ u v, J.weight u v ≤ ν.weight u v) (hcross : J.Crosses D.separator)
    (hfit : ∀ u ∈ D.separator, J.load u ≤
      (w.truncate σ.load σ.load_nonneg).weight d u) :
    ∀ u ∈ D.separatorᶜ, J.load u ≤ (w.truncate σ.load σ.load_nonneg).weight c u := by
  classical
  intro u hu
  by_cases hz : J.load u = 0
  · rw [hz]
    exact (w.truncate σ.load σ.load_nonneg).nonnegative c u
  have hp : 0 < J.load u := lt_of_le_of_ne (J.load_nonneg u) (Ne.symm hz)
  obtain ⟨v, _, huv⟩ := (Finset.sum_pos_iff_of_nonneg (fun v _ ↦ J.nonnegative u v)).mp hp
  have hv : v ∈ D.separator := by
    by_contra hn
    exact (Finset.mem_compl.mp hu) ((hcross u v huv).mpr hn)
  have hvload : 0 < J.load v := J.load_pos_of_weight_pos (by rwa [J.symmetric v u])
  have hwd : 0 < w.weight d v := (hvload.trans_le (hfit v hv)).trans_le
    (w.truncate_weight_le σ.load σ.load_nonneg d v)
  have hdv : G.Adj d v := by
    by_contra hn
    rw [w.supported d v hn] at hwd
    exact lt_irrefl 0 hwd
  have hvR : v ∈ D.reachableNeighbours w c μ :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, d, hd, hdv⟩
  have huR := h.fractional_partner_reachable hm hvR
    (show 0 < ν.weight v u from (by rwa [J.symmetric v u] : 0 < J.weight v u).trans_le (hJ v u))
  have hupper := h.reachable_upper u huR
  have hload := J.load_le_of_weight_le ν hJ u
  change J.load u ≤ max 0 (w.weight c u - σ.load u)
  exact (show J.load u ≤ w.weight c u - σ.load u by linarith).trans (le_max_right _ _)

end GallaiEdmondsPartition

end Erdos547.DPRS

#print axioms Erdos547.DPRS.GallaiEdmondsPartition.IsGEPair.selected_piece_fits_other_side
