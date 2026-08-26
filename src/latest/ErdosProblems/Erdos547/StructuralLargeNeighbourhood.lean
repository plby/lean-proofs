import ErdosProblems.Erdos547.GEReachablePiece
import ErdosProblems.Erdos547.GESelectedPiece
import ErdosProblems.Erdos547.BipartiteOrientation
import ErdosProblems.Erdos547.StructuralCover

/-!
# The structural case with a large reachable separator neighbourhood
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

namespace GallaiEdmondsPartition

theorem IsMaxSaturation.anchoredTotals_of_large_neighbourhood {D : GallaiEdmondsPartition G}
    {w : EdgeWeights G} {c d : V} {μ : FractionalMatching G}
    (h : D.IsMaxSaturation w c μ) (hd : d ∈ D.reachableVertices w c μ) (hcd : G.Adj c d)
    (a₁ a₂ b₁ b₂ : ℝ) (ha₁ : 0 < a₁) (ha₂ : 0 ≤ a₂) (hb₁ : 0 < b₁) (hb₂ : 0 ≤ b₂)
    (hdeg : max a₁ a₂ ≤ w.degree d)
    (hsize : max a₁ a₂ + max b₁ b₂ ≤ ((D.reachableNeighbours w c μ).card : ℝ)) :
    HasAnchoredTotals w (a₂ / a₁) (b₂ / b₁) (a₁ + a₂) (b₁ + b₂) := by
  let R := D.reachableVertices w c μ
  let S := D.reachableNeighbours w c μ
  have hdis : Disjoint D.separator R := Finset.disjoint_left.mpr fun _ hu hv ↦
    D.singleton_not_separator (h.reachable_singleton hv) hu
  obtain ⟨Q, hQ, hbetweenQ, htotalQ, hfitD, _⟩ := h.exists_selected_piece hd (max a₁ a₂)
    (ha₁.le.trans (le_max_left _ _)) hdeg
  obtain ⟨α, hα, htotalα, houtα⟩ := exists_bipartite_orientation Q D.separator R
    hdis hbetweenQ a₁ a₂ ha₁ ha₂ htotalQ.ge
  have hfitα : α.Fits w d := by
    intro u
    by_cases hu : u ∈ D.separator
    · exact ((α.outLoad_le_load u).trans (hα.load_le u)).trans (hfitD u hu)
    · rw [houtα u hu]
      exact w.nonnegative d u
  let F := D.reachablePiece w c μ
  have hQF (u v : V) : Q.weight u v ≤ F.weight u v :=
    D.le_reachablePiece_of_between w c μ Q hQ D.separator hbetweenQ u v
  let P := F.sub Q hQF
  have hPF (u v : V) : P.weight u v ≤ F.weight u v := sub_le_self _ (Q.nonnegative u v)
  have hbetweenP : P.RunsBetween R S := (D.reachablePiece_between w c μ).mono hPF
  have hdisRS : Disjoint R S := Finset.disjoint_left.mpr fun _ hu hv ↦
    D.singleton_not_separator (h.reachable_singleton hu) (h.reachable_neighbour_separator hv)
  have hPsize : max b₁ b₂ ≤ P.total := by
    change max b₁ b₂ ≤ (F.sub Q hQF).total
    rw [FractionalMatching.sub_total, htotalQ]
    have ht : F.total = ((D.reachableNeighbours w c μ).card : ℝ) := h.reachablePiece_total
    rw [ht]
    linarith
  obtain ⟨β, hβ, htotalβ, houtβ⟩ := exists_bipartite_orientation P R S hdisRS hbetweenP
    b₁ b₂ hb₁ hb₂ hPsize
  have hfitβ : β.Fits (w.truncate Q.load Q.load_nonneg) c := by
    intro u
    by_cases hu : u ∈ R
    · have hload := (β.outLoad_le_load u).trans (hβ.load_le u)
      have he : P.load u = μ.load u - Q.load u := by
        rw [show P.load u = F.load u - Q.load u from F.sub_load Q hQF u,
          D.reachablePiece_load w c μ hu]
      rw [he] at hload
      change β.outLoad u ≤ max 0 (w.weight c u - Q.load u)
      exact (hload.trans (sub_le_sub_right (h.reachable_load_le hu) _)).trans (le_max_right _ _)
    · rw [houtβ u hu]
      exact (w.truncate Q.load Q.load_nonneg).nonnegative c u
  have hp₁ := AnchoredPair.single_left α (b₂ / b₁) (div_nonneg hb₂ hb₁.le) w hcd.symm hfitα
  have hp₂ := (AnchoredPair.single_left β (a₂ / a₁) (div_nonneg ha₂ ha₁.le)
    (w.truncate Q.load Q.load_nonneg) hcd hfitβ).swap
  have hd₁ := PairDominated.single_left α (b₂ / b₁) (div_nonneg hb₂ hb₁.le) hα
  have hd₂ := (PairDominated.single_left β (a₂ / a₁) (div_nonneg ha₂ ha₁.le) hβ).swap
  have hpieces (u v : V) : Q.weight u v + P.weight u v ≤ μ.weight u v := by
    change Q.weight u v + (F.weight u v - Q.weight u v) ≤ _
    linarith [D.reachablePiece_le w c μ u v]
  obtain ⟨σ, τ, hp, _, htσ, htτ⟩ := hp₁.combine_pieces hp₂ hd₁ hd₂ hpieces
  refine ⟨d, c, σ, τ, hp, ?_, ?_⟩
  · rw [htotalα] at htσ
    simpa only [SkewMatching.total, SkewMatching.zero, Finset.sum_const_zero,
      add_zero] using htσ
  · rw [htotalβ] at htτ
    simpa only [SkewMatching.total, SkewMatching.zero, Finset.sum_const_zero,
      zero_add] using htτ

end GallaiEdmondsPartition

end Erdos547.DPRS

namespace Erdos547.DPRS.GallaiEdmondsPartition
#print axioms IsMaxSaturation.anchoredTotals_of_large_neighbourhood
end Erdos547.DPRS.GallaiEdmondsPartition
