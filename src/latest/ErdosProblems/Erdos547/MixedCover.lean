import ErdosProblems.Erdos547.MixedRemainder
import ErdosProblems.Erdos547.ResidualNeighbourPiece
import ErdosProblems.Erdos547.BipartiteOrientation
import ErdosProblems.Erdos547.StructuralCover

/-!
# Finishing when a mixed cover contains the entire second skew budget
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph

variable {V : Type*} [Fintype V] {G : SimpleGraph V} {γ δ : ℝ}

theorem anchoredPair_of_residual_fit {σ : SkewMatching G γ} {τ : SkewMatching G δ}
    {w : EdgeWeights G} {c d : V} (hcd : G.Adj c d)
    (hcap : ∀ u, σ.load u + τ.load u ≤ 1)
    (hσ : ∀ u, σ.outLoad u ≤ max 0 (w.weight c u - τ.load u))
    (hτ : τ.Fits w d) : AnchoredPair σ τ w c d := by
  have hfit (u : V) : σ.outLoad u ≤ w.weight c u := (hσ u).trans
    (max_le (w.nonnegative c u) (sub_le_self _ (τ.load_nonneg u)))
  refine ⟨hcd, hcap, hfit, hτ, ?_⟩
  intro u
  by_cases hu : τ.load u ≤ w.weight c u
  · have hh := hσ u
    rw [max_eq_right (sub_nonneg.mpr hu)] at hh
    exact (show σ.outLoad u + τ.outLoad u ≤ w.weight c u by
      linarith [τ.outLoad_le_load u]).trans (le_max_left _ _)
  · have hh := hσ u
    rw [max_eq_left (by linarith)] at hh
    exact (show σ.outLoad u + τ.outLoad u ≤ w.weight d u by
      linarith [hτ u]).trans (le_max_right _ _)

theorem hasAnchoredTotals_of_mixed_cover (σ : SkewMatching G δ) (ν : FractionalMatching G)
    (U : Finset V) (hσ : σ.RunsFrom U) (hδ : 1 ≤ δ)
    (hcap : ∀ u, σ.load u + ν.load u ≤ 1)
    (hcover : ∀ u ∈ U, σ.load u + ν.load u = 1)
    (hzero : ∀ u ∈ U, ∀ v ∈ U, ν.weight u v = 0)
    (w : EdgeWeights G) {c d : V} (hcd : G.Adj c d) (hfit : σ.Fits w c)
    (hN : ∀ u, G.Adj d u → u ∈ U) (a₁ a₂ b : ℝ) (ha₁ : 0 < a₁) (ha₂ : 0 ≤ a₂)
    (hb : 0 ≤ b) (hsize : b ≤ σ.total)
    (hdegree : max a₁ a₂ + b / (1 + δ) ≤ w.degree d) :
    HasAnchoredTotals w (a₂ / a₁) δ (a₁ + a₂) b := by
  classical
  obtain ⟨τ, F, hτ, htotalτ, hcapacity, hcovered, hFzero⟩ :=
    exists_mixed_remainder σ ν U hσ hδ hcap hcover hzero b hb hsize
  have hτruns := hσ.of_suballocation hτ
  have hτfit : τ.Fits w c := fun u ↦ (hτ.outLoad_le u).trans (hfit u)
  obtain ⟨P, hP, hbetween, hallow, htotalP⟩ := exists_residual_neighbour_piece
    F U hFzero w d τ.load τ.load_nonneg hN hcovered
  have hsaturation : w.saturation τ.load d ≤ b / (1 + δ) := by
    have hh := w.saturation_le_sum_of_neighbours_subset τ.load τ.load_nonneg d U hN
    rwa [hτruns.sum_load_side, htotalτ] at hh
  have hPsize : max a₁ a₂ ≤ P.total := by
    have he := w.degree_truncate_add_saturation τ.load τ.load_nonneg d
    rw [htotalP]
    linarith
  obtain ⟨α, hα, htotalα, hout⟩ := exists_bipartite_orientation P U Uᶜ
    disjoint_compl_right hbetween a₁ a₂ ha₁ ha₂ hPsize
  have hαcap (u : V) : α.load u + τ.load u ≤ 1 :=
    (add_le_add ((hα.load_le u).trans (P.load_le_of_weight_le F hP u)) le_rfl).trans
      (hcapacity u)
  have hαallow (u : V) : α.outLoad u ≤ max 0 (w.weight d u - τ.load u) := by
    by_cases hu : u ∈ U
    · exact ((α.outLoad_le_load u).trans (hα.load_le u)).trans (hallow u hu)
    · rw [hout u hu]
      exact le_max_left _ _
  exact ⟨d, c, α, τ, anchoredPair_of_residual_fit hcd.symm hαcap hαallow hτfit,
    htotalα, htotalτ⟩

end Erdos547.DPRS

#print axioms Erdos547.DPRS.hasAnchoredTotals_of_mixed_cover
