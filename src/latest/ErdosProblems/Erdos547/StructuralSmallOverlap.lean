import ErdosProblems.Erdos547.StructuralLargeNeighbourhood
import ErdosProblems.Erdos547.TwoNeighbourhoods

/-!
# Two reachable vertices with small weighted neighbourhood overlap
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

namespace GallaiEdmondsPartition

open scoped Classical in
theorem IsMaxSaturation.anchoredTotals_of_small_overlap {D : GallaiEdmondsPartition G}
    {w : EdgeWeights G} {c d₁ d₂ : V} {μ : FractionalMatching G}
    (h : D.IsMaxSaturation w c μ) (hd₁ : d₁ ∈ D.reachableVertices w c μ)
    (hd₂ : d₂ ∈ D.reachableVertices w c μ)
    (a₁ a₂ b₁ b₂ : ℝ) (ha₁ : 0 < a₁) (ha₂ : 0 ≤ a₂) (hb₁ : 0 < b₁) (hskew : b₁ ≤ b₂)
    (hdeg : ∀ v, (a₁ + a₂ + b₁ + b₂) / 2 ≤ w.degree v)
    (hlargeB : (a₁ + a₂ + b₁ + b₂) / 2 ≤ b₂)
    (hoverlap : w.degreeOn (Finset.univ.filter (G.Adj d₂)) d₁ ≤ b₁) :
    HasAnchoredTotals w (a₂ / a₁) (b₂ / b₁) (a₁ + a₂) (b₁ + b₂) := by
  classical
  have hcd : G.Adj c d₁ := by
    by_contra hn
    have hp := h.reachable_weight_pos hd₁
    rw [w.supported c d₁ hn] at hp
    exact lt_irrefl 0 hp
  have hmaxA : max a₁ a₂ ≤ a₁ + a₂ := max_le (by linarith) (by linarith)
  have hcard := w.two_neighbourhoods_card_bound (D.reachableNeighbours w c μ) d₁ d₂
    (fun u hdu ↦ Finset.mem_filter.mpr ⟨Finset.mem_univ _, d₁, hd₁, hdu⟩)
    (fun u hdu ↦ Finset.mem_filter.mpr ⟨Finset.mem_univ _, d₂, hd₂, hdu⟩)
  apply h.anchoredTotals_of_large_neighbourhood hd₁ hcd a₁ a₂ b₁ b₂ ha₁ ha₂ hb₁
    (hb₁.le.trans hskew)
  · linarith [hdeg d₁]
  · rw [max_eq_right hskew]
    linarith [hdeg d₁, hdeg d₂]

end GallaiEdmondsPartition

end Erdos547.DPRS

namespace Erdos547.DPRS.GallaiEdmondsPartition
#print axioms IsMaxSaturation.anchoredTotals_of_small_overlap
end Erdos547.DPRS.GallaiEdmondsPartition
