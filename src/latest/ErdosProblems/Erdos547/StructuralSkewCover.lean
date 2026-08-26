import ErdosProblems.Erdos547.GEPairSupport
import ErdosProblems.Erdos547.MixedCover

/-!
# The GE skew-cover case
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

namespace GallaiEdmondsPartition

theorem IsGEPair.anchoredTotals_of_skew_cover {D : GallaiEdmondsPartition G}
    {w : EdgeWeights G} {c : V} {μ ν : FractionalMatching G}
    (a₁ a₂ b₁ b₂ : ℝ) {σ : SkewMatching G (b₂ / b₁)}
    (h : D.IsGEPair w c μ σ ν) (hm : D.IsMaxSaturation w c μ)
    (ha₁ : 0 < a₁) (ha₂ : 0 ≤ a₂) (hb₁ : 0 < b₁) (hskew : b₁ ≤ b₂)
    (hR : (D.reachableVertices w c μ).Nonempty)
    (hsize : b₁ + b₂ ≤ σ.total)
    (hdeg : ∀ v, (a₁ + a₂ + b₁ + b₂) / 2 ≤ w.degree v)
    (hsmall : max a₁ a₂ + b₁ ≤ (a₁ + a₂ + b₁ + b₂) / 2) :
    HasAnchoredTotals w (a₂ / a₁) (b₂ / b₁) (a₁ + a₂) (b₁ + b₂) := by
  obtain ⟨d, hd⟩ := hR
  have hcd : G.Adj c d := by
    by_contra hn
    have hp := hm.reachable_weight_pos hd
    rw [w.supported c d hn] at hp
    exact lt_irrefl 0 hp
  have hγ : 1 ≤ b₂ / b₁ := (one_le_div hb₁).mpr hskew
  have he : (b₁ + b₂) / (1 + b₂ / b₁) = b₁ := by
    have hsum : b₁ + b₂ ≠ 0 := by linarith
    field_simp [ne_of_gt hb₁, hsum]
  apply hasAnchoredTotals_of_mixed_cover σ ν D.separator (h.runsFrom_separator hm) hγ
    h.capacity h.covers_separator (fun _ hu _ hv ↦ h.fractional_zero_separator hm hu hv)
    w hcd h.fits (fun _ hx ↦ D.neighbour_of_singleton_mem_separator
      (hm.reachable_singleton hd) hx) a₁ a₂ (b₁ + b₂) ha₁ ha₂ (by linarith) hsize
  rw [he]
  exact hsmall.trans (hdeg d)

end GallaiEdmondsPartition

end Erdos547.DPRS

#print axioms Erdos547.DPRS.GallaiEdmondsPartition.IsGEPair.anchoredTotals_of_skew_cover
