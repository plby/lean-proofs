import ErdosProblems.Erdos547.StructuralBalanced
import ErdosProblems.Erdos547.GESeparationOne

/-!
# The balanced case for an optimal mixed GE pair

The separation hypothesis is discharged by the already proved first
separation lemma at a deficient vertex.
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

namespace GallaiEdmondsPartition

theorem IsOptimalGEPair.anchoredTotals_of_balanced {D : GallaiEdmondsPartition G}
    {w : EdgeWeights G} {c : V} {μ ν : FractionalMatching G}
    (a₁ a₂ b₁ b₂ : ℝ) {σ : SkewMatching G (b₂ / b₁)}
    (h : D.IsOptimalGEPair w c μ σ ν) (hm : D.IsMaxSaturation w c μ)
    (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (hb₁ : 0 < b₁) (hskew : b₁ < b₂)
    (hR : (D.reachableVertices w c μ).Nonempty)
    (hlarge : a₁ + a₂ + b₁ + b₂ ≤ w.degree c)
    (hdeg : ∀ v, (a₁ + a₂ + b₁ + b₂) / 2 ≤ w.degree v)
    (hsmall : max a₁ a₂ + b₁ ≤ (a₁ + a₂ + b₁ + b₂) / 2)
    (hbalanced : b₂ ≤ (a₁ + a₂ + b₁ + b₂) / 2) :
    HasAnchoredTotals w (a₂ / a₁) (b₂ / b₁) (a₁ + a₂) (b₁ + b₂) := by
  by_cases hsat : a₁ + a₂ + b₁ + b₂ ≤ w.saturation (fun u ↦ σ.load u + ν.load u) c
  · exact h.1.anchoredTotals_of_mixed_saturation a₁ a₂ b₁ b₂ hm
      ha₁ ha₂.le hb₁ hskew.le hR hdeg hsmall hsat
  obtain ⟨d, hdef⟩ := w.exists_deficient_of_saturation_lt_degree
    (fun u ↦ σ.load u + ν.load u) c ((lt_of_not_ge hsat).trans_le hlarge)
  have hd : d ∈ D.reachableVertices w c μ := by
    by_contra hn
    exact not_lt_of_ge (h.1.outside_lower d hn) hdef
  have hcd : G.Adj c d := by
    by_contra hn
    rw [w.supported c d hn] at hdef
    linarith [σ.load_nonneg d, ν.load_nonneg d]
  have hδ : 1 < b₂ / b₁ := (one_lt_div hb₁).mpr hskew
  exact h.1.anchoredTotals_of_balanced_with_separation a₁ a₂ b₁ b₂ hm
    ha₁ ha₂ hb₁ hskew.le hd hcd
    (fun _ hdu ↦ IsOptimalGEPair.separation_one hm h hδ hd hdef hdu)
    hlarge hdeg hsmall hbalanced

end GallaiEdmondsPartition

end Erdos547.DPRS

namespace Erdos547.DPRS.GallaiEdmondsPartition
#print axioms IsOptimalGEPair.anchoredTotals_of_balanced
end Erdos547.DPRS.GallaiEdmondsPartition
