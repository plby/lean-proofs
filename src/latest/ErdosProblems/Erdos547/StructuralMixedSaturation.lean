import ErdosProblems.Erdos547.StructuralSkewCover
import ErdosProblems.Erdos547.GEPairSelectedPiece
import ErdosProblems.Erdos547.FixedAnchorMatching
import ErdosProblems.Erdos547.AdditiveSaturation
import ErdosProblems.Erdos547.BudgetIdentities
import ErdosProblems.Erdos547.PrependSkew

/-!
# The mixed-saturation cover case

The existing skew budget is retained, and the fixed-order matching lemma is
applied to the fractional remainder in the truncated host weights.
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

namespace GallaiEdmondsPartition

theorem IsGEPair.anchoredTotals_of_mixed_saturation {D : GallaiEdmondsPartition G}
    {w : EdgeWeights G} {c : V} {μ ν : FractionalMatching G}
    (a₁ a₂ b₁ b₂ : ℝ) {σ : SkewMatching G (b₂ / b₁)}
    (h : D.IsGEPair w c μ σ ν) (hm : D.IsMaxSaturation w c μ)
    (ha₁ : 0 < a₁) (ha₂ : 0 ≤ a₂) (hb₁ : 0 < b₁) (hskew : b₁ ≤ b₂)
    (hR : (D.reachableVertices w c μ).Nonempty)
    (hdeg : ∀ v, (a₁ + a₂ + b₁ + b₂) / 2 ≤ w.degree v)
    (hsmall : max a₁ a₂ + b₁ ≤ (a₁ + a₂ + b₁ + b₂) / 2)
    (hsat : a₁ + a₂ + b₁ + b₂ ≤ w.saturation (fun u ↦ σ.load u + ν.load u) c) :
    HasAnchoredTotals w (a₂ / a₁) (b₂ / b₁) (a₁ + a₂) (b₁ + b₂) := by
  classical
  by_cases hbig : b₁ + b₂ ≤ σ.total
  · exact h.anchoredTotals_of_skew_cover a₁ a₂ b₁ b₂ hm ha₁ ha₂ hb₁ hskew hR hbig hdeg hsmall
  have hremaining : 0 < b₁ + b₂ - σ.total := by linarith
  have hδ : 1 ≤ b₂ / b₁ := (one_le_div hb₁).mpr hskew
  have hγ : 0 ≤ a₂ / a₁ := div_nonneg ha₂ ha₁.le
  obtain ⟨d, hd⟩ := hR
  have hcd : G.Adj c d := by
    by_contra hn
    have hp := hm.reachable_weight_pos hd
    rw [w.supported c d hn] at hp
    exact lt_irrefl 0 hp
  have hN (u : V) (hdu : G.Adj d u) : u ∈ D.separator :=
    D.neighbour_of_singleton_mem_separator (hm.reachable_singleton hd) hdu
  let w' := w.truncate σ.load σ.load_nonneg
  obtain ⟨J, hJ, hbetween, hfitD, htotalJ⟩ := exists_residual_neighbour_piece ν D.separator
    (fun _ hu _ hv ↦ h.fractional_zero_separator hm hu hv) w d σ.load σ.load_nonneg hN
    (fun u hu ↦ by linarith [h.covers_separator u hu])
  have hcross := hbetween.crosses disjoint_compl_right
  have hfitC := h.selected_piece_fits_other_side hm hd J hJ hcross hfitD
  have hsaturation : a₁ + a₂ + (b₁ + b₂ - σ.total) ≤ w'.saturation ν.load c := by
    have he := w.saturation_add_load σ.load ν.load σ.load_nonneg ν.load_nonneg c
    have hσsat := w.saturation_le_sum_load σ.load c
    rw [σ.sum_load] at hσsat
    change w.saturation σ.load c + w'.saturation ν.load c = _ at he
    linarith
  have hdegreeJ : w.degree d - σ.total / (1 + b₂ / b₁) ≤ J.total := by
    have he := w.degree_truncate_add_saturation σ.load σ.load_nonneg d
    have hσsat := w.saturation_le_sum_of_neighbours_subset σ.load σ.load_nonneg d
      D.separator hN
    rw [(h.runsFrom_separator hm).sum_load_side] at hσsat
    rw [htotalJ]
    linarith
  obtain ⟨haParts, haParts'⟩ := skew_parts_of_sum a₁ a₂ ha₁ ha₂
  obtain ⟨hbParts, _⟩ := skew_parts_of_sum b₁ b₂ hb₁ (hb₁.le.trans hskew)
  have hbudget : max ((a₁ + a₂) / (1 + a₂ / a₁))
      ((a₂ / a₁) * ((a₁ + a₂) / (1 + a₂ / a₁))) +
      min ((b₁ + b₂ - σ.total) / (1 + b₂ / b₁))
        ((b₂ / b₁) * ((b₁ + b₂ - σ.total) / (1 + b₂ / b₁))) ≤ J.total := by
    rw [haParts', haParts,
      min_skew_parts_of_one_le _ _ hremaining.le hδ, sub_div, hbParts]
    linarith [hdeg d]
  obtain ⟨α, β, hp, hdom, hα, hβ⟩ := exists_fixed_anchor_matching ν J hJ D.separator hcross
    w' hcd hfitD hfitC (a₂ / a₁) (b₂ / b₁) (a₁ + a₂) (b₁ + b₂ - σ.total)
    hγ (zero_le_one.trans hδ) (by linarith) hremaining hsaturation hbudget
  obtain ⟨ht, hpair⟩ := hp.prepend_right hdom h.capacity h.fits
  refine ⟨d, c, α, σ.add β ht, hpair, hα, ?_⟩
  rw [SkewMatching.add_total, hβ]
  ring

end GallaiEdmondsPartition

end Erdos547.DPRS

#print axioms Erdos547.DPRS.GallaiEdmondsPartition.IsGEPair.anchoredTotals_of_mixed_saturation
