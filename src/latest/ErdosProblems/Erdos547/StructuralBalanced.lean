import ErdosProblems.Erdos547.CappedProfilePiece
import ErdosProblems.Erdos547.CutGreedyFinish
import ErdosProblems.Erdos547.FillBesideRight
import ErdosProblems.Erdos547.SkewSupportTransfer
import ErdosProblems.Erdos547.StructuralMixedSaturation

/-!
# The balanced structural case with the proved separation property
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

namespace GallaiEdmondsPartition

theorem IsGEPair.anchoredTotals_of_balanced_with_separation {D : GallaiEdmondsPartition G}
    {w : EdgeWeights G} {c d : V} {μ ν : FractionalMatching G}
    (a₁ a₂ b₁ b₂ : ℝ) {σ : SkewMatching G (b₂ / b₁)}
    (h : D.IsGEPair w c μ σ ν) (hm : D.IsMaxSaturation w c μ)
    (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (hb₁ : 0 < b₁) (hskew : b₁ ≤ b₂)
    (hd : d ∈ D.reachableVertices w c μ) (hcd : G.Adj c d)
    (hsep : ∀ u, G.Adj d u → σ.outLoad u = w.weight c u)
    (hlarge : a₁ + a₂ + b₁ + b₂ ≤ w.degree c)
    (hdeg : ∀ v, (a₁ + a₂ + b₁ + b₂) / 2 ≤ w.degree v)
    (hsmall : max a₁ a₂ + b₁ ≤ (a₁ + a₂ + b₁ + b₂) / 2)
    (hbalanced : b₂ ≤ (a₁ + a₂ + b₁ + b₂) / 2) :
    HasAnchoredTotals w (a₂ / a₁) (b₂ / b₁) (a₁ + a₂) (b₁ + b₂) := by
  classical
  by_cases hbig : b₁ + b₂ ≤ σ.total
  · exact h.anchoredTotals_of_skew_cover a₁ a₂ b₁ b₂ hm ha₁ ha₂.le hb₁ hskew
      ⟨d, hd⟩ hbig hdeg hsmall
  have hδ : 1 ≤ b₂ / b₁ := (one_le_div hb₁).mpr hskew
  let δ := b₂ / b₁
  have hδpos : 0 < δ := zero_lt_one.trans_le hδ
  have hden : 0 < 1 + δ := by linarith
  obtain ⟨K⟩ := h.exists_capped_profile hm hδ d
  let τ := K.kept
  let F := K.fractional
  let w' := w.truncate τ.load τ.load_nonneg
  have hremaining : 0 < b₁ + b₂ - τ.total := by
    have hh := K.kept_sub.total_le
    change τ.total ≤ σ.total at hh
    linarith
  have hτ0 : 0 ≤ τ.total := by
    rw [← τ.sum_load]
    exact Finset.sum_nonneg fun u _ ↦ τ.load_nonneg u
  let q := δ * ((b₁ + b₂ - τ.total) / (1 + δ))
  have hq : 0 ≤ q := mul_nonneg hδpos.le (div_nonneg hremaining.le hden.le)
  have hN (u : V) (hdu : G.Adj d u) : u ∈ D.separator :=
    D.neighbour_of_singleton_mem_separator (hm.reachable_singleton hd) hdu
  obtain ⟨hbParts, hbParts'⟩ := skew_parts_of_sum b₁ b₂ hb₁ (hb₁.le.trans hskew)
  have hqsize : q ≤ w'.degree d := by
    have he := w.degree_truncate_add_saturation τ.load τ.load_nonneg d
    have hsat := w.saturation_le_sum_of_neighbours_subset τ.load τ.load_nonneg d D.separator hN
    rw [K.kept_runs.sum_load_side] at hsat
    have hqeq : q = b₂ - δ * (τ.total / (1 + δ)) := by
      dsimp [q, δ]
      rw [sub_div, mul_sub, hbParts']
    have hmul := mul_le_mul_of_nonneg_right hδ (div_nonneg hτ0 hden.le)
    rw [one_mul] at hmul
    change τ.total / (1 + δ) ≤ δ * (τ.total / (1 + δ)) at hmul
    rw [hqeq]
    change w'.degree d + w.saturation τ.load d = w.degree d at he
    change w.saturation τ.load d ≤ τ.total / (1 + δ) at hsat
    linarith [hdeg d]
  obtain ⟨P, hPν, hbetween, htotalP, hfitP, hlossP⟩ :=
    K.exists_private_piece (h.runsFrom_separator hm) hN hsep q hq hqsize
  have hPF (u v : V) : P.weight u v ≤ F.weight u v := (hPν u v).trans (K.fractional_le u v)
  have hcross := hbetween.crosses disjoint_compl_right
  obtain ⟨β, hβ, htotalβ, houtβ⟩ := exists_full_orientation P D.separator hcross δ hδpos.le
  have htβ : β.total = b₁ + b₂ - τ.total := by
    rw [htotalβ, htotalP, orientationRate, max_eq_right hδ]
    change ((1 + δ) / δ) * (δ * ((b₁ + b₂ - τ.total) / (1 + δ))) = _
    field_simp [ne_of_gt hden, ne_of_gt hδpos]
  have hβruns := hβ.runsFrom_of_crosses D.separator hcross houtβ
  have hβfit : β.Fits w' d := by
    intro u
    by_cases hu : u ∈ D.separator
    · exact ((β.outLoad_le_load u).trans (hβ.load_le u)).trans (hfitP u hu)
    · rw [houtβ u hu]
      exact w'.nonnegative d u
  have hbudget : w'.saturation P.load c ≤ β.total := by
    have hr := one_le_orientationRate hδpos.le
    rw [htotalβ]
    exact hlossP.trans (le_mul_of_one_le_left P.total_nonneg hr)
  obtain ⟨α, hp, hdom, hsat⟩ := fill_beside_right F P hPF w' hcd β hβ hβfit hbudget
    (a₂ / a₁) (div_nonneg ha₂.le ha₁.le)
  obtain ⟨ht, hp'⟩ := hp.prepend_right hdom
    (fun u ↦ by linarith [K.capacity u]) K.kept_fits
  let τ' := τ.add β ht
  have htτ' : τ'.total = b₁ + b₂ := by rw [SkewMatching.add_total, htβ]; ring
  let l := fun u ↦ F.load u + τ.load u
  have hsaturation : w.saturation l c ≤ α.total + τ'.total := by
    have he := w.saturation_add_load τ.load F.load τ.load_nonneg F.load_nonneg c
    have hl : (fun u ↦ τ.load u + F.load u) = l := funext fun u ↦ add_comm _ _
    rw [hl] at he
    have hh := w.saturation_le_sum_load τ.load c
    rw [τ.sum_load] at hh
    change w.saturation τ.load c + w'.saturation F.load c = _ at he
    change _ ≤ α.total + (τ.add β ht).total
    rw [SkewMatching.add_total]
    linarith
  have hload (u : V) : α.load u + τ'.load u ≤ l u := by
    change α.load u + (τ.add β ht).load u ≤ F.load u + τ.load u
    rw [SkewMatching.add_load]
    linarith [hdom.load_le u]
  have hzero (u : V) (hu : u ∈ D.separator) (v : V) (hv : v ∈ D.separator) :
      α.weight u v = 0 := hdom.left.weight_eq_zero (K.separator_zero u hu v hv)
  have hdis : Disjoint (D.reachableVertices w c μ) D.separator := Finset.disjoint_left.mpr
    fun _ hu hv ↦ D.singleton_not_separator (hm.reachable_singleton hu) hv
  apply finish_anchored_totals_from_cut hp' (D.reachableVertices w c μ) D.separator hdis l
    hload K.cut_upper K.cut_lower hsaturation hzero (K.kept_runs.add hβruns ht)
    (fun _ hx _ hxy ↦ D.neighbour_of_singleton_mem_separator (hm.reachable_singleton hx) hxy)
    (a₁ + a₂) (b₁ + b₂) (by positivity) htτ' (div_pos ha₂ ha₁)
  · linarith
  · intro x _
    obtain ⟨haParts, haParts'⟩ := skew_parts_of_sum a₁ a₂ ha₁ ha₂.le
    rw [haParts', haParts, hbParts]
    exact hsmall.trans (hdeg x)

end GallaiEdmondsPartition

end Erdos547.DPRS

namespace Erdos547.DPRS.GallaiEdmondsPartition
#print axioms IsGEPair.anchoredTotals_of_balanced_with_separation
end Erdos547.DPRS.GallaiEdmondsPartition
