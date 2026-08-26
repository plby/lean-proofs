import ErdosProblems.Erdos547.GEAvoidingAllocation
import ErdosProblems.Erdos547.AvoidingFinish
import ErdosProblems.Erdos547.MixedCover

/-!
# The full avoiding case of the weighted degree structure theorem
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

namespace GallaiEdmondsPartition

open scoped Classical in
theorem IsOptimalGEPair.anchoredTotals_of_avoiding {D : GallaiEdmondsPartition G}
    {w : EdgeWeights G} {c e : V} {μ ν : FractionalMatching G}
    (A b₁ b₂ γ : ℝ) (hA : 0 < A) (hb₁ : 0 < b₁) (hb₂ : b₁ < b₂) (hγ : 0 ≤ γ)
    {σ : SkewMatching G (b₂ / b₁)}
    (h : D.IsOptimalGEPair w c μ σ ν) (hm : D.IsMaxSaturation w c μ)
    (he : e ∈ D.reachableVertices w c μ)
    (hdef : σ.load e + ν.load e < w.weight c e)
    (hσ : σ.total ≤ b₁ + b₂) (hhigh : A + b₁ + b₂ ≤ w.degree c)
    (hdeg : ∀ z, (A + b₁ + b₂) / 2 ≤ w.degree z)
    (hsmall : ((D.reachableVertices w c μ ∪ D.fullFlabellumExtra w c μ e b₁).card : ℝ) < b₂) :
    HasAnchoredTotals w γ (b₂ / b₁) A (b₁ + b₂) := by
  classical
  let R := D.reachableVertices w c μ
  let X := D.fullFlabellumExtra w c μ e b₁
  let C := Finset.univ.filter (G.Adj e)
  let U := D.avoidingFreeSet w c μ σ ν C
  let H := slackRegion w c σ (R ∪ X) C
  have hratio : 1 < b₂ / b₁ := (one_lt_div hb₁).mpr hb₂
  have hpos : 0 < b₂ / b₁ := zero_lt_one.trans hratio
  have hC : C ⊆ D.reachableNeighbours w c μ := fun u hu ↦
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, e, he, (Finset.mem_filter.mp hu).2⟩
  have hR : (R.card : ℝ) < b₂ := (Nat.cast_le.mpr
    (Finset.card_le_card (Finset.subset_union_left : R ⊆ R ∪ X))).trans_lt hsmall
  obtain ⟨ρ, hρ, htρ, _houtρ, hc, hfitβ, hbudget⟩ :=
    h.1.exists_reverse_piece_below_budget b₁ b₂ hb₁ hb₂.le hm C hC hR
  let β := σ.add ρ hc
  obtain ⟨d, α, hcd, htα, hfitα, hcap, _hαzero⟩ := h.exists_avoiding_allocation A b₁ b₂ γ
    hA hb₁ hb₂ hγ hm he hdef hσ hhigh hdeg hsmall ρ hρ htρ hc hbudget
  have hp : AnchoredPair α β w d c :=
    anchoredPair_of_residual_fit hcd.symm hcap hfitα hfitβ
  have hCeq (u : V) (hu : u ∈ C) : w.weight c u = σ.outLoad u :=
    (IsOptimalGEPair.separation_one hm h hratio he hdef (Finset.mem_filter.mp hu).2).symm
  have hH (z : V) (hz : z ∈ H) : z ∉ R ∧ z ∉ X ∧ ¬ G.Adj e z ∧
      σ.outLoad z < w.weight c z := by
    have hh := (Finset.mem_filter.mp hz).2
    refine ⟨?_, ?_, ?_, hh.2⟩
    · exact fun hu ↦ hh.1 (Finset.mem_union_left _ (Finset.mem_union_left _ hu))
    · exact fun hu ↦ hh.1 (Finset.mem_union_left _ (Finset.mem_union_right _ hu))
    · exact fun hu ↦ hh.1 (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu⟩))
  have hβH (z : V) (hz : z ∈ H) : β.load z = σ.outLoad z := by
    have hh := hH z hz
    have hnoW : z ∉ D.coveredReachable w c μ σ ν C := fun hu ↦
      hh.1 (Finset.mem_filter.mp hu).1
    have hzero := (h.1.touching_load_zero_outside_covered hm C hC
      (fun hu ↦ hh.2.2.1 (Finset.mem_filter.mp hu).2) hnoW).2
    have hle := hρ.load_le z
    rw [hzero] at hle
    have hzρ : ρ.load z = 0 := le_antisymm hle (ρ.load_nonneg z)
    change (σ.add ρ hc).load z = _
    rw [SkewMatching.add_load, hzρ, add_zero, h.1.load_eq_outLoad hh.1]
  have hs : (∑ z ∈ H, β.load z) = ∑ z ∈ H, σ.outLoad z :=
    Finset.sum_congr rfl fun z hz ↦ hβH z hz
  have hheadβ : (b₁ + b₂ - β.total) / (1 + b₂ / b₁) ≤ b₁ - σ.total / (1 + b₂ / b₁) := by
    have hρnonneg : 0 ≤ ρ.total := Finset.sum_nonneg fun u _ ↦
      Finset.sum_nonneg fun v _ ↦ ρ.nonnegative u v
    change (b₁ + b₂ - (σ.add ρ hc).total) / _ ≤ _
    rw [SkewMatching.add_total, sub_div, (skew_parts_of_sum b₁ b₂ hb₁ (hb₁.le.trans hb₂.le)).1]
    exact sub_le_sub_left (div_le_div_of_nonneg_right (by linarith) σ.denominator_pos.le) b₁
  have hanchor : (b₁ + b₂ - β.total) / (1 + b₂ / b₁) + A + (∑ z ∈ H, β.load z) ≤
      w.degreeOn H c := by
    have hh := degreeOn_slack_region_lower w c σ (R ∪ X) C hCeq
    change w.degree c - ((R ∪ X).card : ℝ) - σ.total / (1 + b₂ / b₁) +
      (∑ z ∈ H, σ.outLoad z) ≤ w.degreeOn H c at hh
    change ((R ∪ X).card : ℝ) < b₂ at hsmall
    rw [hs]
    linarith
  have hsupply (z : V) (hz : z ∈ H) :
      A + (b₁ + b₂) - β.total ≤ w.degreeOn U z - ∑ u ∈ U, β.load u := by
    have hh := hH z hz
    have hW := h.no_covered_neighbour_of_slack hm hratio he hdef C
      (fun _ hu ↦ (Finset.mem_filter.mp hu).2) hh.2.2.2
    have ht := h.1.avoiding_degree_supply b₁ b₂ (A + b₁ + b₂) hb₁ hb₂.le
      (by linarith) hm he (hdeg e) (hdeg z) hh.1 hh.2.2.1 hh.2.1 hW ρ hρ htρ hc
    simpa only [β, SkewMatching.add_total, add_assoc] using ht
  have hb : β.total ≤ b₁ + b₂ := by
    change (σ.add ρ hc).total ≤ _
    rw [SkewMatching.add_total]
    exact hbudget.le
  exact (hp.swap.finish_from_free_supply H U A (b₁ + b₂) htα hb hpos hanchor hsupply).swap

end GallaiEdmondsPartition

end Erdos547.DPRS

#print axioms Erdos547.DPRS.GallaiEdmondsPartition.IsOptimalGEPair.anchoredTotals_of_avoiding
