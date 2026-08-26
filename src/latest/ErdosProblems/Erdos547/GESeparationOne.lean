import ErdosProblems.Erdos547.GEPairPerturbation

/-!
# First separation lemma for an optimal GE pair

A deficient reachable vertex has no neighbour with unused anchor capacity.
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph
open scoped BigOperators

theorem exists_small_balanced_increment (γ A B C : ℝ) (hγ : 1 < γ)
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) :
    ∃ b q : ℝ, 0 < b ∧ 0 < q ∧ γ * q = b + q ∧ b + q ≤ A ∧ b + q ≤ B ∧ γ * b ≤ C := by
  have hγpos : 0 < γ := by linarith
  have hm : 0 < γ - 1 := sub_pos.mpr hγ
  have hprod : 0 < γ * (γ - 1) := mul_pos hγpos hm
  let q := min (A / γ) (min (B / γ) (C / (γ * (γ - 1))))
  have hq : 0 < q := lt_min (div_pos hA hγpos)
    (lt_min (div_pos hB hγpos) (div_pos hC hprod))
  have hqA : q * γ ≤ A := (le_div_iff₀ hγpos).mp (min_le_left _ _)
  have hqB : q * γ ≤ B := (le_div_iff₀ hγpos).mp ((min_le_right _ _).trans (min_le_left _ _))
  have hqC : q * (γ * (γ - 1)) ≤ C :=
    (le_div_iff₀ hprod).mp ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨(γ - 1) * q, q, mul_pos hm hq, hq, ?_, ?_, ?_, ?_⟩
  · ring
  · nlinarith only [hqA]
  · nlinarith only [hqB]
  · convert hqC using 1
    ring

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {γ : ℝ}

namespace GallaiEdmondsPartition

def IsOptimalGEPair (D : GallaiEdmondsPartition G) (w : EdgeWeights G) (c : V)
    (μ : FractionalMatching G) (σ : SkewMatching G γ) (ν : FractionalMatching G) : Prop :=
  D.IsGEPair w c μ σ ν ∧ ∀ τ : SkewMatching G γ, ∀ ξ : FractionalMatching G,
    D.IsGEPair w c μ τ ξ → w.saturation (fun u ↦ τ.load u + ξ.load u) c ≤
      w.saturation (fun u ↦ σ.load u + ν.load u) c

theorem IsOptimalGEPair.separation_one {D : GallaiEdmondsPartition G} {w : EdgeWeights G}
    {c : V} {μ ν : FractionalMatching G} {σ : SkewMatching G γ}
    (hμ : D.IsMaxSaturation w c μ) (h : D.IsOptimalGEPair w c μ σ ν) (hγ : 1 < γ)
    {d x : V} (hd : d ∈ D.reachableVertices w c μ)
    (hdef : σ.load d + ν.load d < w.weight c d) (hdx : G.Adj d x) :
    σ.outLoad x = w.weight c x := by
  classical
  have hx : x ∈ D.reachableNeighbours w c μ :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, d, hd, hdx⟩
  have hxS := hμ.reachable_neighbour_separator hx
  have hxR : x ∉ D.reachableVertices w c μ := fun hxr ↦
    D.singleton_not_separator (hμ.reachable_singleton hxr) hxS
  apply le_antisymm (h.1.fits x)
  by_contra hn
  have hroom : σ.outLoad x < w.weight c x := lt_of_not_ge hn
  have hcover := h.1.covers_separator x hxS
  rw [h.1.load_eq_outLoad hxR] at hcover
  have hνload : 0 < ν.load x := by linarith [w.at_most_one c x]
  have hex : ∃ y, 0 < ν.weight x y := by
    by_contra hn
    push Not at hn
    have hsum : ν.load x ≤ 0 := Finset.sum_nonpos fun y _ ↦ hn y
    linarith
  obtain ⟨y, hypos⟩ := hex
  have hyR := h.1.partner_reachable hμ hx hypos
  have hxy := ν.adj_of_weight_pos hypos
  obtain ⟨b, q, hb, hq, hbalance, hA, he, hC⟩ := exists_small_balanced_increment γ
    (w.weight c x - σ.outLoad x) (ν.weight x y) (w.weight c d - (σ.load d + ν.load d))
    hγ (sub_pos.mpr hroom) hypos (sub_pos.mpr hdef)
  obtain ⟨σ', ν', hpair, hload⟩ := h.1.augment hμ hx hyR hd hxy hdx.symm b q hb.le hq.le
    hbalance he (by linarith) (by linarith)
  have hγb : 0 < γ * b := mul_pos (by linarith) hb
  have hnewd : σ'.load d + ν'.load d = σ.load d + ν.load d + γ * b := by
    simpa only [ite_true] using hload d
  have hstrict : min (w.weight c d) (σ.load d + ν.load d) <
      min (w.weight c d) (σ'.load d + ν'.load d) := by
    rw [min_eq_right hdef.le, min_eq_right (hpair.reachable_upper d hd), hnewd]
    linarith
  have hle (u : V) : min (w.weight c u) (σ.load u + ν.load u) ≤
      min (w.weight c u) (σ'.load u + ν'.load u) := by
    rw [hload]
    apply min_le_min_left
    split_ifs <;> linarith
  have hsum : w.saturation (fun u ↦ σ.load u + ν.load u) c <
      w.saturation (fun u ↦ σ'.load u + ν'.load u) c :=
    Finset.sum_lt_sum (fun u _ ↦ hle u) ⟨d, Finset.mem_univ d, hstrict⟩
  exact (not_lt_of_ge (h.2 σ' ν' hpair)) hsum

end GallaiEdmondsPartition

end Erdos547.DPRS

#print axioms Erdos547.DPRS.GallaiEdmondsPartition.IsOptimalGEPair.separation_one
