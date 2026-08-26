import ErdosProblems.Erdos547.GESeparationOne
import ErdosProblems.Erdos547.LoadTransfer

/-!
# Moving load between reachable vertices of a GE pair
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {γ : ℝ}

namespace GallaiEdmondsPartition

theorem IsGEPair.of_load_transfer {D : GallaiEdmondsPartition G} {w : EdgeWeights G}
    {c : V} {μ ν : FractionalMatching G} {σ : SkewMatching G γ}
    (hμ : D.IsMaxSaturation w c μ) (h : D.IsGEPair w c μ σ ν)
    (τ : SkewMatching G γ) (ξ : FractionalMatching G) {d y : V}
    (hd : d ∈ D.reachableVertices w c μ) (hy : y ∈ D.reachableVertices w c μ)
    (t : ℝ) (ht : 0 ≤ t) (hroom : σ.load d + ν.load d + t ≤ w.weight c d)
    (hload : ∀ u, τ.load u + ξ.load u = σ.load u + ν.load u +
      (if u = d then t else 0) - (if u = y then t else 0))
    (hout : ∀ u, τ.outLoad u = σ.outLoad u)
    (hs : ∀ u v, ¬ (u ∈ D.reachableNeighbours w c μ ∧
      v ∈ D.reachableVertices w c μ) → τ.weight u v = 0)
    (hf : ∀ u v, ¬ D.ReachableCross w c μ u v → ξ.weight u v = ν.weight u v) :
    D.IsGEPair w c μ τ ξ := by
  classical
  have hle (u : V) : τ.load u + ξ.load u ≤ σ.load u + ν.load u +
      (if u = d then t else 0) := by
    rw [hload]
    split_ifs <;> linarith
  have houtside (u : V) (hu : u ∉ D.reachableVertices w c μ) :
      τ.load u + ξ.load u = σ.load u + ν.load u := by
    have hud : u ≠ d := fun he ↦ hu (he ▸ hd)
    have huy : u ≠ y := fun he ↦ hu (he ▸ hy)
    rw [hload, if_neg hud, if_neg huy, add_zero, sub_zero]
  refine ⟨?_, hs, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro u
    by_cases hud : u = d
    · subst u
      have hh : τ.load d + ξ.load d ≤ σ.load d + ν.load d + t := by
        simpa only [ite_true] using hle d
      exact hh.trans (hroom.trans (w.at_most_one c d))
    · have hh : τ.load u + ξ.load u ≤ σ.load u + ν.load u := by
        simpa only [if_neg hud, add_zero] using hle u
      exact hh.trans (h.capacity u)
  · intro u
    rw [hout]
    exact h.fits u
  · intro u hu
    by_cases hud : u = d
    · subst u
      have hh : τ.load d + ξ.load d ≤ σ.load d + ν.load d + t := by
        simpa only [ite_true] using hle d
      exact hh.trans hroom
    · have hh : τ.load u + ξ.load u ≤ σ.load u + ν.load u := by
        simpa only [if_neg hud, add_zero] using hle u
      exact hh.trans (h.reachable_upper u hu)
  · intro u hu
    rw [houtside u hu]
    exact h.outside_lower u hu
  · intro u hu
    have hn : u ∉ D.reachableVertices w c μ := fun hr ↦
      D.singleton_not_separator (hμ.reachable_singleton hr) hu
    rw [houtside u hn]
    exact h.covers_separator u hu
  · intro u v hu hv
    have hn : ¬ D.ReachableCross w c μ u v := by
      rintro (⟨hur, _⟩ | ⟨_, hus⟩)
      · exact hu (Finset.mem_union_left _ hur)
      · exact hu (Finset.mem_union_right _ hus)
    rw [hf u v hn]
    exact h.fixed_outside u v hu hv
  · intro u v hm hn
    rw [hf u v hn]
    exact h.fractional_cross u v hm hn

theorem IsOptimalGEPair.of_equal_saturation {D : GallaiEdmondsPartition G}
    {w : EdgeWeights G} {c : V} {μ ν ξ : FractionalMatching G}
    {σ τ : SkewMatching G γ} (h : D.IsOptimalGEPair w c μ σ ν)
    (hp : D.IsGEPair w c μ τ ξ)
    (he : w.saturation (fun u ↦ τ.load u + ξ.load u) c =
      w.saturation (fun u ↦ σ.load u + ν.load u) c) :
    D.IsOptimalGEPair w c μ τ ξ := by
  refine ⟨hp, ?_⟩
  intro ρ η hq
  rw [he]
  exact h.2 ρ η hq

theorem IsGEPair.shift_fractional {D : GallaiEdmondsPartition G} {w : EdgeWeights G}
    {c : V} {μ ν : FractionalMatching G} {σ : SkewMatching G γ}
    (hμ : D.IsMaxSaturation w c μ) (h : D.IsGEPair w c μ σ ν) {d y z : V}
    (hd : d ∈ D.reachableVertices w c μ) (hy : y ∈ D.reachableVertices w c μ)
    (hz : z ∈ D.reachableNeighbours w c μ) (hdz : G.Adj d z) (hyz : G.Adj y z)
    (hdy : d ≠ y) (t : ℝ) (ht : 0 ≤ t) (he : t ≤ ν.weight y z)
    (hroom : σ.load d + ν.load d + t ≤ w.weight c d) :
    ∃ ξ : FractionalMatching G, D.IsGEPair w c μ σ ξ ∧
      ∀ u, σ.load u + ξ.load u = σ.load u + ν.load u +
        (if u = d then t else 0) - (if u = y then t else 0) := by
  have hc : ν.load d + t ≤ 1 := by
    linarith [σ.load_nonneg d, w.at_most_one c d]
  let ξ := ν.transfer hdz hyz hdy t ht he hc
  have hl (u : V) : σ.load u + ξ.load u = σ.load u + ν.load u +
      (if u = d then t else 0) - (if u = y then t else 0) := by
    change σ.load u + (ν.transfer hdz hyz hdy t ht he hc).load u = _
    rw [ν.transfer_load]
    split_ifs <;> ring
  refine ⟨ξ, h.of_load_transfer hμ σ ξ hd hy t ht hroom hl (fun _ ↦ rfl)
    h.skew_supported ?_, hl⟩
  intro u v hn
  change ν.weight u v + edgeIncrement d z t u v - edgeIncrement y z t u v = _
  rw [edgeIncrement_zero_of_not_relation (D.ReachableCross w c μ)
      (Or.inl ⟨hd, hz⟩) (Or.inr ⟨hd, hz⟩) hn t,
    edgeIncrement_zero_of_not_relation (D.ReachableCross w c μ)
      (Or.inl ⟨hy, hz⟩) (Or.inr ⟨hy, hz⟩) hn t]
  ring

theorem IsGEPair.shift_skew {D : GallaiEdmondsPartition G} {w : EdgeWeights G}
    {c : V} {μ ν : FractionalMatching G} {σ : SkewMatching G γ}
    (hμ : D.IsMaxSaturation w c μ) (h : D.IsGEPair w c μ σ ν) {d y z : V}
    (hd : d ∈ D.reachableVertices w c μ) (hy : y ∈ D.reachableVertices w c μ)
    (hz : z ∈ D.reachableNeighbours w c μ) (hzd : G.Adj z d) (hzy : G.Adj z y)
    (hyd : y ≠ d) (t : ℝ) (ht : 0 ≤ t) (he : (1 + γ) * t ≤ σ.weight z y)
    (hroom : σ.load d + ν.load d + γ * t ≤ w.weight c d) :
    ∃ τ : SkewMatching G γ, D.IsGEPair w c μ τ ν ∧
      (∀ u, τ.outLoad u = σ.outLoad u) ∧
      ∀ u, τ.load u + ν.load u = σ.load u + ν.load u +
        (if u = d then γ * t else 0) - (if u = y then γ * t else 0) := by
  have hc : σ.load d + γ * t ≤ 1 := by
    linarith [ν.load_nonneg d, w.at_most_one c d]
  obtain ⟨τ, hload, hout, hw⟩ := σ.exists_redirect hzy hzd hyd t ht he hc
  have hl (u : V) : τ.load u + ν.load u = σ.load u + ν.load u +
      (if u = d then γ * t else 0) - (if u = y then γ * t else 0) := by
    rw [hload]
    ring
  refine ⟨τ, h.of_load_transfer hμ τ ν hd hy (γ * t) (mul_nonneg σ.skew_nonneg ht)
    hroom hl hout ?_ (fun _ _ _ ↦ rfl), hout, hl⟩
  intro u v hn
  have hd0 : arcIncrement z d ((1 + γ) * t) u v = 0 := by
    rw [arcIncrement]
    apply if_neg
    rintro ⟨rfl, rfl⟩
    exact hn ⟨hz, hd⟩
  have hy0 : arcIncrement z y ((1 + γ) * t) u v = 0 := by
    rw [arcIncrement]
    apply if_neg
    rintro ⟨rfl, rfl⟩
    exact hn ⟨hz, hy⟩
  rw [hw, h.skew_supported u v hn, hd0, hy0]
  ring

end GallaiEdmondsPartition

end Erdos547.DPRS

#print axioms Erdos547.DPRS.GallaiEdmondsPartition.IsGEPair.shift_fractional
#print axioms Erdos547.DPRS.GallaiEdmondsPartition.IsGEPair.shift_skew
