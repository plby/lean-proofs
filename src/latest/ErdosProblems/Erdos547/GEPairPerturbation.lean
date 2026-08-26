import ErdosProblems.Erdos547.GEPairOptimization
import ErdosProblems.Erdos547.MixedAugmentation

/-!
# Perturbing GE pairs within their feasible constraints
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {γ : ℝ}

namespace GallaiEdmondsPartition

theorem IsGEPair.inLoad_eq_zero {D : GallaiEdmondsPartition G} {w : EdgeWeights G}
    {c : V} {μ ν : FractionalMatching G} {σ : SkewMatching G γ}
    (h : D.IsGEPair w c μ σ ν) {u : V} (hu : u ∉ D.reachableVertices w c μ) :
    σ.inLoad u = 0 := by
  have hcol : (∑ v, σ.weight v u) = 0 := Finset.sum_eq_zero fun v _ ↦
    h.skew_supported v u (fun hp ↦ hu hp.2)
  simp only [SkewMatching.inLoad, hcol, mul_zero, zero_div]

theorem IsGEPair.load_eq_outLoad {D : GallaiEdmondsPartition G} {w : EdgeWeights G}
    {c : V} {μ ν : FractionalMatching G} {σ : SkewMatching G γ}
    (h : D.IsGEPair w c μ σ ν) {u : V} (hu : u ∉ D.reachableVertices w c μ) :
    σ.load u = σ.outLoad u := by rw [SkewMatching.load, h.inLoad_eq_zero hu, add_zero]

theorem IsGEPair.partner_reachable {D : GallaiEdmondsPartition G} {w : EdgeWeights G}
    {c : V} {μ ν : FractionalMatching G} {σ : SkewMatching G γ}
    (hμ : D.IsMaxSaturation w c μ) (h : D.IsGEPair w c μ σ ν) {x y : V}
    (hx : x ∈ D.reachableNeighbours w c μ) (hp : 0 < ν.weight x y) :
    y ∈ D.reachableVertices w c μ := by
  have hxS := hμ.reachable_neighbour_separator hx
  have hxn : x ∉ D.reachableVertices w c μ := fun hxr ↦
    D.singleton_not_separator (hμ.reachable_singleton hxr) hxS
  have hcross : D.ReachableCross w c μ x y := by
    by_contra hn
    rw [h.fractional_cross x y (Or.inl (Finset.mem_union_right _ hx)) hn] at hp
    exact (lt_irrefl 0) hp
  rcases hcross with ⟨hxr, _⟩ | ⟨hy, _⟩
  · exact (hxn hxr).elim
  · exact hy

open scoped Classical in
theorem IsGEPair.augment {D : GallaiEdmondsPartition G} {w : EdgeWeights G}
    {c : V} {μ ν : FractionalMatching G} {σ : SkewMatching G γ}
    (hμ : D.IsMaxSaturation w c μ) (h : D.IsGEPair w c μ σ ν) {x y d : V}
    (hx : x ∈ D.reachableNeighbours w c μ) (hy : y ∈ D.reachableVertices w c μ)
    (hd : d ∈ D.reachableVertices w c μ) (hxy : G.Adj x y) (hxd : G.Adj x d)
    (b q : ℝ) (hb : 0 ≤ b) (hq : 0 ≤ q) (hbalance : γ * q = b + q)
    (he : b + q ≤ ν.weight x y) (hanchor : σ.outLoad x + (b + q) ≤ w.weight c x)
    (hroom : σ.load d + ν.load d + γ * b ≤ w.weight c d) :
    ∃ σ' : SkewMatching G γ, ∃ ν' : FractionalMatching G, D.IsGEPair w c μ σ' ν' ∧
      ∀ u, σ'.load u + ν'.load u = σ.load u + ν.load u + if u = d then γ * b else 0 := by
  classical
  obtain ⟨σ', ν', hload, hout, hsweight, hfweight⟩ := exists_mixed_augmentation σ ν h.capacity
    hxy hxd b q hb hq hbalance he (hroom.trans (w.at_most_one c d))
  have hdS : d ∉ D.separator := D.singleton_not_separator (hμ.reachable_singleton hd)
  have hcrossxy : D.ReachableCross w c μ x y := Or.inr ⟨hy, hx⟩
  have hcrossyx : D.ReachableCross w c μ y x := Or.inl ⟨hy, hx⟩
  refine ⟨σ', ν', ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hload⟩
  · intro u
    rw [hload]
    by_cases hud : u = d
    · subst u
      simpa only [ite_true] using hroom.trans (w.at_most_one c d)
    · simpa only [if_neg hud, add_zero] using h.capacity u
  · intro u v hn
    have hxdzero : arcIncrement x d ((1 + γ) * b) u v = 0 := by
      rw [arcIncrement]
      apply if_neg
      rintro ⟨rfl, rfl⟩
      exact hn ⟨hx, hd⟩
    have hxyzero : arcIncrement x y ((1 + γ) * q) u v = 0 := by
      rw [arcIncrement]
      apply if_neg
      rintro ⟨rfl, rfl⟩
      exact hn ⟨hx, hy⟩
    rw [hsweight, h.skew_supported u v hn, hxdzero, hxyzero]
    ring
  · intro u
    rw [hout]
    by_cases hux : u = x
    · subst u
      simpa only [ite_true] using hanchor
    · simpa only [if_neg hux, add_zero] using h.fits u
  · intro u hu
    rw [hload]
    by_cases hud : u = d
    · subst u
      simpa only [ite_true] using hroom
    · simpa only [if_neg hud, add_zero] using h.reachable_upper u hu
  · intro u hu
    have hud : u ≠ d := fun hud ↦ hu (hud ▸ hd)
    rw [hload, if_neg hud, add_zero]
    exact h.outside_lower u hu
  · intro u hu
    have hud : u ≠ d := fun hud ↦ hdS (hud ▸ hu)
    rw [hload, if_neg hud, add_zero]
    exact h.covers_separator u hu
  · intro u v hu hv
    have hn : ¬ D.ReachableCross w c μ u v := by
      rintro (⟨hur, _⟩ | ⟨_, hus⟩)
      · exact hu (Finset.mem_union_left _ hur)
      · exact hu (Finset.mem_union_right _ hus)
    rw [hfweight, h.fixed_outside u v hu hv,
      edgeIncrement_zero_of_not_relation (D.ReachableCross w c μ) hcrossxy hcrossyx hn (b + q),
      sub_zero]
  · intro u v hm hn
    rw [hfweight, h.fractional_cross u v hm hn,
      edgeIncrement_zero_of_not_relation (D.ReachableCross w c μ) hcrossxy hcrossyx hn (b + q),
      sub_self]

end GallaiEdmondsPartition

end Erdos547.DPRS

#print axioms Erdos547.DPRS.GallaiEdmondsPartition.IsGEPair.augment
