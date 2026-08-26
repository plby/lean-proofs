import ErdosProblems.Erdos547.GEReachableSets

/-!
# Fractional and skew GE pairs

The skew allocation runs from the separator neighbourhood of the reachable
set into that set. The remaining fractional allocation is unchanged outside
these two vertex classes.
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

namespace GallaiEdmondsPartition

theorem IsMaxSaturation.load_ge_of_not_reachable {D : GallaiEdmondsPartition G}
    {w : EdgeWeights G} {c : V} {μ : FractionalMatching G} (h : D.IsMaxSaturation w c μ)
    {u : V} (hu : u ∉ D.reachableVertices w c μ) : w.weight c u ≤ μ.load u := by
  classical
  by_contra hn
  have hd : μ.load u < w.weight c u := lt_of_not_ge hn
  have hs : u ∈ D.singletonVertices := by
    rcases D.vertex_classes u with huS | huSingle | huBig
    · rw [h.1.load_separator huS] at hd
      exact (not_lt_of_ge (w.at_most_one c u) hd).elim
    · exact huSingle
    · rw [h.1.load_nontrivial huBig] at hd
      exact (not_lt_of_ge (w.at_most_one c u) hd).elim
  exact hu (Finset.mem_filter.mpr ⟨Finset.mem_univ _, u, hs, hd, Relation.ReflTransGen.refl⟩)

def ReachableCross (D : GallaiEdmondsPartition G) (w : EdgeWeights G) (c : V)
    (μ : FractionalMatching G) (u v : V) : Prop :=
  (u ∈ D.reachableVertices w c μ ∧ v ∈ D.reachableNeighbours w c μ) ∨
    (v ∈ D.reachableVertices w c μ ∧ u ∈ D.reachableNeighbours w c μ)

theorem reachableCross_of_pos (D : GallaiEdmondsPartition G) (w : EdgeWeights G)
    (c : V) (μ : FractionalMatching G) {u v : V}
    (hm : u ∈ D.reachableVertices w c μ ∪ D.reachableNeighbours w c μ ∨
      v ∈ D.reachableVertices w c μ ∪ D.reachableNeighbours w c μ)
    (hp : 0 < μ.weight u v) : D.ReachableCross w c μ u v := by
  have hps : 0 < μ.weight v u := by rw [μ.symmetric v u]; exact hp
  rcases hm with hu | hv
  · rcases Finset.mem_union.mp hu with hu | hu
    · exact Or.inl ⟨hu, D.reachable_neighbour_mem w c μ hu hp⟩
    · exact Or.inr ⟨D.reachable_partner_mem w c μ hu hp, hu⟩
  · rcases Finset.mem_union.mp hv with hv | hv
    · exact Or.inr ⟨hv, D.reachable_neighbour_mem w c μ hv hps⟩
    · exact Or.inl ⟨D.reachable_partner_mem w c μ hv hps, hv⟩

structure IsGEPair (D : GallaiEdmondsPartition G) (w : EdgeWeights G) (c : V)
    (μ : FractionalMatching G) {γ : ℝ} (σ : SkewMatching G γ)
    (ν : FractionalMatching G) : Prop where
  capacity : ∀ u, σ.load u + ν.load u ≤ 1
  skew_supported : ∀ u v,
    ¬ (u ∈ D.reachableNeighbours w c μ ∧ v ∈ D.reachableVertices w c μ) → σ.weight u v = 0
  fits : σ.Fits w c
  reachable_upper : ∀ u ∈ D.reachableVertices w c μ, σ.load u + ν.load u ≤ w.weight c u
  outside_lower : ∀ u ∉ D.reachableVertices w c μ, w.weight c u ≤ σ.load u + ν.load u
  covers_separator : ∀ u ∈ D.separator, σ.load u + ν.load u = 1
  fixed_outside : ∀ u v,
    u ∉ D.reachableVertices w c μ ∪ D.reachableNeighbours w c μ →
    v ∉ D.reachableVertices w c μ ∪ D.reachableNeighbours w c μ → ν.weight u v = μ.weight u v
  fractional_cross : ∀ u v,
    (u ∈ D.reachableVertices w c μ ∪ D.reachableNeighbours w c μ ∨
      v ∈ D.reachableVertices w c μ ∪ D.reachableNeighbours w c μ) →
    ¬ D.ReachableCross w c μ u v → ν.weight u v = 0

theorem IsMaxSaturation.initial_gePair {D : GallaiEdmondsPartition G}
    {w : EdgeWeights G} {c : V} {μ : FractionalMatching G} (h : D.IsMaxSaturation w c μ)
    (γ : ℝ) (hγ : 0 ≤ γ) : D.IsGEPair w c μ (SkewMatching.zero G γ hγ) μ := by
  have hz (u : V) : (SkewMatching.zero G γ hγ).load u = 0 := by
    simp [SkewMatching.zero, SkewMatching.load, SkewMatching.outLoad, SkewMatching.inLoad]
  refine ⟨?_, fun _ _ _ ↦ rfl, ?_, ?_, ?_, ?_, fun _ _ _ _ ↦ rfl, ?_⟩
  · intro u
    rw [hz, zero_add]
    exact μ.load_le_one u
  · intro u
    simpa only [SkewMatching.outLoad, SkewMatching.zero, Finset.sum_const_zero, zero_div] using
      w.nonnegative c u
  · intro u hu
    rw [hz, zero_add]
    exact h.reachable_load_le hu
  · intro u hu
    rw [hz, zero_add]
    exact h.load_ge_of_not_reachable hu
  · intro u hu
    rw [hz, zero_add]
    exact h.1.load_separator hu
  · intro u v hm hn
    apply le_antisymm _ (μ.nonnegative u v)
    exact le_of_not_gt fun hp ↦ hn (D.reachableCross_of_pos w c μ hm hp)

end GallaiEdmondsPartition

end Erdos547.DPRS

#print axioms Erdos547.DPRS.GallaiEdmondsPartition.IsMaxSaturation.initial_gePair
