import ErdosProblems.Erdos547.GESeparationRestricted
import ErdosProblems.Erdos547.GEPairSelectedPiece
import ErdosProblems.Erdos547.TouchingLoad
import ErdosProblems.Erdos547.MixedCoveredRegion

/-!
# The covered reachable region and its separating neighbourhood
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {γ : ℝ}

namespace GallaiEdmondsPartition

open scoped Classical in
def saturatedSeparator (D : GallaiEdmondsPartition G) (w : EdgeWeights G) (c : V)
    (σ : SkewMatching G γ) : Finset V := D.separator.filter (fun u ↦ σ.outLoad u = w.weight c u)

open scoped Classical in
def coveredReachable (D : GallaiEdmondsPartition G) (w : EdgeWeights G) (c : V)
    (μ : FractionalMatching G) (σ : SkewMatching G γ) (ν : FractionalMatching G)
    (C : Finset V) : Finset V := D.reachableVertices w c μ |>.filter
      (fun u ↦ 0 < (σ.touching (C : Set V)).load u + (ν.touching (C : Set V)).load u)

theorem saturatedSeparator_degree_le (D : GallaiEdmondsPartition G) (w : EdgeWeights G)
    (c : V) (σ : SkewMatching G γ) :
    w.degreeOn (D.saturatedSeparator w c σ) c ≤ σ.total / (1 + γ) := by
  classical
  calc
    _ = ∑ u ∈ D.saturatedSeparator w c σ, σ.outLoad u :=
      Finset.sum_congr rfl fun u hu ↦ (Finset.mem_filter.mp hu).2.symm
    _ ≤ ∑ u, σ.outLoad u := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ _) (fun u _ _ ↦ σ.outLoad_nonneg u)
    _ = _ := σ.sum_outLoad

theorem IsGEPair.restriction_runs_between {D : GallaiEdmondsPartition G}
    {w : EdgeWeights G} {c : V} {μ ν : FractionalMatching G} {σ : SkewMatching G γ}
    (h : D.IsGEPair w c μ σ ν) (hm : D.IsMaxSaturation w c μ)
    (C : Finset V) (hC : C ⊆ D.reachableNeighbours w c μ) :
    (σ.touching (C : Set V)).RunsBetween C (D.reachableVertices w c μ) ∧
      (ν.touching (C : Set V)).RunsBetween C (D.reachableVertices w c μ) := by
  classical
  have hdis : Disjoint C (D.reachableVertices w c μ) := Finset.disjoint_left.mpr
    fun u hu hv ↦ D.singleton_not_separator (hm.reachable_singleton hv)
      (hm.reachable_neighbour_separator (hC hu))
  have htσ (u v : V) (hp : 0 < (σ.touching (C : Set V)).weight u v) : u ∈ C ∨ v ∈ C := by
    by_contra hn
    rw [σ.touching_weight_of_notMem (not_or.mp hn).1 (not_or.mp hn).2] at hp
    exact lt_irrefl 0 hp
  have htν (u v : V) (hp : 0 < (ν.touching (C : Set V)).weight u v) : u ∈ C ∨ v ∈ C := by
    by_contra hn
    rw [ν.touching_weight_of_notMem (not_or.mp hn).1 (not_or.mp hn).2] at hp
    exact lt_irrefl 0 hp
  constructor
  · intro u v hp
    have hmem := htσ u v hp
    rw [σ.touching_weight_of_mem hmem] at hp
    have hc : u ∈ D.reachableNeighbours w c μ ∧ v ∈ D.reachableVertices w c μ := by
      by_contra hn
      rw [h.skew_supported u v hn] at hp
      exact lt_irrefl 0 hp
    exact ⟨hmem.resolve_right (fun hv ↦ Finset.disjoint_left.mp hdis hv hc.2), hc.2⟩
  · intro u v hp
    have hmem := htν u v hp
    rw [ν.touching_weight_of_mem hmem] at hp
    rcases hmem with hu | hv
    · exact Or.inl ⟨hu, h.fractional_partner_reachable hm (hC hu) hp⟩
    · exact Or.inr ⟨h.fractional_partner_reachable hm (hC hv) (by rwa [ν.symmetric]), hv⟩

theorem IsGEPair.coveredReachable_card_bound {D : GallaiEdmondsPartition G}
    {w : EdgeWeights G} {c : V} {μ ν : FractionalMatching G} {σ : SkewMatching G γ}
    (h : D.IsGEPair w c μ σ ν) (hm : D.IsMaxSaturation w c μ) (hγ : 1 ≤ γ)
    (C : Finset V) (hC : C ⊆ D.reachableNeighbours w c μ) :
    (C.card : ℝ) ≤ ((D.coveredReachable w c μ σ ν C).card : ℝ) := by
  classical
  have hr := h.restriction_runs_between hm C hC
  have hdis : Disjoint C (D.reachableVertices w c μ) := Finset.disjoint_left.mpr
    fun u hu hv ↦ D.singleton_not_separator (hm.reachable_singleton hv)
      (hm.reachable_neighbour_separator (hC hu))
  apply mixed_covered_region_card_bound _ _ C _ hdis hr.1 hr.2 hγ
  · intro u
    exact (add_le_add ((σ.retain_isSuballocation _).load_le u)
      ((ν.touching (C : Set V)).load_le_of_weight_le ν (ν.touching_weight_le _) u)).trans
        (h.capacity u)
  · intro u hu
    rw [σ.touching_load_of_mem hu, ν.touching_load_of_mem hu]
    exact h.covers_separator u (hm.reachable_neighbour_separator (hC hu))

theorem IsOptimalGEPair.coveredReachable_neighbours {D : GallaiEdmondsPartition G}
    {w : EdgeWeights G} {c d : V} {μ ν : FractionalMatching G} {σ : SkewMatching G γ}
    (h : D.IsOptimalGEPair w c μ σ ν) (hm : D.IsMaxSaturation w c μ) (hγ : 1 < γ)
    (hd : d ∈ D.reachableVertices w c μ)
    (hdef : σ.load d + ν.load d < w.weight c d)
    (C : Finset V) (hC : ∀ z ∈ C, G.Adj d z)
    {y x : V} (hy : y ∈ D.coveredReachable w c μ σ ν C) (hxy : G.Adj x y) :
    x ∈ D.saturatedSeparator w c σ := by
  classical
  have hyR := (Finset.mem_filter.mp hy).1
  have hyS := D.singleton_not_separator (hm.reachable_singleton hyR)
  have hxS := D.neighbour_of_singleton_mem_separator (hm.reachable_singleton hyR) hxy.symm
  apply Finset.mem_filter.mpr
  refine ⟨hxS, ?_⟩
  by_contra hn
  have hslack : σ.outLoad x < w.weight c x := lt_of_le_of_ne (h.1.fits x) hn
  have hz := h.separation_restricted hm hγ hd hdef hyS hxy.symm hslack
    (C : Set V) hC
  have hp := (Finset.mem_filter.mp hy).2
  rw [hz.1, hz.2, add_zero] at hp
  exact lt_irrefl 0 hp

end GallaiEdmondsPartition

end Erdos547.DPRS

namespace Erdos547.DPRS.GallaiEdmondsPartition
#print axioms IsGEPair.coveredReachable_card_bound
#print axioms IsOptimalGEPair.coveredReachable_neighbours
end Erdos547.DPRS.GallaiEdmondsPartition
