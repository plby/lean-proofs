import ErdosProblems.Erdos547.GEReversePiece
import ErdosProblems.Erdos547.FractionalCut

/-!
# The support and cut identities for the avoiding region
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {γ : ℝ}

namespace GallaiEdmondsPartition

open scoped Classical in
def avoidingFreeSet (D : GallaiEdmondsPartition G) (w : EdgeWeights G) (c : V)
    (μ : FractionalMatching G) (σ : SkewMatching G γ) (ν : FractionalMatching G)
    (C : Finset V) : Finset V := (C ∪ D.coveredReachable w c μ σ ν C)ᶜ

theorem IsGEPair.touching_load_zero_outside_covered {D : GallaiEdmondsPartition G}
    {w : EdgeWeights G} {c : V} {μ ν : FractionalMatching G} {σ : SkewMatching G γ}
    (h : D.IsGEPair w c μ σ ν) (hm : D.IsMaxSaturation w c μ)
    (C : Finset V) (hC : C ⊆ D.reachableNeighbours w c μ) {u : V}
    (huC : u ∉ C) (huW : u ∉ D.coveredReachable w c μ σ ν C) :
    (σ.touching (C : Set V)).load u = 0 ∧ (ν.touching (C : Set V)).load u = 0 := by
  classical
  have hr := h.restriction_runs_between hm C hC
  by_cases huR : u ∈ D.reachableVertices w c μ
  · have hh : (σ.touching (C : Set V)).load u + (ν.touching (C : Set V)).load u ≤ 0 :=
      le_of_not_gt fun hp ↦ huW (Finset.mem_filter.mpr ⟨huR, hp⟩)
    have hs := (σ.touching (C : Set V)).load_nonneg u
    have hn := (ν.touching (C : Set V)).load_nonneg u
    constructor <;> linarith
  · exact ⟨hr.1.load_zero huC huR, hr.2.load_zero_outside
      (fun hu ↦ (Finset.mem_union.mp hu).elim huC huR)⟩

theorem IsGEPair.touching_sum_load_covered {D : GallaiEdmondsPartition G}
    {w : EdgeWeights G} {c : V} {μ ν : FractionalMatching G} {σ : SkewMatching G γ}
    (h : D.IsGEPair w c μ σ ν) (hm : D.IsMaxSaturation w c μ)
    (C : Finset V) (hC : C ⊆ D.reachableNeighbours w c μ) :
    (∑ u ∈ D.coveredReachable w c μ σ ν C, (ν.touching (C : Set V)).load u) =
      (ν.touching (C : Set V)).total := by
  classical
  let R := D.reachableVertices w c μ
  have hr := (h.restriction_runs_between hm C hC).2
  have hswap : (ν.touching (C : Set V)).RunsBetween R C := fun u v hp ↦ (hr u v hp).symm
  have hdis : Disjoint R C := Finset.disjoint_left.mpr fun u hu hv ↦
    D.singleton_not_separator (hm.reachable_singleton hu) (hm.reachable_neighbour_separator (hC hv))
  calc
    _ = ∑ u ∈ R, (ν.touching (C : Set V)).load u := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro u hu hn
      exact (h.touching_load_zero_outside_covered hm C hC
        (fun huC ↦ Finset.disjoint_left.mp hdis hu huC) hn).2
    _ = _ := (hswap.crosses hdis).sum_load_side

theorem IsGEPair.reachable_skew_load {D : GallaiEdmondsPartition G}
    {w : EdgeWeights G} {c : V} {μ ν : FractionalMatching G} {σ : SkewMatching G γ}
    (h : D.IsGEPair w c μ σ ν) (hm : D.IsMaxSaturation w c μ) :
    (∑ u ∈ D.reachableVertices w c μ, σ.load u) = γ * σ.total / (1 + γ) := by
  have hr : σ.RunsBetween (D.reachableNeighbours w c μ) (D.reachableVertices w c μ) :=
    SkewMatching.runsBetween_of_zero h.skew_supported
  apply hr.sum_load_target
  exact Finset.disjoint_left.mpr fun u hu hv ↦
    D.singleton_not_separator (hm.reachable_singleton hv) (hm.reachable_neighbour_separator hu)

end GallaiEdmondsPartition

end Erdos547.DPRS

namespace Erdos547.DPRS.GallaiEdmondsPartition
#print axioms IsGEPair.touching_sum_load_covered
#print axioms IsGEPair.reachable_skew_load
end Erdos547.DPRS.GallaiEdmondsPartition
