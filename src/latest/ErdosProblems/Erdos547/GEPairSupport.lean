import ErdosProblems.Erdos547.GEPairs
import ErdosProblems.Erdos547.SkewBipartiteSupport

/-!
# Separator support properties of mixed GE pairs
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {γ : ℝ}

namespace GallaiEdmondsPartition

theorem IsGEPair.runsFrom_separator {D : GallaiEdmondsPartition G} {w : EdgeWeights G}
    {c : V} {μ ν : FractionalMatching G} {σ : SkewMatching G γ}
    (h : D.IsGEPair w c μ σ ν) (hm : D.IsMaxSaturation w c μ) :
    σ.RunsFrom D.separator := by
  intro u v hp
  have huv : u ∈ D.reachableNeighbours w c μ ∧ v ∈ D.reachableVertices w c μ := by
    by_contra hn
    rw [h.skew_supported u v hn] at hp
    exact lt_irrefl 0 hp
  exact ⟨hm.reachable_neighbour_separator huv.1,
    D.singleton_not_separator (hm.reachable_singleton huv.2)⟩

theorem IsGEPair.fractional_zero_separator {D : GallaiEdmondsPartition G} {w : EdgeWeights G}
    {c : V} {μ ν : FractionalMatching G} {σ : SkewMatching G γ}
    (h : D.IsGEPair w c μ σ ν) (hm : D.IsMaxSaturation w c μ)
    {u v : V} (hu : u ∈ D.separator) (hv : v ∈ D.separator) : ν.weight u v = 0 := by
  have huR : u ∉ D.reachableVertices w c μ := fun hh ↦
    D.singleton_not_separator (hm.reachable_singleton hh) hu
  have hvR : v ∉ D.reachableVertices w c μ := fun hh ↦
    D.singleton_not_separator (hm.reachable_singleton hh) hv
  by_cases hmem : u ∈ D.reachableVertices w c μ ∪ D.reachableNeighbours w c μ ∨
      v ∈ D.reachableVertices w c μ ∪ D.reachableNeighbours w c μ
  · apply h.fractional_cross u v hmem
    rintro (h | h)
    · exact huR h.1
    · exact hvR h.1
  · rw [h.fixed_outside u v (fun hh ↦ hmem (Or.inl hh)) (fun hh ↦ hmem (Or.inr hh))]
    exact hm.1.2 u v (D.not_allowed_separator hu hv)

end GallaiEdmondsPartition

end Erdos547.DPRS

#print axioms Erdos547.DPRS.GallaiEdmondsPartition.IsGEPair.fractional_zero_separator
