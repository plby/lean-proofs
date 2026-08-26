import ErdosProblems.Erdos547.GESeparationTwo
import ErdosProblems.Erdos547.AllocationRestriction

/-!
# Separation after restriction to a deficient vertex's neighbourhood
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {γ : ℝ}

namespace GallaiEdmondsPartition

theorem IsOptimalGEPair.separation_restricted {D : GallaiEdmondsPartition G}
    {w : EdgeWeights G} {c : V} {μ ν : FractionalMatching G} {σ : SkewMatching G γ}
    (hμ : D.IsMaxSaturation w c μ) (h : D.IsOptimalGEPair w c μ σ ν) (hγ : 1 < γ)
    {d y x : V} (hd : d ∈ D.reachableVertices w c μ)
    (hdef : σ.load d + ν.load d < w.weight c d) (hy : y ∉ D.separator)
    (hyx : G.Adj y x) (hslack : σ.outLoad x < w.weight c x)
    (C : Set V) (hC : ∀ z ∈ C, G.Adj d z) :
    (σ.touching C).load y = 0 ∧ (ν.touching C).load y = 0 := by
  classical
  have hyC : y ∉ C := by
    intro hyC
    have hz : y ∈ D.reachableNeighbours w c μ :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, d, hd, hC y hyC⟩
    exact hy (hμ.reachable_neighbour_separator hz)
  have hsy (z : V) : σ.weight y z = 0 := h.1.skew_supported y z
    (fun hp ↦ hy (hμ.reachable_neighbour_separator hp.1))
  have hsout (z : V) : (σ.touching C).weight y z = 0 := by
    by_cases hz : z ∈ C
    · rw [σ.touching_weight_of_mem (Or.inr hz), hsy]
    · exact σ.touching_weight_of_notMem hyC hz
  have hsin (z : V) : (σ.touching C).weight z y = 0 := by
    by_cases hz : z ∈ C
    · rw [σ.touching_weight_of_mem (Or.inl hz)]
      exact h.separation_two_skew hμ hγ hd hdef (hC z hz) hyx hslack
    · exact σ.touching_weight_of_notMem hz hyC
  have hν (z : V) : (ν.touching C).weight y z = 0 := by
    by_cases hz : z ∈ C
    · rw [ν.touching_weight_of_mem (Or.inr hz), ν.symmetric y z]
      exact h.separation_two_fractional hμ hγ hd hdef (hC z hz) hyx hslack
    · exact ν.touching_weight_of_notMem hyC hz
  exact ⟨(σ.touching C).load_eq_zero_of_weights y hsout hsin,
    Finset.sum_eq_zero fun z _ ↦ hν z⟩

end GallaiEdmondsPartition

end Erdos547.DPRS

#print axioms Erdos547.DPRS.GallaiEdmondsPartition.IsOptimalGEPair.separation_restricted
