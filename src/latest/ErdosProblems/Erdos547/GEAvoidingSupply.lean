import ErdosProblems.Erdos547.GEAvoidingSupport
import ErdosProblems.Erdos547.GEAvoidingPiece
import ErdosProblems.Erdos547.FullFlabellum
import ErdosProblems.Erdos547.CoveredRemainder

/-!
# Uniform supply estimates on the free avoiding region
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {γ : ℝ}

theorem EdgeWeights.degreeOn_free_region (w : EdgeWeights G) (z : V) (C W : Finset V)
    (hW : ∀ u ∈ W, ¬ G.Adj z u) :
    w.degreeOn (C ∪ W)ᶜ z = w.degree z - w.degreeOn C z := by
  classical
  have he : w.degreeOn (C ∪ W) z = w.degreeOn C z := by
    symm
    apply Finset.sum_subset Finset.subset_union_left
    intro u hu hn
    exact w.supported z u (hW u ((Finset.mem_union.mp hu).resolve_left hn))
  have hs := Finset.sum_add_sum_compl (C ∪ W) (w.weight z)
  change w.degreeOn (C ∪ W) z + w.degreeOn (C ∪ W)ᶜ z = w.degree z at hs
  rw [he] at hs
  linarith

namespace GallaiEdmondsPartition

theorem IsGEPair.reverse_load_on_free_set_le {D : GallaiEdmondsPartition G}
    {w : EdgeWeights G} {c : V} {μ ν : FractionalMatching G} {σ : SkewMatching G γ}
    (h : D.IsGEPair w c μ σ ν) (hm : D.IsMaxSaturation w c μ)
    (C : Finset V) (hC : C ⊆ D.reachableNeighbours w c μ)
    (ρ : SkewMatching G γ) (hρ : ρ.DominatedByFractional (ν.touching (C : Set V)))
    (hc : ∀ u, σ.load u + ρ.load u ≤ 1) :
    (∑ u ∈ D.avoidingFreeSet w c μ σ ν C, (σ.add ρ hc).load u) ≤
      σ.total - (σ.touching (C : Set V)).total := by
  classical
  let U := D.avoidingFreeSet w c μ σ ν C
  have hz (u : V) (hu : u ∈ U) := h.touching_load_zero_outside_covered hm C hC
    (fun hh ↦ Finset.mem_compl.mp hu (Finset.mem_union_left _ hh))
    (fun hh ↦ Finset.mem_compl.mp hu (Finset.mem_union_right _ hh))
  calc
    _ = ∑ u ∈ U, σ.load u := Finset.sum_congr rfl fun u hu ↦ by
      have hh := hρ.load_le u
      rw [(hz u hu).2] at hh
      have he : ρ.load u = 0 := le_antisymm hh (ρ.load_nonneg u)
      rw [SkewMatching.add_load, he, add_zero]
    _ ≤ _ := (σ.retain_isSuballocation _).sum_load_outside_le U
      (fun u hu ↦ (hz u hu).1)

open scoped Classical in
theorem IsGEPair.avoiding_degree_supply {D : GallaiEdmondsPartition G}
    {w : EdgeWeights G} {c e z : V} {μ ν : FractionalMatching G}
    (b₁ b₂ k : ℝ) (hb₁ : 0 < b₁) (hb₂ : b₁ ≤ b₂) (hbk : b₂ ≤ k)
    {σ : SkewMatching G (b₂ / b₁)}
    (h : D.IsGEPair w c μ σ ν) (hm : D.IsMaxSaturation w c μ)
    (he : e ∈ D.reachableVertices w c μ)
    (hde : k / 2 ≤ w.degree e) (hdz : k / 2 ≤ w.degree z)
    (hzR : z ∉ D.reachableVertices w c μ) (hzC : ¬ G.Adj e z)
    (hzX : z ∉ D.fullFlabellumExtra w c μ e b₁)
    (hW : ∀ u ∈ D.coveredReachable w c μ σ ν (Finset.univ.filter (G.Adj e)), ¬ G.Adj z u)
    (ρ : SkewMatching G (b₂ / b₁))
    (hρ : ρ.DominatedByFractional (ν.touching (Finset.univ.filter (G.Adj e) : Set V)))
    (htρ : ρ.total = (1 + b₂ / b₁) / (b₂ / b₁) *
      (ν.touching (Finset.univ.filter (G.Adj e) : Set V)).total)
    (hc : ∀ u, σ.load u + ρ.load u ≤ 1) :
    k - (σ.total + ρ.total) ≤
      w.degreeOn (D.avoidingFreeSet w c μ σ ν (Finset.univ.filter (G.Adj e))) z -
        ∑ u ∈ D.avoidingFreeSet w c μ σ ν (Finset.univ.filter (G.Adj e)),
          (σ.add ρ hc).load u := by
  classical
  let C := Finset.univ.filter (G.Adj e)
  have hC : C ⊆ D.reachableNeighbours w c μ := fun u hu ↦
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, e, he, (Finset.mem_filter.mp hu).2⟩
  have hov := D.degreeOn_lt_of_not_fullFlabellumExtra w c μ e b₁ hzR hzC hzX
  have hmass := h.restricted_reverse_mass_gt b₁ b₂ k hb₁ hb₂ hbk hm he hde hov
  rw [← htρ] at hmass
  have hs := h.reverse_load_on_free_set_le hm C hC ρ hρ hc
  have hd := w.degreeOn_free_region z C (D.coveredReachable w c μ σ ν C) hW
  change w.degreeOn (D.avoidingFreeSet w c μ σ ν C) z = w.degree z - w.degreeOn C z at hd
  change w.degreeOn C z + k / 2 < ρ.total + (σ.touching (C : Set V)).total at hmass
  change k - (σ.total + ρ.total) ≤ w.degreeOn (D.avoidingFreeSet w c μ σ ν C) z - _
  linarith

theorem IsOptimalGEPair.no_covered_neighbour_of_slack {D : GallaiEdmondsPartition G}
    {w : EdgeWeights G} {c e z : V} {μ ν : FractionalMatching G} {σ : SkewMatching G γ}
    (h : D.IsOptimalGEPair w c μ σ ν) (hm : D.IsMaxSaturation w c μ) (hγ : 1 < γ)
    (he : e ∈ D.reachableVertices w c μ)
    (hdef : σ.load e + ν.load e < w.weight c e)
    (C : Finset V) (hC : ∀ u ∈ C, G.Adj e u) (hz : σ.outLoad z < w.weight c z) :
    ∀ u ∈ D.coveredReachable w c μ σ ν C, ¬ G.Adj z u := by
  intro u hu hzu
  have hh := h.coveredReachable_neighbours hm hγ he hdef C hC hu hzu
  exact (ne_of_lt hz) (Finset.mem_filter.mp hh).2

theorem IsMaxSaturation.no_covered_neighbour_of_singleton {D : GallaiEdmondsPartition G}
    {w : EdgeWeights G} {c z : V} {μ ν : FractionalMatching G} {σ : SkewMatching G γ}
    (hm : D.IsMaxSaturation w c μ) (C : Finset V) (hz : z ∈ D.singletonVertices) :
    ∀ u ∈ D.coveredReachable w c μ σ ν C, ¬ G.Adj z u := by
  intro u hu hzu
  exact D.singleton_not_separator (hm.reachable_singleton (Finset.mem_filter.mp hu).1)
    (D.neighbour_of_singleton_mem_separator hz hzu)

end GallaiEdmondsPartition

end Erdos547.DPRS

#print axioms Erdos547.DPRS.GallaiEdmondsPartition.IsGEPair.avoiding_degree_supply
