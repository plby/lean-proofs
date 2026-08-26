import ErdosProblems.Erdos547.GEAvoidingSupport
import ErdosProblems.Erdos547.GEPairFixedLoads
import ErdosProblems.Erdos547.AvoidingCapacity
import ErdosProblems.Erdos547.DeficitLedger

/-!
# A baseline allocation and the complete deficit bound in the avoiding case

The baseline deletes all edges incident with the covered reachable region.
Its lost load on the other side of that cut is included in the deficit bound.
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {γ : ℝ}

namespace GallaiEdmondsPartition

theorem IsGEPair.exists_avoiding_baseline {D : GallaiEdmondsPartition G}
    {w : EdgeWeights G} {c : V} {μ ν : FractionalMatching G} {σ : SkewMatching G γ}
    (h : D.IsGEPair w c μ σ ν) (hm : D.IsMaxSaturation w c μ)
    (C X : Finset V) (hC : C ⊆ D.reachableNeighbours w c μ)
    (ρ : SkewMatching G γ) (hρ : ρ.DominatedByFractional (ν.touching (C : Set V)))
    (hc : ∀ u, σ.load u + ρ.load u ≤ 1) (d : V) :
    ∃ μ₀ : FractionalMatching G,
      (∀ u, μ₀.load u ≤ freeCapacity (σ.add ρ hc) (D.avoidingFreeSet w c μ σ ν C) u) ∧
      (∑ u ∈ (D.singletonVertices \ (D.reachableVertices w c μ ∪ X))ᶜ,
        max 0 (tailAllowance w d (σ.add ρ hc).load (D.avoidingFreeSet w c μ σ ν C) u -
          μ₀.load u)) ≤
        ((D.reachableVertices w c μ).card : ℝ) + X.card -
          (∑ u ∈ D.reachableVertices w c μ, σ.load u) - (ν.touching (C : Set V)).total := by
  classical
  let R := D.reachableVertices w c μ
  let W := D.coveredReachable w c μ σ ν C
  let U := D.avoidingFreeSet w c μ σ ν C
  let good := D.singletonVertices \ (R ∪ X)
  let F := ν.touching (C : Set V)
  let ξ := ν.sub F (ν.touching_weight_le _)
  let μ₀ := ξ.inside (U : Set V)
  let β := σ.add ρ hc
  let loss (u : V) := ξ.load u - μ₀.load u
  have hW : W ⊆ R := Finset.filter_subset _ _
  have hUF (u : V) (hu : u ∈ U) : F.load u = 0 := by
    have hn : u ∉ C ∪ W := Finset.mem_compl.mp hu
    exact (h.touching_load_zero_outside_covered hm C hC
      (fun hh ↦ hn (Finset.mem_union_left _ hh))
      (fun hh ↦ hn (Finset.mem_union_right _ hh))).2
  have hβ (u : V) (hu : u ∈ U) : β.load u = σ.load u := by
    have hh : ρ.load u ≤ F.load u := hρ.load_le u
    rw [hUF u hu] at hh
    have hz : ρ.load u = 0 := le_antisymm hh (ρ.load_nonneg u)
    change (σ.add ρ hc).load u = _
    rw [SkewMatching.add_load, hz, add_zero]
  have hξ (u : V) : ξ.load u = ν.load u - F.load u := ν.sub_load _ _ u
  have hξC (u : V) (hu : u ∈ C) : ξ.load u = 0 := by
    rw [hξ, ν.touching_load_of_mem hu, sub_self]
  have hξU (u : V) (hu : u ∈ U) : ξ.load u = ν.load u := by
    rw [hξ, hUF u hu, sub_zero]
  have hbasecap (u : V) : ξ.load u + β.load u ≤ 1 := by
    rw [hξ]
    change ν.load u - F.load u + (σ.add ρ hc).load u ≤ _
    rw [SkewMatching.add_load]
    linarith [hρ.load_le u, h.capacity u]
  have hbaseline (u : V) : μ₀.load u ≤ freeCapacity β U u :=
    inside_load_le_freeCapacity ξ β hbasecap U u
  have hl (u : V) : 0 ≤ loss u := sub_nonneg.mpr (ξ.inside_load_le (U : Set V) u)
  have hbaseR (u : V) (huR : u ∈ R) (huU : u ∈ U) : μ₀.load u = ν.load u := by
    apply (ξ.inside_load_eq_of_no_cross U huU ?_).trans (hξU u huU)
    intro v hv
    have hvY : v ∈ C ∪ W := by
      by_contra hn
      exact hv (Finset.mem_compl.mpr hn)
    rcases Finset.mem_union.mp hvY with hvC | hvW
    · change ν.weight u v - F.weight u v = 0
      rw [ν.touching_weight_of_mem (Or.inr hvC), sub_self]
    · apply ξ.supported
      intro huv
      exact D.singleton_not_separator (hm.reachable_singleton (hW hvW))
        (D.neighbour_of_singleton_mem_separator (hm.reachable_singleton huR) huv)
  have hcut : (∑ u ∈ U, loss u) ≤ ∑ u ∈ W, (ν.load u - F.load u) := by
    calc
      _ ≤ ∑ u ∈ Uᶜ, ξ.load u := ξ.sum_inside_loss_le_compl U
      _ = ∑ u ∈ C ∪ W, ξ.load u := by simp only [U, avoidingFreeSet, W, compl_compl]
      _ = ∑ u ∈ W, ξ.load u := by
        symm
        apply Finset.sum_subset Finset.subset_union_right
        intro u hu hn
        exact hξC u ((Finset.mem_union.mp hu).resolve_right hn)
      _ = _ := Finset.sum_congr rfl fun u _ ↦ hξ u
  have hpoint (u : V) (hug : u ∈ goodᶜ) :
      max 0 (tailAllowance w d β.load U u - μ₀.load u) ≤
        (if u ∈ R \ W then 1 - σ.load u - ν.load u else 0) +
        (if u ∈ X then 1 else 0) + (if u ∈ U then loss u else 0) := by
    have hrc : 0 ≤ (if u ∈ R \ W then 1 - σ.load u - ν.load u else 0) := by
      split_ifs <;> linarith [h.capacity u]
    have hxc : (0 : ℝ) ≤ (if u ∈ X then 1 else 0) := by split_ifs <;> norm_num
    by_cases huU : u ∈ U
    · rw [if_pos huU]
      have ha : tailAllowance w d β.load U u ≤ 1 - σ.load u := by
        simpa only [hβ u huU] using tailAllowance_le_capacity w d β.load β.load_le_one U u
      by_cases huR : u ∈ R
      · have huW : u ∉ W := fun hw ↦ Finset.mem_compl.mp huU (Finset.mem_union_right _ hw)
        rw [if_pos (Finset.mem_sdiff.mpr ⟨huR, huW⟩), hbaseR u huR huU]
        have hh : max 0 (tailAllowance w d β.load U u - ν.load u) ≤
            1 - σ.load u - ν.load u := max_le (by linarith [h.capacity u]) (by linarith)
        linarith [hl u]
      · rw [if_neg (fun hh ↦ huR (Finset.mem_sdiff.mp hh).1)]
        by_cases huX : u ∈ X
        · rw [if_pos huX]
          have hh : max 0 (tailAllowance w d β.load U u - μ₀.load u) ≤ 1 := by
            apply max_le (by norm_num)
            linarith [σ.load_nonneg u, μ₀.load_nonneg u]
          linarith [hl u]
        · rw [if_neg huX, zero_add, zero_add]
          have huS : u ∉ D.singletonVertices := by
            intro hus
            apply Finset.mem_compl.mp hug
            exact Finset.mem_sdiff.mpr ⟨hus, fun hh ↦ (Finset.mem_union.mp hh).elim huR huX⟩
          have hcover : σ.load u + ν.load u = 1 := by
            rcases D.vertex_classes u with hu | hu | hu
            · exact h.covers_separator u hu
            · exact (huS hu).elim
            · exact h.covers_nontrivial hm hu
          apply max_le (hl u)
          dsimp [loss]
          rw [hξU u huU]
          linarith
    · rw [if_neg huU, tailAllowance, if_neg huU]
      have hz : max 0 (0 - μ₀.load u) = 0 := max_eq_left (by linarith [μ₀.load_nonneg u])
      rw [hz]
      linarith
  have hbound := avoiding_deficit_ledger R W X U good σ.load ν.load F.load loss
    (fun u ↦ max 0 (tailAllowance w d β.load U u - μ₀.load u)) hW ν.load_nonneg hl
    h.capacity hpoint hcut
  rw [h.touching_sum_load_covered hm C hC] at hbound
  exact ⟨μ₀, hbaseline, hbound⟩

end GallaiEdmondsPartition

end Erdos547.DPRS

#print axioms Erdos547.DPRS.GallaiEdmondsPartition.IsGEPair.exists_avoiding_baseline
