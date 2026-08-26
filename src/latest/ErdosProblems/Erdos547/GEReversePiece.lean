import ErdosProblems.Erdos547.GECoveredRegion
import ErdosProblems.Erdos547.FullOrientation

/-!
# Orienting a restricted fractional GE piece back towards the separator
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {γ : ℝ}

namespace GallaiEdmondsPartition

theorem IsGEPair.restricted_cover_identity {D : GallaiEdmondsPartition G}
    {w : EdgeWeights G} {c : V} {μ ν : FractionalMatching G} {σ : SkewMatching G γ}
    (h : D.IsGEPair w c μ σ ν) (hm : D.IsMaxSaturation w c μ)
    (C : Finset V) (hC : C ⊆ D.reachableNeighbours w c μ) :
    (ν.touching (C : Set V)).total + (σ.touching (C : Set V)).total / (1 + γ) =
      (C.card : ℝ) := by
  have hr := h.restriction_runs_between hm C hC
  have hdis : Disjoint C (D.reachableVertices w c μ) := Finset.disjoint_left.mpr
    fun u hu hv ↦ D.singleton_not_separator (hm.reachable_singleton hv)
      (hm.reachable_neighbour_separator (hC hu))
  rw [← (hr.2.crosses hdis).sum_load_side, ← hr.1.sum_load_source hdis,
    ← Finset.sum_add_distrib]
  calc
    _ = ∑ _u ∈ C, (1 : ℝ) := Finset.sum_congr rfl fun u hu ↦ by
      rw [ν.touching_load_of_mem hu, σ.touching_load_of_mem hu]
      linarith [h.covers_separator u (hm.reachable_neighbour_separator (hC hu))]
    _ = _ := by simp

theorem IsGEPair.exists_reverse_piece {D : GallaiEdmondsPartition G}
    {w : EdgeWeights G} {c : V} {μ ν : FractionalMatching G} {σ : SkewMatching G γ}
    (h : D.IsGEPair w c μ σ ν) (hm : D.IsMaxSaturation w c μ) (hγ : 1 ≤ γ)
    (C : Finset V) (hC : C ⊆ D.reachableNeighbours w c μ) :
    ∃ ρ : SkewMatching G γ,
      ρ.DominatedByFractional (ν.touching (C : Set V)) ∧
      ρ.total = (1 + γ) / γ * (ν.touching (C : Set V)).total ∧
      (∀ u ∉ D.reachableVertices w c μ, ρ.outLoad u = 0) ∧
      ∃ hc : ∀ u, σ.load u + ρ.load u ≤ 1, (σ.add ρ hc).Fits w c ∧
        γ * (σ.total + ρ.total) / (1 + γ) ≤ ((D.reachableVertices w c μ).card : ℝ) := by
  classical
  let R := D.reachableVertices w c μ
  let F := ν.touching (C : Set V)
  have hr := h.restriction_runs_between hm C hC
  have hdis : Disjoint C R := Finset.disjoint_left.mpr fun u hu hv ↦
    D.singleton_not_separator (hm.reachable_singleton hv)
      (hm.reachable_neighbour_separator (hC hu))
  have hRF : F.RunsBetween R C := fun u v hp ↦ (hr.2 u v hp).symm
  have hFle (u : V) : F.load u ≤ ν.load u :=
    F.load_le_of_weight_le ν (ν.touching_weight_le _) u
  have hFc (u : V) : σ.load u + F.load u ≤ 1 :=
    (add_le_add le_rfl (hFle u)).trans (h.capacity u)
  obtain ⟨ρ, hρ, htρ, houtρ⟩ := exists_full_orientation F R (hRF.crosses hdis.symm) γ
    (zero_le_one.trans hγ)
  have ht : ρ.total = (1 + γ) / γ * F.total := by
    simpa only [orientationRate, max_eq_right hγ] using htρ
  have hc (u : V) : σ.load u + ρ.load u ≤ 1 :=
    (add_le_add le_rfl (hρ.load_le u)).trans (hFc u)
  have hfitρ : ρ.Fits (w.truncate σ.load σ.load_nonneg) c := by
    intro u
    by_cases hu : u ∈ R
    · have hl := (ρ.outLoad_le_load u).trans ((hρ.load_le u).trans (hFle u))
      have hb := h.reachable_upper u hu
      change ρ.outLoad u ≤ max 0 (w.weight c u - σ.load u)
      exact (show ρ.outLoad u ≤ w.weight c u - σ.load u by linarith).trans (le_max_right _ _)
    · rw [houtρ u hu]
      exact (w.truncate σ.load σ.load_nonneg).nonnegative c u
  refine ⟨ρ, hρ, ht, houtρ, hc, ?_, ?_⟩
  · intro u
    rw [SkewMatching.add_outLoad]
    exact add_le_of_le_truncated (h.fits u) (σ.outLoad_le_load u) (hfitρ u)
  · have hσruns : σ.RunsBetween (D.reachableNeighbours w c μ) R :=
      SkewMatching.runsBetween_of_zero h.skew_supported
    have hdisSR : Disjoint (D.reachableNeighbours w c μ) R :=
      Finset.disjoint_left.mpr fun u hu hv ↦
        D.singleton_not_separator (hm.reachable_singleton hv) (hm.reachable_neighbour_separator hu)
    have hload : γ * σ.total / (1 + γ) + F.total ≤ (R.card : ℝ) := by
      rw [← hσruns.sum_load_target hdisSR, ← (hRF.crosses hdis.symm).sum_load_side,
        ← Finset.sum_add_distrib]
      calc
        _ ≤ ∑ _u ∈ R, (1 : ℝ) := Finset.sum_le_sum fun u _ ↦ hFc u
        _ = _ := by simp
    have he : γ * (σ.total + ρ.total) / (1 + γ) = γ * σ.total / (1 + γ) + F.total := by
      rw [ht]
      have hgp : 0 < γ := zero_lt_one.trans_le hγ
      field_simp [hgp.ne', σ.denominator_pos.ne']
    rw [he]
    exact hload

end GallaiEdmondsPartition

end Erdos547.DPRS

namespace Erdos547.DPRS.GallaiEdmondsPartition
#print axioms IsGEPair.restricted_cover_identity
#print axioms IsGEPair.exists_reverse_piece
end Erdos547.DPRS.GallaiEdmondsPartition
