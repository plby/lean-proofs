import ErdosProblems.Erdos547.GEPairSupport
import ErdosProblems.Erdos547.SkewRowSplitting

/-!
# Capping a mixed GE allocation at a new anchor and extracting its remainder
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph

variable {V : Type*} [Fintype V] {G : SimpleGraph V} {δ : ℝ}

structure CappedProfile (σ : SkewMatching G δ) (ν : FractionalMatching G)
    (w : EdgeWeights G) (c d : V) (R S : Finset V) where
  kept : SkewMatching G δ
  fractional : FractionalMatching G
  kept_sub : kept.IsSuballocation σ
  kept_fits : kept.Fits w d
  fractional_le : ∀ u v, ν.weight u v ≤ fractional.weight u v
  capacity : ∀ u, fractional.load u + kept.load u ≤ 1
  cut_upper : ∀ u ∈ R, fractional.load u + kept.load u ≤ w.weight c u
  cut_lower : ∀ u ∉ R, w.weight c u ≤ fractional.load u + kept.load u
  separator_zero : ∀ u ∈ S, ∀ v ∈ S, fractional.weight u v = 0
  kept_runs : kept.RunsFrom S
  kept_load : ∀ u ∈ S, kept.load u = min (w.weight d u) (σ.load u)
  residual_available : ∀ u ∈ S, max 0 (w.weight d u - kept.load u) ≤ ν.load u

variable [DecidableEq V]

namespace GallaiEdmondsPartition

theorem IsGEPair.exists_capped_profile {D : GallaiEdmondsPartition G} {w : EdgeWeights G}
    {c : V} {μ ν : FractionalMatching G} {σ : SkewMatching G δ}
    (h : D.IsGEPair w c μ σ ν) (hm : D.IsMaxSaturation w c μ) (hδ : 1 ≤ δ) (d : V) :
    Nonempty (CappedProfile σ ν w c d (D.reachableVertices w c μ) D.separator) := by
  obtain ⟨τ, ρ, hτ, hρ, hout, _, hloads⟩ := σ.exists_row_split (w.weight d) (w.nonnegative d)
  have hσruns := h.runsFrom_separator hm
  have hρruns := hσruns.of_suballocation hρ
  have hτruns := hσruns.of_suballocation hτ
  let Q := ρ.extractFractional hδ
  have hQ (u : V) : Q.load u ≤ ρ.load u := (ρ.extractFractional_dominated hδ).load_le u
  have hcap (u : V) : ν.load u + Q.load u ≤ 1 := by
    linarith [h.capacity u, hloads u, hQ u, τ.load_nonneg u]
  let F := ν.add Q hcap
  have hF (u : V) : F.load u = ν.load u + Q.load u := FractionalMatching.add_load _ _ _ _
  have hcut (u : V) (hu : u ∉ D.reachableVertices w c μ) :
      F.load u + τ.load u = σ.load u + ν.load u := by
    have hin (v : V) : ρ.weight v u = 0 := hρ.weight_eq_zero
      (h.skew_supported v u (fun hh ↦ hu hh.2))
    have hQload : Q.load u = ρ.load u := by
      rw [show Q.load u = ρ.outLoad u from ρ.extractFractional_load_eq_outLoad hδ u hin]
      simp only [SkewMatching.load, SkewMatching.inLoad, hin, Finset.sum_const_zero,
        mul_zero, zero_div, add_zero]
    rw [hF, hQload]
    linarith [hloads u]
  have hτload (u : V) (hu : u ∈ D.separator) :
      τ.load u = min (w.weight d u) (σ.load u) := by
    rw [hτruns.load_eq_outLoad hu, hout, hσruns.load_eq_outLoad hu]
  refine ⟨⟨τ, F, hτ, ?_, ?_, ?_, ?_, ?_, ?_, hτruns, hτload, ?_⟩⟩
  · intro u
    rw [hout]
    exact min_le_left _ _
  · intro u v
    change ν.weight u v ≤ ν.weight u v + Q.weight u v
    exact le_add_of_nonneg_right (Q.nonnegative u v)
  · intro u
    rw [hF]
    linarith [h.capacity u, hloads u, hQ u]
  · intro u hu
    rw [hF]
    linarith [h.reachable_upper u hu, hloads u, hQ u]
  · intro u hu
    rw [hcut u hu]
    exact h.outside_lower u hu
  · intro u hu v hv
    change ν.weight u v + (ρ.weight u v + ρ.weight v u) / (1 + δ) = 0
    rw [h.fractional_zero_separator hm hu hv,
      hρruns.incoming_zero hv u, hρruns.incoming_zero hu v]
    simp only [add_zero, zero_div]
  · intro u hu
    rw [hτload u hu]
    by_cases hle : w.weight d u ≤ σ.load u
    · rw [min_eq_left hle, sub_self, max_self]
      exact ν.load_nonneg u
    · rw [min_eq_right (le_of_not_ge hle)]
      apply max_le (ν.load_nonneg u)
      linarith [h.covers_separator u hu, w.at_most_one d u]

end GallaiEdmondsPartition

end Erdos547.DPRS

#print axioms Erdos547.DPRS.GallaiEdmondsPartition.IsGEPair.exists_capped_profile
