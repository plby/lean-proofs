import ErdosProblems.Erdos547.BoundedFractional
import ErdosProblems.Erdos547.SeparatedRows

/-!
# Converting neighbourhood saturation to a skew allocation

This proves the combination lemma for any nonnegative skew. It first takes
a maximal symmetric submatching within the anchor allowances, then orients
the residual allocation from the remaining unsaturated vertices.
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- A fractional matching provides an anchor-fitted skew allocation of
total weight at least its saturation of the anchor neighbourhood. -/
theorem exists_skew_of_saturation (μ : FractionalMatching G) (w : EdgeWeights G)
    (c : V) (γ : ℝ) (hγ : 0 ≤ γ) :
    ∃ σ : SkewMatching G γ, σ.DominatedByFractional μ ∧ σ.Fits w c ∧
      w.saturation μ.load c ≤ σ.total := by
  obtain ⟨ν, hν, hνa, hres⟩ := μ.exists_maximal_bounded_with_residual
    (w.weight c) (w.nonnegative c)
  let ρ := μ.sub ν hν
  let a := fun u ↦ w.weight c u - ν.load u
  have ha : ∀ u, 0 ≤ a u := fun u ↦ sub_nonneg.mpr (hνa u)
  have hsep : ∀ u v, 0 < ρ.weight u v → a u ≤ 0 ∨ a v ≤ 0 := by
    intro u v huv
    by_cases hu : ν.load u < w.weight c u
    · right
      by_contra hv
      have heq := hres u v hu (by dsimp [a] at hv; linarith)
      change 0 < μ.weight u v - ν.weight u v at huv
      rw [heq, sub_self] at huv
      exact (lt_irrefl 0) huv
    · left
      dsimp [a]
      linarith
  obtain ⟨τ, hτ, hτa, hτtotal⟩ := exists_skew_of_separated_allowances ρ γ hγ a ha hsep
  let β := ν.toSkew γ hγ
  have hβ : β.DominatedByFractional ν := ν.toSkew_dominated γ hγ
  have hcap : ∀ u, β.load u + τ.load u ≤ 1 := by
    intro u
    have ht := hτ.load_le u
    have hb : β.load u = ν.load u := ν.toSkew_load γ hγ u
    have hr : ρ.load u = μ.load u - ν.load u := μ.sub_load ν hν u
    linarith [μ.load_le_one u]
  have hβfit : β.Fits w c := by
    intro u
    exact ((β.outLoad_le_load u).trans (hβ.load_le u)).trans (hνa u)
  have hτfit : τ.Fits (w.truncate ν.load ν.load_nonneg) c := by
    intro u
    exact (hτa u).trans (le_max_right _ _)
  refine ⟨β.add τ hcap, ?_, SkewMatching.fits_add_truncated hβfit hτfit hβ hcap, ?_⟩
  · intro u v
    rw [SkewMatching.add_endpointWeight]
    have := add_le_add (hβ u v) (hτ u v)
    change _ ≤ ν.weight u v + (μ.weight u v - ν.weight u v) at this
    linarith
  · rw [SkewMatching.add_total]
    have hβtotal : β.total = ∑ u, ν.load u := by
      rw [ν.sum_load]
      exact ν.toSkew_total γ hγ
    have hid : (∑ u, ν.load u) + (∑ u, min (a u) (ρ.load u)) =
        w.saturation μ.load c := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro u _
      change ν.load u + min (w.weight c u - ν.load u) ((μ.sub ν hν).load u) = _
      rw [FractionalMatching.sub_load, min_sub_sub_right]
      ring
    rw [hβtotal]
    linarith

/-- Any smaller prescribed total is available by scaling the allocation. -/
theorem exists_skew_of_saturation_exact (μ : FractionalMatching G) (w : EdgeWeights G)
    (c : V) (γ : ℝ) (hγ : 0 ≤ γ) (r : ℝ) (hr : 0 ≤ r)
    (hbound : r ≤ w.saturation μ.load c) :
    ∃ σ : SkewMatching G γ, σ.DominatedByFractional μ ∧ σ.Fits w c ∧ σ.total = r := by
  obtain ⟨σ, hσ, hfit, htotal⟩ := exists_skew_of_saturation μ w c γ hγ
  have hrσ : r ≤ σ.total := hbound.trans htotal
  by_cases hzero : σ.total = 0
  · have hrzero : r = 0 := le_antisymm (hzero ▸ hrσ) hr
    exact ⟨σ, hσ, hfit, hzero.trans hrzero.symm⟩
  have hpos : 0 < σ.total := lt_of_le_of_ne (hr.trans hrσ) (Ne.symm hzero)
  have ht : 0 ≤ r / σ.total := div_nonneg hr hpos.le
  have htone : r / σ.total ≤ 1 := (div_le_one hpos).mpr hrσ
  refine ⟨σ.scale (r / σ.total) ht htone, ?_, ?_, ?_⟩
  · intro u v
    have heq : (σ.scale (r / σ.total) ht htone).endpointWeight u v =
        (r / σ.total) * σ.endpointWeight u v := by
      simp only [SkewMatching.endpointWeight, SkewMatching.scale]
      ring
    rw [heq]
    exact (mul_le_of_le_one_left (σ.endpointWeight_nonneg u v) htone).trans (hσ u v)
  · intro u
    rw [SkewMatching.scale_outLoad]
    exact (mul_le_of_le_one_left (σ.outLoad_nonneg u) htone).trans (hfit u)
  · rw [SkewMatching.scale_total, div_mul_cancel₀ _ hzero]

end Erdos547.DPRS

#print axioms Erdos547.DPRS.exists_skew_of_saturation
#print axioms Erdos547.DPRS.exists_skew_of_saturation_exact
