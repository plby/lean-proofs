import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyLaurent
import Mathlib.Analysis.Complex.Liouville

/-!
# Uniqueness of actual entire Laurent splittings

The positive and reciprocal-coordinate parts here are actual entire
functions. Their uniqueness follows from their literal equality on the
punctured plane and Liouville's theorem, not from formal Laurent series.
-/

noncomputable section

open Complex Filter Set
open scoped Topology

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.ProjectiveCocycle

theorem eventually_ne_zero_cocompact :
    ∀ᶠ z : ℂ in cocompact ℂ, z ≠ 0 := by
  exact (isCompact_singleton (x := (0 : ℂ))).compl_mem_cocompact

theorem tendsto_inv_cocompact :
    Tendsto (fun z : ℂ => z⁻¹) (cocompact ℂ) (𝓝 0) := by
  simpa only [Metric.cobounded_eq_cocompact] using
    (tendsto_inv₀_cobounded : Tendsto (fun z : ℂ => z⁻¹)
      (Bornology.cobounded ℂ) (𝓝 0))

/-- Normalizing the reciprocal-coordinate summand at zero makes the
literal entire Laurent decomposition unique. -/
theorem entire_splitting_unique {p₁ p₂ m₁ m₂ : ℂ → ℂ}
    (hp₁ : AnalyticOnNhd ℂ p₁ univ) (hp₂ : AnalyticOnNhd ℂ p₂ univ)
    (hm₁ : ContinuousAt m₁ 0) (hm₂ : ContinuousAt m₂ 0)
    (hm₁₀ : m₁ 0 = 0) (hm₂₀ : m₂ 0 = 0)
    (heq : ∀ z : ℂ, z ≠ 0 → p₁ z + m₁ z⁻¹ = p₂ z + m₂ z⁻¹) :
    p₁ = p₂ ∧ m₁ = m₂ := by
  have hd : Differentiable ℂ (fun z => p₁ z - p₂ z) := fun z =>
    (hp₁ z (mem_univ _)).differentiableAt.sub
      (hp₂ z (mem_univ _)).differentiableAt
  have hlim : Tendsto (fun z : ℂ => m₂ z⁻¹ - m₁ z⁻¹)
      (cocompact ℂ) (𝓝 0) := by
    simpa only [hm₁₀, hm₂₀, sub_self, Function.comp_apply] using
      (hm₂.tendsto.comp tendsto_inv_cocompact).sub
        (hm₁.tendsto.comp tendsto_inv_cocompact)
  have hlim' : Tendsto (fun z : ℂ => p₁ z - p₂ z)
      (cocompact ℂ) (𝓝 0) := by
    apply hlim.congr'
    filter_upwards [eventually_ne_zero_cocompact] with z hz
    have h := heq z hz
    linear_combination -h
  have hp (z : ℂ) : p₁ z = p₂ z :=
    sub_eq_zero.mp (hd.apply_eq_of_tendsto_cocompact z hlim')
  refine ⟨funext hp, funext fun z => ?_⟩
  by_cases hz : z = 0
  · simp only [hz, hm₁₀, hm₂₀]
  · have h := heq z⁻¹ (inv_ne_zero hz)
    simpa only [inv_inv, hp, add_right_inj] using h

theorem firstSlice_entire {f : ℂ × ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f univ) (w : ℂ) :
    AnalyticOnNhd ℂ (fun z => f (z, w)) univ := by
  intro z _
  exact AnalyticAt.comp (f := fun z : ℂ => (z, w)) (hf (z, w) (mem_univ _))
    (analyticAt_id.prod analyticAt_const)

theorem secondSlice_entire {f : ℂ × ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f univ) (z : ℂ) :
    AnalyticOnNhd ℂ (fun w => f (z, w)) univ := by
  intro w _
  exact AnalyticAt.comp (f := fun w : ℂ => (z, w)) (hf (z, w) (mem_univ _))
    (analyticAt_const.prod analyticAt_id)

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.ProjectiveCocycle
