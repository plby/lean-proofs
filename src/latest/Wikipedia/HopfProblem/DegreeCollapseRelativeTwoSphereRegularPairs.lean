import Wikipedia.HopfProblem.DegreeCollapseRelativeTwoSpherePairDomain
import Wikipedia.HopfProblem.DegreeCollapseRelativeTwoSphereParameterSubmersion
import Wikipedia.NoExoticSixSphere.ParametricRegularOpen

/-!
# Generic double points with at least one unprotected source point

The actual coordinate-difference derivative is surjective even if one source
point is fixed. Parametric Sard gives regular zeros on each active two-point
chart domain. Pairs entirely inside the protected set are not covered by this
theorem and require the separately prescribed local geometry.
-/

noncomputable section

open Set Function
open MeasureTheory MeasureTheory.Measure
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.RelativeTwoSphere

open NoExoticSixSphere

open GLOrthonormalization EuclideanEmbedding
open TwoSpherePerturbation (Parameters SourceChart TargetChart)

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector n) M]
  (e : EuclideanEmbedding n M) (r : TubularRetraction e)
  (f : ℝ → Sphere 2 → M) (χ : Sphere 2 → ℝ)

theorem surjective_fderiv_chartDifference_parameter
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 n) ∞ (uncurry f))
    (hχ : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ χ)
    (s z : SourceChart) (c : TargetChart n M)
    (q : Parameters e × (ℝ × (Vector 2 × Vector 2)))
    (hq : q ∈ activePairDomain e r f χ hf hχ s z c) :
    Surjective (fderiv ℝ
      (fun p : Parameters e ↦ chartDifference e r f χ s z c (p, q.2)) q.1) := by
  have hleft := hq.1.1.1
  have hright := hq.1.1.2
  exact surjective_fderiv_chart_pair_difference_parameter e r f χ c q.1 q.2.1
    (s.symm q.2.2.1) (z.symm q.2.2.2) hq.1.2 hleft.1.1.2 hq.2
    hleft.1.2 hright.1.2 hleft.2 hright.2

theorem surjective_fderiv_chartDifference
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 n) ∞ (uncurry f))
    (hχ : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ χ)
    (s z : SourceChart) (c : TargetChart n M)
    (q : Parameters e × (ℝ × (Vector 2 × Vector 2)))
    (hq : q ∈ activePairDomain e r f χ hf hχ s z c) :
    Surjective (fderiv ℝ (chartDifference e r f χ s z c) q) := by
  have hp := surjective_fderiv_chartDifference_parameter e r f χ hf hχ s z c q hq
  have hD := ((contDiffOn_chartDifference e r f χ hf hχ s z c).contDiffAt
    ((pairDomain e r f χ hf hχ s z c).isOpen.mem_nhds hq.1)).differentiableAt (by simp)
  have ht : HasFDerivAt (fun p : Parameters e ↦ (p, q.2))
      (ContinuousLinearMap.inl ℝ (Parameters e) (ℝ × (Vector 2 × Vector 2))) q.1 :=
    (hasFDerivAt_id q.1).prodMk (hasFDerivAt_const q.2 q.1)
  have he := (hD.hasFDerivAt.comp q.1 ht).fderiv
  change fderiv ℝ (fun p : Parameters e ↦ chartDifference e r f χ s z c (p, q.2)) q.1 = _ at he
  rw [he] at hp
  intro w
  obtain ⟨v, hv⟩ := hp w
  exact ⟨(v, 0), hv⟩

theorem ae_regular_chart_double_points
    [MeasurableSpace (Parameters e)] [BorelSpace (Parameters e)]
    (μ : Measure (Parameters e)) [IsAddHaarMeasure μ]
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 n) ∞ (uncurry f))
    (hχ : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ χ)
    (s z : SourceChart) (c : TargetChart n M) :
    ∀ᵐ p ∂μ, ∀ x : ℝ × (Vector 2 × Vector 2),
      (p, x) ∈ activePairDomain e r f χ hf hχ s z c →
      chartDifference e r f χ s z c (p, x) = 0 →
        Surjective (fderiv ℝ (fun y ↦ chartDifference e r f χ s z c (p, y)) x) :=
  ParametricRegular.ae_parameters_on μ (chartDifference e r f χ s z c)
    (activePairDomain e r f χ hf hχ s z c)
    ((contDiffOn_chartDifference e r f χ hf hχ s z c).mono inter_subset_left)
    (fun q hq _ ↦ surjective_fderiv_chartDifference e r f χ hf hχ s z c q hq)

end Wikipedia.HopfProblem.DegreeCollapse.RelativeTwoSphere
