import Wikipedia.NoExoticSixSphere.RelativeSphereIntersectionDomain
import Wikipedia.NoExoticSixSphere.SpatiallyRelativeSphereParameterSubmersion
import Wikipedia.NoExoticSixSphere.ParametricRegularOpen

/-!
# Parametric regularity of relative intersections with a fixed sphere

The moving chart value has surjective parameter derivative wherever its
cutoff is nonzero. The fixed sphere contributes no parameter derivative.
Parametric Sard therefore controls the actual incidence equation on the
coupled domain without a source-point distinctness assumption.
-/

noncomputable section

open Set Function
open MeasureTheory MeasureTheory.Measure
open scoped Manifold ContDiff

namespace NoExoticSixSphere.RelativeSphereIntersectionFamily

open GLOrthonormalization EuclideanEmbedding
open ManifoldAffineSphereFamily (Parameters SourceChart TargetChart)

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector n) M]
  (e : EuclideanEmbedding n M) (r : TubularRetraction e)
  (f g : ℝ → Sphere 3 → M) (χ : Sphere 3 → ℝ)
  (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 n) ∞ (uncurry f))
  (hg : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 n) ∞ (uncurry g))
  (hχ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ χ)
  (s z : SourceChart) (c : TargetChart n M)

theorem surjective_fderiv_difference_parameter
    (q : Parameters e × (ℝ × (Vector 3 × Vector 3)))
    (hq : q ∈ domain e r f g χ hf hg hχ s z c) :
    Surjective (fderiv ℝ
      (fun p : Parameters e ↦ difference e r f g χ s z c (p, q.2)) q.1) := by
  have heq : (fun p : Parameters e ↦ difference e r f g χ s z c (p, q.2)) =
      fun p ↦ c (SpatiallyRelativeSphereFamily.map e r f χ p q.2.1 (s.symm q.2.2.1)) -
        c (g q.2.1 (z.symm q.2.2.2)) := by
    funext p
    exact difference_apply e r f g χ s z c (p, q.2)
  rw [heq, fderiv_sub_const]
  have hleft := hq.1.1
  exact SpatiallyRelativeSphereFamily.surjective_fderiv_chart_parameter e r f χ c
    q.1 q.2.1 (s.symm q.2.2.1) hleft.1.1.2 hq.1.2 hleft.1.2 hleft.2

theorem surjective_fderiv_difference
    (q : Parameters e × (ℝ × (Vector 3 × Vector 3)))
    (hq : q ∈ domain e r f g χ hf hg hχ s z c) :
    Surjective (fderiv ℝ (difference e r f g χ s z c) q) := by
  have hp := surjective_fderiv_difference_parameter e r f g χ hf hg hχ s z c q hq
  have hD := ((contDiffOn_difference e r f g χ hf hg hχ s z c).contDiffAt
    ((domain e r f g χ hf hg hχ s z c).isOpen.mem_nhds hq)).differentiableAt (by simp)
  have ht : HasFDerivAt (fun p : Parameters e ↦ (p, q.2))
      (ContinuousLinearMap.inl ℝ (Parameters e) (ℝ × (Vector 3 × Vector 3))) q.1 :=
    (hasFDerivAt_id q.1).prodMk (hasFDerivAt_const q.2 q.1)
  have he := (hD.hasFDerivAt.comp q.1 ht).fderiv
  change fderiv ℝ (fun p : Parameters e ↦ difference e r f g χ s z c (p, q.2)) q.1 = _ at he
  rw [he] at hp
  intro w
  obtain ⟨v, hv⟩ := hp w
  exact ⟨(v, 0), hv⟩

theorem ae_regular_intersections [MeasurableSpace (Parameters e)] [BorelSpace (Parameters e)]
    (μ : Measure (Parameters e)) [IsAddHaarMeasure μ] :
    ∀ᵐ p ∂μ, ∀ x : ℝ × (Vector 3 × Vector 3),
      (p, x) ∈ domain e r f g χ hf hg hχ s z c →
      difference e r f g χ s z c (p, x) = 0 →
      Surjective (fderiv ℝ (fun y ↦ difference e r f g χ s z c (p, y)) x) :=
  ParametricRegular.ae_parameters_on μ (difference e r f g χ s z c)
    (domain e r f g χ hf hg hχ s z c) (contDiffOn_difference e r f g χ hf hg hχ s z c)
    (fun q hq _ ↦ surjective_fderiv_difference e r f g χ hf hg hχ s z c q hq)

end NoExoticSixSphere.RelativeSphereIntersectionFamily
