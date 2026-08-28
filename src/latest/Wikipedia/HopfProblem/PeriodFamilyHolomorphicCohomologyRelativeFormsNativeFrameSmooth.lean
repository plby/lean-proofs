import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyRelativeFormsNativeFrameSmoothBasic

/-!
# Smooth inverse coefficients in the actual full antiholomorphic frame

Inversion is applied to the genuine continuously varying linear frame.
Its invertibility is the already proved pointwise frame theorem, and the
smoothness of inversion is the usual Banach-space inverse calculus. The
result extracts smooth coefficients from an actual smooth covector field
on the unchanged original open-base product.
-/

noncomputable section

open TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.RelativeForms.Native

open HolomorphicDolbeaultThree

variable {U : Opens ℂ} (P : HolomorphicPeriodMap ℂ U)

local instance nativeCoverProductChartedSpace : ChartedSpace Model (U × ComplexPlane₂) :=
  inferInstanceAs (ChartedSpace (ModelProd ℂ ComplexPlane₂) (U × ComplexPlane₂))

/-- The genuine inverse operators vary smoothly in the original covering chart. -/
theorem frameRealLinear_inverse_contMDiff :
    ContMDiff 𝓘(ℝ, Model) 𝓘(ℝ, AntiCovector Model →L[ℝ] Model) ∞
      (fun q : U × ComplexPlane₂ =>
        ContinuousLinearMap.inverse (frameRealLinear P ((q.1 : ℂ), q.2))) := by
  intro q
  have h := contDiffAt_map_inverse (n := ∞) (frameRealEquiv P q.1 q.2)
  rw [frameRealEquiv_toContinuousLinearMap] at h
  exact h.comp_contMDiffAt (frameRealLinear_contMDiff P q)

/-- The analytic inverse operator is the inverse of the original complex frame. -/
theorem frameRealLinear_inverse_apply (b : U) (z : ComplexPlane₂)
    (L : AntiCovector Model) :
    ContinuousLinearMap.inverse (frameRealLinear P ((b : ℂ), z)) L =
      (frameEquiv P b z).symm L := by
  rw [← frameRealEquiv_toContinuousLinearMap, ContinuousLinearMap.inverse_equiv]
  exact frameRealEquiv_symm_apply P b z L

/-- Every genuine smooth antiholomorphic covector field has smooth coefficients
in the actual full frame, without an assumed inverse-regularity property. -/
theorem frameEquiv_symm_contMDiff
    {L : U × ComplexPlane₂ → Model →L[ℝ] ℂ}
    (hL : ContMDiff 𝓘(ℝ, Model) 𝓘(ℝ, Model →L[ℝ] ℂ) ∞ L)
    (hanti : ∀ q, L q ∈ antiCovectors) :
    ContMDiff 𝓘(ℝ, Model) 𝓘(ℝ, Model) ∞
      (fun q => (frameEquiv P q.1 q.2).symm ⟨L q, hanti q⟩) := by
  have hA : ContMDiff 𝓘(ℝ, Model) 𝓘(ℝ, AntiCovector Model) ∞
      (fun q => (⟨L q, hanti q⟩ : AntiCovector Model)) := by
    have h := antiCovectorProjection.contDiff.comp_contMDiff hL
    convert h using 1
    funext q
    exact (antiCovectorProjection_val ⟨L q, hanti q⟩).symm
  simpa only [frameRealLinear_inverse_apply] using
    (frameRealLinear_inverse_contMDiff P).clm_apply hA

/-- The same regularity for the explicit triangular coefficient formula. -/
theorem frameCoefficients_contMDiff
    {L : U × ComplexPlane₂ → Model →L[ℝ] ℂ}
    (hL : ContMDiff 𝓘(ℝ, Model) 𝓘(ℝ, Model →L[ℝ] ℂ) ∞ L)
    (hanti : ∀ q, L q ∈ antiCovectors) :
    ContMDiff 𝓘(ℝ, Model) 𝓘(ℝ, Model) ∞
      (fun q => frameCoefficients P q.1 q.2 ⟨L q, hanti q⟩) := by
  simpa only [frameEquiv_symm_apply] using frameEquiv_symm_contMDiff P hL hanti

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.RelativeForms.Native
