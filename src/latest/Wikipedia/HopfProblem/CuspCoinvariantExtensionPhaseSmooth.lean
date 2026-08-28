import Wikipedia.HopfProblem.CuspCoinvariantExtensionPhaseBasic
import Wikipedia.HopfProblem.CuspCoinvariantExtensionPhaseSmoothCoordinates
import Wikipedia.HopfProblem.ConstructionSphereRecognitionEllipticSmoothDescent

/-!
# Smoothness of the original punctured cusp phase

The real gamma coordinate on the logarithmic cover is obtained from the
genuine inverse period matrix. Its normalized exponential is the original
circle phase. Smoothness descends through the existing locally
biholomorphic cusp cover, retaining the original complex-derived real
atlas on the punctured quotient.

No differentiable structure on the additive circle is used here.
-/

noncomputable section

open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.CuspCoinvariantExtension.Phase

open CuspUniformization SpecialPeriods.CuspFamily

local notation "Ilog" => modelWithCornersSelf ℝ (ℂ × ComplexPlane₂)
local notation "I₃" => modelWithCornersSelf ℝ (ToricCharts.CoordinateSpace 3)
local notation "I₁" => modelWithCornersSelf ℝ ℂ

/-- The actual punctured phase pulled back to the original cover is
real smooth, by its exact normalized-exponential formula. -/
theorem puncturedPhase_cover_contMDiff (D : Data) :
    ContMDiff Ilog I₁ ∞
      (puncturedPhase D ∘ puncturedCuspCover D.correction D.radius) := by
  have hexp : ContMDiff I₁ I₁ ∞ exponential :=
    ((exponential_holomorphic.restrict_scalars ℝ).of_le le_top).contMDiff
  have hreal : ContMDiff 𝓘(ℝ, ℝ) I₁ ∞ (fun t : ℝ => (t : ℂ)) :=
    Complex.ofRealCLM.contDiff.contMDiff
  exact (hexp.comp (hreal.comp (logGamma_contMDiff D))).congr
    (fun p => puncturedPhase_cover D p)

/-- The genuine phase is real smooth on the entire punctured cusp, in
the original quotient atlas with only the scalar field restricted. -/
theorem puncturedPhase_contMDiff (D : Data) :
    letI := CuspQuotient.chartedSpace D.correction D.radius D.radius_pos
      D.radius_lt_one D.holomorphic D.smallDrift
    ContMDiff I₃ I₁ ∞ (puncturedPhase D) := by
  let := CuspQuotient.chartedSpace D.correction D.radius D.radius_pos
    D.radius_lt_one D.holomorphic D.smallDrift
  exact ConstructionSphereRecognition.EllipticSmooth.contMDiff_of_comp_real_localDiffeomorph
    (CuspCircleNormalTrivialization.isLocalDiffeomorph_real_of_complex
      (puncturedCuspCover_isLocalDiffeomorph D.correction D.radius D.radius_pos
        D.radius_lt_one D.holomorphic D.smallDrift))
    (puncturedCuspCover_surjective D.correction D.radius)
    (puncturedPhase_cover_contMDiff D)

end Wikipedia.HopfProblem.CuspCoinvariantExtension.Phase
