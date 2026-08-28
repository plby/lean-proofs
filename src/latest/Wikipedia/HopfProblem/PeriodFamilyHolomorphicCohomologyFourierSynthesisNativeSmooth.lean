import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyFourierSynthesisNativeBasic
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyRelativeFormsPullbackFamilyBasic
import Wikipedia.HopfProblem.ConstructionSphereRecognitionEllipticSmoothDescent
import Wikipedia.HopfProblem.SpecialPeriodsCuspGlobalOverlapPeriodPullback

/-!
# Smooth descent in the original period-family manifold atlas

The real scalar is smooth upstairs by the proved inverse-period pullback.
The original quotient map is a local complex diffeomorphism, hence a local
real diffeomorphism in the same charts. Descent through its actual local
inverses proves smoothness in `P.totalChartedSpace`, without introducing
the real-coordinate product as a replacement complex atlas.
-/

noncomputable section

open TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.FourierSynthesisNative

open FourierParameter HolomorphicDolbeaultThree

variable {U : Opens ℂ} (P : HolomorphicPeriodMap ℂ U)

local notation "IR" => modelWithCornersSelf ℝ Model
local notation "IR₁" => modelWithCornersSelf ℝ ℂ

local instance nativeCoverProductChartedSpace : ChartedSpace Model (U × ComplexPlane₂) :=
  inferInstanceAs (ChartedSpace (ModelProd ℂ ComplexPlane₂) (U × ComplexPlane₂))

/-- The actual quotient map remains locally a real diffeomorphism in its original atlas. -/
theorem quotientMap_real_isLocalDiffeomorph :
    letI := P.totalChartedSpace
    IsLocalDiffeomorph IR IR ω P.quotientMap := by
  let := P.totalChartedSpace
  exact CuspCircleNormalTrivialization.isLocalDiffeomorph_real_of_complex
    P.quotientMap_isLocalDiffeomorph

/-- The descended scalar has exactly the previously proved genuine upstairs pullback. -/
theorem scalar_comp_quotientMap (f : SmoothFamily U (Fin 4)) :
    scalar P f ∘ P.quotientMap = RelativeForms.Pullback.upstairs P f := by
  funext q
  exact scalar_quotientMap P f q.1 q.2

/-- Joint real smoothness in the unchanged native complex covering-quotient atlas. -/
theorem scalar_contMDiff (f : SmoothFamily U (Fin 4)) :
    letI := P.totalChartedSpace
    ContMDiff IR IR₁ ∞ (scalar P f) := by
  let := P.totalChartedSpace
  apply ConstructionSphereRecognition.EllipticSmooth.contMDiff_of_comp_real_localDiffeomorph
    (quotientMap_real_isLocalDiffeomorph P) P.quotientMap_surjective
  rw [scalar_comp_quotientMap]
  exact RelativeForms.Pullback.upstairs_contMDiff P f

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.FourierSynthesisNative
