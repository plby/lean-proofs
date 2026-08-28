import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyRelativeFormsPullbackBasic
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyFourierParameterDerivativeFamily

/-!
# Literal upstairs pullbacks of genuine smooth torus families

The function is the original family evaluated at the original inverse
period coordinates modulo the integer lattice. Its ambient representative
agrees literally on the original open base, and is jointly real smooth in
the unchanged covering charts.
-/

noncomputable section

open TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.RelativeForms.Pullback

open HolomorphicDolbeaultThree FourierParameter
open PeriodTorusLineBundleClassification

variable {U : Opens ℂ} (P : HolomorphicPeriodMap ℂ U)

/-- The literal pullback of the actual torus family to the original covering space. -/
def upstairs (f : SmoothFamily U (Fin 4)) (q : U × ComplexPlane₂) : ℂ :=
  f (q.1, torusQuotient ((P.periodEquiv q.1).symm q.2))

/-- Ambient notation for this same original upstairs function, used only
on the full preimage of its original open base. -/
def familyPullback (f : SmoothFamily U (Fin 4)) : Model → ℂ :=
  ambientPullback P (ambientLift f)

/-- On the original base the ambient representative is exactly the genuine
family evaluated at the original inverse-period torus point. -/
@[simp] theorem familyPullback_apply (f : SmoothFamily U (Fin 4))
    (b : U) (z : ComplexPlane₂) :
    familyPullback P f ((b : ℂ), z) =
      f (b, torusQuotient ((P.periodEquiv b).symm z)) := by
  simp only [familyPullback, ambientPullback_apply,
    Smooth.inversePeriodCoordinates_apply, ambientLift_apply]

theorem familyPullback_eq_upstairs (f : SmoothFamily U (Fin 4))
    (b : U) (z : ComplexPlane₂) :
    familyPullback P f ((b : ℂ), z) = upstairs P f (b, z) :=
  familyPullback_apply P f b z

/-- Joint smoothness follows from the actual smooth lifted family and the
proved smoothness of the original inverse period coordinates. -/
theorem familyPullback_contDiffOn (f : SmoothFamily U (Fin 4)) :
    ContDiffOn ℝ ∞ (familyPullback P f) (Smooth.baseProductDomain U ComplexPlane₂) :=
  ambientPullback_contDiffOn P f.smooth_lift

local instance pullbackProductChartedSpace :
    ChartedSpace Model (U × ComplexPlane₂) :=
  inferInstanceAs (ChartedSpace (ModelProd ℂ ComplexPlane₂) (U × ComplexPlane₂))

/-- The literal upstairs function is jointly real smooth in the unchanged
native open-base product charts. No substitute atlas is introduced. -/
theorem upstairs_contMDiff (f : SmoothFamily U (Fin 4)) :
    ContMDiff (modelWithCornersSelf ℝ Model) (modelWithCornersSelf ℝ ℂ) ∞
      (upstairs P f) := by
  have h := Smooth.contMDiff_productOpen_of_contDiffOn (familyPullback_contDiffOn P f)
  exact h.congr (fun q => (familyPullback_eq_upstairs P f q.1 q.2).symm)

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.RelativeForms.Pullback
