import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyRelativeFormsPullbackFamilyBasic

/-!
# Smaller-open smooth torus families in the original covering charts

The family lives over a smaller open base, but the covering space and
inverse period coordinates remain those of the original period family.
Its scalar representative is extended by zero only as ambient notation.
Smoothness is proved exactly above the smaller open, using the original
inherited complex-product chart regarded over the real scalars.
-/

noncomputable section

open TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.FourierSynthesisNative.Local

open FourierParameter HolomorphicDolbeaultThree
open PeriodTorusLineBundleClassification

variable {U V : Opens ℂ} (P : HolomorphicPeriodMap ℂ U)

/-- The actual inverse-period pullback in the unchanged original covering space. -/
def upstairs (f : SmoothFamily V (Fin 4)) (q : U × ComplexPlane₂) : ℂ :=
  RelativeForms.Pullback.ambientPullback P (ambientLift f) ((q.1 : ℂ), q.2)

/-- At every original covering point this is the literal smaller-open ambient family value. -/
theorem upstairs_apply (f : SmoothFamily V (Fin 4)) (q : U × ComplexPlane₂) :
    upstairs P f q =
      ambientValue f ((q.1 : ℂ), torusQuotient ((P.periodEquiv q.1).symm q.2)) := by
  simp only [upstairs, RelativeForms.Pullback.ambientPullback_apply,
    Smooth.inversePeriodCoordinates_apply, ambientLift_eq_ambientValue]

/-- On the smaller base the value uses the original period map at its literal inclusion. -/
@[simp] theorem upstairs_inclusion_apply (hVU : V ≤ U) (f : SmoothFamily V (Fin 4))
    (b : V) (z : ComplexPlane₂) :
    upstairs P f (Set.inclusion hVU b, z) =
      f (b, torusQuotient ((P.periodEquiv (Set.inclusion hVU b)).symm z)) := by
  rw [upstairs_apply]
  exact ambientValue_apply f b _

/-- Joint ambient smoothness holds over the smaller base, with the original inverse coordinates. -/
theorem ambient_local_contDiffOn (hVU : V ≤ U) (f : SmoothFamily V (Fin 4)) :
    ContDiffOn ℝ ∞ (RelativeForms.Pullback.ambientPullback P (ambientLift f))
      (Smooth.baseProductDomain V ComplexPlane₂) :=
  f.smooth_lift.comp
    ((RelativeForms.Pullback.inverseGraph_contDiffOn P).mono (fun _ hq => hVU hq))
    (fun _ hq => hq)

local instance nativeLocalPullbackProductChartedSpace :
    ChartedSpace Model (U × ComplexPlane₂) :=
  inferInstanceAs (ChartedSpace (ModelProd ℂ ComplexPlane₂) (U × ComplexPlane₂))

/-- Real smoothness above the smaller open in the unchanged original covering atlas. -/
theorem upstairs_contMDiffOn (hVU : V ≤ U) (f : SmoothFamily V (Fin 4)) :
    ContMDiffOn (modelWithCornersSelf ℝ Model) (modelWithCornersSelf ℝ ℂ) ∞
      (upstairs P f) {q : U × ComplexPlane₂ | (q.1 : ℂ) ∈ V} :=
  (ambient_local_contDiffOn P hVU f).contMDiffOn.comp
    (Smooth.productOpenInclusion_contMDiff (U := U) (F := ComplexPlane₂)).contMDiffOn
    (fun _ hq => hq)

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.FourierSynthesisNative.Local
