import Wikipedia.SmoothSixDPoincare.MorseIndexThreeRelation
import Wikipedia.SmoothSixDPoincare.MorseBandHomology

/-!
# The retained index-three class is the original transported attaching class

The native sphere parametrization sends the constructed standard top class
to the generator used in the actual relation. The original whole-sublevel
band map therefore carries its transported class to that same relation.
-/

noncomputable section

open Set Metric ContinuousMap

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData

open Wikipedia.HopfProblem.SphereHomology
  Wikipedia.HopfProblem.SingularMayerVietoris
  Wikipedia.HopfProblem.PeriodTorusHigherHomology

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p q : M}
  (d : MorseSurgeryData E f p) (d' : MorseSurgeryData E f q)

theorem indexThreeBoundary_generator
    [hindex : Fact (Module.finrank ℝ d.chart.NegativeCoordinates = 2 + 1)] :
    (d.indexThreeBoundaryEquiv hindex.out).symm 1 =
      singularHomologyMap
        (SphereCoordinates.standardParametrization
          d.chart.NegativeCoordinates 2).toHomeomorph.toHomotopyEquiv.toFun 2
            (unitSphereTopClass 1) := rfl

theorem indexThreeAttachingClass_parametrized
    [hindex : Fact (Module.finrank ℝ d.chart.NegativeCoordinates = 2 + 1)] :
    d.indexThreeAttachingClass hindex.out =
      singularHomologyMap
        (d.coreBoundaryMap.comp (SphereCoordinates.standardParametrization
          d.chart.NegativeCoordinates 2).toHomeomorph.toHomotopyEquiv.toFun) 2
            (unitSphereTopClass 1) := by
  rw [singularHomologyMap_comp]
  rfl

theorem bandHomology_transportedAttachingClass
    [hindex : Fact (Module.finrank ℝ d'.chart.NegativeCoordinates = 2 + 1)]
    (e : d.UpperLevel ≃ₜ d'.LowerLevel) (T : M ≃ₜ M)
    (hT : T '' {y : M | f y ≤ f p + d.radius ^ 2} =
      {y : M | f y ≤ f q - d'.radius ^ 2})
    (he : ∀ x : d.UpperLevel, (e x : M) = T x) :
    homeomorphHomologyEquiv (d.bandSublevelHomeomorph d' T hT) 2
      (singularHomologyMap (d.transportedCoreBoundary d' 2 e) 2 (unitSphereTopClass 1)) =
        d'.indexThreeAttachingClass hindex.out := by
  change singularHomologyMap
    (d.bandSublevelHomeomorph d' T hT).toHomotopyEquiv.toFun 2
      (singularHomologyMap (d.transportedCoreBoundary d' 2 e) 2 (unitSphereTopClass 1)) = _
  rw [← LinearMap.comp_apply, ← singularHomologyMap_comp,
    d.bandSublevel_transportedCore d' 2 e T hT he,
    d'.indexThreeAttachingClass_parametrized]

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData
