import Wikipedia.HopfProblem.CuspNormalizationSheafCurveStalkPullbackCoordinates
import Wikipedia.HopfProblem.CuspNormalizationSheafCurveStalkPullbackFunctions
import Wikipedia.HopfProblem.CuspNormalizationSheafCurveStalkAxes
import Wikipedia.HopfProblem.CuspNormalizationSheafNormalizationStalkBranches

/-!
# Actual signed pullbacks on centered section representatives

The literal axis representative of a section pulled back along either
actual signed lift is exactly the corresponding literal branch
representative composed with its coordinate-axis inclusion.
-/

noncomputable section

open Set TopologicalSpace CategoryTheory Opposite
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.CuspNormalization.SheafCurveStalk

open CuspQuotient ToricCharts ToricSpace ToricComponent ToricFan
  NormalizationCurves NormalizationLocalCoordinates SheafResolution SheafNormalizationStalk

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
  (hε1 : ε < 1)
  (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
  (hR : SmallDrift C ε) (s : Triangle) (b : CoordinateSpace 3) (k : Fin 3)
  (hk : sourcePair s k ⊆ Germs.activeBranches b)

include hk in
/-- The actual positive section pullback in the actual centered charts. -/
theorem axisRepresentative_plusPullback (U : Opens (CentralSpace C ε))
    (f : HolomorphicFunctionSheaf.Section 𝓘(ℂ, CoordinateSpace 2) (rayDivisor 0)
      ((Opens.map (normalizationMap C ε hε)).obj U)) :
    axisSectionRepresentative C ε hε hε1 hC hR s k
        (b (s.axisIndex (sourceEdgeIndex k)))
        ((Opens.map (sourceCurveMap C ε hε k)).obj U)
        ((plusPullback C ε hε hε1 hC hR k).hom.app (op U) f) =
      branchSectionRepresentative C s (plusBranch s k)
          (removeCoordinate (plusBranch s k) b)
          ((Opens.map (normalizationMap C ε hε)).obj U) f ∘ Pi.single (plusAxisIndex s k) := by
  let := curveChartedSpace C ε hε hε1 hC hR (sourceEdgeIndex k)
  funext z
  exact (congrFun (plusPullback_extend C ε hε hε1 hC hR k U f)
    (axisSection C ε hε s (sourceEdgeIndex k)
      (b (s.axisIndex (sourceEdgeIndex k)) + z))).trans
    (congrArg
      (HolomorphicFunctionSheaf.extendManifoldSection 𝓘(ℂ, CoordinateSpace 2)
        ((Opens.map (normalizationMap C ε hε)).obj U) f)
      (sourcePlusLift_axisSection_centered C ε hε s b k hk z))

include hk in
/-- The actual negative section pullback in the actual centered charts. -/
theorem axisRepresentative_minusPullback (U : Opens (CentralSpace C ε))
    (f : HolomorphicFunctionSheaf.Section 𝓘(ℂ, CoordinateSpace 2) (rayDivisor 0)
      ((Opens.map (normalizationMap C ε hε)).obj U)) :
    axisSectionRepresentative C ε hε hε1 hC hR s k
        (b (s.axisIndex (sourceEdgeIndex k)))
        ((Opens.map (sourceCurveMap C ε hε k)).obj U)
        ((minusPullback C ε hε hε1 hC hR k).hom.app (op U) f) =
      branchSectionRepresentative C s (minusBranch s k)
          (removeCoordinate (minusBranch s k) b)
          ((Opens.map (normalizationMap C ε hε)).obj U) f ∘ Pi.single (minusAxisIndex s k) := by
  let := curveChartedSpace C ε hε hε1 hC hR (sourceEdgeIndex k)
  funext z
  exact (congrFun (minusPullback_extend C ε hε hε1 hC hR k U f)
    (axisSection C ε hε s (sourceEdgeIndex k)
      (b (s.axisIndex (sourceEdgeIndex k)) + z))).trans
    (congrArg
      (HolomorphicFunctionSheaf.extendManifoldSection 𝓘(ℂ, CoordinateSpace 2)
        ((Opens.map (normalizationMap C ε hε)).obj U) f)
      (sourceMinusLift_axisSection_centered C ε hε s b k hk z))

end Wikipedia.HopfProblem.CuspNormalization.SheafCurveStalk
