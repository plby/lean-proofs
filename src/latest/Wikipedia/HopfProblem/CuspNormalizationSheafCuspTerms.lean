import Wikipedia.HopfProblem.CuspNormalizationSheafCuspBasic
import Wikipedia.HopfProblem.CuspNormalizationSheafCurves
import Wikipedia.HopfProblem.CuspNormalizationSheafPullback
import Wikipedia.HopfProblem.CuspNormalizationSheafOverBase
import Mathlib.Topology.Sheaves.Abelian

/-!
# The actual holomorphic terms of the cusp normalization resolution

The singular term consists of actual functions locally extending to the cusp
threefold. The other terms are the genuine sheaf pushforwards from the actual
normalization component and its three actual double curves. The maps below
are literal holomorphic pullbacks, with the source's ordering and orientation.
-/

noncomputable section

open Set TopologicalSpace CategoryTheory Opposite
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.CuspNormalization.SheafResolution

open CuspQuotient ToricCharts ToricSpace
open CuspQuotient.NormalizationCurves

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
  (hε1 : ε < 1)
  (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
  (hR : SmallDrift C ε)

/-- The reduced holomorphic-function ring sheaf on the actual singular fibre. -/
def reducedRingSheaf : TopCat.Sheaf CommRingCat (TopCat.of (CentralSpace C ε)) := by
  letI := CuspQuotient.chartedSpace C ε hε hε1 hC hR
  exact SheafReduced.sheaf 𝓘(ℂ, CoordinateSpace 3) (centralSet C ε)

/-- The additive sheaf underlying the actual reduced holomorphic functions. -/
def reducedSheaf : TopCat.Sheaf AddCommGrpCat (TopCat.of (CentralSpace C ε)) := by
  letI := CuspQuotient.chartedSpace C ε hε hε1 hC hR
  exact SheafReduced.additiveSheaf 𝓘(ℂ, CoordinateSpace 3) (centralSet C ε)

/-- The genuine ring-sheaf direct image under the actual normalization map. -/
def normalizationRingSheaf : TopCat.Sheaf CommRingCat (TopCat.of (CentralSpace C ε)) :=
  (TopCat.Sheaf.pushforward CommRingCat (normalizationMap C ε hε)).obj
    (HolomorphicFunctionSheaf.sheaf 𝓘(ℂ, CoordinateSpace 2) (rayDivisor 0))

/-- The genuine additive direct image of the normalization's holomorphic sheaf. -/
def normalizationSheaf : TopCat.Sheaf AddCommGrpCat (TopCat.of (CentralSpace C ε)) :=
  (TopCat.Sheaf.pushforward AddCommGrpCat (normalizationMap C ε hε)).obj
    (HolomorphicFunctionSheaf.additiveSheaf 𝓘(ℂ, CoordinateSpace 2) (rayDivisor 0))

/-- The actual inclusion of the `k`-th double curve in the source ordering. -/
def sourceCurveMap (k : Fin 3) :
    TopCat.of (sourceDoubleCurve C ε hε k) ⟶ TopCat.of (CentralSpace C ε) :=
  curveMap C ε hε (sourceEdgeIndex k)

/-- The genuine ring-sheaf direct image from the actual `k`-th double curve. -/
def curveRingSheaf (k : Fin 3) :
    TopCat.Sheaf CommRingCat (TopCat.of (CentralSpace C ε)) := by
  letI := curveChartedSpace C ε hε hε1 hC hR (sourceEdgeIndex k)
  exact (TopCat.Sheaf.pushforward CommRingCat (sourceCurveMap C ε hε k)).obj
    (HolomorphicFunctionSheaf.sheaf 𝓘(ℂ, ℂ) (sourceDoubleCurve C ε hε k))

/-- The genuine additive direct image from the actual `k`-th double curve. -/
def curveSheaf (k : Fin 3) :
    TopCat.Sheaf AddCommGrpCat (TopCat.of (CentralSpace C ε)) := by
  letI := curveChartedSpace C ε hε hε1 hC hR (sourceEdgeIndex k)
  exact (TopCat.Sheaf.pushforward AddCommGrpCat (sourceCurveMap C ε hε k)).obj
    (HolomorphicFunctionSheaf.additiveSheaf 𝓘(ℂ, ℂ) (sourceDoubleCurve C ε hε k))

/-- The actual normalization pullback on reduced holomorphic functions. -/
def normalizationRingPullback : reducedRingSheaf C ε hε hε1 hC hR ⟶
    normalizationRingSheaf C ε hε := by
  letI := CuspQuotient.chartedSpace C ε hε hε1 hC hR
  let g : ContMDiffMap 𝓘(ℂ, CoordinateSpace 2) 𝓘(ℂ, CoordinateSpace 3)
      (rayDivisor 0) (QuotientSpace C ε) ω :=
    ⟨componentProjection C ε hε, componentProjection_holomorphic C ε hε hε1 hC hR⟩
  exact SheafPullback.pullback 𝓘(ℂ, CoordinateSpace 3) 𝓘(ℂ, CoordinateSpace 2)
    (centralSet C ε) g (projection_componentProjection C ε hε)

/-- The actual first arrow in the additive normalization sequence. -/
def normalizationPullback : reducedSheaf C ε hε hε1 hC hR ⟶
    normalizationSheaf C ε hε := by
  letI := CuspQuotient.chartedSpace C ε hε hε1 hC hR
  let g : ContMDiffMap 𝓘(ℂ, CoordinateSpace 2) 𝓘(ℂ, CoordinateSpace 3)
      (rayDivisor 0) (QuotientSpace C ε) ω :=
    ⟨componentProjection C ε hε, componentProjection_holomorphic C ε hε hε1 hC hR⟩
  exact SheafPullback.additivePullback 𝓘(ℂ, CoordinateSpace 3) 𝓘(ℂ, CoordinateSpace 2)
    (centralSet C ε) g (projection_componentProjection C ε hε)

@[simp] theorem normalization_sourcePlusLift (k : Fin 3)
    (x : sourceDoubleCurve C ε hε k) :
    normalizationMap C ε hε (sourcePlusLift C ε hε k x) = sourceCurveMap C ε hε k x := by
  apply Subtype.ext
  exact componentProjection_sourcePlusLift C ε hε k x

@[simp] theorem normalization_sourceMinusLift (k : Fin 3)
    (x : sourceDoubleCurve C ε hε k) :
    normalizationMap C ε hε (sourceMinusLift C ε hε k x) = sourceCurveMap C ε hε k x := by
  apply Subtype.ext
  exact componentProjection_sourceMinusLift C ε hε k x

/-- Restriction to the source-oriented positive boundary lift. -/
def plusPullback (k : Fin 3) : normalizationSheaf C ε hε ⟶ curveSheaf C ε hε hε1 hC hR k := by
  letI := curveChartedSpace C ε hε hε1 hC hR (sourceEdgeIndex k)
  let g : ContMDiffMap 𝓘(ℂ, ℂ) 𝓘(ℂ, CoordinateSpace 2)
      (sourceDoubleCurve C ε hε k) (rayDivisor 0) ω :=
    ⟨sourcePlusLift C ε hε k, sourcePlusLift_holomorphic C ε hε hε1 hC hR k⟩
  exact SheafOverBase.additivePullback 𝓘(ℂ, CoordinateSpace 2) 𝓘(ℂ, ℂ)
    (normalizationMap C ε hε) (sourceCurveMap C ε hε k) g
    (normalization_sourcePlusLift C ε hε k)

/-- Restriction to the source-oriented negative boundary lift. -/
def minusPullback (k : Fin 3) : normalizationSheaf C ε hε ⟶ curveSheaf C ε hε hε1 hC hR k := by
  letI := curveChartedSpace C ε hε hε1 hC hR (sourceEdgeIndex k)
  let g : ContMDiffMap 𝓘(ℂ, ℂ) 𝓘(ℂ, CoordinateSpace 2)
      (sourceDoubleCurve C ε hε k) (rayDivisor 0) ω :=
    ⟨sourceMinusLift C ε hε k, sourceMinusLift_holomorphic C ε hε hε1 hC hR k⟩
  exact SheafOverBase.additivePullback 𝓘(ℂ, CoordinateSpace 2) 𝓘(ℂ, ℂ)
    (normalizationMap C ε hε) (sourceCurveMap C ε hε k) g
    (normalization_sourceMinusLift C ε hε k)

/-- The actual signed difference along the two preimages of a double curve. -/
def boundaryDifference (k : Fin 3) :
    normalizationSheaf C ε hε ⟶ curveSheaf C ε hε hε1 hC hR k :=
  plusPullback C ε hε hε1 hC hR k - minusPullback C ε hε hε1 hC hR k

end Wikipedia.HopfProblem.CuspNormalization.SheafResolution
