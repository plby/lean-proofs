import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyFinitePushforwardDegreeZero
import Wikipedia.HopfProblem.CuspNormalizationSheafConstantsResolutionCuspRetractionBasic

/-!
# Actual normalization and double-curve cohomology comparisons

The constructed normalization is closed with finite fibres. Each actual
double-curve map is a closed inclusion, hence also has finite fibres.
Their Hausdorff source spaces therefore satisfy the proved finite closed
pushforward theorem, for arbitrary genuine abelian sheaves. The concrete
holomorphic and constant direct images are the existing resolution terms.
-/

noncomputable section

open Set TopologicalSpace CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.CuspNormalization.SheafResolution

open CuspQuotient ToricCharts ToricSpace NormalizationCurves
open SheafCohomologyFinitePushforward

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
  (hε1 : ε < 1)
  (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
  (hR : SmallDrift C ε)

/-- The actual normalization direct image preserves genuine cohomology
of every actual sheaf, in every degree. -/
def normalizationCohomologyEquiv (F : AbelianSheaf (TopCat.of (rayDivisor 0))) (n : ℕ) :
    CategoryTheory.Sheaf.H.{0} ((pushforward (normalizationMap C ε hε)).obj F) n ≃+
      CategoryTheory.Sheaf.H.{0} F n :=
  cohomologyEquiv (normalizationMap C ε hε) (normalization_isClosedMap C ε hε)
    (normalization_fibre_finite C ε hε hε1 hC hR) F n

/-- The actual source-ordered curve inclusion preserves genuine
cohomology of every actual sheaf, in every degree. -/
def curveCohomologyEquiv (k : Fin 3)
    (F : AbelianSheaf (TopCat.of (sourceDoubleCurve C ε hε k))) (n : ℕ) :
    CategoryTheory.Sheaf.H.{0} ((pushforward (sourceCurveMap C ε hε k)).obj F) n ≃+
      CategoryTheory.Sheaf.H.{0} F n := by
  letI := quotient_t2Space C ε hε hε1 hC hR
  exact cohomologyEquiv (sourceCurveMap C ε hε k)
    (SheafCurveStalk.sourceCurveMap_isClosedMap C ε hε k)
    (sourceCurveMap_fibre_finite C ε hε k) F n

/-- The actual holomorphic normalization resolution term has the
genuine cohomology of the actual normalization component. -/
def normalizationHolomorphicCohomologyEquiv (n : ℕ) :
    CategoryTheory.Sheaf.H.{0} (normalizationSheaf C ε hε) n ≃+
      CategoryTheory.Sheaf.H.{0}
        (HolomorphicFunctionSheaf.additiveSheaf 𝓘(ℂ, CoordinateSpace 2) (rayDivisor 0)) n :=
  normalizationCohomologyEquiv C ε hε hε1 hC hR
    (HolomorphicFunctionSheaf.additiveSheaf 𝓘(ℂ, CoordinateSpace 2) (rayDivisor 0)) n

/-- The actual constant normalization direct image has the cohomology
of the genuine constant sheaf on the actual normalization component. -/
def normalizationConstantCohomologyEquiv (n : ℕ) :
    CategoryTheory.Sheaf.H.{0} (normalizationConstantSheaf C ε hε) n ≃+
      CategoryTheory.Sheaf.H.{0}
        (SheafConstants.complexAdditiveSheaf (TopCat.of (rayDivisor 0))) n :=
  normalizationCohomologyEquiv C ε hε hε1 hC hR
    (SheafConstants.complexAdditiveSheaf (TopCat.of (rayDivisor 0))) n

/-- The actual holomorphic curve resolution term has the cohomology of
the actual curve with its constructed holomorphic atlas. -/
def curveHolomorphicCohomologyEquiv (k : Fin 3) (n : ℕ) :
    letI := curveChartedSpace C ε hε hε1 hC hR (sourceEdgeIndex k)
    CategoryTheory.Sheaf.H.{0} (curveSheaf C ε hε hε1 hC hR k) n ≃+
      CategoryTheory.Sheaf.H.{0}
        (HolomorphicFunctionSheaf.additiveSheaf 𝓘(ℂ, ℂ) (sourceDoubleCurve C ε hε k)) n := by
  letI := curveChartedSpace C ε hε hε1 hC hR (sourceEdgeIndex k)
  exact curveCohomologyEquiv C ε hε hε1 hC hR k
    (HolomorphicFunctionSheaf.additiveSheaf 𝓘(ℂ, ℂ) (sourceDoubleCurve C ε hε k)) n

/-- The actual constant curve direct image has the cohomology of the
genuine constant sheaf on that actual source-ordered curve. -/
def curveConstantCohomologyEquiv (k : Fin 3) (n : ℕ) :
    CategoryTheory.Sheaf.H.{0} (curveConstantSheaf C ε hε k) n ≃+
      CategoryTheory.Sheaf.H.{0}
        (SheafConstants.complexAdditiveSheaf (TopCat.of (sourceDoubleCurve C ε hε k))) n :=
  curveCohomologyEquiv C ε hε hε1 hC hR k
    (SheafConstants.complexAdditiveSheaf (TopCat.of (sourceDoubleCurve C ε hε k))) n

/-- The normalization cohomology comparisons preserve the actual
constant-to-holomorphic map of the normalization resolutions. -/
theorem normalizationConstantsCohomology_naturality (n : ℕ)
    (e : CategoryTheory.Sheaf.H.{0} (normalizationConstantSheaf C ε hε) n) :
    normalizationHolomorphicCohomologyEquiv C ε hε hε1 hC hR n
        (CategoryTheory.Sheaf.H.map (normalizationConstantsMap C ε hε) n e) =
      CategoryTheory.Sheaf.H.map
        (SheafConstants.holomorphicAdditiveMap 𝓘(ℂ, CoordinateSpace 2) (rayDivisor 0)) n
        (normalizationConstantCohomologyEquiv C ε hε hε1 hC hR n e) := by
  have h := cohomologyEquiv_naturality (normalizationMap C ε hε)
    (normalization_isClosedMap C ε hε) (normalization_fibre_finite C ε hε hε1 hC hR)
    (SheafConstants.holomorphicAdditiveMap 𝓘(ℂ, CoordinateSpace 2) (rayDivisor 0)) n e
  exact h

/-- The same genuine comparison square for each actual source-ordered
double curve and its constructed holomorphic atlas. -/
theorem curveConstantsCohomology_naturality (k : Fin 3) (n : ℕ) :
    letI := curveChartedSpace C ε hε hε1 hC hR (sourceEdgeIndex k)
    ∀ e : CategoryTheory.Sheaf.H.{0} (curveConstantSheaf C ε hε k) n,
    curveHolomorphicCohomologyEquiv C ε hε hε1 hC hR k n
        (CategoryTheory.Sheaf.H.map (curveConstantsMap C ε hε hε1 hC hR k) n e) =
      CategoryTheory.Sheaf.H.map
        (SheafConstants.holomorphicAdditiveMap 𝓘(ℂ, ℂ) (sourceDoubleCurve C ε hε k)) n
        (curveConstantCohomologyEquiv C ε hε hε1 hC hR k n e) := by
  let _ := quotient_t2Space C ε hε hε1 hC hR
  let _ := curveChartedSpace C ε hε hε1 hC hR (sourceEdgeIndex k)
  intro e
  have h := cohomologyEquiv_naturality (sourceCurveMap C ε hε k)
    (SheafCurveStalk.sourceCurveMap_isClosedMap C ε hε k) (sourceCurveMap_fibre_finite C ε hε k)
    (SheafConstants.holomorphicAdditiveMap 𝓘(ℂ, ℂ) (sourceDoubleCurve C ε hε k)) n e
  exact h

end Wikipedia.HopfProblem.CuspNormalization.SheafResolution
