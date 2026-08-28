import Wikipedia.HopfProblem.CuspNormalizationSheafConstants
import Wikipedia.HopfProblem.CuspNormalizationSheafCuspTerms

/-!
# Actual constant-sheaf terms on the cusp normalization

The base, normalization component and double curves are the actual
constructed spaces.  The constant terms are genuine constant additive
complex sheaves and their genuine pushforwards along the same geometric
maps used for the holomorphic normalization sequence.  The termwise maps
are the proved inclusions into actual holomorphic functions.
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

/-- The actual constant additive complex sheaf on the singular central fibre. -/
def constantSheaf : TopCat.Sheaf AddCommGrpCat (TopCat.of (CentralSpace C ε)) :=
  SheafConstants.complexAdditiveSheaf (TopCat.of (CentralSpace C ε))

/-- The genuine direct image of constants from the actual normalization. -/
def normalizationConstantSheaf : TopCat.Sheaf AddCommGrpCat (TopCat.of (CentralSpace C ε)) :=
  (TopCat.Sheaf.pushforward AddCommGrpCat (normalizationMap C ε hε)).obj
    (SheafConstants.complexAdditiveSheaf (TopCat.of (rayDivisor 0)))

/-- The genuine direct image of constants from the actual source-ordered double curve. -/
def curveConstantSheaf (k : Fin 3) :
    TopCat.Sheaf AddCommGrpCat (TopCat.of (CentralSpace C ε)) :=
  (TopCat.Sheaf.pushforward AddCommGrpCat (sourceCurveMap C ε hε k)).obj
    (SheafConstants.complexAdditiveSheaf (TopCat.of (sourceDoubleCurve C ε hε k)))

/-- Actual pullback of locally constant sections along the normalization map. -/
def normalizationConstantPullback : constantSheaf C ε ⟶ normalizationConstantSheaf C ε hε :=
  SheafConstants.additivePullbackMap (normalizationMap C ε hε)

/-- The constants inclusion on the actual singular central fibre. -/
def reducedConstantsMap : constantSheaf C ε ⟶ reducedSheaf C ε hε hε1 hC hR := by
  letI := CuspQuotient.chartedSpace C ε hε hε1 hC hR
  exact SheafConstants.reducedAdditiveMap 𝓘(ℂ, CoordinateSpace 3) (centralSet C ε)

/-- The actual constants inclusion pushed forward from the normalization component. -/
def normalizationConstantsMap :
    normalizationConstantSheaf C ε hε ⟶ normalizationSheaf C ε hε :=
  (TopCat.Sheaf.pushforward AddCommGrpCat (normalizationMap C ε hε)).map
    (SheafConstants.holomorphicAdditiveMap 𝓘(ℂ, CoordinateSpace 2) (rayDivisor 0))

/-- The actual constants inclusion pushed forward from a double curve. -/
def curveConstantsMap (k : Fin 3) :
    curveConstantSheaf C ε hε k ⟶ curveSheaf C ε hε hε1 hC hR k := by
  letI := curveChartedSpace C ε hε hε1 hC hR (sourceEdgeIndex k)
  exact (TopCat.Sheaf.pushforward AddCommGrpCat (sourceCurveMap C ε hε k)).map
    (SheafConstants.holomorphicAdditiveMap 𝓘(ℂ, ℂ) (sourceDoubleCurve C ε hε k))

/-- The singular-fibre constants map is genuinely injective. -/
instance reducedConstantsMap_mono : Mono (reducedConstantsMap C ε hε hε1 hC hR) := by
  let _ := CuspQuotient.chartedSpace C ε hε hε1 hC hR
  exact SheafConstants.reducedAdditiveMap_mono 𝓘(ℂ, CoordinateSpace 3) (centralSet C ε)

/-- Direct image retains the actual componentwise constants inclusion. -/
instance normalizationConstantsMap_mono : Mono (normalizationConstantsMap C ε hε) := by
  apply CategoryTheory.Sheaf.mono_of_injective
  intro U
  exact SheafConstants.holomorphicMap_app_injective 𝓘(ℂ, CoordinateSpace 2) (rayDivisor 0)
    ((Opens.map (normalizationMap C ε hε)).obj U.unop)

/-- Each actual double-curve constants map is genuinely injective. -/
instance curveConstantsMap_mono (k : Fin 3) : Mono (curveConstantsMap C ε hε hε1 hC hR k) := by
  let _ := curveChartedSpace C ε hε hε1 hC hR (sourceEdgeIndex k)
  apply CategoryTheory.Sheaf.mono_of_injective
  intro U
  exact SheafConstants.holomorphicMap_app_injective 𝓘(ℂ, ℂ) (sourceDoubleCurve C ε hε k)
    ((Opens.map (sourceCurveMap C ε hε k)).obj U.unop)

/-- The first square of the actual constant/holomorphic normalization
diagram commutes by actual holomorphic pullback naturality. -/
theorem normalization_constants_naturality :
    reducedConstantsMap C ε hε hε1 hC hR ≫ normalizationPullback C ε hε hε1 hC hR =
      normalizationConstantPullback C ε hε ≫ normalizationConstantsMap C ε hε := by
  let _ := CuspQuotient.chartedSpace C ε hε hε1 hC hR
  let g : ContMDiffMap 𝓘(ℂ, CoordinateSpace 2) 𝓘(ℂ, CoordinateSpace 3)
      (rayDivisor 0) (QuotientSpace C ε) ω :=
    ⟨componentProjection C ε hε, componentProjection_holomorphic C ε hε hε1 hC hR⟩
  exact SheafConstants.reduced_holomorphic_additive_naturality
    𝓘(ℂ, CoordinateSpace 3) 𝓘(ℂ, CoordinateSpace 2) (centralSet C ε) g
    (projection_componentProjection C ε hε)

end Wikipedia.HopfProblem.CuspNormalization.SheafResolution
