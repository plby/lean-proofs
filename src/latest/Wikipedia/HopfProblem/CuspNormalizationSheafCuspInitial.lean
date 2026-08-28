import Wikipedia.HopfProblem.CuspNormalizationSheafCuspTerms
import Mathlib.CategoryTheory.Sites.LocallyInjective

/-!
# Injectivity and the first complex identity for the actual normalization

The normalization pullback is injective because the actual normalization
map is surjective. Its two restrictions along a double curve coincide
because both actual lifts project to the same point of the singular fibre.
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

/-- Actual pullback is injective on every relative-open section group. -/
theorem normalizationPullback_app_injective (U : Opens (CentralSpace C ε)) :
    Function.Injective ((normalizationPullback C ε hε hε1 hC hR).hom.app (op U)) := by
  let := CuspQuotient.chartedSpace C ε hε hε1 hC hR
  let g : ContMDiffMap 𝓘(ℂ, CoordinateSpace 2) 𝓘(ℂ, CoordinateSpace 3)
      (rayDivisor 0) (QuotientSpace C ε) ω :=
    ⟨componentProjection C ε hε, componentProjection_holomorphic C ε hε hε1 hC hR⟩
  exact SheafPullback.pullbackSection_injective
    𝓘(ℂ, CoordinateSpace 3) 𝓘(ℂ, CoordinateSpace 2) (centralSet C ε) g
    (projection_componentProjection C ε hε) (normalization_surjective C ε hε) U

/-- The initial arrow is a monomorphism of genuine sheaves. -/
instance normalizationPullback_mono : Mono (normalizationPullback C ε hε hε1 hC hR) :=
  CategoryTheory.Sheaf.mono_of_injective _ fun U =>
    normalizationPullback_app_injective C ε hε hε1 hC hR U.unop

/-- Pullbacks of an actual reduced holomorphic function agree along the
two actual lifts of every double curve. -/
theorem normalizationPullback_plus_eq_minus (k : Fin 3) :
    normalizationPullback C ε hε hε1 hC hR ≫ plusPullback C ε hε hε1 hC hR k =
      normalizationPullback C ε hε hε1 hC hR ≫ minusPullback C ε hε hε1 hC hR k := by
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.ext
  intro s
  let := CuspQuotient.chartedSpace C ε hε hε1 hC hR
  let := curveChartedSpace C ε hε hε1 hC hR (sourceEdgeIndex k)
  change SheafReduced.Section 𝓘(ℂ, CoordinateSpace 3) (centralSet C ε) U.unop at s
  apply ContMDiffMap.ext
  intro x
  change s ⟨normalization C ε hε (sourcePlusLift C ε hε k x.val), _⟩ =
    s ⟨normalization C ε hε (sourceMinusLift C ε hε k x.val), _⟩
  apply congrArg s
  apply Subtype.ext
  apply Subtype.ext
  exact (componentProjection_sourcePlusLift C ε hε k x.val).trans
    (componentProjection_sourceMinusLift C ε hε k x.val).symm

/-- The actual first two arrows compose to zero on each double-curve term. -/
theorem normalizationPullback_boundaryDifference (k : Fin 3) :
    normalizationPullback C ε hε hε1 hC hR ≫ boundaryDifference C ε hε hε1 hC hR k = 0 := by
  rw [boundaryDifference, Preadditive.comp_sub,
    normalizationPullback_plus_eq_minus C ε hε hε1 hC hR k, sub_self]

end Wikipedia.HopfProblem.CuspNormalization.SheafResolution
