import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyOpenBaseActionBasic
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyOpenBaseActionComparisonBasic

/-!
# Native restricted-family comparison and base-open multiplication

The actual restriction biholomorphism preserves the literal base projection.
Consequently its holomorphic sheaf pullback commutes with multiplication by
the same original base-open function. Coefficient naturality then proves
compatibility of the original cohomology comparison in every degree.
Both original varying-period quotient atlases are retained explicitly.
-/

noncomputable section

open CategoryTheory TopologicalSpace Opposite
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.OpenBaseAction

open PeriodFamilyHigherDirectImage HolomorphicSheafCohomology

variable {V : Type*} {B : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [TopologicalSpace B] [ChartedSpace V B]
  [IsManifold (modelWithCornersSelf ℂ V) ω B]

/-- The original holomorphic pullback square commutes with actual
base-open multiplication on every open of the two native manifolds. -/
@[reassoc] theorem restrictionBiholomorph_sheafIso_baseMultiply
    (P : HolomorphicPeriodMap V B) (U : Opens B) (g : Zero.BaseSection P U) :
    letI := (Restriction.restrictedPeriods P U).totalChartedSpace
    letI := P.totalChartedSpace
    preimageMultiplyEnd P U g ≫
        (Biholomorph.additiveSheafIso (Restriction.restrictionBiholomorph P U)).hom =
      (Biholomorph.additiveSheafIso (Restriction.restrictionBiholomorph P U)).hom ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat
          (Biholomorph.underlyingMap (Restriction.restrictionBiholomorph P U))).map
          (BaseFunctionAction.baseMultiplyEnd (Restriction.restrictedPeriods P U) g) := by
  let := (Restriction.restrictedPeriods P U).totalChartedSpace
  let := P.totalChartedSpace
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext W
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro s
  apply ContMDiffMap.ext
  intro x
  rfl

/-- The genuine all-degree restricted-family comparison preserves
the original coefficient maps of a holomorphic base-open function. -/
theorem restrictedFamilyCohomologyEquiv_baseMultiply [T2Space B]
    (P : HolomorphicPeriodMap V B) (U : Opens B) (q : ℕ) (g : Zero.BaseSection P U)
    (x : CategoryTheory.Sheaf.H.{0} (OpenClasses.preimageHolomorphicSheaf P U) q) :
    OpenClasses.restrictedFamilyCohomologyEquiv P U q
        (CategoryTheory.Sheaf.H.map (preimageMultiplyEnd P U g) q x) =
      CategoryTheory.Sheaf.H.map
        (BaseFunctionAction.baseMultiplyEnd (Restriction.restrictedPeriods P U) g) q
        (OpenClasses.restrictedFamilyCohomologyEquiv P U q x) := by
  let := (Restriction.restrictedPeriods P U).totalChartedSpace
  let := P.totalChartedSpace
  exact biholomorph_cohomologyEquiv_naturality
    (Restriction.restrictionBiholomorph P U) (preimageMultiplyEnd P U g)
    (BaseFunctionAction.baseMultiplyEnd (Restriction.restrictedPeriods P U) g)
    (restrictionBiholomorph_sheafIso_baseMultiply P U g) q x

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.OpenBaseAction
