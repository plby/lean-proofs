import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyOpenClassRestrictionGeneric
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyOpenClassRestrictionFamilyClass
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyOpenClasses
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyCechFibreClass

/-!
# The genuine neighborhood comparison of an original global period class

First restrict the actual extension class to the actual full base
preimage. Then use the original restriction biholomorphism and its true
holomorphic section pullback. The common-refinement calculation identifies
the resulting cocycle class with the independently constructed period
class of the original restricted family. All cohomology groups and maps
are the previously defined native ones.
-/

noncomputable section

open TopologicalSpace CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.OpenClassRestriction

open HolomorphicFunctionSheaf.SphereH1 HolomorphicPicard.CechExtension
open HolomorphicSheafCohomology PeriodFamilyHigherDirectImage

variable {V : Type*} {B : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [TopologicalSpace B] [ChartedSpace V B]

local notation "IT" => modelWithCornersSelf ℂ (V × ComplexPlane₂)

/-- The literal original cover on the actual full base preimage. -/
abbrev familyOpenCover (P : HolomorphicPeriodMap V B) (A : Opens B) :
    B × ComplexPlane₂ → Opens (Zero.basePreimage P A) :=
  restrictedCover (X := TopCat.of P.TotalSpace) (Zero.basePreimage P A) (Cocycle.coverOpen P)

theorem familyOpenCover_covers (P : HolomorphicPeriodMap V B) (A : Opens B) :
    ∀ x : Zero.basePreimage P A, ∃ i, x ∈ familyOpenCover P A i :=
  restrictedCover_covers (X := TopCat.of P.TotalSpace) (Zero.basePreimage P A)
    (Cocycle.coverOpen_covers P)

variable [IsManifold (modelWithCornersSelf ℂ V) ω B]

/-- The actual restricted holomorphic cocycle in the inherited original total atlas. -/
def familyOpenCocycle (P : HolomorphicPeriodMap V B) (A : Opens B)
    (a : Cocycle.Coefficients V B) :
    CechOneCocycle (OpenClasses.preimageHolomorphicSheaf P A) (familyOpenCover P A) := by
  letI := P.totalChartedSpace
  exact holomorphicRestrictedCocycle IT (Zero.basePreimage P A) (Cocycle.cocycle P a)

/-- The actual biholomorphic pullback of this literal open cocycle. -/
def familyBiholomorphicPullbackCocycle (P : HolomorphicPeriodMap V B) (A : Opens B)
    (a : Cocycle.Coefficients V B) :
    CechOneCocycle (Zero.totalAdditiveSheaf (Restriction.restrictedPeriods P A))
      (familyPullbackCover P A) := by
  letI := (Restriction.restrictedPeriods P A).totalChartedSpace
  letI := P.totalChartedSpace
  exact CechFibre.pullbackCocycle
    (Biholomorph.underlyingMap (Restriction.restrictionBiholomorph P A))
    (Biholomorph.additiveSheafIso (Restriction.restrictionBiholomorph P A)).hom
    (familyOpenCocycle P A a)

/-- The two genuine section pullbacks evaluate the same original functions. -/
theorem familyBiholomorphicPullbackCocycle_eq (P : HolomorphicPeriodMap V B) (A : Opens B)
    (a : Cocycle.Coefficients V B) :
    familyBiholomorphicPullbackCocycle P A a = familyPullbackCocycle P A a := by
  let := (Restriction.restrictedPeriods P A).totalChartedSpace
  let := P.totalChartedSpace
  apply HolomorphicPicard.Cech.cocycle_ext
  intro i j
  apply ContMDiffMap.ext
  intro x
  rfl

/-- Native open restriction of the original global class has the literal open cocycle. -/
theorem openCohomologyEquiv_globalPeriodClass (P : HolomorphicPeriodMap V B) (A : Opens B)
    (a : Cocycle.Coefficients V B) :
    OpenClasses.openCohomologyEquiv P A 1
      (GlobalRestriction.restrictionMap (Zero.totalAdditiveSheaf P) (Zero.basePreimage P A)
        1 (Cocycle.periodClass P a)) =
      classOf (familyOpenCocycle P A a) (familyOpenCover_covers P A) := by
  let := P.totalChartedSpace
  exact holomorphicCohomologyEquiv_restrictionMap_classOf IT (Zero.basePreimage P A)
    (Cocycle.cocycle P a) (Cocycle.coverOpen_covers P)

variable [T2Space B]

/-- The actual homeomorphic finite-closed comparison sends the literal
open cocycle class to the class of its genuine biholomorphic pullback. -/
theorem restrictedFamilyCohomologyEquiv_openClassOf
    (P : HolomorphicPeriodMap V B) (A : Opens B) (a : Cocycle.Coefficients V B) :
    OpenClasses.restrictedFamilyCohomologyEquiv P A 1
        (classOf (familyOpenCocycle P A a) (familyOpenCover_covers P A)) =
      classOf (familyBiholomorphicPullbackCocycle P A a) (familyPullbackCover_covers P A) := by
  let := (Restriction.restrictedPeriods P A).totalChartedSpace
  let := P.totalChartedSpace
  exact CechFibre.cohomologyEquiv_map_classOf
    (Biholomorph.underlyingMap (Restriction.restrictionBiholomorph P A))
    (Restriction.restrictionBiholomorph P A).toHomeomorph.isClosedMap
    (Biholomorph.underlyingMap_fibre_finite (Restriction.restrictionBiholomorph P A))
    (Biholomorph.additiveSheafIso (Restriction.restrictionBiholomorph P A)).hom
    (familyOpenCocycle P A a) (familyOpenCover_covers P A)

/-- The genuine neighborhood comparison of a globally restricted
period class is the original period class with literally restricted coefficients. -/
theorem neighborhoodCohomologyEquiv_globalPeriodClass
    (P : HolomorphicPeriodMap V B) (A : Opens B) (a : Cocycle.Coefficients V B) :
    OpenClasses.neighborhoodCohomologyEquiv P A 1
      (GlobalRestriction.restrictionMap (Zero.totalAdditiveSheaf P) (Zero.basePreimage P A)
        1 (Cocycle.periodClass P a)) =
      Cocycle.periodClass (Restriction.restrictedPeriods P A) (restrictCoefficients A a) := by
  change OpenClasses.restrictedFamilyCohomologyEquiv P A 1
    (OpenClasses.openCohomologyEquiv P A 1 _) = _
  exact (congrArg (OpenClasses.restrictedFamilyCohomologyEquiv P A 1)
    (openCohomologyEquiv_globalPeriodClass P A a)).trans
    ((restrictedFamilyCohomologyEquiv_openClassOf P A a).trans
      ((congrArg (fun c => classOf c (familyPullbackCover_covers P A))
        (familyBiholomorphicPullbackCocycle_eq P A a)).trans
        (familyPullbackCocycle_classOf P A a)))

/-- The constructed native neighborhood class of restricted global
coefficients is precisely the original cohomology-presheaf restriction. -/
theorem openPeriodClass_restrictCoefficients
    (P : HolomorphicPeriodMap V B) (A : Opens B) (a : Cocycle.Coefficients V B) :
    OpenClasses.periodClass P A (restrictCoefficients A a) =
      GlobalRestriction.restrictionMap (Zero.totalAdditiveSheaf P) (Zero.basePreimage P A)
        1 (Cocycle.periodClass P a) := by
  apply (OpenClasses.neighborhoodCohomologyEquiv P A 1).injective
  exact (OpenClasses.periodClass_comparison P A (restrictCoefficients A a)).trans
    (neighborhoodCohomologyEquiv_globalPeriodClass P A a).symm

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.OpenClassRestriction
