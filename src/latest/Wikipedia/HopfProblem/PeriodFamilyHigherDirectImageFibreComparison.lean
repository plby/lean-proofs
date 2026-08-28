import Wikipedia.HopfProblem.PeriodFamilyHigherDirectImageFibreStalk
import Wikipedia.HopfProblem.PeriodFamilyHigherDirectImageFibreGeometry
import Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomology

/-!
# Original regular period-family stalks map to their actual fibre cohomology

The family and the fibres use their unchanged native complex atlases.
The genuine holomorphic restriction map and the proved closed finite
fibre inclusion construct additive maps from the original right-derived
pushforward stalks to the original fibre's Ext-defined cohomology.

Every neighborhood representative is sent to its actual restriction.
The degree-one and degree-two target coordinates are the previously
proved marked Haar-mean coordinates. No bijectivity, local freeness,
or positive-degree base-change theorem is asserted here.
-/

noncomputable section

open CategoryTheory TopologicalSpace Opposite
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodFamilyHigherDirectImage

variable {V : Type*} {B : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [TopologicalSpace B] [ChartedSpace V B]

/-- The genuine right-derived holomorphic-function pushforward for the original family. -/
abbrev higherDirectImage (P : HolomorphicPeriodMap V B) (n : ℕ) :=
  SheafHigherDirectImage.sheaf (Zero.projectionMap P) (Zero.totalAdditiveSheaf P) n

/-- The actual stalk of that native derived sheaf. -/
abbrev higherDirectImageStalk (P : HolomorphicPeriodMap V B) (b : B) (n : ℕ) :=
  TopCat.Presheaf.stalk (higherDirectImage P n).obj b

/-- Mathlib's original neighborhood cohomology for the full inverse image of a base open. -/
abbrev neighborhoodCohomology (P : HolomorphicPeriodMap V B) (U : Opens B) (n : ℕ) :=
  CategoryTheory.Sheaf.H'.{0} (Zero.totalAdditiveSheaf P) n
    ((Opens.map (Zero.projectionMap P)).obj U)

/-- An original neighborhood class gives its actual derived-stalk germ. -/
def neighborhoodGerm (P : HolomorphicPeriodMap V B) (b : B) (n : ℕ)
    (U : Opens B) (hb : b ∈ U) :
    neighborhoodCohomology P U n ⟶ higherDirectImageStalk P b n :=
  FibreNeighborhood.derivedNeighborhoodGerm
    (F := Zero.totalAdditiveSheaf P) (Zero.projectionMap P) b n U hb

variable [IsManifold (modelWithCornersSelf ℂ V) ω B] [T2Space B]

/-- The genuine closed-fibre restriction of a neighborhood's original Ext class. -/
def neighborhoodFibreEvaluation (P : HolomorphicPeriodMap V B) (b : B)
    (n : ℕ) (U : Opens B) (hb : b ∈ U) :
    ↥(neighborhoodCohomology P U n) →+
      PeriodTorusHolomorphicCohomology.H (P.point b) n :=
  FibreNeighborhood.cohomologyEvaluation (FibreGeometry.fibreMap P b)
    (FibreGeometry.fibreMap_isClosedMap P b) (FibreGeometry.fibreMap_finite_fibres P b)
    (FibreGeometry.coefficientPullback P b)
    ((Opens.map (Zero.projectionMap P)).obj U)
    (FibreGeometry.fibreMap_mem_fullPreimage P b hb) n

/-- The actual higher-direct-image stalk maps to the original native period-torus cohomology. -/
def fibreEvaluation (P : HolomorphicPeriodMap V B) (b : B) (n : ℕ) :
    higherDirectImageStalk P b n ⟶
      AddCommGrpCat.of (PeriodTorusHolomorphicCohomology.H (P.point b) n) :=
  FibreNeighborhood.derivedStalkEvaluation (FibreGeometry.fibreMap P b)
    (FibreGeometry.fibreMap_isClosedMap P b) (FibreGeometry.fibreMap_finite_fibres P b)
    (FibreGeometry.coefficientPullback P b) (Zero.projectionMap P) b
    (FibreGeometry.projection_fibreMap_apply P b) n

/-- Every actual neighborhood germ is evaluated by its genuine coefficient-sheaf restriction. -/
theorem fibreEvaluation_neighborhoodGerm (P : HolomorphicPeriodMap V B) (b : B) (n : ℕ)
    (U : Opens B) (hb : b ∈ U) :
    neighborhoodGerm P b n U hb ≫ fibreEvaluation P b n =
      AddCommGrpCat.ofHom (neighborhoodFibreEvaluation P b n U hb) :=
  FibreNeighborhood.derivedStalkEvaluation_germ (FibreGeometry.fibreMap P b)
    (FibreGeometry.fibreMap_isClosedMap P b) (FibreGeometry.fibreMap_finite_fibres P b)
    (FibreGeometry.coefficientPullback P b) (Zero.projectionMap P) b
    (FibreGeometry.projection_fibreMap_apply P b) n U hb

theorem fibreEvaluation_neighborhoodGerm_apply (P : HolomorphicPeriodMap V B)
    (b : B) (n : ℕ) (U : Opens B) (hb : b ∈ U) (a : neighborhoodCohomology P U n) :
    fibreEvaluation P b n (neighborhoodGerm P b n U hb a) =
      neighborhoodFibreEvaluation P b n U hb a :=
  ConcreteCategory.congr_hom (fibreEvaluation_neighborhoodGerm P b n U hb) a

/-- The degree-one fibre coordinate map uses the actual proved two Haar-mean coordinates. -/
def oneFibreCoordinates (P : HolomorphicPeriodMap V B) (b : B) :
    ↥(higherDirectImageStalk P b 1) →+ (Fin 2 → ℂ) :=
  (PeriodTorusHolomorphicCohomology.h1Equiv (P.point b)).toAddEquiv.toAddMonoidHom.comp
    (fibreEvaluation P b 1).hom

/-- The degree-two fibre coordinate map uses the actual proved top Haar-mean coordinate. -/
def twoFibreCoordinate (P : HolomorphicPeriodMap V B) (b : B) :
    ↥(higherDirectImageStalk P b 2) →+ ℂ :=
  (PeriodTorusHolomorphicCohomology.h2Equiv (P.point b)).toAddEquiv.toAddMonoidHom.comp
    (fibreEvaluation P b 2).hom

/-- The marked coordinates of a neighborhood class are taken after actual fibre restriction. -/
theorem oneFibreCoordinates_neighborhoodGerm (P : HolomorphicPeriodMap V B) (b : B)
    (U : Opens B) (hb : b ∈ U) (a : neighborhoodCohomology P U 1) :
    oneFibreCoordinates P b (neighborhoodGerm P b 1 U hb a) =
      PeriodTorusHolomorphicCohomology.h1Equiv (P.point b)
        (neighborhoodFibreEvaluation P b 1 U hb a) :=
  congrArg (PeriodTorusHolomorphicCohomology.h1Equiv (P.point b))
    (fibreEvaluation_neighborhoodGerm_apply P b 1 U hb a)

theorem twoFibreCoordinate_neighborhoodGerm (P : HolomorphicPeriodMap V B) (b : B)
    (U : Opens B) (hb : b ∈ U) (a : neighborhoodCohomology P U 2) :
    twoFibreCoordinate P b (neighborhoodGerm P b 2 U hb a) =
      PeriodTorusHolomorphicCohomology.h2Equiv (P.point b)
        (neighborhoodFibreEvaluation P b 2 U hb a) :=
  congrArg (PeriodTorusHolomorphicCohomology.h2Equiv (P.point b))
    (fibreEvaluation_neighborhoodGerm_apply P b 2 U hb a)

end Wikipedia.HopfProblem.PeriodFamilyHigherDirectImage
