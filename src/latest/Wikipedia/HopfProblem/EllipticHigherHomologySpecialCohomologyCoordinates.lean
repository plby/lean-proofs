import Wikipedia.HopfProblem.EllipticHigherHomologyCohomologyCoordinates
import Wikipedia.HopfProblem.EllipticHigherHomologySpecialProperties

/-!
# Native integral cohomology coordinates of the special elliptic spaces

The actual special central surface, its literal reduced fibre, and the
entire filling have native singular cohomology coordinates obtained from
their proved homology coordinates and the proved evaluation equivalence.
The formulas retain the actual central inclusion, fibre homeomorphism,
and finite period-torus covering.
-/

noncomputable section

open scoped BigOperators ContinuousMap

namespace Wikipedia.HopfProblem.SpecialPeriods.EllipticFilling

open Elliptic Elliptic.HigherHomology
open SingularMayerVietoris SingularCohomologyFree PeriodTorusHigherHomology

/-- Coordinates on the actual singular cohomology of the special central surface. -/
def specialCentralSurfaceCohomologyCoordinates (j : Kind) (n : ℕ) :
    SingularCohomology (SpecialCentralSurface j) n ≃ₗ[ℤ]
      (Fin (ellipticBettiNumber n) → ℤ) :=
  cohomologyCoordinatesOfHomology (SpecialCentralSurface j) ellipticBettiNumber
    (specialCentralSurfaceHomologyCoordinates j) n

/-- Coordinates on the actual singular cohomology of the literal reduced fibre. -/
def specialCentralFibreCohomologyCoordinates (j : Kind) (n : ℕ) :
    SingularCohomology (SpecialCentralFibre j) n ≃ₗ[ℤ]
      (Fin (ellipticBettiNumber n) → ℤ) :=
  cohomologyCoordinatesOfHomology (SpecialCentralFibre j) ellipticBettiNumber
    (specialCentralFibreHomologyCoordinates j) n

/-- Coordinates on the actual singular cohomology of the entire special filling. -/
def specialFullFillingCohomologyCoordinates (j : Kind) (n : ℕ) :
    SingularCohomology (SpecialFullFilling j) n ≃ₗ[ℤ]
      (Fin (ellipticBettiNumber n) → ℤ) :=
  cohomologyCoordinatesOfHomology (SpecialFullFilling j) ellipticBettiNumber
    (specialFullFillingHomologyCoordinates j) n

@[simp] theorem specialCentralSurfaceCohomologyCoordinates_apply (j : Kind) (n : ℕ)
    (a : SingularCohomology (SpecialCentralSurface j) n) :
    specialCentralSurfaceCohomologyCoordinates j n a =
      intDualCoordinatesOfEquiv (specialCentralSurfaceHomologyCoordinates j n)
        (singularEvaluation (SpecialCentralSurface j) n a) := rfl

@[simp] theorem specialCentralFibreCohomologyCoordinates_apply (j : Kind) (n : ℕ)
    (a : SingularCohomology (SpecialCentralFibre j) n) :
    specialCentralFibreCohomologyCoordinates j n a =
      intDualCoordinatesOfEquiv (specialCentralFibreHomologyCoordinates j n)
        (singularEvaluation (SpecialCentralFibre j) n a) := rfl

@[simp] theorem specialFullFillingCohomologyCoordinates_apply (j : Kind) (n : ℕ)
    (a : SingularCohomology (SpecialFullFilling j) n) :
    specialFullFillingCohomologyCoordinates j n a =
      intDualCoordinatesOfEquiv (specialFullFillingHomologyCoordinates j n)
        (singularEvaluation (SpecialFullFilling j) n a) := rfl

theorem specialCentralSurfaceCohomologyCoordinates_apply_coordinate (j : Kind) (n : ℕ)
    (a : SingularCohomology (SpecialCentralSurface j) n) (i : Fin (ellipticBettiNumber n)) :
    specialCentralSurfaceCohomologyCoordinates j n a i =
      singularEvaluation (SpecialCentralSurface j) n a
        ((specialCentralSurfaceHomologyCoordinates j n).symm (Pi.single i 1)) :=
  cohomologyCoordinatesOfHomology_apply_coordinate (SpecialCentralSurface j) ellipticBettiNumber
    (specialCentralSurfaceHomologyCoordinates j) n a i

theorem specialCentralFibreCohomologyCoordinates_apply_coordinate (j : Kind) (n : ℕ)
    (a : SingularCohomology (SpecialCentralFibre j) n) (i : Fin (ellipticBettiNumber n)) :
    specialCentralFibreCohomologyCoordinates j n a i =
      singularEvaluation (SpecialCentralFibre j) n a
        ((specialCentralFibreHomologyCoordinates j n).symm (Pi.single i 1)) :=
  cohomologyCoordinatesOfHomology_apply_coordinate (SpecialCentralFibre j) ellipticBettiNumber
    (specialCentralFibreHomologyCoordinates j) n a i

theorem specialFullFillingCohomologyCoordinates_apply_coordinate (j : Kind) (n : ℕ)
    (a : SingularCohomology (SpecialFullFilling j) n) (i : Fin (ellipticBettiNumber n)) :
    specialFullFillingCohomologyCoordinates j n a i =
      singularEvaluation (SpecialFullFilling j) n a
        ((specialFullFillingHomologyCoordinates j n).symm (Pi.single i 1)) :=
  cohomologyCoordinatesOfHomology_apply_coordinate (SpecialFullFilling j) ellipticBettiNumber
    (specialFullFillingHomologyCoordinates j) n a i

theorem specialCentralSurfaceCohomologyCoordinates_evaluate (j : Kind) (n : ℕ)
    (a : SingularCohomology (SpecialCentralSurface j) n)
    (b : SingularHomology (SpecialCentralSurface j) n) :
    singularEvaluation (SpecialCentralSurface j) n a b =
      ∑ i, specialCentralSurfaceCohomologyCoordinates j n a i *
        specialCentralSurfaceHomologyCoordinates j n b i :=
  cohomologyCoordinatesOfHomology_evaluate (SpecialCentralSurface j) ellipticBettiNumber
    (specialCentralSurfaceHomologyCoordinates j) n a b

theorem specialCentralFibreCohomologyCoordinates_evaluate (j : Kind) (n : ℕ)
    (a : SingularCohomology (SpecialCentralFibre j) n)
    (b : SingularHomology (SpecialCentralFibre j) n) :
    singularEvaluation (SpecialCentralFibre j) n a b =
      ∑ i, specialCentralFibreCohomologyCoordinates j n a i *
        specialCentralFibreHomologyCoordinates j n b i :=
  cohomologyCoordinatesOfHomology_evaluate (SpecialCentralFibre j) ellipticBettiNumber
    (specialCentralFibreHomologyCoordinates j) n a b

theorem specialFullFillingCohomologyCoordinates_evaluate (j : Kind) (n : ℕ)
    (a : SingularCohomology (SpecialFullFilling j) n)
    (b : SingularHomology (SpecialFullFilling j) n) :
    singularEvaluation (SpecialFullFilling j) n a b =
      ∑ i, specialFullFillingCohomologyCoordinates j n a i *
        specialFullFillingHomologyCoordinates j n b i :=
  cohomologyCoordinatesOfHomology_evaluate (SpecialFullFilling j) ellipticBettiNumber
    (specialFullFillingHomologyCoordinates j) n a b

/-- Pullback along the genuine central inclusion is the identity in these coordinates. -/
theorem specialCentralSurfaceCohomologyCoordinates_centralInclusion (j : Kind) (n : ℕ)
    (a : SingularCohomology (SpecialFullFilling j) n) :
    specialCentralSurfaceCohomologyCoordinates j n
        (singularCohomologyPullback (specialCentralSurfaceIntoFilling j) n a) =
      specialFullFillingCohomologyCoordinates j n a :=
  cohomologyCoordinatesOfHomology_naturality ellipticBettiNumber
    (specialCentralSurfaceHomologyCoordinates j) (specialFullFillingHomologyCoordinates j)
    (specialCentralSurfaceIntoFilling j) n
    (specialFullFillingHomologyCoordinates_centralInclusion j n) a

/-- The literal surface-to-reduced-fibre homeomorphism also preserves the dual coordinates. -/
theorem specialCentralSurfaceCohomologyCoordinates_centralFibreHomeomorph
    (j : Kind) (n : ℕ) (a : SingularCohomology (SpecialCentralFibre j) n) :
    specialCentralSurfaceCohomologyCoordinates j n
        (singularCohomologyPullback
          (toContinuousMap ((specialLocalData j).centralFibreHomeomorph
            j.twist (mainTwist_admissible j))) n a) =
      specialCentralFibreCohomologyCoordinates j n a := by
  apply cohomologyCoordinatesOfHomology_naturality ellipticBettiNumber
    (specialCentralSurfaceHomologyCoordinates j) (specialCentralFibreHomologyCoordinates j)
    _ n _ a
  intro b
  change specialCentralFibreHomologyCoordinates j n (specialCentralFibreHomologyEquiv j n b) =
    specialCentralSurfaceHomologyCoordinates j n b
  exact specialCentralFibreHomologyCoordinates_centralSurface j n b

/-- Native evaluation makes pullback by the actual finite torus covering dual
to its actual homology map, with no covering matrix assumed. -/
theorem specialCentralPeriodCover_cohomology_evaluate (j : Kind) (n : ℕ)
    (a : SingularCohomology (SpecialCentralSurface j) n)
    (b : SingularHomology (SpecialCentralPeriodTorus j) n) :
    singularEvaluation (SpecialCentralPeriodTorus j) n
        (singularCohomologyPullback (specialCentralPeriodCover j) n a) b =
      ∑ i, specialCentralSurfaceCohomologyCoordinates j n a i *
        specialCentralSurfaceHomologyCoordinates j n
          (singularHomologyMap (specialCentralPeriodCover j) n b) i := by
  rw [singularEvaluation_naturality]
  exact specialCentralSurfaceCohomologyCoordinates_evaluate j n a _

/-- The literal period-torus map into the full filling has the same genuine
covering map on the homology side of the evaluation pairing. -/
theorem specialPeriodTorusIntoFilling_cohomology_evaluate (j : Kind) (n : ℕ)
    (a : SingularCohomology (SpecialFullFilling j) n)
    (b : SingularHomology (SpecialCentralPeriodTorus j) n) :
    singularEvaluation (SpecialCentralPeriodTorus j) n
        (singularCohomologyPullback (specialPeriodTorusIntoFilling j) n a) b =
      ∑ i, specialFullFillingCohomologyCoordinates j n a i *
        specialCentralSurfaceHomologyCoordinates j n
          (singularHomologyMap (specialCentralPeriodCover j) n b) i := by
  rw [singularEvaluation_naturality, specialFullFillingCohomologyCoordinates_evaluate]
  simp only [specialFullFillingHomologyCoordinates_periodCover]

end Wikipedia.HopfProblem.SpecialPeriods.EllipticFilling
