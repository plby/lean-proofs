import Wikipedia.HopfProblem.EllipticHigherHomologyCohomologyCoordinates
import Wikipedia.HopfProblem.EllipticHigherHomologyProperties

/-!
# Native integral cohomology of the actual elliptic spaces

The previously proved coordinates on singular homology give coordinates
on the homology of the actual singular cochain complex.  The evaluation
pairing is a dot product in these coordinates, in every degree.  The
required freeness hypotheses are discharged by the actual homology
computations; no universal-coefficient conclusion is assumed.
-/

noncomputable section

open scoped BigOperators ContinuousMap

namespace Wikipedia.HopfProblem.Elliptic.HigherHomology

open SingularMayerVietoris SingularCohomologyFree

/-- All-degree native cohomology coordinates of the actual mapping torus. -/
def mappingTorusCohomologyCoordinates (j : Kind) (n : ℕ) :
    SingularCohomology (mappingTorusModel j) n ≃ₗ[ℤ]
      (Fin (ellipticBettiNumber n) → ℤ) :=
  cohomologyCoordinatesOfHomology (mappingTorusModel j) ellipticBettiNumber
    (mappingTorusHomologyCoordinates j) n

/-- All-degree native cohomology coordinates of the actual central surface. -/
def surfaceCohomologyCoordinates (j : Kind) (p : FixedPeriod j) (n : ℕ) :
    SingularCohomology (Surface j p j.twist (mainTwist_admissible j)) n ≃ₗ[ℤ]
      (Fin (ellipticBettiNumber n) → ℤ) :=
  cohomologyCoordinatesOfHomology (Surface j p j.twist (mainTwist_admissible j))
    ellipticBettiNumber (surfaceHomologyCoordinates j p) n

@[simp] theorem mappingTorusCohomologyCoordinates_apply (j : Kind) (n : ℕ)
    (a : SingularCohomology (mappingTorusModel j) n) :
    mappingTorusCohomologyCoordinates j n a =
      intDualCoordinatesOfEquiv (mappingTorusHomologyCoordinates j n)
        (singularEvaluation (mappingTorusModel j) n a) := rfl

@[simp] theorem surfaceCohomologyCoordinates_apply (j : Kind) (p : FixedPeriod j) (n : ℕ)
    (a : SingularCohomology (Surface j p j.twist (mainTwist_admissible j)) n) :
    surfaceCohomologyCoordinates j p n a =
      intDualCoordinatesOfEquiv (surfaceHomologyCoordinates j p n)
        (singularEvaluation (Surface j p j.twist (mainTwist_admissible j)) n a) := rfl

theorem mappingTorusCohomologyCoordinates_apply_coordinate (j : Kind) (n : ℕ)
    (a : SingularCohomology (mappingTorusModel j) n) (i : Fin (ellipticBettiNumber n)) :
    mappingTorusCohomologyCoordinates j n a i =
      singularEvaluation (mappingTorusModel j) n a
        ((mappingTorusHomologyCoordinates j n).symm (Pi.single i 1)) :=
  cohomologyCoordinatesOfHomology_apply_coordinate (mappingTorusModel j) ellipticBettiNumber
    (mappingTorusHomologyCoordinates j) n a i

theorem surfaceCohomologyCoordinates_apply_coordinate
    (j : Kind) (p : FixedPeriod j) (n : ℕ)
    (a : SingularCohomology (Surface j p j.twist (mainTwist_admissible j)) n)
    (i : Fin (ellipticBettiNumber n)) :
    surfaceCohomologyCoordinates j p n a i =
      singularEvaluation (Surface j p j.twist (mainTwist_admissible j)) n a
        ((surfaceHomologyCoordinates j p n).symm (Pi.single i 1)) :=
  cohomologyCoordinatesOfHomology_apply_coordinate
    (Surface j p j.twist (mainTwist_admissible j)) ellipticBettiNumber
    (surfaceHomologyCoordinates j p) n a i

theorem mappingTorusCohomologyCoordinates_evaluate (j : Kind) (n : ℕ)
    (a : SingularCohomology (mappingTorusModel j) n)
    (b : SingularHomology (mappingTorusModel j) n) :
    singularEvaluation (mappingTorusModel j) n a b =
      ∑ i, mappingTorusCohomologyCoordinates j n a i *
        mappingTorusHomologyCoordinates j n b i :=
  cohomologyCoordinatesOfHomology_evaluate (mappingTorusModel j) ellipticBettiNumber
    (mappingTorusHomologyCoordinates j) n a b

theorem surfaceCohomologyCoordinates_evaluate (j : Kind) (p : FixedPeriod j) (n : ℕ)
    (a : SingularCohomology (Surface j p j.twist (mainTwist_admissible j)) n)
    (b : SingularHomology (Surface j p j.twist (mainTwist_admissible j)) n) :
    singularEvaluation (Surface j p j.twist (mainTwist_admissible j)) n a b =
      ∑ i, surfaceCohomologyCoordinates j p n a i * surfaceHomologyCoordinates j p n b i :=
  cohomologyCoordinatesOfHomology_evaluate
    (Surface j p j.twist (mainTwist_admissible j)) ellipticBettiNumber
    (surfaceHomologyCoordinates j p) n a b

variable {j : Kind} (D : Equivariant.Data j)

/-- All-degree native cohomology coordinates of the actual entire filling. -/
def fillingCohomologyCoordinates (n : ℕ) :
    SingularCohomology (D.Space j.twist (mainTwist_admissible j)) n ≃ₗ[ℤ]
      (Fin (ellipticBettiNumber n) → ℤ) :=
  cohomologyCoordinatesOfHomology (D.Space j.twist (mainTwist_admissible j))
    ellipticBettiNumber (fillingHomologyCoordinates D) n

@[simp] theorem fillingCohomologyCoordinates_apply (n : ℕ)
    (a : SingularCohomology (D.Space j.twist (mainTwist_admissible j)) n) :
    fillingCohomologyCoordinates D n a =
      intDualCoordinatesOfEquiv (fillingHomologyCoordinates D n)
        (singularEvaluation (D.Space j.twist (mainTwist_admissible j)) n a) := rfl

theorem fillingCohomologyCoordinates_apply_coordinate (n : ℕ)
    (a : SingularCohomology (D.Space j.twist (mainTwist_admissible j)) n)
    (i : Fin (ellipticBettiNumber n)) :
    fillingCohomologyCoordinates D n a i =
      singularEvaluation (D.Space j.twist (mainTwist_admissible j)) n a
        ((fillingHomologyCoordinates D n).symm (Pi.single i 1)) :=
  cohomologyCoordinatesOfHomology_apply_coordinate
    (D.Space j.twist (mainTwist_admissible j)) ellipticBettiNumber
    (fillingHomologyCoordinates D) n a i

theorem fillingCohomologyCoordinates_evaluate (n : ℕ)
    (a : SingularCohomology (D.Space j.twist (mainTwist_admissible j)) n)
    (b : SingularHomology (D.Space j.twist (mainTwist_admissible j)) n) :
    singularEvaluation (D.Space j.twist (mainTwist_admissible j)) n a b =
      ∑ i, fillingCohomologyCoordinates D n a i * fillingHomologyCoordinates D n b i :=
  cohomologyCoordinatesOfHomology_evaluate
    (D.Space j.twist (mainTwist_admissible j)) ellipticBettiNumber
    (fillingHomologyCoordinates D) n a b

end Wikipedia.HopfProblem.Elliptic.HigherHomology
