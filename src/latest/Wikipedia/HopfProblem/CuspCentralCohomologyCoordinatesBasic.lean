import Wikipedia.HopfProblem.CuspCentralCohomologyEvaluation
import Wikipedia.HopfProblem.CuspCentralCohomologyCoordinatesDual
import Wikipedia.HopfProblem.CuspCentralHomologySpecializationKernelOneCoordinates

/-!
# Actual singular-cohomology coordinates on the original four-torus

The native cochain cohomology is first mapped by its proved canonical
evaluation equivalence, and only then expressed in the duals of the fixed
positive-loop and ordered-minor homology coordinates.  Naturality of the
actual evaluation pairing proves the transpose-matrix formulas for the
actual singular-cohomology pullbacks.
-/

noncomputable section

open scoped BigOperators Matrix ContinuousMap

namespace Wikipedia.HopfProblem.CuspCentralCohomology

open SingularMayerVietoris SingularCohomologyFree PeriodTorusHigherHomology
open CuspCentralHomology.SpecializationModel Elliptic.HigherHomology LocalSystemMatrices

/-- Coordinates on native cohomology from the actual evaluation map and
one specified, proved homology marking. -/
def coordinateTorusCohomologyCoordinates (n : ℕ) {k : ℕ}
    (e : SingularHomology (ProductTorus 4) n ≃ₗ[ℤ] (Fin k → ℤ)) :
    SingularCohomology (ProductTorus 4) n ≃ₗ[ℤ] (Fin k → ℤ) :=
  (coordinateTorusEvaluationEquiv n).trans (intDualCoordinatesOfEquiv e)

@[simp] theorem coordinateTorusCohomologyCoordinates_apply (n : ℕ) {k : ℕ}
    (e : SingularHomology (ProductTorus 4) n ≃ₗ[ℤ] (Fin k → ℤ))
    (a : SingularCohomology (ProductTorus 4) n) :
    coordinateTorusCohomologyCoordinates n e a =
      intDualCoordinatesOfEquiv e (singularEvaluation (ProductTorus 4) n a) := rfl

/-- Each coordinate is evaluation on the original actual homology basis class. -/
theorem coordinateTorusCohomologyCoordinates_apply_coordinate (n : ℕ) {k : ℕ}
    (e : SingularHomology (ProductTorus 4) n ≃ₗ[ℤ] (Fin k → ℤ))
    (a : SingularCohomology (ProductTorus 4) n) (i : Fin k) :
    coordinateTorusCohomologyCoordinates n e a i =
      singularEvaluation (ProductTorus 4) n a (e.symm (Pi.single i 1)) := by
  rw [coordinateTorusCohomologyCoordinates_apply, intDualCoordinatesOfEquiv_apply]

/-- Evaluation on arbitrary actual homology classes is the integral coordinate pairing. -/
theorem coordinateTorusCohomologyCoordinates_evaluate (n : ℕ) {k : ℕ}
    (e : SingularHomology (ProductTorus 4) n ≃ₗ[ℤ] (Fin k → ℤ))
    (a : SingularCohomology (ProductTorus 4) n) (b : SingularHomology (ProductTorus 4) n) :
    singularEvaluation (ProductTorus 4) n a b =
      ∑ i, coordinateTorusCohomologyCoordinates n e a i * e b i := by
  rw [coordinateTorusCohomologyCoordinates_apply]
  exact intDualCoordinatesOfEquiv_evaluate e (singularEvaluation (ProductTorus 4) n a) b

theorem coordinateTorusCohomologyCoordinates_symm_evaluate (n : ℕ) {k : ℕ}
    (e : SingularHomology (ProductTorus 4) n ≃ₗ[ℤ] (Fin k → ℤ))
    (v : Fin k → ℤ) (b : SingularHomology (ProductTorus 4) n) :
    singularEvaluation (ProductTorus 4) n ((coordinateTorusCohomologyCoordinates n e).symm v) b =
      ∑ i, v i * e b i := by
  rw [coordinateTorusCohomologyCoordinates_evaluate, LinearEquiv.apply_symm_apply]

/-- The actual native pullback has the transpose of a proved actual homology matrix. -/
theorem coordinateTorusCohomologyCoordinates_pullback_matrix (n : ℕ) {k : ℕ}
    (e : SingularHomology (ProductTorus 4) n ≃ₗ[ℤ] (Fin k → ℤ))
    (f : C(ProductTorus 4, ProductTorus 4)) (A : Matrix (Fin k) (Fin k) ℤ)
    (hA : ∀ b, e (singularHomologyMap f n b) = A *ᵥ e b)
    (a : SingularCohomology (ProductTorus 4) n) :
    coordinateTorusCohomologyCoordinates n e (singularCohomologyPullback f n a) =
      A.transpose *ᵥ coordinateTorusCohomologyCoordinates n e a := by
  rw [coordinateTorusCohomologyCoordinates_apply, coordinateTorusCohomologyCoordinates_apply]
  have hn : singularEvaluation (ProductTorus 4) n (singularCohomologyPullback f n a) =
      (singularEvaluation (ProductTorus 4) n a).comp (singularHomologyMap f n) := by
    apply LinearMap.ext
    exact singularEvaluation_naturality f n a
  rw [hn]
  exact intDualCoordinatesOfEquiv_comp_matrix e (singularHomologyMap f n) A hA
    (singularEvaluation (ProductTorus 4) n a)

/-- Native first-cohomology coordinates dual to the actual positive coordinate loops. -/
def coordinateTorusH1CohomologyCoordinates :
    SingularCohomology (ProductTorus 4) 1 ≃ₗ[ℤ] (Fin 4 → ℤ) :=
  coordinateTorusCohomologyCoordinates 1 coordinateTorusH1Coordinates

/-- Native second-cohomology coordinates in the ordered dual-minor basis
`γu, γw, γδ, uw, uδ, wδ`. -/
def coordinateTorusH2CohomologyCoordinates :
    SingularCohomology (ProductTorus 4) 2 ≃ₗ[ℤ] (Fin 6 → ℤ) :=
  coordinateTorusCohomologyCoordinates 2 coordinateTorusH2Coordinates

/-- Native third-cohomology coordinates in the ordered dual-minor basis
`γuw, γuδ, γwδ, uwδ`. -/
def coordinateTorusH3CohomologyCoordinates :
    SingularCohomology (ProductTorus 4) 3 ≃ₗ[ℤ] (Fin 4 → ℤ) :=
  coordinateTorusCohomologyCoordinates 3 coordinateTorusH3Coordinates

/-- The actual first-cohomology pullback has the transpose integer matrix. -/
theorem coordinateTorusH1CohomologyCoordinates_pullback (A : LatticeMatrix)
    (a : SingularCohomology (ProductTorus 4) 1) :
    coordinateTorusH1CohomologyCoordinates (singularCohomologyPullback (torusMatrixMap A) 1 a) =
      A.transpose *ᵥ coordinateTorusH1CohomologyCoordinates a :=
  coordinateTorusCohomologyCoordinates_pullback_matrix 1 coordinateTorusH1Coordinates
    (torusMatrixMap A) A (coordinateTorusH1Coordinates_matrix A) a

/-- The actual second-cohomology pullback has the transpose ordered square-minor matrix. -/
theorem coordinateTorusH2CohomologyCoordinates_pullback (A : LatticeMatrix)
    (a : SingularCohomology (ProductTorus 4) 2) :
    coordinateTorusH2CohomologyCoordinates (singularCohomologyPullback (torusMatrixMap A) 2 a) =
      (exteriorSquare A).transpose *ᵥ coordinateTorusH2CohomologyCoordinates a :=
  coordinateTorusCohomologyCoordinates_pullback_matrix 2 coordinateTorusH2Coordinates
    (torusMatrixMap A) (exteriorSquare A) (coordinateTorusH2Coordinates_matrix A) a

/-- The actual third-cohomology pullback has the transpose ordered cube-minor matrix. -/
theorem coordinateTorusH3CohomologyCoordinates_pullback (A : LatticeMatrix)
    (a : SingularCohomology (ProductTorus 4) 3) :
    coordinateTorusH3CohomologyCoordinates (singularCohomologyPullback (torusMatrixMap A) 3 a) =
      (exteriorCube A).transpose *ᵥ coordinateTorusH3CohomologyCoordinates a :=
  coordinateTorusCohomologyCoordinates_pullback_matrix 3 coordinateTorusH3Coordinates
    (torusMatrixMap A) (exteriorCube A) (coordinateTorusH3Coordinates_matrix A) a

end Wikipedia.HopfProblem.CuspCentralCohomology
