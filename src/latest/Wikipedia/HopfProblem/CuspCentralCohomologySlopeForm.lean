import Wikipedia.HopfProblem.CuspCentralCohomologyCoordinatesGenerators

/-!
# The native degree-two slope classes in cusp specialization

For an integral character `ν = (a,b)`, this file constructs the actual
singular-cohomology class with coefficients
`b² γδ - a² uw + ab (γw-uδ)`.  Its evaluations and invariance concern the
actual singular cochain complex and its actual pullback.  Identification
with a particular geometric double-curve dual is a separate theorem;
none is assumed in this construction.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.CuspCentralCohomology

open SingularMayerVietoris SingularCohomologyFree PeriodTorusHigherHomology

/-- The source's ordered integral coefficients for a character `(a,b)`. -/
def slopeCoefficients (a b : ℤ) : Fin 6 → ℤ :=
  ![0, a * b, b ^ 2, -(a ^ 2), -(a * b), 0]

/-- A class of the actual singular cochain cohomology, defined through
the proved evaluation-dual period marking. -/
def slopeClass (a b : ℤ) : SingularCohomology (ProductTorus 4) 2 :=
  coordinateTorusH2CohomologyCoordinates.symm (slopeCoefficients a b)

@[simp] theorem slopeClass_coordinates (a b : ℤ) :
    coordinateTorusH2CohomologyCoordinates (slopeClass a b) = slopeCoefficients a b :=
  coordinateTorusH2CohomologyCoordinates.apply_symm_apply _

/-- The displayed polynomial is an equality of actual native classes. -/
theorem slopeClass_eq_linearCombination (a b : ℤ) :
    slopeClass a b =
      (b ^ 2) • coordinateTorusH2DualClass 2 -
        (a ^ 2) • coordinateTorusH2DualClass 3 +
        (a * b) • (coordinateTorusH2DualClass 1 - coordinateTorusH2DualClass 4) := by
  apply coordinateTorusH2CohomologyCoordinates.injective
  rw [slopeClass_coordinates]
  simp only [map_add, map_sub]
  funext i
  fin_cases i <;> simp [slopeCoefficients]

/-- Exact evaluation on every actual degree-two homology class. -/
theorem slopeClass_evaluate (a b : ℤ) (z : SingularHomology (ProductTorus 4) 2) :
    singularEvaluation (ProductTorus 4) 2 (slopeClass a b) z =
      (b ^ 2) * coordinateTorusH2Coordinates z 2 -
        (a ^ 2) * coordinateTorusH2Coordinates z 3 +
        (a * b) * (coordinateTorusH2Coordinates z 1 - coordinateTorusH2Coordinates z 4) := by
  change singularEvaluation (ProductTorus 4) 2
    ((coordinateTorusCohomologyCoordinates 2 coordinateTorusH2Coordinates).symm
      (slopeCoefficients a b)) z = _
  rw [coordinateTorusCohomologyCoordinates_symm_evaluate]
  simp [slopeCoefficients, Fin.sum_univ_succ]
  ring

/-- These coefficients satisfy the actual integral monodromy fixed
condition, including the relation between the two mixed positions. -/
theorem slopeClass_pullback_fixed (a b : ℤ) :
    singularCohomologyPullback (torusMatrixMap M₀) 2 (slopeClass a b) = slopeClass a b := by
  rw [coordinateTorusH2_pullback_fixed_iff, slopeClass_coordinates]
  simp [slopeCoefficients]

/-- Reversing the character's orientation leaves its quadratic class unchanged. -/
@[simp] theorem slopeClass_neg (a b : ℤ) : slopeClass (-a) (-b) = slopeClass a b := by
  apply coordinateTorusH2CohomologyCoordinates.injective
  rw [slopeClass_coordinates, slopeClass_coordinates]
  funext i
  fin_cases i <;> simp [slopeCoefficients]

/-- The construction is quadratic in the integral character. -/
theorem slopeClass_mul (m a b : ℤ) :
    slopeClass (m * a) (m * b) = (m ^ 2) • slopeClass a b := by
  apply coordinateTorusH2CohomologyCoordinates.injective
  rw [map_zsmul, slopeClass_coordinates, slopeClass_coordinates]
  funext i
  fin_cases i <;> simp [slopeCoefficients, mul_pow] <;> ring

/-- The four mixed positions of the original period homology coordinates. -/
def mixedPeriodCoordinates (β v : Fin 2 → ℤ) : Fin 6 → ℤ :=
  ![0, β 0 * v 0, β 0 * v 1, β 1 * v 0, β 1 * v 1, 0]

/-- In actual homology coordinates, the mixed evaluation is the
negative product `-ν(B₀β)ν(v)`; this fixes the sign used when the separate
geometric cylinder calculation identifies a curve dual. -/
theorem slopeClass_evaluate_mixedCoordinates (a b : ℤ) (β v : Fin 2 → ℤ) :
    singularEvaluation (ProductTorus 4) 2 (slopeClass a b)
        (coordinateTorusH2Coordinates.symm (mixedPeriodCoordinates β v)) =
      (b * β 0 - a * β 1) * (a * v 0 + b * v 1) := by
  rw [slopeClass_evaluate, LinearEquiv.apply_symm_apply]
  simp [mixedPeriodCoordinates]
  ring

/-- The preceding sign is expressed using the original integral shear
matrix, not a newly chosen identification of the two period lattices. -/
theorem slopeClass_evaluate_mixedCoordinates_B₀ (a b : ℤ) (β v : Fin 2 → ℤ) :
    singularEvaluation (ProductTorus 4) 2 (slopeClass a b)
        (coordinateTorusH2Coordinates.symm (mixedPeriodCoordinates β v)) =
      -(a * (B₀ *ᵥ β) 0 + b * (B₀ *ᵥ β) 1) * (a * v 0 + b * v 1) := by
  rw [slopeClass_evaluate_mixedCoordinates]
  conv_rhs => simp [B₀, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

end Wikipedia.HopfProblem.CuspCentralCohomology
