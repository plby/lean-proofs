import Wikipedia.HopfProblem.CuspCentralHomologySpecializationCoinvariantsCoordinates
import Wikipedia.HopfProblem.CuspCentralHomologySpecializationCoinvariantsTransport
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyExterior

/-!
# Integral coinvariants of the actual exterior powers of cusp monodromy

The ordered-minor coordinates intertwine the actual `exteriorPower.map` with
the integral matrices. Transporting the explicit quotient coordinates gives
free quotients of ranks four and two in exterior degrees two and three.
These are algebraic results about the single lattice action `M₀`.
-/

noncomputable section

namespace Wikipedia.HopfProblem.CuspCentralHomology.SpecializationCoinvariants

open PeriodTorusHigherHomologyExterior
open scoped Matrix

/-- The actual exterior-square monodromy minus identity. -/
def exteriorSquareDifference : latticeExterior 2 →ₗ[ℤ] latticeExterior 2 :=
  exteriorPower.map 2 M₀.mulVecLin - LinearMap.id

/-- The actual exterior-cube monodromy minus identity. -/
def exteriorCubeDifference : latticeExterior 3 →ₗ[ℤ] latticeExterior 3 :=
  exteriorPower.map 3 M₀.mulVecLin - LinearMap.id

theorem squareCoordinates_difference (x : latticeExterior 2) :
    squareCoordinates (exteriorSquareDifference x) =
      squareDifference (squareCoordinates x) := by
  change squareCoordinates (exteriorMap 2 M₀ x - x) = _
  rw [map_sub, squareCoordinates_M₀]
  simp only [squareDifference, Matrix.mulVecLin_apply,
    Matrix.sub_mulVec, Matrix.one_mulVec]

theorem cubeCoordinates_difference (x : latticeExterior 3) :
    cubeCoordinates (exteriorCubeDifference x) =
      cubeDifference (cubeCoordinates x) := by
  change cubeCoordinates (exteriorMap 3 M₀ x - x) = _
  rw [map_sub, cubeCoordinates_M₀]
  simp only [cubeDifference, Matrix.mulVecLin_apply,
    Matrix.sub_mulVec, Matrix.one_mulVec]

/-- An exact coordinate description of the exterior-square image. -/
theorem exteriorSquareDifference_range_iff (x : latticeExterior 2) :
    x ∈ LinearMap.range exteriorSquareDifference ↔
      squareCoordinates x 0 = 0 ∧ squareCoordinates x 2 = 0 ∧
        squareCoordinates x 3 = 0 ∧ squareCoordinates x 4 = squareCoordinates x 1 := by
  rw [mem_range_iff_of_intertwines squareCoordinates exteriorSquareDifference
    squareDifference squareCoordinates_difference, squareDifference_range_iff]

/-- An exact coordinate description of the exterior-cube image. -/
theorem exteriorCubeDifference_range_iff (x : latticeExterior 3) :
    x ∈ LinearMap.range exteriorCubeDifference ↔
      cubeCoordinates x 0 = 0 ∧ cubeCoordinates x 1 = 0 := by
  rw [mem_range_iff_of_intertwines cubeCoordinates exteriorCubeDifference
    cubeDifference cubeCoordinates_difference, cubeDifference_range_iff]

theorem exteriorSquareDifference_eq_zero_iff (x : latticeExterior 2) :
    exteriorSquareDifference x = 0 ↔
      squareCoordinates x 0 = 0 ∧ squareCoordinates x 1 + squareCoordinates x 4 = 0 := by
  rw [← squareCoordinates.map_eq_zero_iff, squareCoordinates_difference,
    squareDifference_eq_zero_iff]

theorem exteriorCubeDifference_eq_zero_iff (x : latticeExterior 3) :
    exteriorCubeDifference x = 0 ↔
      cubeCoordinates x 0 = 0 ∧ cubeCoordinates x 1 = 0 := by
  rw [← cubeCoordinates.map_eq_zero_iff, cubeCoordinates_difference,
    cubeDifference_eq_zero_iff]

/-- Four explicit free integral coordinates for the actual square coinvariants. -/
def exteriorSquareCoinvariantEquiv :
    (latticeExterior 2 ⧸ LinearMap.range exteriorSquareDifference) ≃ₗ[ℤ] (Fin 4 → ℤ) :=
  (quotientRangeEquiv squareCoordinates exteriorSquareDifference squareDifference
    squareCoordinates_difference).trans squareCoinvariantEquiv

/-- Two explicit free integral coordinates for the actual cube coinvariants. -/
def exteriorCubeCoinvariantEquiv :
    (latticeExterior 3 ⧸ LinearMap.range exteriorCubeDifference) ≃ₗ[ℤ] (Fin 2 → ℤ) :=
  (quotientRangeEquiv cubeCoordinates exteriorCubeDifference cubeDifference
    cubeCoordinates_difference).trans cubeCoinvariantEquiv

@[simp] theorem exteriorSquareCoinvariantEquiv_mk (x : latticeExterior 2) :
    exteriorSquareCoinvariantEquiv (Submodule.Quotient.mk x) =
      squareProjection (squareCoordinates x) := by
  simp [exteriorSquareCoinvariantEquiv]

@[simp] theorem exteriorCubeCoinvariantEquiv_mk (x : latticeExterior 3) :
    exteriorCubeCoinvariantEquiv (Submodule.Quotient.mk x) =
      cubeProjection (cubeCoordinates x) := by
  simp [exteriorCubeCoinvariantEquiv]

@[simp] theorem exteriorSquareCoinvariantEquiv_symm_apply (z : Fin 4 → ℤ) :
    exteriorSquareCoinvariantEquiv.symm z =
      Submodule.Quotient.mk (squareCoordinates.symm (squareSection z)) := by
  apply exteriorSquareCoinvariantEquiv.injective
  rw [LinearEquiv.apply_symm_apply, exteriorSquareCoinvariantEquiv_mk,
    LinearEquiv.apply_symm_apply, squareProjection_section]

@[simp] theorem exteriorCubeCoinvariantEquiv_symm_apply (z : Fin 2 → ℤ) :
    exteriorCubeCoinvariantEquiv.symm z =
      Submodule.Quotient.mk (cubeCoordinates.symm (cubeSection z)) := by
  apply exteriorCubeCoinvariantEquiv.injective
  rw [LinearEquiv.apply_symm_apply, exteriorCubeCoinvariantEquiv_mk,
    LinearEquiv.apply_symm_apply, cubeProjection_section]

instance exteriorSquareCoinvariant_free :
    Module.Free ℤ (latticeExterior 2 ⧸ LinearMap.range exteriorSquareDifference) :=
  Module.Free.of_equiv exteriorSquareCoinvariantEquiv.symm

instance exteriorCubeCoinvariant_free :
    Module.Free ℤ (latticeExterior 3 ⧸ LinearMap.range exteriorCubeDifference) :=
  Module.Free.of_equiv exteriorCubeCoinvariantEquiv.symm

instance exteriorSquareCoinvariant_finite :
    Module.Finite ℤ (latticeExterior 2 ⧸ LinearMap.range exteriorSquareDifference) :=
  Module.Finite.of_surjective exteriorSquareCoinvariantEquiv.symm.toLinearMap
    exteriorSquareCoinvariantEquiv.symm.surjective

instance exteriorCubeCoinvariant_finite :
    Module.Finite ℤ (latticeExterior 3 ⧸ LinearMap.range exteriorCubeDifference) :=
  Module.Finite.of_surjective exteriorCubeCoinvariantEquiv.symm.toLinearMap
    exteriorCubeCoinvariantEquiv.symm.surjective

theorem exteriorSquareCoinvariant_finrank :
    Module.finrank ℤ (latticeExterior 2 ⧸ LinearMap.range exteriorSquareDifference) = 4 := by
  rw [exteriorSquareCoinvariantEquiv.finrank_eq, Module.finrank_fin_fun]

theorem exteriorCubeCoinvariant_finrank :
    Module.finrank ℤ (latticeExterior 3 ⧸ LinearMap.range exteriorCubeDifference) = 2 := by
  rw [exteriorCubeCoinvariantEquiv.finrank_eq, Module.finrank_fin_fun]

end Wikipedia.HopfProblem.CuspCentralHomology.SpecializationCoinvariants
