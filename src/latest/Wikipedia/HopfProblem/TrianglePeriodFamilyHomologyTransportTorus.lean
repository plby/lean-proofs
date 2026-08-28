import Wikipedia.HopfProblem.PeriodTorusHigherHomologyMarkingProductTorus
import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyTransportCoordinates

/-!
# Canonical higher-homology markings of the actual flat period torus

The actual flat-to-circle homeomorphism transports the proved canonical
exterior-square and exterior-cube markings of the four-circle torus.
The triangle action is computed from its actual coordinate-map square,
and the ordered integral coordinate formulas are its genuine minors.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.FlatTorus

open Elliptic SpecialPeriods SingularMayerVietoris PeriodTorusHigherHomology
open PeriodTorusHigherHomologyExterior

/-- The canonical exterior-square marking of the actual flat torus's second singular homology. -/
def singularH2Equiv : SingularHomology RealTorus₄ 2 ≃ₗ[ℤ] latticeExterior 2 :=
  (homeomorphHomologyEquiv flatTorusCircleHomeomorph 2).trans coordinateTorusH2ExteriorEquiv

/-- The canonical exterior-cube marking of the actual flat torus's third singular homology. -/
def singularH3Equiv : SingularHomology RealTorus₄ 3 ≃ₗ[ℤ] latticeExterior 3 :=
  (homeomorphHomologyEquiv flatTorusCircleHomeomorph 3).trans coordinateTorusH3ExteriorEquiv

@[simp] theorem singularH2Equiv_apply (a : SingularHomology RealTorus₄ 2) :
    singularH2Equiv a = coordinateTorusH2ExteriorEquiv
      (singularHomologyMap (flatTorusCircleHomeomorph : C(RealTorus₄, ProductTorus 4)) 2 a) := rfl

@[simp] theorem singularH3Equiv_apply (a : SingularHomology RealTorus₄ 3) :
    singularH3Equiv a = coordinateTorusH3ExteriorEquiv
      (singularHomologyMap (flatTorusCircleHomeomorph : C(RealTorus₄, ProductTorus 4)) 3 a) := rfl

@[simp] theorem singularH2Equiv_symm_apply (v : latticeExterior 2) :
    singularH2Equiv.symm v =
      singularHomologyMap (flatTorusCircleHomeomorph.symm : C(ProductTorus 4, RealTorus₄)) 2
        (coordinateTorusH2ExteriorEquiv.symm v) := rfl

@[simp] theorem singularH3Equiv_symm_apply (v : latticeExterior 3) :
    singularH3Equiv.symm v =
      singularHomologyMap (flatTorusCircleHomeomorph.symm : C(ProductTorus 4, RealTorus₄)) 3
        (coordinateTorusH3ExteriorEquiv.symm v) := rfl

/-- Actual second singular homology in the ordered six-minor coordinates. -/
def singularH2Coordinates : SingularHomology RealTorus₄ 2 ≃ₗ[ℤ] (Fin 6 → ℤ) :=
  singularH2Equiv.trans squareCoordinates

/-- Actual third singular homology in the ordered four-minor coordinates. -/
def singularH3Coordinates : SingularHomology RealTorus₄ 3 ≃ₗ[ℤ] (Fin 4 → ℤ) :=
  singularH3Equiv.trans cubeCoordinates

@[simp] theorem singularH2Coordinates_apply (a : SingularHomology RealTorus₄ 2) :
    singularH2Coordinates a = squareCoordinates (singularH2Equiv a) := rfl

@[simp] theorem singularH3Coordinates_apply (a : SingularHomology RealTorus₄ 3) :
    singularH3Coordinates a = cubeCoordinates (singularH3Equiv a) := rfl

/-- The actual geometric coordinate square induces a commuting square in every homology degree. -/
theorem flatTorusCircleHomology_triangle (g : TriangleGroup) (n : ℕ) :
    (singularHomologyMap (flatTorusCircleHomeomorph : C(RealTorus₄, ProductTorus 4)) n).comp
        (singularHomologyMap (triangleTorusHomeomorph g : C(RealTorus₄, RealTorus₄)) n) =
      (singularHomologyMap (torusMatrixMap (triangleDualRepresentation g : LatticeMatrix)) n).comp
        (singularHomologyMap (flatTorusCircleHomeomorph : C(RealTorus₄, ProductTorus 4)) n) := by
  rw [← singularHomologyMap_comp, ← singularHomologyMap_comp,
    flatTorusCircleHomeomorph_triangle_comp]

theorem flatTorusCircleHomology_triangle_apply (g : TriangleGroup) (n : ℕ)
    (a : SingularHomology RealTorus₄ n) :
    singularHomologyMap (flatTorusCircleHomeomorph : C(RealTorus₄, ProductTorus 4)) n
        (singularHomologyMap (triangleTorusHomeomorph g : C(RealTorus₄, RealTorus₄)) n a) =
      singularHomologyMap (torusMatrixMap (triangleDualRepresentation g : LatticeMatrix)) n
        (singularHomologyMap (flatTorusCircleHomeomorph : C(RealTorus₄, ProductTorus 4)) n a) :=
  LinearMap.congr_fun (flatTorusCircleHomology_triangle g n) a

/-- Every actual triangle-group homeomorphism acts on marked second homology
by the exterior square. -/
theorem singularH2Equiv_inducedHomology_triangle (g : TriangleGroup)
    (a : SingularHomology RealTorus₄ 2) :
    singularH2Equiv
        (singularHomologyMap (triangleTorusHomeomorph g : C(RealTorus₄, RealTorus₄)) 2 a) =
      exteriorPower.map 2 (triangleDualRepresentation g : LatticeMatrix).mulVecLin
        (singularH2Equiv a) := by
  change coordinateTorusH2ExteriorEquiv
      (singularHomologyMap (flatTorusCircleHomeomorph : C(RealTorus₄, ProductTorus 4)) 2
        (singularHomologyMap (triangleTorusHomeomorph g : C(RealTorus₄, RealTorus₄)) 2 a)) =
    exteriorPower.map 2 (triangleDualRepresentation g : LatticeMatrix).mulVecLin
      (coordinateTorusH2ExteriorEquiv
        (singularHomologyMap (flatTorusCircleHomeomorph : C(RealTorus₄, ProductTorus 4)) 2 a))
  rw [flatTorusCircleHomology_triangle_apply, coordinateTorusH2ExteriorEquiv_matrix]

/-- Every actual triangle-group homeomorphism acts on marked third homology by the exterior cube. -/
theorem singularH3Equiv_inducedHomology_triangle (g : TriangleGroup)
    (a : SingularHomology RealTorus₄ 3) :
    singularH3Equiv
        (singularHomologyMap (triangleTorusHomeomorph g : C(RealTorus₄, RealTorus₄)) 3 a) =
      exteriorPower.map 3 (triangleDualRepresentation g : LatticeMatrix).mulVecLin
        (singularH3Equiv a) := by
  change coordinateTorusH3ExteriorEquiv
      (singularHomologyMap (flatTorusCircleHomeomorph : C(RealTorus₄, ProductTorus 4)) 3
        (singularHomologyMap (triangleTorusHomeomorph g : C(RealTorus₄, RealTorus₄)) 3 a)) =
    exteriorPower.map 3 (triangleDualRepresentation g : LatticeMatrix).mulVecLin
      (coordinateTorusH3ExteriorEquiv
        (singularHomologyMap (flatTorusCircleHomeomorph : C(RealTorus₄, ProductTorus 4)) 3 a))
  rw [flatTorusCircleHomology_triangle_apply, coordinateTorusH3ExteriorEquiv_matrix]

/-- Conjugation by the canonical second-homology marking gives the actual exterior-square map. -/
theorem singularH2_triangle_conjugate (g : TriangleGroup) :
    singularH2Equiv.toLinearMap.comp
      ((singularHomologyMap (triangleTorusHomeomorph g : C(RealTorus₄, RealTorus₄)) 2).comp
        singularH2Equiv.symm.toLinearMap) =
      exteriorPower.map 2 (triangleDualRepresentation g : LatticeMatrix).mulVecLin := by
  apply LinearMap.ext
  intro v
  change singularH2Equiv
      (singularHomologyMap (triangleTorusHomeomorph g : C(RealTorus₄, RealTorus₄)) 2
        (singularH2Equiv.symm v)) = _
  rw [singularH2Equiv_inducedHomology_triangle, LinearEquiv.apply_symm_apply]

/-- Conjugation by the canonical third-homology marking gives the actual exterior-cube map. -/
theorem singularH3_triangle_conjugate (g : TriangleGroup) :
    singularH3Equiv.toLinearMap.comp
      ((singularHomologyMap (triangleTorusHomeomorph g : C(RealTorus₄, RealTorus₄)) 3).comp
        singularH3Equiv.symm.toLinearMap) =
      exteriorPower.map 3 (triangleDualRepresentation g : LatticeMatrix).mulVecLin := by
  apply LinearMap.ext
  intro v
  change singularH3Equiv
      (singularHomologyMap (triangleTorusHomeomorph g : C(RealTorus₄, RealTorus₄)) 3
        (singularH3Equiv.symm v)) = _
  rw [singularH3Equiv_inducedHomology_triangle, LinearEquiv.apply_symm_apply]

/-- The actual second-homology action in ordered coordinates is the matrix of two-by-two minors. -/
theorem singularH2Coordinates_inducedHomology_triangle (g : TriangleGroup)
    (a : SingularHomology RealTorus₄ 2) :
    singularH2Coordinates
        (singularHomologyMap (triangleTorusHomeomorph g : C(RealTorus₄, RealTorus₄)) 2 a) =
      LocalSystemMatrices.exteriorSquare (triangleDualRepresentation g : LatticeMatrix) *ᵥ
        singularH2Coordinates a := by
  rw [singularH2Coordinates_apply, singularH2Equiv_inducedHomology_triangle]
  exact squareCoordinates_map (triangleDualRepresentation g : LatticeMatrix) (singularH2Equiv a)

/-- The actual third-homology action in ordered coordinates is the matrix
of three-by-three minors. -/
theorem singularH3Coordinates_inducedHomology_triangle (g : TriangleGroup)
    (a : SingularHomology RealTorus₄ 3) :
    singularH3Coordinates
        (singularHomologyMap (triangleTorusHomeomorph g : C(RealTorus₄, RealTorus₄)) 3 a) =
      LocalSystemMatrices.exteriorCube (triangleDualRepresentation g : LatticeMatrix) *ᵥ
        singularH3Coordinates a := by
  rw [singularH3Coordinates_apply, singularH3Equiv_inducedHomology_triangle]
  exact cubeCoordinates_map (triangleDualRepresentation g : LatticeMatrix) (singularH3Equiv a)

theorem singularH2Coordinates_triangle_conjugate (g : TriangleGroup) :
    singularH2Coordinates.toLinearMap.comp
      ((singularHomologyMap (triangleTorusHomeomorph g : C(RealTorus₄, RealTorus₄)) 2).comp
        singularH2Coordinates.symm.toLinearMap) =
      (LocalSystemMatrices.exteriorSquare
        (triangleDualRepresentation g : LatticeMatrix)).mulVecLin := by
  apply LinearMap.ext
  intro v
  change singularH2Coordinates
      (singularHomologyMap (triangleTorusHomeomorph g : C(RealTorus₄, RealTorus₄)) 2
        (singularH2Coordinates.symm v)) = _
  rw [singularH2Coordinates_inducedHomology_triangle, LinearEquiv.apply_symm_apply]
  rfl

theorem singularH3Coordinates_triangle_conjugate (g : TriangleGroup) :
    singularH3Coordinates.toLinearMap.comp
      ((singularHomologyMap (triangleTorusHomeomorph g : C(RealTorus₄, RealTorus₄)) 3).comp
        singularH3Coordinates.symm.toLinearMap) =
      (LocalSystemMatrices.exteriorCube
        (triangleDualRepresentation g : LatticeMatrix)).mulVecLin := by
  apply LinearMap.ext
  intro v
  change singularH3Coordinates
      (singularHomologyMap (triangleTorusHomeomorph g : C(RealTorus₄, RealTorus₄)) 3
        (singularH3Coordinates.symm v)) = _
  rw [singularH3Coordinates_inducedHomology_triangle, LinearEquiv.apply_symm_apply]
  rfl

end Wikipedia.HopfProblem.TrianglePeriodFamily.FlatTorus
