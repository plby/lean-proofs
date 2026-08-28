import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticCapProductSection
import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyTransportTorus

/-!
# The cap section's fibre in the source's ordered third-homology marking

The time-zero section fibre is the literal coordinate subtorus
`(u,w,δ) ↦ (0,u,w,δ)`.  Naturality of actual positive-loop triple products
identifies its positively oriented top class with the `uwδ` axis of the
original rank-four exterior-cube marking.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.EllipticCapProduct

open Elliptic Elliptic.HigherHomology PeriodTorusHigherHomology SingularMayerVietoris
open FirstHurewicz PeriodTorusHigherHomologyExterior PeriodTorusHigherHomologyPontryagin
open scoped Matrix

/-- The literal zero-head coordinate inclusion matrix. -/
def sectionFibreMatrix : Matrix (Fin 4) (Fin 3) ℤ := omitHeadMatrix (1 : FibreMatrix)

@[simp] theorem sectionFibreMatrix_basis (i : Fin 3) :
    sectionFibreMatrix *ᵥ Pi.single i 1 = Pi.single i.succ 1 := by
  fin_cases i <;> decide

/-- The genuine flat-to-circle homeomorphism carries the section fibre to the
actual zero-head torus matrix map. -/
theorem capSectionFibre_zero_flatCoordinates (j : Kind) :
    (flatTorusCircleHomeomorph : C(RealTorus₄, ProductTorus 4)).comp
      (capSectionFibre j 0) = torusMatrixMap sectionFibreMatrix := by
  apply ContinuousMap.ext
  intro y
  obtain ⟨k, rfl⟩ := coordinateProjection_surjective 3 y
  change flatTorusCircleHomeomorph (capSectionFibre j 0 (coordinateProjection 3 k)) = _
  rw [capSectionFibre_zero_coordinateProjection, flatTorusCircleHomeomorph_mkQ]
  rw [sectionFibreMatrix, torusMatrixMap_omitHeadMatrix, torusMatrixMap_one]
  funext i
  refine Fin.cases ?_ (fun k => ?_) i
  · change ((0 : ℝ) : MappingTorus.Circle) = 0
    simp only [AddCircle.coe_zero]
  · rfl

/-- The matrix inclusion takes each actual positive coordinate loop to its
literal successor-coordinate loop. -/
theorem sectionFibreMatrix_loopHomology (i : Fin 3) :
    singularHomologyMap (torusMatrixMap sectionFibreMatrix) 1
      (loopHomologyClass (coordinatePeriodLoop 3 (Pi.single i 1))) =
        loopHomologyClass (coordinatePeriodLoop 4 (Pi.single i.succ 1)) := by
  rw [singularHomologyMap_one, torusMatrixMap_coordinatePeriodHomology,
    sectionFibreMatrix_basis]

/-- The positive three-torus orientation maps to the literal `uwδ` exterior basis class. -/
theorem sectionFibreMatrix_topClass :
    singularHomologyMap (torusMatrixMap sectionFibreMatrix) 3
      (torusH3Coordinates.symm 1) = coordinateTorusH3ExteriorEquiv.symm (cubeBasis 3) := by
  rw [torusH3Coordinates_symm_one,
    tripleProduct_natural _ (torusMatrixMap_add sectionFibreMatrix),
    sectionFibreMatrix_loopHomology, sectionFibreMatrix_loopHomology,
    sectionFibreMatrix_loopHomology, cubeBasis_apply,
    coordinateTorusH3ExteriorEquiv_symm_ιMulti]
  have hi : LocalSystemMatrices.tripleIndices 3 = Fin.succ := by decide
  rw [hi]
  simp only [Function.comp_apply, latticeBasis, Pi.basisFun_apply]

/-- The actual cap section's positive fibre orientation is the source's fourth
ordered exterior-cube coordinate, with no sign change. -/
theorem capSectionFibre_zero_h3_one (j : Kind) :
    FlatTorus.singularH3Coordinates
      (singularHomologyMap (capSectionFibre j 0) 3 (torusH3Coordinates.symm 1)) =
        Pi.single (3 : Fin 4) 1 := by
  change cubeCoordinates
    (coordinateTorusH3ExteriorEquiv
      (singularHomologyMap (flatTorusCircleHomeomorph : C(RealTorus₄, ProductTorus 4)) 3
        (singularHomologyMap (capSectionFibre j 0) 3 (torusH3Coordinates.symm 1)))) = _
  rw [← LinearMap.comp_apply, ← singularHomologyMap_comp,
    capSectionFibre_zero_flatCoordinates, sectionFibreMatrix_topClass,
    LinearEquiv.apply_symm_apply]
  change cubeBasis.equivFun (cubeBasis 3) = _
  ext i
  simp [Pi.single_apply, eq_comm]

/-- Every actual third-homology fibre class has the exact `uwδ` coordinate. -/
theorem capSectionFibre_zero_h3 (j : Kind) (a : SingularHomology (ProductTorus 3) 3) :
    FlatTorus.singularH3Coordinates (singularHomologyMap (capSectionFibre j 0) 3 a) =
      Pi.single (3 : Fin 4) (torusH3Coordinates a) := by
  have ha : a = torusH3Coordinates a • torusH3Coordinates.symm 1 := by
    apply torusH3Coordinates.injective
    simp
  calc
    _ = FlatTorus.singularH3Coordinates (singularHomologyMap (capSectionFibre j 0) 3
        (torusH3Coordinates a • torusH3Coordinates.symm 1)) :=
      congrArg (fun b => FlatTorus.singularH3Coordinates
        (singularHomologyMap (capSectionFibre j 0) 3 b)) ha
    _ = torusH3Coordinates a • Pi.single (3 : Fin 4) 1 := by
      rw [map_zsmul, map_zsmul, capSectionFibre_zero_h3_one]
    _ = _ := by
      ext i
      by_cases hi : i = 3
      · subst i
        simp
      · simp [hi]

end Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.EllipticCapProduct
