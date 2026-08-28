import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticCapKernelWangSplitClasses
import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyTransportCoordinates
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyTorusProductDecomposition

/-!
# Original degree-one coordinates of the elliptic split classes

The inverse splitting is the original integral twist-basis map after
unsplitting the circle coordinates. Its action on the actual positive
coordinate loops gives the original flat-torus marking of both summands.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.EllipticCapKernelWang

open Elliptic Elliptic.HigherHomology FirstHurewicz SingularMayerVietoris
open PeriodTorusHigherHomology CircleTopology

/-- In original circle coordinates, inverse splitting is the literal twist-basis map. -/
theorem splitFlat_inverse_circle_comp (j : Kind) :
    (flatTorusCircleHomeomorph : C(RealTorus₄, ProductTorus 4)).comp
        ((splitFlatTorusHomeomorph j).symm : C(Circle × ProductTorus 3, RealTorus₄)) =
      (torusMatrixMap (twistBasisMatrix j)).comp
        ((productTorusSuccHomeomorph 3).symm :
          C(Circle × ProductTorus 3, ProductTorus 4)) := by
  apply ContinuousMap.ext
  intro x
  change flatTorusCircleHomeomorph
      (flatTorusCircleHomeomorph.symm
        (torusMatrixMap (twistBasisMatrix j) ((productTorusSuccHomeomorph 3).symm x))) = _
  exact flatTorusCircleHomeomorph.apply_symm_apply _

/-- The same original coordinate comparison on actual homology in every degree. -/
theorem splitFlat_inverse_circle_homology (j : Kind) (n : ℕ)
    (a : SingularHomology (Circle × ProductTorus 3) n) :
    singularHomologyMap (flatTorusCircleHomeomorph : C(RealTorus₄, ProductTorus 4)) n
        (singularHomologyMap ((splitFlatTorusHomeomorph j).symm :
          C(Circle × ProductTorus 3, RealTorus₄)) n a) =
      singularHomologyMap (torusMatrixMap (twistBasisMatrix j)) n
        (singularHomologyMap ((productTorusSuccHomeomorph 3).symm :
          C(Circle × ProductTorus 3, ProductTorus 4)) n a) := by
  rw [← LinearMap.comp_apply, ← singularHomologyMap_comp,
    splitFlat_inverse_circle_comp, singularHomologyMap_comp, LinearMap.comp_apply]

/-- The fibre section becomes the actual positive vector loop with first coordinate zero. -/
theorem splitOne_unsplit_fibre (v : FibreLattice) :
    singularHomologyMap ((productTorusSuccHomeomorph 3).symm :
        C(Circle × ProductTorus 3, ProductTorus 4)) 1
      (circleSectionHomology (ProductTorus 3) 1 (torusH1Equiv.symm v)) =
      loopHomologyClass (coordinatePeriodLoop 4 (Fin.cons 0 v)) := by
  rw [torusH1Equiv_symm_apply_loop, circleSectionHomology,
    ← LinearMap.comp_apply, ← singularHomologyMap_comp]
  exact torusTailMap_coordinatePeriodHomology 3 v

/-- Crossing the positive circle with the origin is its literal coordinate insertion. -/
theorem splitOne_unsplit_circle :
    singularHomologyMap ((productTorusSuccHomeomorph 3).symm :
        C(Circle × ProductTorus 3, ProductTorus 4)) 1
      (positiveCircleCross (ProductTorus 3) 0 (pointClass (0 : ProductTorus 3))) =
      loopHomologyClass (coordinatePeriodLoop 4 (Pi.single 0 1)) := by
  rw [positiveCircleCross, crossProductHomology_pointClass_right]
  have hmap : ((productTorusSuccHomeomorph 3).symm :
        C(Circle × ProductTorus 3, ProductTorus 4)).comp
      (crossInsertRight (0 : ProductTorus 3)) = torusHeadCircleMap 3 := by
    apply ContinuousMap.ext
    intro z
    rw [torusHeadCircleMap_apply]
    rfl
  rw [← LinearMap.comp_apply, ← singularHomologyMap_comp, hmap]
  exact torusHeadCircleMap_positiveHomology 3

private theorem splitOne_originalCoordinates
    (a : SingularHomology RealTorus₄ 1) (v : Lattice)
    (h : singularHomologyMap (flatTorusCircleHomeomorph :
        C(RealTorus₄, ProductTorus 4)) 1 a =
      loopHomologyClass (coordinatePeriodLoop 4 v)) :
    FlatTorus.singularH1Equiv a = v := by
  apply FlatTorus.singularH1Equiv.symm.injective
  rw [LinearEquiv.symm_apply_apply]
  apply (homeomorphHomologyEquiv flatTorusCircleHomeomorph 1).injective
  exact h.trans (FlatTorus.inducedHomology_singularH1Equiv_symm_circle v).symm

/-- The positive `w`-loop of the split fibre is the third original period loop. -/
theorem splitFibreClassOne_coordinates (j : Kind) :
    FlatTorus.singularH1Equiv (splitFibreClassOne j) = ![0, 0, 1, 0] := by
  apply splitOne_originalCoordinates
  rw [splitFibreClassOne, splitFlat_inverse_circle_homology, splitFibreInputOne,
    splitOne_unsplit_fibre, singularHomologyMap_one, torusMatrixMap_coordinatePeriodHomology]
  have h : twistBasisMatrix j *ᵥ Fin.cons 0 ![0, 1, 0] = ![0, 0, 1, 0] := by
    cases j <;> decide
  rw [h]

/-- The positive split-circle generator is the actual primitive elliptic twist. -/
theorem splitCircleClassOne_coordinates (j : Kind) :
    FlatTorus.singularH1Equiv (splitCircleClassOne j) = j.twist := by
  apply splitOne_originalCoordinates
  rw [splitCircleClassOne, splitFlat_inverse_circle_homology,
    splitOne_unsplit_circle, singularHomologyMap_one, torusMatrixMap_coordinatePeriodHomology]
  have h : twistBasisMatrix j *ᵥ Pi.single 0 1 = j.twist := by
    cases j <;> decide
  rw [h]

end Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.EllipticCapKernelWang
