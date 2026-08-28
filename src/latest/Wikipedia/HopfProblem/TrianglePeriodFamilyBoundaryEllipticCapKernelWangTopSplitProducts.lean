import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticCapKernelWangTopSourceBasic
import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticCapKernelWangSplitTwoProducts
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyMarkingProductTorus

/-!
# The actual degree-three split inputs as ordered positive loop products

The fibre-section input is the positive `u,w,δ` triple.  The positive
circle cross input is the ordered `γ,u,w` triple before applying the
actual twist-basis matrix.  These identities use the genuine cross and
Pontryagin products and retain their orientation.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.EllipticCapKernelWang

open FirstHurewicz Elliptic Elliptic.HigherHomology SingularMayerVietoris
open PeriodTorusHigherHomology PeriodTorusHigherHomologyPontryagin
open PeriodTorusHigherHomologyExterior CircleTopology

/-- The genuine positive split-fibre top class becomes the ordered final-coordinate triple. -/
theorem splitThree_fibre_unsplit :
    singularHomologyMap ((productTorusSuccHomeomorph 3).symm :
      C(CircleTopology.Circle × ProductTorus 3, ProductTorus 4)) 3
        (circleSectionHomology (ProductTorus 3) 3 splitFibreInputThree) =
      tripleProduct (ProductTorus 4)
        (loopHomologyClass (coordinatePeriodLoop 4 (Pi.single 1 1)))
        (loopHomologyClass (coordinatePeriodLoop 4 (Pi.single 2 1)))
        (loopHomologyClass (coordinatePeriodLoop 4 (Pi.single 3 1))) := by
  rw [circleSectionHomology, ← LinearMap.comp_apply, ← singularHomologyMap_comp]
  change singularHomologyMap (torusTailMap 3) 3 splitFibreInputThree = _
  rw [splitFibreInputThree_product,
    tripleProduct_natural (torusTailMap 3) (torusTailMap_add 3),
    torusTailMap_coordinatePeriodHomology, torusTailMap_coordinatePeriodHomology,
    torusTailMap_coordinatePeriodHomology]
  have hu : (Fin.cons 0 (Pi.single (0 : Fin 3) 1) : Lattice) = Pi.single 1 1 := by decide
  have hw : (Fin.cons 0 (Pi.single (1 : Fin 3) 1) : Lattice) = Pi.single 2 1 := by decide
  have hd : (Fin.cons 0 (Pi.single (2 : Fin 3) 1) : Lattice) = Pi.single 3 1 := by decide
  rw [hu, hw, hd]

/-- Crossing the actual positive split circle with `u ∧ w` gives the ordered first triple. -/
theorem splitThree_circle_unsplit :
    singularHomologyMap ((productTorusSuccHomeomorph 3).symm :
      C(CircleTopology.Circle × ProductTorus 3, ProductTorus 4)) 3
        (positiveCircleCross (ProductTorus 3) 2 splitFibreInputTwo) =
      tripleProduct (ProductTorus 4)
        (loopHomologyClass (coordinatePeriodLoop 4 (Pi.single 0 1)))
        (loopHomologyClass (coordinatePeriodLoop 4 (Pi.single 1 1)))
        (loopHomologyClass (coordinatePeriodLoop 4 (Pi.single 2 1))) := by
  rw [torusSplit_positiveCircleCross, torusHeadCircleMap_positiveHomology,
    splitFibreInputTwo_product, tripleProduct_apply]
  change product (ProductTorus 4) 2 _
    (singularHomologyMap (torusTailMap 3) 2 (product (ProductTorus 3) 1 _ _)) = _
  rw [product_natural (torusTailMap 3) (torusTailMap_add 3) 1,
    torusTailMap_coordinatePeriodHomology, torusTailMap_coordinatePeriodHomology]
  have hu : (Fin.cons 0 (Pi.single (0 : Fin 3) 1) : Lattice) = Pi.single 1 1 := by decide
  have hw : (Fin.cons 0 (Pi.single (1 : Fin 3) 1) : Lattice) = Pi.single 2 1 := by decide
  rw [hu, hw]

/-- Each ordered actual positive coordinate triple is its corresponding exterior-cube basis. -/
theorem splitThree_basis_coordinates (i : Fin 4) :
    coordinateTorusH3Coordinates
      (tripleProduct (ProductTorus 4)
        (loopHomologyClass
          (coordinatePeriodLoop 4 (Pi.single (LocalSystemMatrices.tripleIndices i 0) 1)))
        (loopHomologyClass
          (coordinatePeriodLoop 4 (Pi.single (LocalSystemMatrices.tripleIndices i 1) 1)))
        (loopHomologyClass
          (coordinatePeriodLoop 4 (Pi.single (LocalSystemMatrices.tripleIndices i 2) 1)))) =
      Pi.single i 1 := by
  have h : coordinateTorusH3ExteriorEquiv.symm (cubeBasis i) =
      tripleProduct (ProductTorus 4)
        (loopHomologyClass
          (coordinatePeriodLoop 4 (Pi.single (LocalSystemMatrices.tripleIndices i 0) 1)))
        (loopHomologyClass
          (coordinatePeriodLoop 4 (Pi.single (LocalSystemMatrices.tripleIndices i 1) 1)))
        (loopHomologyClass
          (coordinatePeriodLoop 4 (Pi.single (LocalSystemMatrices.tripleIndices i 2) 1))) := by
    rw [cubeBasis_apply, coordinateTorusH3ExteriorEquiv_symm_ιMulti]
    simp only [Function.comp_apply, latticeBasis, Pi.basisFun_apply]
  rw [← h]
  change cubeCoordinates (coordinateTorusH3ExteriorEquiv
    (coordinateTorusH3ExteriorEquiv.symm (cubeBasis i))) = _
  rw [LinearEquiv.apply_symm_apply]
  change cubeBasis.equivFun (cubeBasis i) = _
  ext k
  simp [Pi.single_apply, eq_comm]

/-- The actual unsplit fibre-section input has the positive `uwδ` coordinate. -/
theorem splitThree_fibre_unsplit_coordinates :
    coordinateTorusH3Coordinates
      (singularHomologyMap ((productTorusSuccHomeomorph 3).symm :
        C(CircleTopology.Circle × ProductTorus 3, ProductTorus 4)) 3
          (circleSectionHomology (ProductTorus 3) 3 splitFibreInputThree)) =
      Pi.single 3 1 := by
  rw [splitThree_fibre_unsplit]
  exact splitThree_basis_coordinates 3

/-- The actual unsplit positive-circle input has the positive `γuw` coordinate. -/
theorem splitThree_circle_unsplit_coordinates :
    coordinateTorusH3Coordinates
      (singularHomologyMap ((productTorusSuccHomeomorph 3).symm :
        C(CircleTopology.Circle × ProductTorus 3, ProductTorus 4)) 3
          (positiveCircleCross (ProductTorus 3) 2 splitFibreInputTwo)) =
      Pi.single 0 1 := by
  rw [splitThree_circle_unsplit]
  exact splitThree_basis_coordinates 0

end Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.EllipticCapKernelWang
