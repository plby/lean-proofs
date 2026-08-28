import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticCapKernelWangSplitClasses
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyTorusProductDecomposition
import Wikipedia.HopfProblem.PeriodTorusCohomologyCupPairs

/-!
# The actual degree-two split inputs as ordered positive loop products

The section summand is the positive `u,w` product. The positive-circle
summand is the ordered product of the first circle with the `w`-loop.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.EllipticCapKernelWang

open FirstHurewicz Elliptic Elliptic.HigherHomology SingularMayerVietoris
open PeriodTorusHigherHomology PeriodTorusHigherHomologyPontryagin CircleTopology

theorem splitFibreInputTwo_product :
    splitFibreInputTwo = product11 (ProductTorus 3)
      (loopHomologyClass (coordinatePeriodLoop 3 (Pi.single 0 1)))
      (loopHomologyClass (coordinatePeriodLoop 3 (Pi.single 1 1))) := by
  have hv : (![1, 0, 0] : Fin 3 → ℤ) = Pi.single 0 1 := by decide
  rw [splitFibreInputTwo, hv, torusH2Coordinates_symm_basis]
  rfl

theorem splitTwo_fibre_unsplit :
    singularHomologyMap ((productTorusSuccHomeomorph 3).symm :
      C(CircleTopology.Circle × ProductTorus 3, ProductTorus 4)) 2
        (circleSectionHomology (ProductTorus 3) 2 splitFibreInputTwo) =
      product11 (ProductTorus 4)
        (loopHomologyClass (coordinatePeriodLoop 4 (Pi.single 1 1)))
        (loopHomologyClass (coordinatePeriodLoop 4 (Pi.single 2 1))) := by
  rw [circleSectionHomology, ← LinearMap.comp_apply, ← singularHomologyMap_comp]
  change singularHomologyMap (torusTailMap 3) 2 splitFibreInputTwo = _
  rw [splitFibreInputTwo_product]
  change singularHomologyMap (torusTailMap 3) 2
    (product (ProductTorus 3) 1 _ _) = product (ProductTorus 4) 1 _ _
  rw [product_natural (torusTailMap 3) (torusTailMap_add 3) 1,
    torusTailMap_coordinatePeriodHomology, torusTailMap_coordinatePeriodHomology]
  have hu : (Fin.cons 0 (Pi.single (0 : Fin 3) 1) : Lattice) = Pi.single 1 1 := by decide
  have hw : (Fin.cons 0 (Pi.single (1 : Fin 3) 1) : Lattice) = Pi.single 2 1 := by decide
  rw [hu, hw]

theorem splitTwo_circle_unsplit :
    singularHomologyMap ((productTorusSuccHomeomorph 3).symm :
      C(CircleTopology.Circle × ProductTorus 3, ProductTorus 4)) 2
        (positiveCircleCross (ProductTorus 3) 1 splitFibreInputOne) =
      product11 (ProductTorus 4)
        (loopHomologyClass (coordinatePeriodLoop 4 (Pi.single 0 1)))
        (loopHomologyClass (coordinatePeriodLoop 4 (Pi.single 2 1))) := by
  rw [torusSplit_positiveCircleCross, torusHeadCircleMap_positiveHomology,
    splitFibreInputOne, torusH1Equiv_symm_apply_loop, torusTailMap_coordinatePeriodHomology]
  have hw : (Fin.cons 0 ![0, 1, 0] : Lattice) = Pi.single 2 1 := by decide
  rw [hw]

theorem splitTwo_fibre_unsplit_coordinates :
    coordinateTorusH2Coordinates
      (singularHomologyMap ((productTorusSuccHomeomorph 3).symm :
        C(CircleTopology.Circle × ProductTorus 3, ProductTorus 4)) 2
          (circleSectionHomology (ProductTorus 3) 2 splitFibreInputTwo)) =
      Pi.single 3 1 := by
  rw [splitTwo_fibre_unsplit]
  exact PeriodTorusCohomologyCup.coordinateTorusH2Coordinates_basis_pair 3

theorem splitTwo_circle_unsplit_coordinates :
    coordinateTorusH2Coordinates
      (singularHomologyMap ((productTorusSuccHomeomorph 3).symm :
        C(CircleTopology.Circle × ProductTorus 3, ProductTorus 4)) 2
          (positiveCircleCross (ProductTorus 3) 1 splitFibreInputOne)) =
      Pi.single 1 1 := by
  rw [splitTwo_circle_unsplit]
  exact PeriodTorusCohomologyCup.coordinateTorusH2Coordinates_basis_pair 1

end Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.EllipticCapKernelWang
