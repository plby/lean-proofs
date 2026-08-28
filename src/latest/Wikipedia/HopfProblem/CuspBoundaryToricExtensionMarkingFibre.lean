import Wikipedia.HopfProblem.CuspBoundaryToricExtensionTorus
import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyTransportCoordinates

/-!
# The actual fixed phase fibre in the original first-homology marking

The literal two-torus inclusion has circle coordinates `(0,0,y₀,y₁)`.
Its action on actual positive period loops, followed by the proved
flat-torus marking, therefore gives the original integral vector
`(0,0,v₀,v₁)`. In particular its two positive coordinate generators are
the third and fourth original period classes, with no change of sign.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.CuspBoundaryToricExtension

open Elliptic FirstHurewicz SingularMayerVietoris PeriodTorusHigherHomology TrianglePeriodFamily

/-- The literal inclusion matrix places the two fibre periods last. -/
theorem fibreInclusionMatrix_mulVec (v : Fin 2 → ℤ) :
    fibreInclusionMatrix *ᵥ v = ![0, 0, v 0, v 1] := by
  ext i
  fin_cases i <;>
    simp [fibreInclusionMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- The actual inclusion and the original coordinate homeomorphism
compose to the already specified integral matrix map. -/
theorem fibreMap_coordinates_comp :
    (flatTorusCircleHomeomorph : C(RealTorus₄, ProductTorus 4)).comp fibreMap =
      torusMatrixMap fibreInclusionMatrix := by
  rw [← fibreCoordinates_eq_matrixMap]
  apply ContinuousMap.ext
  exact fibreMap_coordinates

/-- Before applying the flat marking, the actual homology class maps to
the positive four-coordinate loop with two leading zeros. -/
theorem fibreMap_homologyOne_circle_coordinates (v : Fin 2 → ℤ) :
    singularHomologyMap (flatTorusCircleHomeomorph : C(RealTorus₄, ProductTorus 4)) 1
      (singularHomologyMap fibreMap 1 (loopHomologyClass (coordinatePeriodLoop 2 v))) =
      loopHomologyClass (coordinatePeriodLoop 4 ![0, 0, v 0, v 1]) := by
  rw [← LinearMap.comp_apply, ← singularHomologyMap_comp, fibreMap_coordinates_comp,
    singularHomologyMap_one, torusMatrixMap_coordinatePeriodHomology,
    fibreInclusionMatrix_mulVec]

/-- The actual fibre inclusion in the original ordered flat-torus
first-homology marking. -/
theorem fibreMap_homologyOne_coordinates (v : Fin 2 → ℤ) :
    FlatTorus.singularH1Equiv
      (singularHomologyMap fibreMap 1 (loopHomologyClass (coordinatePeriodLoop 2 v))) =
      ![0, 0, v 0, v 1] := by
  apply FlatTorus.singularH1Equiv.symm.injective
  rw [LinearEquiv.symm_apply_apply]
  apply (homeomorphHomologyEquiv flatTorusCircleHomeomorph 1).injective
  exact (fibreMap_homologyOne_circle_coordinates v).trans
    (FlatTorus.inducedHomology_singularH1Equiv_symm_circle ![0, 0, v 0, v 1]).symm

/-- Equivalently, the actual image class is the inverse original marking
of the displayed integral fibre vector. -/
theorem fibreMap_homologyOne_eq (v : Fin 2 → ℤ) :
    singularHomologyMap fibreMap 1 (loopHomologyClass (coordinatePeriodLoop 2 v)) =
      FlatTorus.singularH1Equiv.symm ![0, 0, v 0, v 1] := by
  apply FlatTorus.singularH1Equiv.injective
  rw [fibreMap_homologyOne_coordinates, LinearEquiv.apply_symm_apply]

/-- The positive zeroth fibre loop is the third original period class. -/
theorem fibreMap_homologyOne_basis_zero :
    FlatTorus.singularH1Equiv
      (singularHomologyMap fibreMap 1
        (loopHomologyClass (coordinatePeriodLoop 2 (Pi.single 0 1)))) =
      Pi.single (2 : Fin 4) 1 := by
  rw [fibreMap_homologyOne_coordinates]
  ext i
  fin_cases i <;> rfl

/-- The positive first fibre loop is the fourth original period class. -/
theorem fibreMap_homologyOne_basis_one :
    FlatTorus.singularH1Equiv
      (singularHomologyMap fibreMap 1
        (loopHomologyClass (coordinatePeriodLoop 2 (Pi.single 1 1)))) =
      Pi.single (3 : Fin 4) 1 := by
  rw [fibreMap_homologyOne_coordinates]
  ext i
  fin_cases i <;> rfl

/-- The same third-period identification as an equality of actual homology classes. -/
theorem fibreMap_homologyOne_basis_zero_eq :
    singularHomologyMap fibreMap 1
      (loopHomologyClass (coordinatePeriodLoop 2 (Pi.single 0 1))) =
      FlatTorus.singularH1Equiv.symm (Pi.single (2 : Fin 4) 1) := by
  apply FlatTorus.singularH1Equiv.injective
  rw [fibreMap_homologyOne_basis_zero, LinearEquiv.apply_symm_apply]

/-- The same fourth-period identification as an equality of actual homology classes. -/
theorem fibreMap_homologyOne_basis_one_eq :
    singularHomologyMap fibreMap 1
      (loopHomologyClass (coordinatePeriodLoop 2 (Pi.single 1 1))) =
      FlatTorus.singularH1Equiv.symm (Pi.single (3 : Fin 4) 1) := by
  apply FlatTorus.singularH1Equiv.injective
  rw [fibreMap_homologyOne_basis_one, LinearEquiv.apply_symm_apply]

end Wikipedia.HopfProblem.CuspBoundaryToricExtension
