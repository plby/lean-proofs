import Wikipedia.HopfProblem.PeriodTorusHigherHomologyMarking
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyWedgeSurjectiveProductTorus

/-!
# Canonical exterior markings of the actual four-circle torus

The constructed products of positive coordinate loops define surjective
maps from the actual integral exterior square and cube. The proved finite
free homology calculation supplies the matching ranks, so those maps are
isomorphisms. Their inverses are canonical markings of actual second and
third singular homology.

Every integral four-by-four matrix acts by its actual exterior-power map.
The coordinate homeomorphism from every admissible period torus preserves
these markings. No rank, surjectivity, or homology comparison is assumed.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusHigherHomology

open FirstHurewicz SingularMayerVietoris
open PeriodTorusHigherHomologyExterior PeriodTorusHigherHomologyPontryagin
open LocalSystemMatrices
open scoped Matrix

/-- The actual positive coordinate-loop exterior-square map is an integral isomorphism. -/
theorem coordinateTorusWedgeTwo_bijective : Function.Bijective coordinateTorusWedgeTwo := by
  let := productTorus_homology_free 4 2
  let := productTorus_homology_finite 4 2
  apply OrzechProperty.bijective_of_surjective_of_finrank_le
    coordinateTorusWedgeTwo coordinateTorusWedgeTwo_surjective
  rw [latticeExterior_finrank, productTorus_homology_finrank]

/-- The actual positive coordinate-loop exterior-cube map is an integral isomorphism. -/
theorem coordinateTorusWedgeThree_bijective : Function.Bijective coordinateTorusWedgeThree := by
  let := productTorus_homology_free 4 3
  let := productTorus_homology_finite 4 3
  apply OrzechProperty.bijective_of_surjective_of_finrank_le
    coordinateTorusWedgeThree coordinateTorusWedgeThree_surjective
  rw [latticeExterior_finrank, productTorus_homology_finrank]

/-- Products of actual positive coordinate loops identify the exterior square with `H₂`. -/
def coordinateTorusWedgeTwoEquiv :
    latticeExterior 2 ≃ₗ[ℤ] SingularHomology (ProductTorus 4) 2 :=
  LinearEquiv.ofBijective coordinateTorusWedgeTwo coordinateTorusWedgeTwo_bijective

/-- Products of actual positive coordinate loops identify the exterior cube with `H₃`. -/
def coordinateTorusWedgeThreeEquiv :
    latticeExterior 3 ≃ₗ[ℤ] SingularHomology (ProductTorus 4) 3 :=
  LinearEquiv.ofBijective coordinateTorusWedgeThree coordinateTorusWedgeThree_bijective

@[simp] theorem coordinateTorusWedgeTwoEquiv_apply (v : latticeExterior 2) :
    coordinateTorusWedgeTwoEquiv v = coordinateTorusWedgeTwo v := rfl

@[simp] theorem coordinateTorusWedgeThreeEquiv_apply (v : latticeExterior 3) :
    coordinateTorusWedgeThreeEquiv v = coordinateTorusWedgeThree v := rfl

/-- The canonical exterior-square marking of actual second singular homology. -/
def coordinateTorusH2ExteriorEquiv :
    SingularHomology (ProductTorus 4) 2 ≃ₗ[ℤ] latticeExterior 2 :=
  coordinateTorusWedgeTwoEquiv.symm

/-- The canonical exterior-cube marking of actual third singular homology. -/
def coordinateTorusH3ExteriorEquiv :
    SingularHomology (ProductTorus 4) 3 ≃ₗ[ℤ] latticeExterior 3 :=
  coordinateTorusWedgeThreeEquiv.symm

@[simp] theorem coordinateTorusH2ExteriorEquiv_wedge (v : latticeExterior 2) :
    coordinateTorusH2ExteriorEquiv (coordinateTorusWedgeTwo v) = v :=
  coordinateTorusWedgeTwoEquiv.symm_apply_apply v

@[simp] theorem coordinateTorusH3ExteriorEquiv_wedge (v : latticeExterior 3) :
    coordinateTorusH3ExteriorEquiv (coordinateTorusWedgeThree v) = v :=
  coordinateTorusWedgeThreeEquiv.symm_apply_apply v

/-- The inverse square marking sends a decomposable vector to the actual ordered loop product. -/
theorem coordinateTorusH2ExteriorEquiv_symm_ιMulti (v : Fin 2 → Lattice) :
    coordinateTorusH2ExteriorEquiv.symm (exteriorPower.ιMulti ℤ 2 v) =
      product11 (ProductTorus 4)
        (loopHomologyClass (coordinatePeriodLoop 4 (v 0)))
        (loopHomologyClass (coordinatePeriodLoop 4 (v 1))) :=
  coordinateTorusWedgeTwo_apply_ιMulti_periodLoops (Elliptic.examplePeriod .four) v

/-- The inverse cubic marking is the actual ordered product of the three coordinate loops. -/
theorem coordinateTorusH3ExteriorEquiv_symm_ιMulti (v : Fin 3 → Lattice) :
    coordinateTorusH3ExteriorEquiv.symm (exteriorPower.ιMulti ℤ 3 v) =
      tripleProduct (ProductTorus 4)
        (loopHomologyClass (coordinatePeriodLoop 4 (v 0)))
        (loopHomologyClass (coordinatePeriodLoop 4 (v 1)))
        (loopHomologyClass (coordinatePeriodLoop 4 (v 2))) :=
  coordinateTorusWedgeThree_apply_ιMulti_periodLoops (Elliptic.examplePeriod .four) v

/-- Every actual integral-matrix torus map acts by its exterior square on the canonical marking. -/
theorem coordinateTorusH2ExteriorEquiv_matrix (A : LatticeMatrix)
    (a : SingularHomology (ProductTorus 4) 2) :
    coordinateTorusH2ExteriorEquiv (singularHomologyMap (torusMatrixMap A) 2 a) =
      exteriorPower.map 2 A.mulVecLin (coordinateTorusH2ExteriorEquiv a) := by
  obtain ⟨v, rfl⟩ := coordinateTorusWedgeTwo_surjective a
  have h := LinearMap.congr_fun
    (coordinateTorusWedgeTwo_matrix (Elliptic.examplePeriod .four) A) v
  change singularHomologyMap (torusMatrixMap A) 2 (coordinateTorusWedgeTwo v) =
    coordinateTorusWedgeTwo (exteriorPower.map 2 A.mulVecLin v) at h
  rw [h, coordinateTorusH2ExteriorEquiv_wedge, coordinateTorusH2ExteriorEquiv_wedge]

/-- Every actual integral-matrix torus map acts by its exterior cube on the canonical marking. -/
theorem coordinateTorusH3ExteriorEquiv_matrix (A : LatticeMatrix)
    (a : SingularHomology (ProductTorus 4) 3) :
    coordinateTorusH3ExteriorEquiv (singularHomologyMap (torusMatrixMap A) 3 a) =
      exteriorPower.map 3 A.mulVecLin (coordinateTorusH3ExteriorEquiv a) := by
  obtain ⟨v, rfl⟩ := coordinateTorusWedgeThree_surjective a
  have h := LinearMap.congr_fun
    (coordinateTorusWedgeThree_matrix (Elliptic.examplePeriod .four) A) v
  change singularHomologyMap (torusMatrixMap A) 3 (coordinateTorusWedgeThree v) =
    coordinateTorusWedgeThree (exteriorPower.map 3 A.mulVecLin v) at h
  rw [h, coordinateTorusH3ExteriorEquiv_wedge, coordinateTorusH3ExteriorEquiv_wedge]

/-- Conjugating the actual second-homology map gives the actual exterior-square map. -/
theorem coordinateTorusH2ExteriorEquiv_matrix_conjugate (A : LatticeMatrix) :
    (coordinateTorusH2ExteriorEquiv.toLinearMap.comp
        (singularHomologyMap (torusMatrixMap A) 2)).comp
        coordinateTorusH2ExteriorEquiv.symm.toLinearMap = exteriorPower.map 2 A.mulVecLin := by
  apply LinearMap.ext
  intro v
  change coordinateTorusH2ExteriorEquiv
    (singularHomologyMap (torusMatrixMap A) 2 (coordinateTorusH2ExteriorEquiv.symm v)) = _
  rw [coordinateTorusH2ExteriorEquiv_matrix, LinearEquiv.apply_symm_apply]

/-- Conjugating the actual third-homology map gives the actual exterior-cube map. -/
theorem coordinateTorusH3ExteriorEquiv_matrix_conjugate (A : LatticeMatrix) :
    (coordinateTorusH3ExteriorEquiv.toLinearMap.comp
        (singularHomologyMap (torusMatrixMap A) 3)).comp
        coordinateTorusH3ExteriorEquiv.symm.toLinearMap = exteriorPower.map 3 A.mulVecLin := by
  apply LinearMap.ext
  intro v
  change coordinateTorusH3ExteriorEquiv
    (singularHomologyMap (torusMatrixMap A) 3 (coordinateTorusH3ExteriorEquiv.symm v)) = _
  rw [coordinateTorusH3ExteriorEquiv_matrix, LinearEquiv.apply_symm_apply]

/-- Actual second homology in the source's ordered six-minor coordinates. -/
def coordinateTorusH2Coordinates :
    SingularHomology (ProductTorus 4) 2 ≃ₗ[ℤ] (Fin 6 → ℤ) :=
  coordinateTorusH2ExteriorEquiv.trans squareCoordinates

/-- Actual third homology in the source's ordered four-minor coordinates. -/
def coordinateTorusH3Coordinates :
    SingularHomology (ProductTorus 4) 3 ≃ₗ[ℤ] (Fin 4 → ℤ) :=
  coordinateTorusH3ExteriorEquiv.trans cubeCoordinates

/-- The actual second-homology action is the literal matrix of ordered two-by-two minors. -/
theorem coordinateTorusH2Coordinates_matrix (A : LatticeMatrix)
    (a : SingularHomology (ProductTorus 4) 2) :
    coordinateTorusH2Coordinates (singularHomologyMap (torusMatrixMap A) 2 a) =
      exteriorSquare A *ᵥ coordinateTorusH2Coordinates a := by
  change squareCoordinates
    (coordinateTorusH2ExteriorEquiv (singularHomologyMap (torusMatrixMap A) 2 a)) = _
  rw [coordinateTorusH2ExteriorEquiv_matrix]
  exact squareCoordinates_map A (coordinateTorusH2ExteriorEquiv a)

/-- The actual third-homology action is the literal matrix of ordered three-by-three minors. -/
theorem coordinateTorusH3Coordinates_matrix (A : LatticeMatrix)
    (a : SingularHomology (ProductTorus 4) 3) :
    coordinateTorusH3Coordinates (singularHomologyMap (torusMatrixMap A) 3 a) =
      exteriorCube A *ᵥ coordinateTorusH3Coordinates a := by
  change cubeCoordinates
    (coordinateTorusH3ExteriorEquiv (singularHomologyMap (torusMatrixMap A) 3 a)) = _
  rw [coordinateTorusH3ExteriorEquiv_matrix]
  exact cubeCoordinates_map A (coordinateTorusH3ExteriorEquiv a)

/-- The actual period-coordinate homeomorphism preserves the canonical second-homology marking. -/
theorem coordinateTorusH2ExteriorEquiv_periodCoordinates (p : PeriodDomain)
    (a : SingularHomology p.Torus 2) :
    coordinateTorusH2ExteriorEquiv
        (singularHomologyMap (periodTorusCircleHomeomorph p : C(_, _)) 2 a) =
      periodTorusH2ExteriorEquiv p a := by
  obtain ⟨v, rfl⟩ := periodTorusWedgeTwo_surjective p a
  have h := LinearMap.congr_fun (periodTorusWedgeTwo_coordinates p) v
  change singularHomologyMap (periodTorusCircleHomeomorph p : C(_, _)) 2
    (periodTorusWedgeTwo p v) = coordinateTorusWedgeTwo v at h
  rw [h, coordinateTorusH2ExteriorEquiv_wedge, periodTorusH2ExteriorEquiv_wedge]

/-- The actual period-coordinate homeomorphism preserves the canonical third-homology marking. -/
theorem coordinateTorusH3ExteriorEquiv_periodCoordinates (p : PeriodDomain)
    (a : SingularHomology p.Torus 3) :
    coordinateTorusH3ExteriorEquiv
        (singularHomologyMap (periodTorusCircleHomeomorph p : C(_, _)) 3 a) =
      periodTorusH3ExteriorEquiv p a := by
  obtain ⟨v, rfl⟩ := periodTorusWedgeThree_surjective p a
  have h := LinearMap.congr_fun (periodTorusWedgeThree_coordinates p) v
  change singularHomologyMap (periodTorusCircleHomeomorph p : C(_, _)) 3
    (periodTorusWedgeThree p v) = coordinateTorusWedgeThree v at h
  rw [h, coordinateTorusH3ExteriorEquiv_wedge, periodTorusH3ExteriorEquiv_wedge]

theorem coordinateTorusH2Coordinates_periodCoordinates (p : PeriodDomain)
    (a : SingularHomology p.Torus 2) :
    coordinateTorusH2Coordinates
        (singularHomologyMap (periodTorusCircleHomeomorph p : C(_, _)) 2 a) =
      periodTorusH2Coordinates p a :=
  congrArg squareCoordinates (coordinateTorusH2ExteriorEquiv_periodCoordinates p a)

theorem coordinateTorusH3Coordinates_periodCoordinates (p : PeriodDomain)
    (a : SingularHomology p.Torus 3) :
    coordinateTorusH3Coordinates
        (singularHomologyMap (periodTorusCircleHomeomorph p : C(_, _)) 3 a) =
      periodTorusH3Coordinates p a :=
  congrArg cubeCoordinates (coordinateTorusH3ExteriorEquiv_periodCoordinates p a)

end Wikipedia.HopfProblem.PeriodTorusHigherHomology
