import Wikipedia.HopfProblem.EllipticHigherHomologyTorusProducts
import Wikipedia.HopfProblem.EllipticHigherHomologyTorusExterior
import Mathlib.LinearAlgebra.Dimension.Free

/-!
# Canonical integral homology markings of the elliptic three-torus

Products of actual positive coordinate loops define the canonical exterior
markings of actual singular homology in degrees two and three. The proved
coordinate-subtorus basis gives surjectivity, and the actual finite free
homology calculation gives the matching ranks, so these very maps are
isomorphisms.

Every integral three-by-three matrix acts by its actual exterior powers.
In the ordered `01, 02, 12` coordinates its second-homology action is the
matrix of two-by-two minors; on third homology it is its determinant.
The degree-one marking is imported from the proved coordinate-loop map.
No homology calculation or comparison is assumed in the final results.
-/

noncomputable section

namespace Wikipedia.HopfProblem.Elliptic.HigherHomology

open FirstHurewicz SingularMayerVietoris PeriodTorusHigherHomology
open PeriodTorusHigherHomologyPontryagin
open scoped Matrix

/-- The actual rank-three exterior-square product is an integral isomorphism. -/
theorem torusWedgeTwo_bijective : Function.Bijective torusWedgeTwo := by
  let := productTorus_homology_free 3 2
  let := productTorus_homology_finite 3 2
  apply OrzechProperty.bijective_of_surjective_of_finrank_le
    torusWedgeTwo torusWedgeTwo_surjective
  rw [torusExterior_finrank, productTorus_homology_finrank]

/-- The actual rank-three exterior-cube product is an integral isomorphism. -/
theorem torusWedgeThree_bijective : Function.Bijective torusWedgeThree := by
  let := productTorus_homology_free 3 3
  let := productTorus_homology_finite 3 3
  apply OrzechProperty.bijective_of_surjective_of_finrank_le
    torusWedgeThree torusWedgeThree_surjective
  rw [torusExterior_finrank, productTorus_homology_finrank]

/-- The exterior square identifies with actual second homology by loop products. -/
def torusWedgeTwoEquiv : torusExterior 2 ≃ₗ[ℤ] SingularHomology (ProductTorus 3) 2 :=
  LinearEquiv.ofBijective torusWedgeTwo torusWedgeTwo_bijective

/-- The exterior cube identifies with actual third homology by loop products. -/
def torusWedgeThreeEquiv : torusExterior 3 ≃ₗ[ℤ] SingularHomology (ProductTorus 3) 3 :=
  LinearEquiv.ofBijective torusWedgeThree torusWedgeThree_bijective

@[simp] theorem torusWedgeTwoEquiv_apply (v : torusExterior 2) :
    torusWedgeTwoEquiv v = torusWedgeTwo v := rfl

@[simp] theorem torusWedgeThreeEquiv_apply (v : torusExterior 3) :
    torusWedgeThreeEquiv v = torusWedgeThree v := rfl

/-- The canonical exterior-square marking of actual second singular homology. -/
def torusH2ExteriorEquiv : SingularHomology (ProductTorus 3) 2 ≃ₗ[ℤ] torusExterior 2 :=
  torusWedgeTwoEquiv.symm

/-- The canonical exterior-cube marking of actual third singular homology. -/
def torusH3ExteriorEquiv : SingularHomology (ProductTorus 3) 3 ≃ₗ[ℤ] torusExterior 3 :=
  torusWedgeThreeEquiv.symm

@[simp] theorem torusH2ExteriorEquiv_wedge (v : torusExterior 2) :
    torusH2ExteriorEquiv (torusWedgeTwo v) = v :=
  torusWedgeTwoEquiv.symm_apply_apply v

@[simp] theorem torusH3ExteriorEquiv_wedge (v : torusExterior 3) :
    torusH3ExteriorEquiv (torusWedgeThree v) = v :=
  torusWedgeThreeEquiv.symm_apply_apply v

@[simp] theorem torusH2ExteriorEquiv_symm_apply (v : torusExterior 2) :
    torusH2ExteriorEquiv.symm v = torusWedgeTwo v := rfl

@[simp] theorem torusH3ExteriorEquiv_symm_apply (v : torusExterior 3) :
    torusH3ExteriorEquiv.symm v = torusWedgeThree v := rfl

/-- The inverse square marking is the actual ordered product of the vector loops. -/
theorem torusH2ExteriorEquiv_symm_ιMulti (v : Fin 2 → FibreLattice) :
    torusH2ExteriorEquiv.symm (exteriorPower.ιMulti ℤ 2 v) =
      product11 (ProductTorus 3)
        (loopHomologyClass (coordinatePeriodLoop 3 (v 0)))
        (loopHomologyClass (coordinatePeriodLoop 3 (v 1))) :=
  torusWedgeTwo_ιMulti_loops v

/-- The inverse cubic marking is the actual ordered product of the vector loops. -/
theorem torusH3ExteriorEquiv_symm_ιMulti (v : Fin 3 → FibreLattice) :
    torusH3ExteriorEquiv.symm (exteriorPower.ιMulti ℤ 3 v) =
      tripleProduct (ProductTorus 3)
        (loopHomologyClass (coordinatePeriodLoop 3 (v 0)))
        (loopHomologyClass (coordinatePeriodLoop 3 (v 1)))
        (loopHomologyClass (coordinatePeriodLoop 3 (v 2))) :=
  torusWedgeThree_ιMulti_loops v

/-- The square marking sends every actual product to the exterior product of its markings. -/
theorem torusH2ExteriorEquiv_product (a b : SingularHomology (ProductTorus 3) 1) :
    torusH2ExteriorEquiv (product11 (ProductTorus 3) a b) =
      exteriorPower.ιMulti ℤ 2 ![torusH1Equiv a, torusH1Equiv b] := by
  obtain ⟨v, rfl⟩ := coordinateH1_three_bijective.surjective a
  obtain ⟨w, rfl⟩ := coordinateH1_three_bijective.surjective b
  rw [torusH1Equiv_coordinateH1, torusH1Equiv_coordinateH1]
  simpa only [torusWedgeTwo_ιMulti, Matrix.cons_val_zero, Matrix.cons_val_one] using
    torusH2ExteriorEquiv_wedge (exteriorPower.ιMulti ℤ 2 ![v, w])

/-- The cubic marking sends every actual triple product to the marked exterior product. -/
theorem torusH3ExteriorEquiv_tripleProduct (a b c : SingularHomology (ProductTorus 3) 1) :
    torusH3ExteriorEquiv (tripleProduct (ProductTorus 3) a b c) =
      exteriorPower.ιMulti ℤ 3 ![torusH1Equiv a, torusH1Equiv b, torusH1Equiv c] := by
  obtain ⟨v, rfl⟩ := coordinateH1_three_bijective.surjective a
  obtain ⟨w, rfl⟩ := coordinateH1_three_bijective.surjective b
  obtain ⟨u, rfl⟩ := coordinateH1_three_bijective.surjective c
  rw [torusH1Equiv_coordinateH1, torusH1Equiv_coordinateH1, torusH1Equiv_coordinateH1]
  have h := torusH3ExteriorEquiv_wedge (exteriorPower.ιMulti ℤ 3 ![v, w, u])
  rw [torusWedgeThree_ιMulti] at h
  exact h

/-- The canonical square marking is natural for compatible actual additive continuous maps. -/
theorem torusH2ExteriorEquiv_natural (f : C(ProductTorus 3, ProductTorus 3))
    (hf : ∀ x y, f (x + y) = f x + f y) (A : FibreLattice →ₗ[ℤ] FibreLattice)
    (hmark : ∀ v, singularHomologyMap f 1 (coordinateH1 3 v) = coordinateH1 3 (A v))
    (a : SingularHomology (ProductTorus 3) 2) :
    torusH2ExteriorEquiv (singularHomologyMap f 2 a) =
      exteriorPower.map 2 A (torusH2ExteriorEquiv a) := by
  obtain ⟨v, rfl⟩ := torusWedgeTwo_surjective a
  have h := LinearMap.congr_fun (torusWedgeTwo_natural f hf A hmark) v
  change singularHomologyMap f 2 (torusWedgeTwo v) =
    torusWedgeTwo (exteriorPower.map 2 A v) at h
  rw [h, torusH2ExteriorEquiv_wedge, torusH2ExteriorEquiv_wedge]

/-- The canonical cubic marking is natural for compatible actual additive continuous maps. -/
theorem torusH3ExteriorEquiv_natural (f : C(ProductTorus 3, ProductTorus 3))
    (hf : ∀ x y, f (x + y) = f x + f y) (A : FibreLattice →ₗ[ℤ] FibreLattice)
    (hmark : ∀ v, singularHomologyMap f 1 (coordinateH1 3 v) = coordinateH1 3 (A v))
    (a : SingularHomology (ProductTorus 3) 3) :
    torusH3ExteriorEquiv (singularHomologyMap f 3 a) =
      exteriorPower.map 3 A (torusH3ExteriorEquiv a) := by
  obtain ⟨v, rfl⟩ := torusWedgeThree_surjective a
  have h := LinearMap.congr_fun (torusWedgeThree_natural f hf A hmark) v
  change singularHomologyMap f 3 (torusWedgeThree v) =
    torusWedgeThree (exteriorPower.map 3 A v) at h
  rw [h, torusH3ExteriorEquiv_wedge, torusH3ExteriorEquiv_wedge]

/-- Every integral matrix acts on actual second homology by its exterior square. -/
theorem torusH2ExteriorEquiv_matrix_natural (A : FibreMatrix)
    (a : SingularHomology (ProductTorus 3) 2) :
    torusH2ExteriorEquiv (singularHomologyMap (torusMatrixMap A) 2 a) =
      exteriorPower.map 2 A.mulVecLin (torusH2ExteriorEquiv a) :=
  torusH2ExteriorEquiv_natural (torusMatrixMap A) (torusMatrixMap_add A) A.mulVecLin
    (coordinateH1_three_matrix_natural A) a

/-- Every integral matrix acts on actual third homology by its exterior cube. -/
theorem torusH3ExteriorEquiv_matrix_natural (A : FibreMatrix)
    (a : SingularHomology (ProductTorus 3) 3) :
    torusH3ExteriorEquiv (singularHomologyMap (torusMatrixMap A) 3 a) =
      exteriorPower.map 3 A.mulVecLin (torusH3ExteriorEquiv a) :=
  torusH3ExteriorEquiv_natural (torusMatrixMap A) (torusMatrixMap_add A) A.mulVecLin
    (coordinateH1_three_matrix_natural A) a

/-- Conjugation of the actual second-homology map gives the exterior-square linear map. -/
theorem torusH2ExteriorEquiv_matrix_conjugate (A : FibreMatrix) :
    (torusH2ExteriorEquiv.toLinearMap.comp
        (singularHomologyMap (torusMatrixMap A) 2)).comp
        torusH2ExteriorEquiv.symm.toLinearMap = exteriorPower.map 2 A.mulVecLin := by
  apply LinearMap.ext
  intro v
  change torusH2ExteriorEquiv
    (singularHomologyMap (torusMatrixMap A) 2 (torusH2ExteriorEquiv.symm v)) = _
  rw [torusH2ExteriorEquiv_matrix_natural, LinearEquiv.apply_symm_apply]

/-- Conjugation of the actual third-homology map gives the exterior-cube linear map. -/
theorem torusH3ExteriorEquiv_matrix_conjugate (A : FibreMatrix) :
    (torusH3ExteriorEquiv.toLinearMap.comp
        (singularHomologyMap (torusMatrixMap A) 3)).comp
        torusH3ExteriorEquiv.symm.toLinearMap = exteriorPower.map 3 A.mulVecLin := by
  apply LinearMap.ext
  intro v
  change torusH3ExteriorEquiv
    (singularHomologyMap (torusMatrixMap A) 3 (torusH3ExteriorEquiv.symm v)) = _
  rw [torusH3ExteriorEquiv_matrix_natural, LinearEquiv.apply_symm_apply]

/-- Actual second homology in the ordered `01, 02, 12` integral coordinates. -/
def torusH2Coordinates : SingularHomology (ProductTorus 3) 2 ≃ₗ[ℤ] (Fin 3 → ℤ) :=
  torusH2ExteriorEquiv.trans torusSquareCoordinates

/-- Actual third homology in the positively ordered `012` integral coordinate. -/
def torusH3Coordinates : SingularHomology (ProductTorus 3) 3 ≃ₗ[ℤ] ℤ :=
  torusH3ExteriorEquiv.trans torusCubeCoordinates

/-- The literal matrix of ordered two-by-two minors acts on actual second homology. -/
theorem torusH2Coordinates_matrix_natural (A : FibreMatrix)
    (a : SingularHomology (ProductTorus 3) 2) :
    torusH2Coordinates (singularHomologyMap (torusMatrixMap A) 2 a) =
      torusSquareMatrix A *ᵥ torusH2Coordinates a := by
  change torusSquareCoordinates
    (torusH2ExteriorEquiv (singularHomologyMap (torusMatrixMap A) 2 a)) = _
  rw [torusH2ExteriorEquiv_matrix_natural]
  exact torusSquareCoordinates_map A (torusH2ExteriorEquiv a)

/-- The literal determinant acts on the positive actual third-homology coordinate. -/
theorem torusH3Coordinates_matrix_natural (A : FibreMatrix)
    (a : SingularHomology (ProductTorus 3) 3) :
    torusH3Coordinates (singularHomologyMap (torusMatrixMap A) 3 a) =
      A.det * torusH3Coordinates a := by
  change torusCubeCoordinates
    (torusH3ExteriorEquiv (singularHomologyMap (torusMatrixMap A) 3 a)) = _
  rw [torusH3ExteriorEquiv_matrix_natural]
  exact torusCubeCoordinates_map A (torusH3ExteriorEquiv a)

/-- Each second-homology coordinate is normalized by its actual ordered loop product. -/
theorem torusH2Coordinates_symm_basis (i : Fin 3) :
    torusH2Coordinates.symm (Pi.single i 1) =
      product11 (ProductTorus 3)
        (loopHomologyClass (coordinatePeriodLoop 3 (Pi.single (fibrePair i 0) 1)))
        (loopHomologyClass (coordinatePeriodLoop 3 (Pi.single (fibrePair i 1) 1))) := by
  change torusH2ExteriorEquiv.symm (torusSquareCoordinates.symm (Pi.single i 1)) = _
  rw [← torusSquareCoordinates_basis i, LinearEquiv.symm_apply_apply,
    torusSquareBasis_apply, torusH2ExteriorEquiv_symm_ιMulti]
  simp only [Function.comp_apply, torusLatticeBasis, Pi.basisFun_apply]

/-- The positive third-homology generator is the actual ordered `0, 1, 2` loop product. -/
theorem torusH3Coordinates_symm_one :
    torusH3Coordinates.symm 1 =
      tripleProduct (ProductTorus 3)
        (loopHomologyClass (coordinatePeriodLoop 3 (Pi.single 0 1)))
        (loopHomologyClass (coordinatePeriodLoop 3 (Pi.single 1 1)))
        (loopHomologyClass (coordinatePeriodLoop 3 (Pi.single 2 1))) := by
  change torusH3ExteriorEquiv.symm (torusCubeCoordinates.symm 1) = _
  have h : torusCubeCoordinates.symm 1 = torusCubeBasis (0 : Fin 1) := by
    rw [← torusCubeCoordinates_basis (0 : Fin 1), LinearEquiv.symm_apply_apply]
  rw [h, torusCubeBasis_apply, torusH3ExteriorEquiv_symm_ιMulti]
  simp only [torusLatticeBasis, Pi.basisFun_apply]

/-- The source elliptic matrices act by their stated ordered-minor matrices on actual `H₂`. -/
theorem torusH2Coordinates_fibreMatrix (j : Kind)
    (a : SingularHomology (ProductTorus 3) 2) :
    torusH2Coordinates (singularHomologyMap (torusMatrixMap (fibreMatrix j)) 2 a) =
      fibreSquareMatrix j *ᵥ torusH2Coordinates a := by
  rw [torusH2Coordinates_matrix_natural, torusSquareMatrix_fibreMatrix]

/-- Both source elliptic matrices preserve the positive actual third-homology generator. -/
theorem torusH3Coordinates_fibreMatrix (j : Kind)
    (a : SingularHomology (ProductTorus 3) 3) :
    torusH3Coordinates (singularHomologyMap (torusMatrixMap (fibreMatrix j)) 3 a) =
      torusH3Coordinates a := by
  rw [torusH3Coordinates_matrix_natural, fibreMatrix_det, one_mul]

end Wikipedia.HopfProblem.Elliptic.HigherHomology
