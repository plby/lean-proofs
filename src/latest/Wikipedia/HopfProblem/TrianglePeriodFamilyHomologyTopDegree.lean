import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyTopDegreeConnecting
import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyTopDegreeMatrix
import Wikipedia.HopfProblem.EllipticHigherHomologyTorus

/-!
# Actual fourth-homology actions of the regular-family torus matrices

In the first-circle splitting of the four-torus, the signed actual
Mayer--Vietoris connecting map is an isomorphism onto third homology of
the three-torus: the other summand vanishes by the proved homology
calculation. Its inverse is the actual positive-circle cross product.

A matrix fixing the first circle acts on this connecting coordinate by
the tail matrix. The canonical rank-three marking therefore proves that
its actual fourth-homology map is multiplication by its determinant.
In particular the three source monodromy matrices act as the identity.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Homology

open SingularMayerVietoris PeriodTorusHigherHomology
open PeriodTorusHigherHomology.CircleTopology PeriodTorusHigherHomology.CirclePaths
open Elliptic.HigherHomology

/-- The actual signed connecting coordinate is injective in the top degree. -/
theorem circleTopDegreeBoundary_injective :
    Function.Injective (circleBoundary (ProductTorus 3) 3) := by
  let := productTorus_homology_subsingleton_of_lt (show 3 < 4 by decide)
  intro a b hab
  apply (circleProductHomologyEquiv (ProductTorus 3) 3).injective
  apply Prod.ext
  · exact Subsingleton.elim _ _
  · exact hab

/-- The actual connecting map identifies top product homology with the fibre's third homology. -/
def circleTopDegreeEquiv :
    SingularHomology (Circle × ProductTorus 3) 4 ≃ₗ[ℤ]
      SingularHomology (ProductTorus 3) 3 :=
  LinearEquiv.ofBijective (circleBoundary (ProductTorus 3) 3)
    ⟨circleTopDegreeBoundary_injective, circleBoundary_surjective (ProductTorus 3) 3⟩

@[simp] theorem circleTopDegreeEquiv_apply
    (a : SingularHomology (Circle × ProductTorus 3) 4) :
    circleTopDegreeEquiv a = circleBoundary (ProductTorus 3) 3 a := rfl

/-- The sign agrees with the proved actual positive-circle cross product. -/
@[simp] theorem circleTopDegreeEquiv_positiveCircleCross
    (a : SingularHomology (ProductTorus 3) 3) :
    circleTopDegreeEquiv (positiveCircleCross (ProductTorus 3) 3 a) = a :=
  circleBoundary_positiveCircleCross (ProductTorus 3) 3 a

/-- The inverse is the actual chain-constructed cross product, not a rank-only identification. -/
theorem circleTopDegreeEquiv_symm_apply (a : SingularHomology (ProductTorus 3) 3) :
    circleTopDegreeEquiv.symm a = positiveCircleCross (ProductTorus 3) 3 a := by
  apply circleTopDegreeEquiv.injective
  rw [LinearEquiv.apply_symm_apply, circleTopDegreeEquiv_positiveCircleCross]

/-- The positive integral top coordinate in the first-circle splitting. -/
def circleTopDegreeCoordinates :
    SingularHomology (Circle × ProductTorus 3) 4 ≃ₗ[ℤ] ℤ :=
  circleTopDegreeEquiv.trans torusH3Coordinates

@[simp] theorem circleTopDegreeCoordinates_apply
    (a : SingularHomology (Circle × ProductTorus 3) 4) :
    circleTopDegreeCoordinates a = torusH3Coordinates (circleBoundary (ProductTorus 3) 3 a) :=
  rfl

/-- The canonical positive top-degree marking of the actual coordinate four-torus. -/
def topDegreeTorusCoordinates : SingularHomology (ProductTorus 4) 4 ≃ₗ[ℤ] ℤ :=
  (homeomorphHomologyEquiv (productTorusSuccHomeomorph 3) 4).trans circleTopDegreeCoordinates

@[simp] theorem topDegreeTorusCoordinates_apply (a : SingularHomology (ProductTorus 4) 4) :
    topDegreeTorusCoordinates a =
      torusH3Coordinates (circleBoundary (ProductTorus 3) 3
        (homeomorphHomologyEquiv (productTorusSuccHomeomorph 3) 4 a)) := rfl

/-- Inverse top coordinates are represented by the actual positive-circle product. -/
theorem topDegreeTorusCoordinates_symm_apply (m : ℤ) :
    topDegreeTorusCoordinates.symm m =
      singularHomologyMap ((productTorusSuccHomeomorph 3).symm : C(_, _)) 4
        (positiveCircleCross (ProductTorus 3) 3 (torusH3Coordinates.symm m)) := by
  change (homeomorphHomologyEquiv (productTorusSuccHomeomorph 3) 4).symm
    (circleTopDegreeEquiv.symm (torusH3Coordinates.symm m)) = _
  rw [circleTopDegreeEquiv_symm_apply, homeomorphHomologyEquiv_symm_apply]

/-- The coordinate agrees with the already normalized actual four-torus top class. -/
@[simp] theorem topDegreeTorusCoordinates_topClass :
    topDegreeTorusCoordinates (productTorusTopClass 4) = 1 := by
  rw [topDegreeTorusCoordinates_apply, productTorusTopClass_succ_boundary]
  have h : productTorusTopClass 3 = torusH3Coordinates.symm 1 :=
    productTorusTopClass_three.trans torusH3Coordinates_symm_one.symm
  rw [h, LinearEquiv.apply_symm_apply]

/-- A head-preserving matrix acts on the actual connecting coordinate by its tail block. -/
theorem circleTopDegreeBoundary_matrix (A : LatticeMatrix)
    (hA : ∀ j, A 0 j = if j = 0 then 1 else 0)
    (a : SingularHomology (Circle × ProductTorus 3) 4) :
    circleBoundary (ProductTorus 3) 3 (singularHomologyMap (topDegreeCircleMap A) 4 a) =
      singularHomologyMap (torusMatrixMap (topDegreeTailMatrix A)) 3
        (circleBoundary (ProductTorus 3) 3 a) := by
  have h := circleBoundary_headMap (topDegreeCircleMap A)
    (topDegreeCircleMap_fst A hA) 3 a
  change circleBoundary (ProductTorus 3) 3
      (singularHomologyMap (topDegreeCircleMap A) 4 a) =
    singularHomologyMap (topDegreeFibreMap A quarterPoint) 3
      (circleBoundary (ProductTorus 3) 3 a) at h
  rw [topDegreeFibreMap_singularHomologyMap] at h
  exact h

/-- In the actual first-circle coordinates the top homology action is its determinant. -/
theorem circleTopDegreeCoordinates_matrix (A : LatticeMatrix)
    (hA : ∀ j, A 0 j = if j = 0 then 1 else 0)
    (a : SingularHomology (Circle × ProductTorus 3) 4) :
    circleTopDegreeCoordinates (singularHomologyMap (topDegreeCircleMap A) 4 a) =
      A.det * circleTopDegreeCoordinates a := by
  change torusH3Coordinates
    (circleBoundary (ProductTorus 3) 3 (singularHomologyMap (topDegreeCircleMap A) 4 a)) = _
  rw [circleTopDegreeBoundary_matrix A hA, torusH3Coordinates_matrix_natural,
    topDegree_det_eq_tail A hA]
  rfl

/-- The literal matrix map on the actual four-torus acts by its determinant on `H₄`. -/
theorem topDegreeTorusCoordinates_matrix (A : LatticeMatrix)
    (hA : ∀ j, A 0 j = if j = 0 then 1 else 0)
    (a : SingularHomology (ProductTorus 4) 4) :
    topDegreeTorusCoordinates (singularHomologyMap (torusMatrixMap A) 4 a) =
      A.det * topDegreeTorusCoordinates a := by
  change circleTopDegreeCoordinates
    (singularHomologyMap (productTorusSuccHomeomorph 3 : C(_, _)) 4
      (singularHomologyMap (torusMatrixMap A) 4 a)) = _
  rw [← LinearMap.comp_apply, ← singularHomologyMap_comp,
    ← topDegreeCircleMap_comp_homeomorph, singularHomologyMap_comp, LinearMap.comp_apply]
  exact circleTopDegreeCoordinates_matrix A hA _

/-- Pointwise action on actual fourth singular homology, independent of the chosen marking. -/
theorem torusMatrixMap_homologyFour_apply (A : LatticeMatrix)
    (hA : ∀ j, A 0 j = if j = 0 then 1 else 0)
    (a : SingularHomology (ProductTorus 4) 4) :
    singularHomologyMap (torusMatrixMap A) 4 a = A.det • a := by
  apply topDegreeTorusCoordinates.injective
  rw [map_zsmul]
  simpa only [zsmul_eq_mul, Int.cast_id] using topDegreeTorusCoordinates_matrix A hA a

/-- The actual induced fourth-homology linear map is determinant times identity. -/
theorem torusMatrixMap_homologyFour (A : LatticeMatrix)
    (hA : ∀ j, A 0 j = if j = 0 then 1 else 0) :
    singularHomologyMap (torusMatrixMap A) 4 =
      A.det • (LinearMap.id : SingularHomology (ProductTorus 4) 4 →ₗ[ℤ] _) := by
  apply LinearMap.ext
  intro a
  exact torusMatrixMap_homologyFour_apply A hA a

/-- A head-preserving determinant-one matrix acts trivially on actual fourth homology. -/
theorem torusMatrixMap_homologyFour_of_det_one (A : LatticeMatrix)
    (hA : ∀ j, A 0 j = if j = 0 then 1 else 0) (hdet : A.det = 1) :
    singularHomologyMap (torusMatrixMap A) 4 = LinearMap.id := by
  rw [torusMatrixMap_homologyFour A hA, hdet, one_smul]

/-- The source first monodromy has the identity action on actual top torus homology. -/
theorem torusMatrixMap_A₁_homologyFour :
    singularHomologyMap (torusMatrixMap A₁) 4 = LinearMap.id := by
  apply torusMatrixMap_homologyFour_of_det_one A₁
  · intro j
    fin_cases j <;> decide
  · decide

/-- The source second monodromy has the identity action on actual top torus homology. -/
theorem torusMatrixMap_A₂_homologyFour :
    singularHomologyMap (torusMatrixMap A₂) 4 = LinearMap.id := by
  apply torusMatrixMap_homologyFour_of_det_one A₂
  · intro j
    fin_cases j <;> decide
  · decide

/-- The source cusp monodromy has the identity action on actual top torus homology. -/
theorem torusMatrixMap_M₀_homologyFour :
    singularHomologyMap (torusMatrixMap M₀) 4 = LinearMap.id := by
  apply torusMatrixMap_homologyFour_of_det_one M₀
  · intro j
    fin_cases j <;> decide
  · decide

end Wikipedia.HopfProblem.TrianglePeriodFamily.Homology
