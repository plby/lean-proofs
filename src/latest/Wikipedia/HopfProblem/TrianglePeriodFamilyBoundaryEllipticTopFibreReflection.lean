import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyTopDegree
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyTorusProductDecomposition

/-!
# Reversing the actual first circle in top singular homology

The reversed positive loop is identified pointwise in the original
additive circle.  Naturality of the actual singular cross product then
computes the sign on the top homology of the circle times the three-torus.
This sign is used for the negative order-four twist, not inferred merely
from an abstract rank-one module identification.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.EllipticTopFibre

open FirstHurewicz SingularMayerVietoris PeriodTorusHigherHomology Homology
open PeriodTorusHigherHomology.CircleTopology PeriodTorusHigherHomology.CirclePaths

/-- Literal inversion of the original additive circle. -/
def circleNegation : C(Circle, Circle) := ⟨fun z => -z, continuous_neg⟩

@[simp] theorem circleNegation_zero : circleNegation 0 = 0 := neg_zero

/-- Its image of the positive loop is the reversed actual loop. -/
theorem circleNegation_positiveLoop :
    positiveLoop.map circleNegation.continuous =
      positiveLoop.symm.cast circleNegation_zero circleNegation_zero := by
  apply Path.ext
  funext t
  change -((t : ℝ) : Circle) = (((1 - (t : ℝ)) : ℝ) : Circle)
  rw [AddCircle.coe_sub, AddCircle.coe_period, zero_sub]

/-- The actual first singular-homology class changes sign. -/
theorem circleNegation_positiveHomology :
    singularHomologyMap circleNegation 1 (loopHomologyClass positiveLoop) =
      -loopHomologyClass positiveLoop := by
  rw [singularHomologyMap_one, inducedHomology_loopHomologyClass,
    circleNegation_positiveLoop]
  apply homologyToChainClass_injective Circle
  rw [homologyToChainClass_loopHomologyClass, map_neg,
    homologyToChainClass_loopHomologyClass, pathClass_cast, pathClass_symm]

/-- Reverse the circle and leave every actual three-torus point fixed. -/
def productNegation : C(Circle × ProductTorus 3, Circle × ProductTorus 3) :=
  circleNegation.prodMap (ContinuousMap.id (ProductTorus 3))

/-- Naturality computes the sign on every genuine positive-circle cross product. -/
theorem productNegation_positiveCircleCross
    (a : SingularHomology (ProductTorus 3) 3) :
    singularHomologyMap productNegation 4
        (positiveCircleCross (ProductTorus 3) 3 a) =
      -positiveCircleCross (ProductTorus 3) 3 a := by
  change singularHomologyMap
    (circleNegation.prodMap (ContinuousMap.id (ProductTorus 3))) 4
      (crossProductHomology Circle (ProductTorus 3) 3
        (loopHomologyClass positiveLoop) a) = _
  rw [crossProductHomology_natural, circleNegation_positiveHomology]
  change crossProductHomology Circle (ProductTorus 3) 3
    (-loopHomologyClass positiveLoop)
    (singularHomologyMap (ContinuousMap.id (ProductTorus 3)) 3 a) = _
  rw [singularHomologyMap_id, LinearMap.id_apply, map_neg, LinearMap.neg_apply]
  rfl

/-- The actual circle boundary is an isomorphism here, so this computes
the action on every top singular-homology class. -/
theorem productNegation_homology_four
    (a : SingularHomology (Circle × ProductTorus 3) 4) :
    singularHomologyMap productNegation 4 a = -a := by
  obtain ⟨b, rfl⟩ := circleTopDegreeEquiv.symm.surjective a
  rw [circleTopDegreeEquiv_symm_apply]
  exact productNegation_positiveCircleCross b

/-- The literal integral first-coordinate reflection. -/
def headReflectionMatrix : LatticeMatrix :=
  !![-1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

/-- The matrix map and the actual reflected-circle product map agree pointwise. -/
theorem headReflectionMatrix_circleMap :
    topDegreeCircleMap headReflectionMatrix = productNegation := by
  apply ContinuousMap.ext
  rintro ⟨z, x⟩
  apply Prod.ext
  · change (∑ i : Fin 4, headReflectionMatrix 0 i • Fin.cons z x i) = -z
    simp [headReflectionMatrix, Fin.sum_univ_succ]
  · funext i
    change (∑ k : Fin 4, headReflectionMatrix i.succ k • Fin.cons z x k) = x i
    fin_cases i <;> simp [headReflectionMatrix, Fin.sum_univ_succ]

/-- The original coordinate four-torus top class changes sign under
this actual integral reflection. -/
theorem headReflectionMatrix_homology_four
    (a : SingularHomology (ProductTorus 4) 4) :
    singularHomologyMap (torusMatrixMap headReflectionMatrix) 4 a = -a := by
  apply (homeomorphHomologyEquiv (productTorusSuccHomeomorph 3) 4).injective
  rw [homeomorphHomologyEquiv_apply, homeomorphHomologyEquiv_apply]
  rw [← LinearMap.comp_apply, ← singularHomologyMap_comp,
    ← topDegreeCircleMap_comp_homeomorph, singularHomologyMap_comp,
    LinearMap.comp_apply, headReflectionMatrix_circleMap,
    productNegation_homology_four, map_neg]

end Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.EllipticTopFibre
