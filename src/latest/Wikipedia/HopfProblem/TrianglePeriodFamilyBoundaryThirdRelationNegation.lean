import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyTransportTorus
import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyFibreInclusionMaps

/-!
# Fibre negation on the original regular quotient family

Negation of the actual flat period coordinate commutes with every
original linear triangle action.  It therefore defines a continuous
involution of the original quotient family.  Its second and third
fibre-homology actions are computed from the genuine exterior markings.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.ThirdRelation

open Elliptic SpecialPeriods SingularMayerVietoris PeriodTorusHigherHomology
open PeriodTorusHigherHomologyExterior LocalSystemMatrices Homology
open scoped Matrix

attribute [local instance] triangleTorusAction triangleTorusAction_continuous

/-- Negation of the original real period coordinate. -/
def flatNegation : C(RealTorus₄, RealTorus₄) := ⟨Neg.neg, continuous_neg⟩

@[simp] theorem flatNegation_apply (x : RealTorus₄) : flatNegation x = -x := rfl

/-- Every original triangle action is linear, including at the quotient level. -/
theorem triangleTorusHomeomorph_neg (g : TriangleGroup) (x : RealTorus₄) :
    triangleTorusHomeomorph g (-x) = -triangleTorusHomeomorph g x := by
  obtain ⟨v, rfl⟩ := standardLattice.mkQ_surjective x
  rw [← map_neg, triangleTorusHomeomorph_mkQ, map_neg,
    map_neg, triangleTorusHomeomorph_mkQ]

variable (D : Data ℂ TriangleRegularPoint)

/-- Actual fibre negation descended through the original diagonal quotient. -/
def familyNegation : C(D.Space, D.Space) where
  toFun := Quotient.lift
    (fun x : TriangleRegularPoint × RealTorus₄ => D.quotient (x.1, -x.2)) (by
      rintro x y ⟨g, hg⟩
      apply (D.quotient_eq_iff _ _).mpr
      refine ⟨g, ?_⟩
      apply Prod.ext
      · change g • y.1 = x.1
        exact congrArg (fun p : TriangleRegularPoint × RealTorus₄ => p.1) hg
      · change triangleTorusHomeomorph g (-y.2) = -x.2
        rw [triangleTorusHomeomorph_neg]
        exact congrArg Neg.neg (congrArg Prod.snd hg))
  continuous_toFun := D.quotient_isQuotientMap.continuous_iff.mpr
    (D.quotient_continuous.comp (continuous_fst.prodMk continuous_snd.neg))

@[simp] theorem familyNegation_quotient (b : TriangleRegularPoint) (x : RealTorus₄) :
    familyNegation D (D.quotient (b, x)) = D.quotient (b, -x) := rfl

/-- The map is a genuine involution of the original space. -/
theorem familyNegation_involutive : Function.Involutive (familyNegation D) := by
  intro x
  obtain ⟨⟨b, y⟩, rfl⟩ := D.quotient_surjective x
  rw [familyNegation_quotient, familyNegation_quotient, neg_neg]

/-- Literal fibre inclusions commute with the actual negation maps. -/
theorem familyNegation_comp_fibre (b : SlitBaseLift) :
    (familyNegation D).comp (familyFibreInclusion D b) =
      (familyFibreInclusion D b).comp flatNegation := rfl

private theorem torusMatrixMap_neg_one (x : ProductTorus 4) :
    torusMatrixMap (-1 : LatticeMatrix) x = -x := by
  ext i
  simp [torusMatrixMap_apply, Matrix.one_apply]

private theorem square_neg_one : exteriorSquare (-1 : LatticeMatrix) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

private theorem cube_neg_one : exteriorCube (-1 : LatticeMatrix) = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

/-- The actual coordinate homeomorphism conjugates fibre negation to the integral matrix `-I`. -/
theorem flatNegation_circle_comp :
    (flatTorusCircleHomeomorph : C(RealTorus₄, ProductTorus 4)).comp flatNegation =
      (torusMatrixMap (-1 : LatticeMatrix)).comp
        (flatTorusCircleHomeomorph : C(RealTorus₄, ProductTorus 4)) := by
  apply ContinuousMap.ext
  intro x
  change flatTorusCircleHomeomorph (-x) =
    torusMatrixMap (-1 : LatticeMatrix) (flatTorusCircleHomeomorph x)
  rw [torusMatrixMap_neg_one]
  exact map_neg flatTorusCircleMap x

theorem flatNegation_circle_homology (n : ℕ) (a : SingularHomology RealTorus₄ n) :
    singularHomologyMap (flatTorusCircleHomeomorph : C(RealTorus₄, ProductTorus 4)) n
        (singularHomologyMap flatNegation n a) =
      singularHomologyMap (torusMatrixMap (-1 : LatticeMatrix)) n
        (singularHomologyMap (flatTorusCircleHomeomorph : C(RealTorus₄, ProductTorus 4)) n a) := by
  have h := congrArg (fun f : C(RealTorus₄, ProductTorus 4) => singularHomologyMap f n)
    flatNegation_circle_comp
  rw [singularHomologyMap_comp, singularHomologyMap_comp] at h
  exact LinearMap.congr_fun h a

/-- The genuine negation map fixes all actual second fibre-homology classes. -/
theorem flatNegation_homology_two (a : SingularHomology RealTorus₄ 2) :
    singularHomologyMap flatNegation 2 a = a := by
  apply FlatTorus.singularH2Coordinates.injective
  change coordinateTorusH2Coordinates
      (singularHomologyMap (flatTorusCircleHomeomorph : C(RealTorus₄, ProductTorus 4)) 2
        (singularHomologyMap flatNegation 2 a)) =
    coordinateTorusH2Coordinates
      (singularHomologyMap (flatTorusCircleHomeomorph : C(RealTorus₄, ProductTorus 4)) 2 a)
  rw [flatNegation_circle_homology, coordinateTorusH2Coordinates_matrix,
    square_neg_one, Matrix.one_mulVec]

/-- The genuine negation map acts by minus one on actual third fibre homology. -/
theorem flatNegation_homology_three (a : SingularHomology RealTorus₄ 3) :
    singularHomologyMap flatNegation 3 a = -a := by
  apply FlatTorus.singularH3Coordinates.injective
  change coordinateTorusH3Coordinates
      (singularHomologyMap (flatTorusCircleHomeomorph : C(RealTorus₄, ProductTorus 4)) 3
        (singularHomologyMap flatNegation 3 a)) =
    coordinateTorusH3Coordinates
      (singularHomologyMap (flatTorusCircleHomeomorph : C(RealTorus₄, ProductTorus 4)) 3 (-a))
  rw [flatNegation_circle_homology, coordinateTorusH3Coordinates_matrix,
    cube_neg_one, Matrix.neg_mulVec, Matrix.one_mulVec, map_neg, map_neg]

/-- On the actual third-homology image of every literal fibre, negation is minus one. -/
theorem familyNegation_homology_fibre_three (b : SlitBaseLift)
    (a : SingularHomology RealTorus₄ 3) :
    singularHomologyMap (familyNegation D) 3
        (singularHomologyMap (familyFibreInclusion D b) 3 a) =
      -singularHomologyMap (familyFibreInclusion D b) 3 a := by
  have h := congrArg (fun f : C(RealTorus₄, D.Space) => singularHomologyMap f 3)
    (familyNegation_comp_fibre D b)
  rw [singularHomologyMap_comp, singularHomologyMap_comp] at h
  have ha := LinearMap.congr_fun h a
  simpa only [LinearMap.comp_apply, flatNegation_homology_three, map_neg] using ha

end Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.ThirdRelation
