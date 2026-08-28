import Wikipedia.HopfProblem.EllipticHigherHomologyCoordinatesLattice
import Wikipedia.HopfProblem.EllipticHigherHomologyCoordinatesReal
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyMatrixMaps

/-!
# Actual torus coordinates adapted to the elliptic twist

The verified unimodular basis descends to a homeomorphism of the actual
real torus with one additive circle times three additive circles.  The
explicit covering-space formula identifies the first circle with the
primitive twist direction.  The actual affine elliptic homeomorphism
then becomes translation by `1 / m` on that circle and the actual
restricted matrix map on the remaining three circles.
-/

noncomputable section

open scoped Matrix MatrixGroups

namespace Wikipedia.HopfProblem.Elliptic.HigherHomology

open PeriodTorusHigherHomology

/-- Mutually inverse integral matrices give mutually inverse continuous
maps of the actual products of additive circles. -/
def matrixTorusHomeomorph {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℤ)
    (hBA : B * A = 1) (hAB : A * B = 1) : ProductTorus n ≃ₜ ProductTorus n where
  toFun := torusMatrixMap A
  invFun := torusMatrixMap B
  left_inv x := by
    change ((torusMatrixMap B).comp (torusMatrixMap A)) x = x
    rw [← torusMatrixMap_mul, hBA, torusMatrixMap_one]
    rfl
  right_inv x := by
    change ((torusMatrixMap A).comp (torusMatrixMap B)) x = x
    rw [← torusMatrixMap_mul, hAB, torusMatrixMap_one]
    rfl
  continuous_toFun := torusMatrixLinearMap_continuous A
  continuous_invFun := torusMatrixLinearMap_continuous B

@[simp] theorem matrixTorusHomeomorph_apply {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℤ) (hBA : B * A = 1) (hAB : A * B = 1)
    (x : ProductTorus n) :
    matrixTorusHomeomorph A B hBA hAB x = torusMatrixMap A x := rfl

@[simp] theorem matrixTorusHomeomorph_symm_apply {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℤ) (hBA : B * A = 1) (hAB : A * B = 1)
    (x : ProductTorus n) :
    (matrixTorusHomeomorph A B hBA hAB).symm x = torusMatrixMap B x := rfl

/-- The actual determinant-one three-dimensional torus automorphism
induced by the elliptic fibre matrix. -/
def fibreTorusHomeomorph (j : Kind) : ProductTorus 3 ≃ₜ ProductTorus 3 :=
  matrixTorusHomeomorph (fibreMatrix j) (((fibreSL j)⁻¹ : SL(3, ℤ)) : FibreMatrix)
    (congrArg (fun C : SL(3, ℤ) => C.val) (inv_mul_cancel (fibreSL j)))
    (congrArg (fun C : SL(3, ℤ) => C.val) (mul_inv_cancel (fibreSL j)))

@[simp] theorem fibreTorusHomeomorph_apply (j : Kind) (x : ProductTorus 3) :
    fibreTorusHomeomorph j x = torusMatrixMap (fibreMatrix j) x := rfl

@[simp] theorem fibreTorusHomeomorph_symm_apply (j : Kind) (x : ProductTorus 3) :
    (fibreTorusHomeomorph j).symm x =
      torusMatrixMap (((fibreSL j)⁻¹ : SL(3, ℤ)) : FibreMatrix) x := rfl

/-- The fibre automorphism is literally the quotient of its real matrix map. -/
theorem fibreTorusHomeomorph_coordinateProjection (j : Kind) (k : FibreCoordinates) :
    fibreTorusHomeomorph j (coordinateProjection 3 k) =
      coordinateProjection 3 (fibreLinear j k) :=
  torusMatrixMap_coordinateProjection (fibreMatrix j) k

/-- The integral inverse basis is exactly the real coordinate splitting. -/
theorem twistBasisInvMatrix_real_mulVec (j : Kind) (x : RealCoordinates) :
    (twistBasisInvMatrix j).map (Int.castRingHom ℝ) *ᵥ x =
      Fin.cons (splitRealCoordinates j x).1 (splitRealCoordinates j x).2 := by
  ext i
  refine Fin.cases ?_ (fun a => ?_) i
  · cases j <;> simp [twistBasisInvMatrix, splitRealCoordinates_apply,
      Kind.twist, ε, ε', Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  · rw [Fin.cons_succ]
    cases j <;> fin_cases a <;>
      simp [twistBasisInvMatrix, splitRealCoordinates_apply,
        Kind.twist, ε, ε', Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

/-- The actual real torus splits into its primitive twist circle and the
three-dimensional fibre torus by the verified integral coordinate change. -/
def splitFlatTorusHomeomorph (j : Kind) :
    RealTorus₄ ≃ₜ AddCircle (1 : ℝ) × ProductTorus 3 :=
  flatTorusCircleHomeomorph.trans
    ((matrixTorusHomeomorph (twistBasisInvMatrix j) (twistBasisMatrix j)
      (twistBasisMatrix_mul_twistBasisInvMatrix j)
      (twistBasisInvMatrix_mul_twistBasisMatrix j)).trans (productTorusSuccHomeomorph 3))

/-- Covering-space coordinates fix the actual quotient homeomorphism. -/
@[simp] theorem splitFlatTorusHomeomorph_mkQ (j : Kind) (x : RealCoordinates) :
    splitFlatTorusHomeomorph j (standardLattice.mkQ x) =
      (((splitRealCoordinates j x).1 : AddCircle (1 : ℝ)),
        coordinateProjection 3 (splitRealCoordinates j x).2) := by
  change productTorusSuccHomeomorph 3
    (torusMatrixMap (twistBasisInvMatrix j) (coordinateProjection 4 x)) = _
  rw [torusMatrixMap_coordinateProjection, twistBasisInvMatrix_real_mulVec]
  apply Prod.ext
  · rfl
  · funext i
    rfl

/-- Inverse coordinates on every real representative of the product torus. -/
theorem splitFlatTorusHomeomorph_symm_coordinateProjection (j : Kind)
    (t : ℝ) (k : FibreCoordinates) :
    (splitFlatTorusHomeomorph j).symm ((t : AddCircle (1 : ℝ)), coordinateProjection 3 k) =
      standardLattice.mkQ ((splitRealCoordinates j).symm (t, k)) := by
  apply (splitFlatTorusHomeomorph j).injective
  rw [Homeomorph.apply_symm_apply, splitFlatTorusHomeomorph_mkQ,
    ContinuousLinearEquiv.apply_symm_apply]

/-- The actual affine torus map has the required product formula:
translation by `1 / m` and the verified fibre torus automorphism. -/
theorem splitFlatTorusHomeomorph_flatTorusAffine (j : Kind) (x : RealTorus₄) :
    splitFlatTorusHomeomorph j (flatTorusAffine j j.twist x) =
      ((splitFlatTorusHomeomorph j x).1 + ((1 / (j.order : ℝ) : ℝ) : AddCircle (1 : ℝ)),
        fibreTorusHomeomorph j (splitFlatTorusHomeomorph j x).2) := by
  obtain ⟨v, rfl⟩ := standardLattice.mkQ_surjective x
  simp only [flatTorusAffine_mkQ, splitFlatTorusHomeomorph_mkQ,
    splitRealCoordinates_flatAffine, AddCircle.coe_add,
    fibreTorusHomeomorph_coordinateProjection]

/-- The conjugacy in the inverse direction, with arbitrary actual
circle and fibre-torus coordinates. -/
theorem flatTorusAffine_splitFlatTorusHomeomorph_symm (j : Kind)
    (t : AddCircle (1 : ℝ)) (k : ProductTorus 3) :
    flatTorusAffine j j.twist ((splitFlatTorusHomeomorph j).symm (t, k)) =
      (splitFlatTorusHomeomorph j).symm
        (t + ((1 / (j.order : ℝ) : ℝ) : AddCircle (1 : ℝ)), fibreTorusHomeomorph j k) := by
  apply (splitFlatTorusHomeomorph j).injective
  rw [splitFlatTorusHomeomorph_flatTorusAffine, Homeomorph.apply_symm_apply,
    Homeomorph.apply_symm_apply]

/-- Period coordinates give the same explicit splitting for every
actual complex period torus. -/
def splitPeriodTorusHomeomorph (j : Kind) (p : PeriodDomain) :
    p.Torus ≃ₜ AddCircle (1 : ℝ) × ProductTorus 3 :=
  (flatTorusPeriodHomeomorph p).symm.trans (splitFlatTorusHomeomorph j)

@[simp] theorem splitPeriodTorusHomeomorph_flatProjection (j : Kind)
    (p : PeriodDomain) (x : RealCoordinates) :
    splitPeriodTorusHomeomorph j p (flatProjection p x) =
      (((splitRealCoordinates j x).1 : AddCircle (1 : ℝ)),
        coordinateProjection 3 (splitRealCoordinates j x).2) := by
  rw [splitPeriodTorusHomeomorph, Homeomorph.trans_apply,
    flatTorusPeriodHomeomorph_symm_flatProjection, splitFlatTorusHomeomorph_mkQ]

/-- At every actual fixed period, the complex affine elliptic map has
the same proved twist-circle and fibre-torus coordinates. -/
theorem splitPeriodTorusHomeomorph_affineBiholomorph (j : Kind) (p : FixedPeriod j)
    (x : p.val.Torus) :
    splitPeriodTorusHomeomorph j p.val (affineBiholomorph j p j.twist x) =
      ((splitPeriodTorusHomeomorph j p.val x).1 +
          ((1 / (j.order : ℝ) : ℝ) : AddCircle (1 : ℝ)),
        fibreTorusHomeomorph j (splitPeriodTorusHomeomorph j p.val x).2) := by
  obtain ⟨y, rfl⟩ := (flatTorusPeriodHomeomorph p.val).surjective x
  rw [← flatTorusAffine_periodHomeomorph]
  simp only [splitPeriodTorusHomeomorph, Homeomorph.trans_apply,
    Homeomorph.symm_apply_apply]
  exact splitFlatTorusHomeomorph_flatTorusAffine j y

end Wikipedia.HopfProblem.Elliptic.HigherHomology
