import Wikipedia.HopfProblem.EllipticHigherHomologyData
import Wikipedia.HopfProblem.EllipticFixedPeriods
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyTorusDegreeOne

/-!
# The actual first homology of the elliptic three-torus

The three-circle product is an actual coordinate retract of the four-circle
product.  Its positive coordinate-loop map is therefore an isomorphism, by
the already proved rank-four Hurewicz marking.  The resulting marking has
no auxiliary period parameter and is natural for every integral matrix.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.Elliptic.HigherHomology

open FirstHurewicz SingularMayerVietoris PeriodTorusHigherHomology

private def inclusionMatrix : Matrix (Fin 4) (Fin 3) ℤ :=
  !![0, 0, 0; 1, 0, 0; 0, 1, 0; 0, 0, 1]

private def projectionMatrix : Matrix (Fin 3) (Fin 4) ℤ :=
  !![0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

private theorem projection_inclusion : projectionMatrix * inclusionMatrix = 1 := by decide

private theorem projection_inclusion_mulVec (v : FibreLattice) :
    projectionMatrix *ᵥ (inclusionMatrix *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, projection_inclusion, Matrix.one_mulVec]

private theorem projected_coordinateH1_four :
    (inducedHomology (torusMatrixMap projectionMatrix)).comp
        ((coordinateH1 4).comp inclusionMatrix.mulVecLin) = coordinateH1 3 := by
  apply (Pi.basisFun ℤ (Fin 3)).ext
  intro i
  simp only [LinearMap.comp_apply, Matrix.mulVecLin_apply]
  rw [coordinateH1_four_apply (examplePeriod .four),
    torusMatrixMap_coordinatePeriodHomology, projection_inclusion_mulVec, coordinateH1_basis]
  simp only [Pi.basisFun_apply]

/-- The actual vector loop represents its integral combination of positive coordinate loops. -/
theorem coordinateH1_three_apply (v : FibreLattice) :
    coordinateH1 3 v = loopHomologyClass (coordinatePeriodLoop 3 v) := by
  rw [← projected_coordinateH1_four]
  change inducedHomology (torusMatrixMap projectionMatrix)
    (coordinateH1 4 (inclusionMatrix *ᵥ v)) = _
  rw [coordinateH1_four_apply (examplePeriod .four),
    torusMatrixMap_coordinatePeriodHomology, projection_inclusion_mulVec]

private theorem projection_inclusion_homology (a : SingularHomology (ProductTorus 3) 1) :
    inducedHomology (torusMatrixMap projectionMatrix)
        (inducedHomology (torusMatrixMap inclusionMatrix) a) = a := by
  calc
    _ = inducedHomology
        ((torusMatrixMap projectionMatrix).comp (torusMatrixMap inclusionMatrix)) a := by
      rw [inducedHomology_comp, LinearMap.comp_apply]
    _ = a := by
      rw [← torusMatrixMap_mul, projection_inclusion, torusMatrixMap_one,
        inducedHomology_id, LinearMap.id_apply]

/-- The actual positive coordinate-loop classes form a basis in singular degree one. -/
theorem coordinateH1_three_bijective : Function.Bijective (coordinateH1 3) := by
  constructor
  · intro v w hvw
    have h := congrArg (inducedHomology (torusMatrixMap inclusionMatrix)) hvw
    rw [coordinateH1_three_apply, coordinateH1_three_apply,
      torusMatrixMap_coordinatePeriodHomology, torusMatrixMap_coordinatePeriodHomology] at h
    have h' : inclusionMatrix *ᵥ v = inclusionMatrix *ᵥ w :=
      (coordinateH1_four_bijective (examplePeriod .four)).injective (by
        simpa only [coordinateH1_four_apply (examplePeriod .four)] using h)
    have h'' := congrArg (fun u => projectionMatrix *ᵥ u) h'
    simpa only [projection_inclusion_mulVec] using h''
  · intro a
    obtain ⟨v, hv⟩ := (coordinateH1_four_bijective (examplePeriod .four)).surjective
      (inducedHomology (torusMatrixMap inclusionMatrix) a)
    refine ⟨projectionMatrix *ᵥ v, ?_⟩
    calc
      _ = inducedHomology (torusMatrixMap projectionMatrix) (coordinateH1 4 v) := by
        rw [coordinateH1_three_apply, coordinateH1_four_apply (examplePeriod .four),
          torusMatrixMap_coordinatePeriodHomology]
      _ = a := by rw [hv, projection_inclusion_homology]

/-- Every integral three-by-three matrix acts by its literal entries on coordinate classes. -/
theorem coordinateH1_three_matrix_natural (A : FibreMatrix) (v : FibreLattice) :
    singularHomologyMap (torusMatrixMap A) 1 (coordinateH1 3 v) =
      coordinateH1 3 (A *ᵥ v) := by
  rw [singularHomologyMap_one, coordinateH1_three_apply, coordinateH1_three_apply,
    torusMatrixMap_coordinatePeriodHomology]

theorem coordinateH1_three_matrix_intertwines (A : FibreMatrix) :
    (singularHomologyMap (torusMatrixMap A) 1).comp (coordinateH1 3) =
      (coordinateH1 3).comp A.mulVecLin := by
  apply LinearMap.ext
  intro v
  exact coordinateH1_three_matrix_natural A v

/-- The integral marking of the actual first singular homology of the elliptic fibre torus. -/
def torusH1Equiv : SingularHomology (ProductTorus 3) 1 ≃ₗ[ℤ] FibreLattice :=
  (LinearEquiv.ofBijective (coordinateH1 3) coordinateH1_three_bijective).symm

@[simp] theorem torusH1Equiv_symm_apply (v : FibreLattice) :
    torusH1Equiv.symm v = coordinateH1 3 v := rfl

@[simp] theorem torusH1Equiv_symm_toLinearMap :
    torusH1Equiv.symm.toLinearMap = coordinateH1 3 := rfl

/-- The inverse marking is represented by the actual positive straight coordinate loop. -/
theorem torusH1Equiv_symm_apply_loop (v : FibreLattice) :
    torusH1Equiv.symm v = loopHomologyClass (coordinatePeriodLoop 3 v) :=
  coordinateH1_three_apply v

@[simp] theorem torusH1Equiv_coordinateH1 (v : FibreLattice) :
    torusH1Equiv (coordinateH1 3 v) = v := torusH1Equiv.apply_symm_apply v

@[simp] theorem torusH1Equiv_coordinatePeriodLoop (v : FibreLattice) :
    torusH1Equiv (loopHomologyClass (coordinatePeriodLoop 3 v)) = v := by
  rw [← coordinateH1_three_apply, torusH1Equiv_coordinateH1]

/-- Naturality on every actual singular class, not only on the chosen generators. -/
theorem torusH1Equiv_matrix_natural (A : FibreMatrix)
    (a : SingularHomology (ProductTorus 3) 1) :
    torusH1Equiv (singularHomologyMap (torusMatrixMap A) 1 a) = A *ᵥ torusH1Equiv a := by
  obtain ⟨v, rfl⟩ := coordinateH1_three_bijective.surjective a
  rw [coordinateH1_three_matrix_natural, torusH1Equiv_coordinateH1,
    torusH1Equiv_coordinateH1]

/-- Conjugation of the actual singular homology map is the integral matrix map. -/
theorem torusH1Equiv_matrix_conjugate (A : FibreMatrix) :
    torusH1Equiv.toLinearMap.comp
        ((singularHomologyMap (torusMatrixMap A) 1).comp torusH1Equiv.symm.toLinearMap) =
      A.mulVecLin := by
  apply LinearMap.ext
  intro v
  change torusH1Equiv
    (singularHomologyMap (torusMatrixMap A) 1 (torusH1Equiv.symm v)) = A *ᵥ v
  rw [torusH1Equiv_matrix_natural, torusH1Equiv.apply_symm_apply]

end Wikipedia.HopfProblem.Elliptic.HigherHomology
