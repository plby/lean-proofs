import Wikipedia.HopfProblem.EllipticHigherHomologyMappingTorusMonodromy
import Wikipedia.HopfProblem.EllipticHigherHomologyNorm

/-!
# Actual fibre-homology norms in the integral markings

The norm here is the finite sum of powers of the actual induced singular
homology map of the actual fibre homeomorphism.  The proved loop-product
markings identify these operators with the explicit integral norm
matrices, and identify their primitive invariant coordinates and images.
No assertion identifying a covering map with this norm is assumed here.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.Elliptic.HigherHomology

open SingularMayerVietoris PeriodTorusHigherHomology MappingTorusHomology

/-- A genuine integral marking transports every power of an intertwined operator. -/
theorem markedLinearPower {M : Type*} [AddCommGroup M] [Module ℤ M]
    (e : M ≃ₗ[ℤ] FibreLattice) (f : M →ₗ[ℤ] M) (A : FibreMatrix)
    (h : ∀ a, e (f a) = A *ᵥ e a) (k : ℕ) (a : M) :
    e ((f ^ k) a) = A ^ k *ᵥ e a := by
  induction k generalizing a with
  | zero => simp only [pow_zero, Module.End.one_apply, Matrix.one_mulVec]
  | succ k ih =>
    rw [pow_succ, Module.End.mul_apply, ih, h, pow_succ, Matrix.mulVec_mulVec]

/-- The norm of the actual induced fibre-homeomorphism map. -/
def fibreHomologyNorm (j : Kind) (n : ℕ) :
    SingularHomology (ProductTorus 3) n →ₗ[ℤ] SingularHomology (ProductTorus 3) n :=
  ∑ k ∈ Finset.range j.order, (monodromyHomologyMap (fibreTorusHomeomorph j) n) ^ k

/-- The actual forward monodromy on positive fibre loops is the stated integral matrix. -/
theorem fibreHomologyMonodromy_one (j : Kind)
    (a : SingularHomology (ProductTorus 3) 1) :
    torusH1Equiv (monodromyHomologyMap (fibreTorusHomeomorph j) 1 a) =
      fibreMatrix j *ᵥ torusH1Equiv a :=
  torusH1Equiv_matrix_natural (fibreMatrix j) a

/-- The actual forward second-homology action is the ordered matrix of minors. -/
theorem fibreHomologyMonodromy_two (j : Kind)
    (a : SingularHomology (ProductTorus 3) 2) :
    torusH2Coordinates (monodromyHomologyMap (fibreTorusHomeomorph j) 2 a) =
      fibreSquareMatrix j *ᵥ torusH2Coordinates a :=
  torusH2Coordinates_fibreMatrix j a

/-- The actual forward monodromy fixes the positive integral orientation. -/
theorem fibreHomologyMonodromy_three (j : Kind) :
    monodromyHomologyMap (fibreTorusHomeomorph j) 3 = 1 := by
  ext a
  apply torusH3Coordinates.injective
  exact torusH3Coordinates_fibreMatrix j a

/-- The actual first-homology norm has the previously calculated integral coordinates. -/
theorem fibreHomologyNorm_one (j : Kind)
    (a : SingularHomology (ProductTorus 3) 1) :
    torusH1Equiv (fibreHomologyNorm j 1 a) = fibreNorm j (torusH1Equiv a) := by
  simp only [fibreHomologyNorm, LinearMap.sum_apply, map_sum,
    fibreNorm, Matrix.mulVecLin_apply, fibreNormMatrix]
  apply Finset.sum_congr rfl
  intro k hk
  exact markedLinearPower torusH1Equiv _ _ (fibreHomologyMonodromy_one j) k a

/-- The actual second-homology norm has the calculated ordered-minor coordinates. -/
theorem fibreHomologyNorm_two (j : Kind)
    (a : SingularHomology (ProductTorus 3) 2) :
    torusH2Coordinates (fibreHomologyNorm j 2 a) =
      fibreSquareNorm j (torusH2Coordinates a) := by
  simp only [fibreHomologyNorm, LinearMap.sum_apply, map_sum,
    fibreSquareNorm, Matrix.mulVecLin_apply, fibreSquareNormMatrix]
  apply Finset.sum_congr rfl
  intro k hk
  exact markedLinearPower torusH2Coordinates _ _ (fibreHomologyMonodromy_two j) k a

/-- In top fibre degree the actual norm multiplies the integral orientation by the order. -/
theorem fibreHomologyNorm_three (j : Kind)
    (a : SingularHomology (ProductTorus 3) 3) :
    torusH3Coordinates (fibreHomologyNorm j 3 a) =
      (j.order : ℤ) * torusH3Coordinates a := by
  simp [fibreHomologyNorm, fibreHomologyMonodromy_three]

/-- The actual first-homology norm lands in the inverse-convention Wang invariants. -/
theorem fibreHomologyNorm_one_mem_ker (j : Kind)
    (a : SingularHomology (ProductTorus 3) 1) :
    fibreHomologyNorm j 1 a ∈ LinearMap.ker (wangDifference (fibreTorusHomeomorph j).symm 1) := by
  change wangDifference (fibreTorusHomeomorph j).symm 1 (fibreHomologyNorm j 1 a) = 0
  apply torusH1Equiv.injective
  rw [mappingTorusDifference_one, fibreHomologyNorm_one, map_zero]
  exact fibreNorm_mem_inverse_ker j (torusH1Equiv a)

/-- The actual second-homology norm lands in the inverse-convention Wang invariants. -/
theorem fibreHomologyNorm_two_mem_ker (j : Kind)
    (a : SingularHomology (ProductTorus 3) 2) :
    fibreHomologyNorm j 2 a ∈ LinearMap.ker (wangDifference (fibreTorusHomeomorph j).symm 2) := by
  change wangDifference (fibreTorusHomeomorph j).symm 2 (fibreHomologyNorm j 2 a) = 0
  apply torusH2Coordinates.injective
  rw [mappingTorusDifference_two, fibreHomologyNorm_two, map_zero]
  exact fibreSquareNorm_mem_inverse_ker j (torusH2Coordinates a)

/-- The primitive invariant coefficient of the actual first-homology norm. -/
def fibreHomologyNormOneCoordinate (j : Kind) :
    SingularHomology (ProductTorus 3) 1 →ₗ[ℤ] ℤ :=
  (LinearMap.proj (2 : Fin 3)).comp (torusH1Equiv.toLinearMap.comp (fibreHomologyNorm j 1))

theorem fibreHomologyNormOneCoordinate_apply (j : Kind)
    (a : SingularHomology (ProductTorus 3) 1) :
    fibreHomologyNormOneCoordinate j a =
      (fibreNormIndex j : ℤ) * fibreCoinvariantCoordinate j (torusH1Equiv a) := by
  change torusH1Equiv (fibreHomologyNorm j 1 a) 2 = _
  rw [fibreHomologyNorm_one, fibreNorm_apply_two]

/-- The primitive invariant coefficient of the actual second-homology norm. -/
def fibreHomologyNormTwoCoordinate (j : Kind) :
    SingularHomology (ProductTorus 3) 2 →ₗ[ℤ] ℤ :=
  (-LinearMap.proj (1 : Fin 3)).comp
    (torusH2Coordinates.toLinearMap.comp (fibreHomologyNorm j 2))

theorem fibreHomologyNormTwoCoordinate_apply (j : Kind)
    (a : SingularHomology (ProductTorus 3) 2) :
    fibreHomologyNormTwoCoordinate j a =
      (fibreNormIndex j : ℤ) * torusH2Coordinates a 0 := by
  change -(torusH2Coordinates (fibreHomologyNorm j 2 a) 1) = _
  rw [fibreHomologyNorm_two]
  exact fibreSquareNormCoordinate_apply j (torusH2Coordinates a)

/-- The integral orientation coefficient of the actual third-homology norm. -/
def fibreHomologyNormThreeCoordinate (j : Kind) :
    SingularHomology (ProductTorus 3) 3 →ₗ[ℤ] ℤ :=
  torusH3Coordinates.toLinearMap.comp (fibreHomologyNorm j 3)

theorem fibreHomologyNormThreeCoordinate_apply (j : Kind)
    (a : SingularHomology (ProductTorus 3) 3) :
    fibreHomologyNormThreeCoordinate j a = (j.order : ℤ) * torusH3Coordinates a :=
  fibreHomologyNorm_three j a

/-- The actual degree-one invariant norm image is the indicated principal integer subgroup. -/
theorem fibreHomologyNormOneCoordinate_range (j : Kind) :
    LinearMap.range (fibreHomologyNormOneCoordinate j) =
      Submodule.span ℤ {(fibreNormIndex j : ℤ)} := by
  have heq : fibreHomologyNormOneCoordinate j = (fibreNormIndex j : ℤ) •
      ((fibreCoinvariantCoordinate j).comp torusH1Equiv.toLinearMap) := by
    ext a
    exact fibreHomologyNormOneCoordinate_apply j a
  rw [heq]
  apply int_scaled_coordinate_range
    ((fibreCoinvariantCoordinate j).comp torusH1Equiv.toLinearMap)
  intro z
  obtain ⟨v, hv⟩ := fibreCoinvariantCoordinate_surjective j z
  refine ⟨torusH1Equiv.symm v, ?_⟩
  change fibreCoinvariantCoordinate j (torusH1Equiv (torusH1Equiv.symm v)) = z
  rw [LinearEquiv.apply_symm_apply]
  exact hv

/-- The actual degree-two invariant norm image has the same one-or-two index. -/
theorem fibreHomologyNormTwoCoordinate_range (j : Kind) :
    LinearMap.range (fibreHomologyNormTwoCoordinate j) =
      Submodule.span ℤ {(fibreNormIndex j : ℤ)} := by
  have heq : fibreHomologyNormTwoCoordinate j = (fibreNormIndex j : ℤ) •
      (fibreSquareFirstCoordinate.comp torusH2Coordinates.toLinearMap) := by
    ext a
    exact fibreHomologyNormTwoCoordinate_apply j a
  rw [heq]
  apply int_scaled_coordinate_range
    (fibreSquareFirstCoordinate.comp torusH2Coordinates.toLinearMap)
  intro z
  refine ⟨torusH2Coordinates.symm ![z, 0, 0], ?_⟩
  change torusH2Coordinates (torusH2Coordinates.symm ![z, 0, 0]) 0 = z
  rw [LinearEquiv.apply_symm_apply]
  rfl

/-- The actual top fibre-homology norm image is the order-times-orientation subgroup. -/
theorem fibreHomologyNormThreeCoordinate_range (j : Kind) :
    LinearMap.range (fibreHomologyNormThreeCoordinate j) =
      Submodule.span ℤ {(j.order : ℤ)} := by
  have heq : fibreHomologyNormThreeCoordinate j =
      (j.order : ℤ) • torusH3Coordinates.toLinearMap := by
    ext a
    exact fibreHomologyNormThreeCoordinate_apply j a
  rw [heq]
  exact int_scaled_coordinate_range _ torusH3Coordinates.surjective _

end Wikipedia.HopfProblem.Elliptic.HigherHomology
