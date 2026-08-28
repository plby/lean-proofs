import Wikipedia.HopfProblem.EllipticHigherHomologyNormData

/-!
# The integral degree-one norm and its exact invariant image

The finite norm is the primitive coinvariant functional times the fixed
vector, with coefficient one or two.  Its image in the invariant lattice
has exactly that index.  The algebraic map from coinvariants to invariants
is also constructed in both monodromy conventions.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.Elliptic.HigherHomology

/-- The finite degree-one norm as an integral linear map. -/
def fibreNorm (j : Kind) : FibreLattice →ₗ[ℤ] FibreLattice :=
  (fibreNormMatrix j).mulVecLin

theorem fibreNorm_apply (j : Kind) (v : FibreLattice) :
    fibreNorm j v =
      ((fibreNormIndex j : ℤ) * fibreCoinvariantCoordinate j v) • fibreKernelVector := by
  cases j <;> ext i <;> fin_cases i <;>
    simp [fibreNorm, fibreKernelVector, dotProduct, Fin.sum_univ_succ]
  all_goals ring

@[simp] theorem fibreNorm_apply_two (j : Kind) (v : FibreLattice) :
    fibreNorm j v 2 = (fibreNormIndex j : ℤ) * fibreCoinvariantCoordinate j v := by
  rw [fibreNorm_apply]
  simp [fibreKernelVector]

theorem fibreNorm_section (j : Kind) (k : ℤ) :
    fibreNorm j ![0, k, 0] =
      ((fibreNormIndex j : ℤ) * k) • fibreKernelVector := by
  rw [fibreNorm_apply, fibreCoinvariantCoordinate_section]

theorem fibreNorm_mem_ker (j : Kind) (v : FibreLattice) :
    fibreNorm j v ∈ LinearMap.ker (fibreDifference j) := by
  rw [fibreDifference_mem_ker_iff, fibreNorm_apply]
  simp [fibreKernelVector]

theorem fibreNorm_mem_inverse_ker (j : Kind) (v : FibreLattice) :
    fibreNorm j v ∈ LinearMap.ker (fibreInverseDifference j) := by
  rw [fibreInverseDifference_ker_eq]
  exact fibreNorm_mem_ker j v

/-- The norm has its actual invariant lattice as codomain. -/
def fibreNormToKernel (j : Kind) :
    FibreLattice →ₗ[ℤ] LinearMap.ker (fibreDifference j) :=
  (fibreNorm j).codRestrict _ (fibreNorm_mem_ker j)

@[simp] theorem fibreNormToKernel_coe (j : Kind) (v : FibreLattice) :
    (fibreNormToKernel j v : FibreLattice) = fibreNorm j v := rfl

/-- The same actual norm factors through the inverse-convention invariant lattice. -/
def fibreNormToInverseKernel (j : Kind) :
    FibreLattice →ₗ[ℤ] LinearMap.ker (fibreInverseDifference j) :=
  (fibreNorm j).codRestrict _ (fibreNorm_mem_inverse_ker j)

@[simp] theorem fibreNormToInverseKernel_coe (j : Kind) (v : FibreLattice) :
    (fibreNormToInverseKernel j v : FibreLattice) = fibreNorm j v := rfl

/-- The invariant coefficient of the actual norm. -/
def fibreNormCoordinate (j : Kind) : FibreLattice →ₗ[ℤ] ℤ :=
  (fibreKernelEquivInt j).toLinearMap.comp (fibreNormToKernel j)

@[simp] theorem fibreNormCoordinate_apply (j : Kind) (v : FibreLattice) :
    fibreNormCoordinate j v =
      (fibreNormIndex j : ℤ) * fibreCoinvariantCoordinate j v :=
  fibreNorm_apply_two j v

theorem fibreNormCoordinate_eq_smul (j : Kind) :
    fibreNormCoordinate j = (fibreNormIndex j : ℤ) • fibreCoinvariantCoordinate j := by
  apply LinearMap.ext
  intro v
  exact fibreNormCoordinate_apply j v

@[simp] theorem fibreNormCoordinate_section (j : Kind) (k : ℤ) :
    fibreNormCoordinate j ![0, k, 0] = (fibreNormIndex j : ℤ) * k := by
  rw [fibreNormCoordinate_apply, fibreCoinvariantCoordinate_section]

theorem fibreNormCoordinate_range_eq_span (j : Kind) :
    LinearMap.range (fibreNormCoordinate j) =
      Submodule.span ℤ {(fibreNormIndex j : ℤ)} := by
  rw [fibreNormCoordinate_eq_smul]
  exact int_scaled_coordinate_range _ (fibreCoinvariantCoordinate_surjective j) _

theorem fibreNormCoordinate_range_iff (j : Kind) (k : ℤ) :
    k ∈ LinearMap.range (fibreNormCoordinate j) ↔ (fibreNormIndex j : ℤ) ∣ k := by
  rw [fibreNormCoordinate_range_eq_span, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, by simpa [smul_eq_mul, mul_comm] using ha.symm⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, by simpa [smul_eq_mul, mul_comm] using ha.symm⟩

theorem fibreNormCoordinate_range_index (j : Kind) :
    (LinearMap.range (fibreNormCoordinate j)).toAddSubgroup.index = fibreNormIndex j := by
  rw [fibreNormCoordinate_range_eq_span, int_span_singleton_index]
  simp

/-- This index is measured in the actual invariant lattice. -/
theorem fibreNormToKernel_range_index (j : Kind) :
    (LinearMap.range (fibreNormToKernel j)).toAddSubgroup.index = fibreNormIndex j := by
  calc
    _ = (LinearMap.range (fibreNormCoordinate j)).toAddSubgroup.index := by
      rw [fibreNormCoordinate, LinearMap.range_comp, Submodule.map_toAddSubgroup]
      exact (AddSubgroup.index_map_equiv _ (fibreKernelEquivInt j).toAddEquiv).symm
    _ = fibreNormIndex j := fibreNormCoordinate_range_index j

theorem fibreNormToInverseKernel_range_index (j : Kind) :
    (LinearMap.range (fibreNormToInverseKernel j)).toAddSubgroup.index = fibreNormIndex j := by
  have hc : (fibreInverseKernelEquivInt j).toLinearMap.comp
      (fibreNormToInverseKernel j) = fibreNormCoordinate j := by
    apply LinearMap.ext
    intro v
    rfl
  calc
    _ = (LinearMap.range (fibreNormCoordinate j)).toAddSubgroup.index := by
      rw [← hc, LinearMap.range_comp, Submodule.map_toAddSubgroup]
      exact (AddSubgroup.index_map_equiv _ (fibreInverseKernelEquivInt j).toAddEquiv).symm
    _ = fibreNormIndex j := fibreNormCoordinate_range_index j

theorem fibreNorm_range_eq_span (j : Kind) :
    LinearMap.range (fibreNorm j) =
      Submodule.span ℤ {(fibreNormIndex j : ℤ) • fibreKernelVector} := by
  ext v
  rw [Submodule.mem_span_singleton]
  constructor
  · rintro ⟨w, rfl⟩
    refine ⟨fibreCoinvariantCoordinate j w, ?_⟩
    rw [fibreNorm_apply, smul_smul, mul_comm]
  · rintro ⟨k, rfl⟩
    refine ⟨![0, k, 0], ?_⟩
    rw [fibreNorm_section, smul_smul, mul_comm]

theorem fibreNorm_ker_eq_range (j : Kind) :
    LinearMap.ker (fibreNorm j) = LinearMap.range (fibreDifference j) := by
  ext v
  rw [LinearMap.mem_ker, fibreDifference_range_iff]
  constructor
  · intro hv
    have h : (fibreNormIndex j : ℤ) * fibreCoinvariantCoordinate j v = 0 := by
      simpa using congrFun hv 2
    exact (mul_eq_zero.mp h).resolve_left (fibreNormIndex_int_ne_zero j)
  · intro hv
    rw [fibreNorm_apply, hv, mul_zero, zero_smul]

theorem fibreNorm_ker_eq_inverse_range (j : Kind) :
    LinearMap.ker (fibreNorm j) = LinearMap.range (fibreInverseDifference j) := by
  rw [fibreInverseDifference_range_eq]
  exact fibreNorm_ker_eq_range j

theorem fibreNormToKernel_ker_eq_range (j : Kind) :
    LinearMap.ker (fibreNormToKernel j) = LinearMap.range (fibreDifference j) := by
  rw [fibreNormToKernel, LinearMap.ker_codRestrict, fibreNorm_ker_eq_range]

theorem fibreNormToInverseKernel_ker_eq_range (j : Kind) :
    LinearMap.ker (fibreNormToInverseKernel j) =
      LinearMap.range (fibreInverseDifference j) := by
  rw [fibreNormToInverseKernel, LinearMap.ker_codRestrict, fibreNorm_ker_eq_inverse_range]

@[simp] theorem fibreNorm_difference (j : Kind) (v : FibreLattice) :
    fibreNorm j (fibreDifference j v) = 0 := by
  rw [fibreNorm_apply, fibreCoinvariantCoordinate_difference, mul_zero, zero_smul]

/-- The actual algebraic norm descends from coinvariants to invariants. -/
def fibreNormDesc (j : Kind) :
    (FibreLattice ⧸ LinearMap.range (fibreDifference j)) →ₗ[ℤ]
      LinearMap.ker (fibreDifference j) :=
  (LinearMap.range (fibreDifference j)).liftQ (fibreNormToKernel j) (by
    rintro v ⟨w, rfl⟩
    apply Subtype.ext
    exact fibreNorm_difference j w)

@[simp] theorem fibreNormDesc_apply_mk (j : Kind) (v : FibreLattice) :
    fibreNormDesc j (Submodule.Quotient.mk v) = fibreNormToKernel j v := rfl

theorem fibreNormDesc_coordinate (j : Kind)
    (v : FibreLattice ⧸ LinearMap.range (fibreDifference j)) :
    fibreKernelEquivInt j (fibreNormDesc j v) =
      (fibreNormIndex j : ℤ) * fibreCokernelEquivInt j v := by
  refine Submodule.Quotient.induction_on _ v ?_
  intro w
  exact fibreNormCoordinate_apply j w

theorem fibreNormDesc_coordinate_symm (j : Kind) (k : ℤ) :
    fibreKernelEquivInt j (fibreNormDesc j ((fibreCokernelEquivInt j).symm k)) =
      (fibreNormIndex j : ℤ) * k := by
  rw [fibreNormDesc_coordinate, LinearEquiv.apply_symm_apply]

theorem fibreNormDesc_coordinateMap (j : Kind) :
    (fibreKernelEquivInt j).toLinearMap.comp
        ((fibreNormDesc j).comp (fibreCokernelEquivInt j).symm.toLinearMap) =
      (fibreNormIndex j : ℤ) • (LinearMap.id : ℤ →ₗ[ℤ] ℤ) := by
  apply LinearMap.ext
  intro k
  exact fibreNormDesc_coordinate_symm j k

theorem fibreNormDesc_injective (j : Kind) : Function.Injective (fibreNormDesc j) := by
  intro x y h
  apply (fibreCokernelEquivInt j).injective
  apply mul_left_cancel₀ (fibreNormIndex_int_ne_zero j)
  simpa only [fibreNormDesc_coordinate] using congrArg (fibreKernelEquivInt j) h

theorem fibreNormDesc_range_index (j : Kind) :
    (LinearMap.range (fibreNormDesc j)).toAddSubgroup.index = fibreNormIndex j := by
  rw [fibreNormDesc, Submodule.range_liftQ]
  exact fibreNormToKernel_range_index j

/-- The same descent for the inverse-monodromy convention. -/
def fibreNormInverseDesc (j : Kind) :
    (FibreLattice ⧸ LinearMap.range (fibreInverseDifference j)) →ₗ[ℤ]
      LinearMap.ker (fibreInverseDifference j) :=
  (LinearMap.range (fibreInverseDifference j)).liftQ (fibreNormToInverseKernel j)
    (fibreNormToInverseKernel_ker_eq_range j).symm.le

@[simp] theorem fibreNormInverseDesc_apply_mk (j : Kind) (v : FibreLattice) :
    fibreNormInverseDesc j (Submodule.Quotient.mk v) = fibreNormToInverseKernel j v := rfl

@[simp] theorem fibreNormInverseDesc_apply_mk_coe (j : Kind) (v : FibreLattice) :
    (fibreNormInverseDesc j (Submodule.Quotient.mk v) : FibreLattice) =
      fibreNorm j v := rfl

theorem fibreNormInverseDesc_coordinate (j : Kind)
    (v : FibreLattice ⧸ LinearMap.range (fibreInverseDifference j)) :
    fibreInverseKernelEquivInt j (fibreNormInverseDesc j v) =
      (fibreNormIndex j : ℤ) * fibreInverseCokernelEquivInt j v := by
  refine Submodule.Quotient.induction_on _ v ?_
  intro w
  exact fibreNormCoordinate_apply j w

theorem fibreNormInverseDesc_coordinate_symm (j : Kind) (k : ℤ) :
    fibreInverseKernelEquivInt j
        (fibreNormInverseDesc j ((fibreInverseCokernelEquivInt j).symm k)) =
      (fibreNormIndex j : ℤ) * k := by
  rw [fibreNormInverseDesc_coordinate, LinearEquiv.apply_symm_apply]

theorem fibreNormInverseDesc_coordinateMap (j : Kind) :
    (fibreInverseKernelEquivInt j).toLinearMap.comp
        ((fibreNormInverseDesc j).comp (fibreInverseCokernelEquivInt j).symm.toLinearMap) =
      (fibreNormIndex j : ℤ) • (LinearMap.id : ℤ →ₗ[ℤ] ℤ) := by
  apply LinearMap.ext
  intro k
  exact fibreNormInverseDesc_coordinate_symm j k

theorem fibreNormInverseDesc_injective (j : Kind) :
    Function.Injective (fibreNormInverseDesc j) := by
  intro x y h
  apply (fibreInverseCokernelEquivInt j).injective
  apply mul_left_cancel₀ (fibreNormIndex_int_ne_zero j)
  simpa only [fibreNormInverseDesc_coordinate] using congrArg (fibreInverseKernelEquivInt j) h

theorem fibreNormInverseDesc_range_index (j : Kind) :
    (LinearMap.range (fibreNormInverseDesc j)).toAddSubgroup.index = fibreNormIndex j := by
  rw [fibreNormInverseDesc, Submodule.range_liftQ]
  exact fibreNormToInverseKernel_range_index j

end Wikipedia.HopfProblem.Elliptic.HigherHomology
