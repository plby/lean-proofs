import Wikipedia.HopfProblem.EllipticHigherHomologyNormData

/-!
# The integral norm in exterior degree two

The finite norm of the actual exterior-square monodromy lands in its
invariant lattice, in either convention.  Its invariant coordinate is
the first coinvariant coordinate multiplied by one or two.  The norm
therefore descends to an injective map from the actual coinvariants to
the actual invariants with precisely that image index.

These statements concern the integer lattice maps, without a comparison
to a topological transfer or a covering map.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.Elliptic.HigherHomology

/-- The finite norm of the actual degree-two elliptic monodromy. -/
def fibreSquareNorm (j : Kind) : FibreLattice →ₗ[ℤ] FibreLattice :=
  (fibreSquareNormMatrix j).mulVecLin

@[simp] theorem fibreSquareNorm_apply (j : Kind) (v : FibreLattice) :
    fibreSquareNorm j v =
      ((fibreNormIndex j : ℤ) * v 0) • fibreSquareKernelVector j := by
  cases j <;> ext i <;> fin_cases i <;>
    simp [fibreSquareNorm, dotProduct, Fin.sum_univ_succ]
  all_goals ring

/-- The ambient image is the integral span of the scaled primitive invariant. -/
theorem fibreSquareNorm_range_eq_span (j : Kind) :
    LinearMap.range (fibreSquareNorm j) =
      Submodule.span ℤ {(fibreNormIndex j : ℤ) • fibreSquareKernelVector j} := by
  ext v
  rw [Submodule.mem_span_singleton]
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨w 0, by rw [fibreSquareNorm_apply, smul_smul, mul_comm]⟩
  · rintro ⟨k, rfl⟩
    exact ⟨![k, 0, 0], by
      rw [fibreSquareNorm_apply, smul_smul, mul_comm]
      rfl⟩

theorem fibreSquareNorm_mem_ker (j : Kind) (v : FibreLattice) :
    fibreSquareNorm j v ∈ LinearMap.ker (fibreSquareDifference j) := by
  rw [LinearMap.mem_ker, fibreSquareNorm_apply, map_smul,
    fibreSquareDifference_kernelVector, smul_zero]

theorem fibreSquareNorm_mem_inverse_ker (j : Kind) (v : FibreLattice) :
    fibreSquareNorm j v ∈ LinearMap.ker (fibreSquareInverseDifference j) := by
  rw [fibreSquareInverseDifference_ker_eq]
  exact fibreSquareNorm_mem_ker j v

/-- The norm with its codomain restricted to the actual forward invariants. -/
def fibreSquareNormToKernel (j : Kind) :
    FibreLattice →ₗ[ℤ] LinearMap.ker (fibreSquareDifference j) :=
  (fibreSquareNorm j).codRestrict _ (fibreSquareNorm_mem_ker j)

@[simp] theorem fibreSquareNormToKernel_apply_coe (j : Kind) (v : FibreLattice) :
    (fibreSquareNormToKernel j v : FibreLattice) = fibreSquareNorm j v := rfl

/-- The same norm with codomain the actual inverse-convention invariants. -/
def fibreSquareNormToInverseKernel (j : Kind) :
    FibreLattice →ₗ[ℤ] LinearMap.ker (fibreSquareInverseDifference j) :=
  (fibreSquareNorm j).codRestrict _ (fibreSquareNorm_mem_inverse_ker j)

@[simp] theorem fibreSquareNormToInverseKernel_apply_coe (j : Kind) (v : FibreLattice) :
    (fibreSquareNormToInverseKernel j v : FibreLattice) = fibreSquareNorm j v := rfl

/-- The primitive invariant coordinate of the norm, namely minus its second entry. -/
def fibreSquareNormCoordinate (j : Kind) : FibreLattice →ₗ[ℤ] ℤ :=
  (fibreSquareKernelEquivInt j).toLinearMap.comp (fibreSquareNormToKernel j)

theorem fibreSquareNormCoordinate_eq_neg_second (j : Kind) (v : FibreLattice) :
    fibreSquareNormCoordinate j v = -(fibreSquareNorm j v) 1 := rfl

@[simp] theorem fibreSquareNormCoordinate_apply (j : Kind) (v : FibreLattice) :
    fibreSquareNormCoordinate j v = (fibreNormIndex j : ℤ) * v 0 := by
  rw [fibreSquareNormCoordinate_eq_neg_second, fibreSquareNorm_apply]
  simp

@[simp] theorem fibreSquareNormToKernel_coordinate (j : Kind) (v : FibreLattice) :
    fibreSquareKernelEquivInt j (fibreSquareNormToKernel j v) =
      (fibreNormIndex j : ℤ) * v 0 :=
  fibreSquareNormCoordinate_apply j v

@[simp] theorem fibreSquareNormToInverseKernel_coordinate (j : Kind) (v : FibreLattice) :
    fibreSquareInverseKernelEquivInt j (fibreSquareNormToInverseKernel j v) =
      (fibreNormIndex j : ℤ) * v 0 :=
  fibreSquareNormCoordinate_apply j v

theorem fibreSquareNormCoordinate_eq_smul (j : Kind) :
    fibreSquareNormCoordinate j = (fibreNormIndex j : ℤ) • fibreSquareFirstCoordinate := by
  ext v
  simp

/-- Every multiple of the norm index has an explicit integral preimage. -/
theorem fibreSquareNormCoordinate_preimage (j : Kind) (k : ℤ) :
    fibreSquareNormCoordinate j ![k, 0, 0] = (fibreNormIndex j : ℤ) * k := by
  simp

theorem fibreSquareNormCoordinate_range_eq_span (j : Kind) :
    LinearMap.range (fibreSquareNormCoordinate j) =
      Submodule.span ℤ {(fibreNormIndex j : ℤ)} := by
  rw [fibreSquareNormCoordinate_eq_smul]
  exact int_scaled_coordinate_range fibreSquareFirstCoordinate
    fibreSquareFirstCoordinate_surjective _

theorem fibreSquareNormCoordinate_range_index (j : Kind) :
    (LinearMap.range (fibreSquareNormCoordinate j)).toAddSubgroup.index = fibreNormIndex j := by
  rw [fibreSquareNormCoordinate_range_eq_span, int_span_singleton_index]
  simp

/-- The computed index is in the actual degree-two invariant lattice. -/
theorem fibreSquareNormToKernel_range_index (j : Kind) :
    (LinearMap.range (fibreSquareNormToKernel j)).toAddSubgroup.index = fibreNormIndex j := by
  calc
    _ = (LinearMap.range (fibreSquareNormCoordinate j)).toAddSubgroup.index := by
      rw [fibreSquareNormCoordinate, LinearMap.range_comp, Submodule.map_toAddSubgroup]
      exact (AddSubgroup.index_map_equiv _ (fibreSquareKernelEquivInt j).toAddEquiv).symm
    _ = fibreNormIndex j := fibreSquareNormCoordinate_range_index j

theorem fibreSquareNormToInverseKernel_range_index (j : Kind) :
    (LinearMap.range (fibreSquareNormToInverseKernel j)).toAddSubgroup.index =
      fibreNormIndex j := by
  have hc : (fibreSquareInverseKernelEquivInt j).toLinearMap.comp
      (fibreSquareNormToInverseKernel j) = fibreSquareNormCoordinate j := by
    ext v
    rfl
  calc
    _ = (LinearMap.range (fibreSquareNormCoordinate j)).toAddSubgroup.index := by
      rw [← hc, LinearMap.range_comp, Submodule.map_toAddSubgroup]
      exact (AddSubgroup.index_map_equiv _
        (fibreSquareInverseKernelEquivInt j).toAddEquiv).symm
    _ = fibreNormIndex j := fibreSquareNormCoordinate_range_index j

theorem fibreSquareNorm_eq_zero_iff (j : Kind) (v : FibreLattice) :
    fibreSquareNorm j v = 0 ↔ v 0 = 0 := by
  constructor
  · intro hv
    have hc : fibreSquareNormCoordinate j v = 0 := by
      rw [fibreSquareNormCoordinate_eq_neg_second, hv]
      rfl
    rw [fibreSquareNormCoordinate_apply] at hc
    exact (mul_eq_zero.mp hc).resolve_left (fibreNormIndex_int_ne_zero j)
  · intro hv
    simp [hv]

/-- The norm annihilates exactly the image of the actual monodromy difference. -/
theorem fibreSquareNorm_ker_eq_range (j : Kind) :
    LinearMap.ker (fibreSquareNorm j) = LinearMap.range (fibreSquareDifference j) := by
  ext v
  rw [LinearMap.mem_ker, fibreSquareNorm_eq_zero_iff, fibreSquareDifference_range_iff]

theorem fibreSquareNorm_ker_eq_inverse_range (j : Kind) :
    LinearMap.ker (fibreSquareNorm j) = LinearMap.range (fibreSquareInverseDifference j) := by
  rw [fibreSquareInverseDifference_range_eq, fibreSquareNorm_ker_eq_range]

theorem fibreSquareNormToKernel_ker_eq_range (j : Kind) :
    LinearMap.ker (fibreSquareNormToKernel j) =
      LinearMap.range (fibreSquareDifference j) := by
  rw [fibreSquareNormToKernel, LinearMap.ker_codRestrict, fibreSquareNorm_ker_eq_range]

theorem fibreSquareNormToInverseKernel_ker_eq_range (j : Kind) :
    LinearMap.ker (fibreSquareNormToInverseKernel j) =
      LinearMap.range (fibreSquareInverseDifference j) := by
  rw [fibreSquareNormToInverseKernel, LinearMap.ker_codRestrict,
    fibreSquareNorm_ker_eq_inverse_range]

/-- The norm descends from the actual coinvariants to the actual invariants. -/
def fibreSquareNormDesc (j : Kind) :
    (FibreLattice ⧸ LinearMap.range (fibreSquareDifference j)) →ₗ[ℤ]
      LinearMap.ker (fibreSquareDifference j) :=
  (LinearMap.range (fibreSquareDifference j)).liftQ (fibreSquareNormToKernel j)
    (fibreSquareNormToKernel_ker_eq_range j).symm.le

@[simp] theorem fibreSquareNormDesc_apply_mk (j : Kind) (v : FibreLattice) :
    fibreSquareNormDesc j (Submodule.Quotient.mk v) = fibreSquareNormToKernel j v := rfl

theorem fibreSquareNormDesc_coordinate (j : Kind)
    (x : FibreLattice ⧸ LinearMap.range (fibreSquareDifference j)) :
    fibreSquareKernelEquivInt j (fibreSquareNormDesc j x) =
      (fibreNormIndex j : ℤ) * fibreSquareCokernelEquivInt j x := by
  refine Quotient.inductionOn' x ?_
  intro v
  change fibreSquareKernelEquivInt j
      (fibreSquareNormDesc j (Submodule.Quotient.mk v)) =
    (fibreNormIndex j : ℤ) * fibreSquareCokernelEquivInt j (Submodule.Quotient.mk v)
  rw [fibreSquareNormDesc_apply_mk, fibreSquareNormToKernel_coordinate,
    fibreSquareCokernelEquivInt_apply_mk]

/-- In the explicit integer coordinates, the descended norm is multiplication by its index. -/
theorem fibreSquareNormDesc_in_coordinates (j : Kind) (k : ℤ) :
    fibreSquareKernelEquivInt j
        (fibreSquareNormDesc j ((fibreSquareCokernelEquivInt j).symm k)) =
      (fibreNormIndex j : ℤ) * k := by
  rw [fibreSquareNormDesc_coordinate, LinearEquiv.apply_symm_apply]

theorem fibreSquareNormDesc_coordinateMap (j : Kind) :
    (fibreSquareKernelEquivInt j).toLinearMap.comp
        ((fibreSquareNormDesc j).comp (fibreSquareCokernelEquivInt j).symm.toLinearMap) =
      (fibreNormIndex j : ℤ) • (LinearMap.id : ℤ →ₗ[ℤ] ℤ) := by
  apply LinearMap.ext
  intro k
  exact fibreSquareNormDesc_in_coordinates j k

theorem fibreSquareNormDesc_injective (j : Kind) :
    Function.Injective (fibreSquareNormDesc j) := by
  intro x y h
  apply (fibreSquareCokernelEquivInt j).injective
  apply mul_left_cancel₀ (fibreNormIndex_int_ne_zero j)
  simpa only [fibreSquareNormDesc_coordinate] using
    congrArg (fibreSquareKernelEquivInt j) h

theorem fibreSquareNormDesc_range_index (j : Kind) :
    (LinearMap.range (fibreSquareNormDesc j)).toAddSubgroup.index = fibreNormIndex j := by
  rw [fibreSquareNormDesc, Submodule.range_liftQ]
  exact fibreSquareNormToKernel_range_index j

/-- The norm descended using the actual inverse-monodromy quotient and kernel. -/
def fibreSquareNormInverseDesc (j : Kind) :
    (FibreLattice ⧸ LinearMap.range (fibreSquareInverseDifference j)) →ₗ[ℤ]
      LinearMap.ker (fibreSquareInverseDifference j) :=
  (LinearMap.range (fibreSquareInverseDifference j)).liftQ (fibreSquareNormToInverseKernel j)
    (fibreSquareNormToInverseKernel_ker_eq_range j).symm.le

@[simp] theorem fibreSquareNormInverseDesc_apply_mk (j : Kind) (v : FibreLattice) :
    fibreSquareNormInverseDesc j (Submodule.Quotient.mk v) =
      fibreSquareNormToInverseKernel j v := rfl

theorem fibreSquareNormInverseDesc_coordinate (j : Kind)
    (x : FibreLattice ⧸ LinearMap.range (fibreSquareInverseDifference j)) :
    fibreSquareInverseKernelEquivInt j (fibreSquareNormInverseDesc j x) =
      (fibreNormIndex j : ℤ) * fibreSquareInverseCokernelEquivInt j x := by
  refine Quotient.inductionOn' x ?_
  intro v
  change fibreSquareInverseKernelEquivInt j
      (fibreSquareNormInverseDesc j (Submodule.Quotient.mk v)) =
    (fibreNormIndex j : ℤ) * fibreSquareInverseCokernelEquivInt j (Submodule.Quotient.mk v)
  rw [fibreSquareNormInverseDesc_apply_mk, fibreSquareNormToInverseKernel_coordinate,
    fibreSquareInverseCokernelEquivInt_apply_mk]

theorem fibreSquareNormInverseDesc_in_coordinates (j : Kind) (k : ℤ) :
    fibreSquareInverseKernelEquivInt j
        (fibreSquareNormInverseDesc j ((fibreSquareInverseCokernelEquivInt j).symm k)) =
      (fibreNormIndex j : ℤ) * k := by
  rw [fibreSquareNormInverseDesc_coordinate, LinearEquiv.apply_symm_apply]

theorem fibreSquareNormInverseDesc_coordinateMap (j : Kind) :
    (fibreSquareInverseKernelEquivInt j).toLinearMap.comp
        ((fibreSquareNormInverseDesc j).comp
          (fibreSquareInverseCokernelEquivInt j).symm.toLinearMap) =
      (fibreNormIndex j : ℤ) • (LinearMap.id : ℤ →ₗ[ℤ] ℤ) := by
  apply LinearMap.ext
  intro k
  exact fibreSquareNormInverseDesc_in_coordinates j k

theorem fibreSquareNormInverseDesc_injective (j : Kind) :
    Function.Injective (fibreSquareNormInverseDesc j) := by
  intro x y h
  apply (fibreSquareInverseCokernelEquivInt j).injective
  apply mul_left_cancel₀ (fibreNormIndex_int_ne_zero j)
  simpa only [fibreSquareNormInverseDesc_coordinate] using
    congrArg (fibreSquareInverseKernelEquivInt j) h

theorem fibreSquareNormInverseDesc_range_index (j : Kind) :
    (LinearMap.range (fibreSquareNormInverseDesc j)).toAddSubgroup.index =
      fibreNormIndex j := by
  rw [fibreSquareNormInverseDesc, Submodule.range_liftQ]
  exact fibreSquareNormToInverseKernel_range_index j

end Wikipedia.HopfProblem.Elliptic.HigherHomology
