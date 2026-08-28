import Wikipedia.HomotopyGroupsOfSpheres.SymmetricUnitaryLogarithmRelations
import Wikipedia.HomotopyGroupsOfSpheres.FiniteSubmoduleProjection

/-!
# Exponential coordinates on symmetric determinant-one unitary matrices

The logarithm has a smooth ambient extension: take entrywise imaginary
parts and project linearly onto the symmetric trace-zero subspace. On the
specified open domain the projection is the identity, by the proved
logarithm relations. Its inverse is the original constrained exponential.
-/

noncomputable section

open scoped Matrix.Norms.Frobenius ContDiff
open Set

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices

open RealSymmetricMixing ImaginarySymmetricMatrices

namespace LocalLogarithm

variable {N : Type*} [Fintype N] [DecidableEq N]

def imaginaryPart : Matrix N N ℂ →ₗ[ℝ] Matrix N N ℝ where
  toFun B := B.map Complex.im
  map_add' B C := by ext i j; simp
  map_smul' c B := by ext i j; simp

theorem imaginaryPart_imaginary (A : Matrix N N ℝ) : imaginaryPart (imaginary A) = A := by
  ext i j
  exact imaginary_im A i j

def coordinateProjection : Matrix N N ℂ →L[ℝ] DirectionSpace N :=
  (finiteSubmoduleProjection (symmetricTraceZero N)).comp imaginaryPart.toContinuousLinearMap

theorem coordinateProjection_imaginary (A : DirectionSpace N) :
    coordinateProjection (imaginary A.val) = A := by
  change finiteSubmoduleProjection (symmetricTraceZero N) (imaginaryPart (imaginary A.val)) = A
  rw [imaginaryPart_imaginary]
  exact finiteSubmoduleProjection_apply _ A

def coordinates (B : Matrix N N ℂ) : DirectionSpace N :=
  coordinateProjection (ComplexMatrixLocalLogarithm.logarithm B)

theorem contDiffOn_coordinates : ContDiffOn ℝ ∞ (coordinates (N := N))
    (ComplexMatrixLocalLogarithm.exponentialChart N).target := by
  have hp : ContDiff ℝ ∞ (coordinateProjection (N := N)) :=
    finiteLinearMap_contDiff (coordinateProjection (N := N)).toLinearMap
  exact hp.comp_contDiffOn (ComplexMatrixLocalLogarithm.contDiffOn_logarithm (N := N))

def matrix : C(SpecialSpace N, Matrix N N ℂ) :=
  ⟨fun B ↦ B.val.val.val, by fun_prop⟩

def domain (N : Type*) [Fintype N] [DecidableEq N] : Set (SpecialSpace N) :=
  matrix ⁻¹' ComplexMatrixLocalLogarithm.domain N

def target (N : Type*) [Fintype N] [DecidableEq N] : Set (DirectionSpace N) :=
  {A | ‖imaginary A.val‖ < ComplexMatrixLocalLogarithm.radius N}

theorem isOpen_domain : IsOpen (domain N) :=
  ComplexMatrixLocalLogarithm.isOpen_domain.preimage matrix.continuous

theorem isOpen_target : IsOpen (target N) :=
  isOpen_lt (finiteLinearMap_contDiff (directionMap (N := N))).continuous.norm continuous_const

theorem coordinates_val (B : SpecialSpace N) (hB : B ∈ domain N) :
    (coordinates (matrix B)).val = ComplexMatrixLocalLogarithm.realLogarithm (matrix B) := by
  let A : DirectionSpace N := ⟨_, ComplexMatrixLocalLogarithm.realLogarithm_mem B hB⟩
  change (finiteSubmoduleProjection (symmetricTraceZero N) A.val).val = A.val
  exact congrArg Subtype.val (finiteSubmoduleProjection_apply _ A)

theorem imaginary_coordinates (B : SpecialSpace N) (hB : B ∈ domain N) :
    imaginary (coordinates (matrix B)).val = ComplexMatrixLocalLogarithm.logarithm (matrix B) := by
  rw [coordinates_val B hB]
  exact ComplexMatrixLocalLogarithm.imaginary_realLogarithm _ hB B.val.property B.val.val.property

theorem coordinates_mem_target (B : SpecialSpace N) (hB : B ∈ domain N) :
    coordinates (matrix B) ∈ target N := by
  change ‖imaginary (coordinates (matrix B)).val‖ < ComplexMatrixLocalLogarithm.radius N
  rw [imaginary_coordinates B hB]
  exact hB.2

theorem exponential_mem_domain (A : DirectionSpace N) (hA : A ∈ target N) :
    exponential A ∈ domain N :=
  ComplexMatrixLocalLogarithm.exp_mem_domain (imaginary A.val) hA

theorem exponential_coordinates (B : SpecialSpace N) (hB : B ∈ domain N) :
    exponential (coordinates (matrix B)) = B := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  change NormedSpace.exp (imaginary (coordinates (matrix B)).val) = matrix B
  rw [imaginary_coordinates B hB]
  exact ComplexMatrixLocalLogarithm.exp_logarithm _ hB.1

theorem coordinates_exponential (A : DirectionSpace N) (hA : A ∈ target N) :
    coordinates (matrix (exponential A)) = A := by
  change coordinateProjection
    (ComplexMatrixLocalLogarithm.logarithm (NormedSpace.exp (imaginary A.val))) = A
  rw [ComplexMatrixLocalLogarithm.logarithm_exp _
    (ComplexMatrixLocalLogarithm.mem_safeSource_of_norm_lt _ hA).1]
  exact coordinateProjection_imaginary A

theorem continuousOn_coordinates_matrix :
    ContinuousOn (fun B : SpecialSpace N ↦ coordinates (matrix B)) (domain N) := by
  have hc : ContinuousOn (coordinates (N := N)) (ComplexMatrixLocalLogarithm.domain N) :=
    (contDiffOn_coordinates (N := N)).continuousOn.mono (fun _ h ↦ h.1)
  exact hc.comp matrix.continuous.continuousOn (fun _ h ↦ h)

def chart (N : Type*) [Fintype N] [DecidableEq N] :
    OpenPartialHomeomorph (SpecialSpace N) (DirectionSpace N) where
  toFun B := coordinates (matrix B)
  invFun := exponential
  source := domain N
  target := target N
  map_source' := coordinates_mem_target
  map_target' := exponential_mem_domain
  left_inv' := exponential_coordinates
  right_inv' := coordinates_exponential
  open_source := isOpen_domain
  open_target := isOpen_target
  continuousOn_toFun := continuousOn_coordinates_matrix
  continuousOn_invFun := continuous_exponential.continuousOn

theorem identity_mem_source : (specialIdentity : SpecialSpace N) ∈ (chart N).source :=
  ComplexMatrixLocalLogarithm.one_mem_domain

theorem zero_mem_target : (0 : DirectionSpace N) ∈ (chart N).target := by
  change ‖imaginary (0 : Matrix N N ℝ)‖ < ComplexMatrixLocalLogarithm.radius N
  rw [map_zero, norm_zero]
  exact ComplexMatrixLocalLogarithm.radius_pos

theorem chart_identity : chart N specialIdentity = 0 := by
  have h := (chart N).right_inv (zero_mem_target (N := N))
  change chart N (exponential 0) = 0 at h
  rwa [exponential_zero] at h

end LocalLogarithm

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices
