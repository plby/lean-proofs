import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Kernels and cokernels of integrally conjugate operators

An actual integral linear equivalence intertwining two operators maps
their kernels and ranges onto one another.  Restriction and passage to
the quotient therefore give explicit kernel and cokernel equivalences.
-/

namespace Wikipedia.HopfProblem.Elliptic.HigherHomology

variable {M N : Type*} [AddCommGroup M] [Module ℤ M]
  [AddCommGroup N] [Module ℤ N]
  (e : M ≃ₗ[ℤ] N) (L : M →ₗ[ℤ] M) (A : N →ₗ[ℤ] N)
  (h : ∀ x, e (L x) = A (e x))

include h

theorem conjugacy_ker_mem_iff (x : M) :
    x ∈ LinearMap.ker L ↔ e x ∈ LinearMap.ker A := by
  change L x = 0 ↔ A (e x) = 0
  rw [← h x, e.map_eq_zero_iff]

theorem conjugacy_range_mem_iff (x : M) :
    x ∈ LinearMap.range L ↔ e x ∈ LinearMap.range A := by
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨e y, (h y).symm⟩
  · rintro ⟨y, hy⟩
    refine ⟨e.symm y, ?_⟩
    apply e.injective
    rw [h, e.apply_symm_apply]
    exact hy

/-- The kernel correspondence is proved directly from the
intertwining equation, rather than supplied as an extra hypothesis. -/
theorem conjugacy_map_ker :
    (LinearMap.ker L).map e.toLinearMap = LinearMap.ker A := by
  ext y
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (conjugacy_ker_mem_iff e L A h x).mp hx
  · intro hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    apply (conjugacy_ker_mem_iff e L A h (e.symm y)).mpr
    simpa only [e.apply_symm_apply] using hy

/-- The range correspondence uses the surjectivity of the given
linear equivalence and the same literal intertwining equation. -/
theorem conjugacy_map_range :
    (LinearMap.range L).map e.toLinearMap = LinearMap.range A := by
  ext y
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (conjugacy_range_mem_iff e L A h x).mp hx
  · intro hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    apply (conjugacy_range_mem_iff e L A h (e.symm y)).mpr
    simpa only [e.apply_symm_apply] using hy

/-- Restriction of the actual conjugating equivalence to the kernels. -/
def conjugacyKernelEquiv : LinearMap.ker L ≃ₗ[ℤ] LinearMap.ker A :=
  (@LinearEquiv.toAddEquiv _ _ _ _ _ _ _ _ _ _ _ _
    (LinearMap.ker L).module (LinearMap.ker A).module
    (e.ofSubmodules _ _ (conjugacy_map_ker e L A h))).toIntLinearEquiv

@[simp] theorem conjugacyKernelEquiv_coe_apply (x : LinearMap.ker L) :
    (conjugacyKernelEquiv e L A h x : N) = e (x : M) := rfl

@[simp] theorem conjugacyKernelEquiv_coe_symm_apply (y : LinearMap.ker A) :
    ((conjugacyKernelEquiv e L A h).symm y : M) = e.symm (y : N) := rfl

/-- Passage of the actual conjugating equivalence to the cokernels. -/
def conjugacyCokernelEquiv :
    (M ⧸ LinearMap.range L) ≃ₗ[ℤ] (N ⧸ LinearMap.range A) :=
  (@LinearEquiv.toAddEquiv _ _ _ _ _ _ _ _ _ _ _ _
    (Submodule.Quotient.module (LinearMap.range L))
    (Submodule.Quotient.module (LinearMap.range A))
    (Submodule.Quotient.equiv _ _ e (conjugacy_map_range e L A h))).toIntLinearEquiv

@[simp] theorem conjugacyCokernelEquiv_mkQ (x : M) :
    conjugacyCokernelEquiv e L A h ((LinearMap.range L).mkQ x) =
      (LinearMap.range A).mkQ (e x) := rfl

@[simp] theorem conjugacyCokernelEquiv_symm_mkQ (y : N) :
    (conjugacyCokernelEquiv e L A h).symm ((LinearMap.range A).mkQ y) =
      (LinearMap.range L).mkQ (e.symm y) := rfl

end Wikipedia.HopfProblem.Elliptic.HigherHomology
