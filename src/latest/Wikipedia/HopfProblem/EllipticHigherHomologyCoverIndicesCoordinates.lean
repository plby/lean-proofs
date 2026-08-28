import Wikipedia.HopfProblem.EllipticHigherHomologyCoverAlgebra

/-!
# Transporting actual covering cokernels into integral coordinates

Changing the codomain by a genuine linear equivalence transports the
actual image submodule, its quotient, and its additive index.  These
helpers retain the quotient representative formula and do not replace
an image calculation by an assumed cokernel isomorphism.
-/

noncomputable section

namespace Wikipedia.HopfProblem.Elliptic.HigherHomology

variable {M N P : Type*} [AddCommGroup M] [Module ℤ M]
  [AddCommGroup N] [Module ℤ N] [AddCommGroup P] [Module ℤ P]

/-- A surjective change in the domain does not alter the actual image. -/
theorem cover_range_comp_of_surjective (F : N →ₗ[ℤ] P) (G : M →ₗ[ℤ] N)
    (hG : Function.Surjective G) : LinearMap.range (F.comp G) = LinearMap.range F := by
  ext p
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨G x, rfl⟩
  · rintro ⟨y, rfl⟩
    obtain ⟨x, rfl⟩ := hG y
    exact ⟨x, rfl⟩

/-- The actual codomain quotient is transported by the given coordinate equivalence. -/
def coverCokernelCoordinatesEquiv (f : M →ₗ[ℤ] N) (e : N ≃ₗ[ℤ] P) :
    (N ⧸ LinearMap.range f) ≃ₗ[ℤ] (P ⧸ LinearMap.range (e.toLinearMap.comp f)) := by
  letI := Submodule.Quotient.module (LinearMap.range f)
  letI := Submodule.Quotient.module (LinearMap.range (e.toLinearMap.comp f))
  exact (Submodule.Quotient.equiv _ _ e (by rw [LinearMap.range_comp])).toAddEquiv.toIntLinearEquiv

@[simp] theorem coverCokernelCoordinatesEquiv_mk (f : M →ₗ[ℤ] N) (e : N ≃ₗ[ℤ] P)
    (x : N) :
    coverCokernelCoordinatesEquiv f e (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (e x) := rfl

@[simp] theorem coverCokernelCoordinatesEquiv_symm_mk (f : M →ₗ[ℤ] N) (e : N ≃ₗ[ℤ] P)
    (x : P) :
    (coverCokernelCoordinatesEquiv f e).symm (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (e.symm x) := rfl

/-- The image index is unchanged by the actual coordinate equivalence. -/
theorem cover_range_index_coordinates (f : M →ₗ[ℤ] N) (e : N ≃ₗ[ℤ] P) :
    (LinearMap.range f).toAddSubgroup.index =
      (LinearMap.range (e.toLinearMap.comp f)).toAddSubgroup.index := by
  change Nat.card (N ⧸ LinearMap.range f) = Nat.card (P ⧸ LinearMap.range (e.toLinearMap.comp f))
  exact Nat.card_congr (coverCokernelCoordinatesEquiv f e).toEquiv

end Wikipedia.HopfProblem.Elliptic.HigherHomology
