import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Transport of integral single-map coinvariants

An integral intertwining equivalence identifies the actual ranges and their
quotients. This is independent of any geometric specialization map.
-/

noncomputable section

namespace Wikipedia.HopfProblem.CuspCentralHomology.SpecializationCoinvariants

variable {M N : Type*} [AddCommGroup M] [Module ℤ M] [AddCommGroup N] [Module ℤ N]

/-- An intertwining equivalence carries the actual range onto the other range. -/
theorem map_range_of_intertwines (e : M ≃ₗ[ℤ] N)
    (A : M →ₗ[ℤ] M) (B : N →ₗ[ℤ] N)
    (h : ∀ x, e (A x) = B (e x)) :
    (LinearMap.range A).map e.toLinearMap = LinearMap.range B := by
  ext y
  constructor
  · rintro ⟨x, ⟨z, rfl⟩, rfl⟩
    exact ⟨e z, (h z).symm⟩
  · rintro ⟨z, rfl⟩
    refine ⟨A (e.symm z), ⟨e.symm z, rfl⟩, ?_⟩
    change e (A (e.symm z)) = B z
    rw [h, LinearEquiv.apply_symm_apply]

/-- The quotient equivalence induced by actual intertwining maps. -/
def quotientRangeEquiv (e : M ≃ₗ[ℤ] N)
    (A : M →ₗ[ℤ] M) (B : N →ₗ[ℤ] N)
    (h : ∀ x, e (A x) = B (e x)) :
    (M ⧸ LinearMap.range A) ≃ₗ[ℤ] (N ⧸ LinearMap.range B) := by
  let q := Submodule.Quotient.equiv (LinearMap.range A) (LinearMap.range B) e
    (map_range_of_intertwines e A B h)
  let qa : (M ⧸ LinearMap.range A) ≃+ (N ⧸ LinearMap.range B) := by
    letI := Submodule.Quotient.module (LinearMap.range A)
    letI := Submodule.Quotient.module (LinearMap.range B)
    exact q.toAddEquiv
  exact qa.toIntLinearEquiv

@[simp] theorem quotientRangeEquiv_mk (e : M ≃ₗ[ℤ] N)
    (A : M →ₗ[ℤ] M) (B : N →ₗ[ℤ] N)
    (h : ∀ x, e (A x) = B (e x)) (x : M) :
    quotientRangeEquiv e A B h (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (e x) := rfl

@[simp] theorem quotientRangeEquiv_symm_mk (e : M ≃ₗ[ℤ] N)
    (A : M →ₗ[ℤ] M) (B : N →ₗ[ℤ] N)
    (h : ∀ x, e (A x) = B (e x)) (y : N) :
    (quotientRangeEquiv e A B h).symm (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk (e.symm y) := rfl

/-- Range membership can be checked in any actual intertwining coordinates. -/
theorem mem_range_iff_of_intertwines (e : M ≃ₗ[ℤ] N)
    (A : M →ₗ[ℤ] M) (B : N →ₗ[ℤ] N)
    (h : ∀ x, e (A x) = B (e x)) (x : M) :
    x ∈ LinearMap.range A ↔ e x ∈ LinearMap.range B := by
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨e z, (h z).symm⟩
  · rintro ⟨z, hz⟩
    refine ⟨e.symm z, e.injective ?_⟩
    rw [h, LinearEquiv.apply_symm_apply, hz]

end Wikipedia.HopfProblem.CuspCentralHomology.SpecializationCoinvariants
