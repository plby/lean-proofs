import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.FiniteType

/-!
# Exact integral kernels from finite free coinvariant coordinates

A surjective integral linear map that kills a specified submodule descends
to the actual quotient. If that quotient and the target are finite free of
the same rank, the descended map is injective and the specified submodule
is exactly the original kernel. No geometric assertion is assumed here.
-/

noncomputable section

namespace Wikipedia.HopfProblem.CuspCentralHomology.SpecializationCoinvariants

variable {M N : Type*} [AddCommGroup M] [Module ℤ M] [AddCommGroup N] [Module ℤ N]

private def integerLinearMapOfAdd (g : M →+ N) : M →ₗ[ℤ] N where
  toFun := g
  map_add' := g.map_add
  map_smul' c x := by
    simpa only [Int.cast_id, RingHom.id_apply] using map_intCast_smul g ℤ ℤ c x

/-- The actual quotient lift with the canonical integral module on its source. -/
def quotientLiftMap (S : Submodule ℤ M) (f : M →ₗ[ℤ] N)
    (hS : S ≤ LinearMap.ker f) : (M ⧸ S) →ₗ[ℤ] N :=
  integerLinearMapOfAdd (S.liftQ f hS).toAddMonoidHom

@[simp] theorem quotientLiftMap_apply (S : Submodule ℤ M) (f : M →ₗ[ℤ] N)
    (hS : S ≤ LinearMap.ker f) (q : M ⧸ S) :
    quotientLiftMap S f hS q = S.liftQ f hS q := rfl

@[simp] theorem quotientLiftMap_mk (S : Submodule ℤ M) (f : M →ₗ[ℤ] N)
    (hS : S ≤ LinearMap.ker f) (x : M) :
    quotientLiftMap S f hS (Submodule.Quotient.mk x) = f x := rfl

/-- Surjectivity passes to the actual induced quotient map. -/
theorem quotientLift_surjective (S : Submodule ℤ M) (f : M →ₗ[ℤ] N)
    (hf : Function.Surjective f) (hS : S ≤ LinearMap.ker f) :
    Function.Surjective (S.liftQ f hS) := by
  intro y
  obtain ⟨x, rfl⟩ := hf y
  exact ⟨Submodule.Quotient.mk x, rfl⟩

section EqualRank

variable [Module.Free ℤ N] [Module.Finite ℤ N]

/-- Transport to the displayed free coordinates and use integral equal-rank surjectivity. -/
theorem quotientLift_bijective_of_finrank (S : Submodule ℤ M) {r : ℕ}
    (e : (M ⧸ S) ≃ₗ[ℤ] (Fin r → ℤ)) (f : M →ₗ[ℤ] N)
    (hf : Function.Surjective f) (hS : S ≤ LinearMap.ker f)
    (hrank : Module.finrank ℤ N = r) : Function.Bijective (S.liftQ f hS) := by
  let g : (Fin r → ℤ) →ₗ[ℤ] N := (quotientLiftMap S f hS).comp e.symm.toLinearMap
  have hgs : Function.Surjective g :=
    (quotientLift_surjective S f hf hS).comp e.symm.surjective
  have hgb : Function.Bijective g := by
    apply OrzechProperty.bijective_of_surjective_of_finrank_le g hgs
    rw [Module.finrank_fin_fun, hrank]
  refine ⟨?_, quotientLift_surjective S f hf hS⟩
  intro x y hxy
  apply e.injective
  apply hgb.injective
  change S.liftQ f hS (e.symm (e x)) = S.liftQ f hS (e.symm (e y))
  simpa only [LinearEquiv.symm_apply_apply] using hxy

/-- The actual map induced on the quotient is an integral linear equivalence. -/
def quotientLiftEquiv (S : Submodule ℤ M) {r : ℕ}
    (e : (M ⧸ S) ≃ₗ[ℤ] (Fin r → ℤ)) (f : M →ₗ[ℤ] N)
    (hf : Function.Surjective f) (hS : S ≤ LinearMap.ker f)
    (hrank : Module.finrank ℤ N = r) : (M ⧸ S) ≃ₗ[ℤ] N :=
  LinearEquiv.ofBijective (quotientLiftMap S f hS)
    (quotientLift_bijective_of_finrank S e f hf hS hrank)

@[simp] theorem quotientLiftEquiv_apply (S : Submodule ℤ M) {r : ℕ}
    (e : (M ⧸ S) ≃ₗ[ℤ] (Fin r → ℤ)) (f : M →ₗ[ℤ] N)
    (hf : Function.Surjective f) (hS : S ≤ LinearMap.ker f)
    (hrank : Module.finrank ℤ N = r) (q : M ⧸ S) :
    quotientLiftEquiv S e f hf hS hrank q = S.liftQ f hS q := rfl

@[simp] theorem quotientLiftEquiv_mk (S : Submodule ℤ M) {r : ℕ}
    (e : (M ⧸ S) ≃ₗ[ℤ] (Fin r → ℤ)) (f : M →ₗ[ℤ] N)
    (hf : Function.Surjective f) (hS : S ≤ LinearMap.ker f)
    (hrank : Module.finrank ℤ N = r) (x : M) :
    quotientLiftEquiv S e f hf hS hrank (Submodule.Quotient.mk x) = f x := rfl

/-- Equal finite free quotient rank makes the prescribed relations the exact kernel. -/
theorem kernel_eq_of_quotient_equiv (S : Submodule ℤ M) {r : ℕ}
    (e : (M ⧸ S) ≃ₗ[ℤ] (Fin r → ℤ)) (f : M →ₗ[ℤ] N)
    (hf : Function.Surjective f) (hS : S ≤ LinearMap.ker f)
    (hrank : Module.finrank ℤ N = r) : LinearMap.ker f = S := by
  apply le_antisymm ?_ hS
  intro x hx
  apply (Submodule.Quotient.mk_eq_zero S).mp
  apply (quotientLift_bijective_of_finrank S e f hf hS hrank).injective
  rw [Submodule.liftQ_apply, map_zero]
  exact hx

theorem mem_kernel_iff (S : Submodule ℤ M) {r : ℕ}
    (e : (M ⧸ S) ≃ₗ[ℤ] (Fin r → ℤ)) (f : M →ₗ[ℤ] N)
    (hf : Function.Surjective f) (hS : S ≤ LinearMap.ker f)
    (hrank : Module.finrank ℤ N = r) (x : M) : x ∈ LinearMap.ker f ↔ x ∈ S := by
  rw [kernel_eq_of_quotient_equiv S e f hf hS hrank]

theorem map_eq_zero_iff (S : Submodule ℤ M) {r : ℕ}
    (e : (M ⧸ S) ≃ₗ[ℤ] (Fin r → ℤ)) (f : M →ₗ[ℤ] N)
    (hf : Function.Surjective f) (hS : S ≤ LinearMap.ker f)
    (hrank : Module.finrank ℤ N = r) (x : M) : f x = 0 ↔ x ∈ S :=
  mem_kernel_iff S e f hf hS hrank x

end EqualRank

end Wikipedia.HopfProblem.CuspCentralHomology.SpecializationCoinvariants
