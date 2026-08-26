import ErdosProblems.Erdos394.FiniteIndexBasis
import Mathlib.LinearAlgebra.Isomorphisms

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Finite-index kernel lattices from surjective residue maps
-/

open Module Submodule

namespace Erdos394

/-- A surjective integer-linear map to a finite module identifies the quotient
by its kernel with the target, hence their natural cardinalities agree. -/
theorem kernel_quotient_natCard_eq
    {M : Type*} [AddCommGroup M] [Module ℤ M] [Finite M]
    (f : (Fin 2 → ℤ) →ₗ[ℤ] M) (hf : Function.Surjective f) :
    Nat.card ((Fin 2 → ℤ) ⧸ LinearMap.ker f) = Nat.card M := by
  exact Nat.card_congr (f.quotKerEquivOfSurjective hf).toEquiv

/-- The quotient by such a kernel is finite. -/
theorem finite_quotient_kernel_of_finite_surjective
    {M : Type*} [AddCommGroup M] [Module ℤ M] [Finite M]
    (f : (Fin 2 → ℤ) →ₗ[ℤ] M) (hf : Function.Surjective f) :
    Finite ((Fin 2 → ℤ) ⧸ LinearMap.ker f) := by
  exact Finite.of_equiv M (f.quotKerEquivOfSurjective hf).toEquiv.symm

/-- Consequently every surjective finite residue map supplies a two-element
integer basis of its kernel lattice. -/
noncomputable def kernelFinTwoBasis
    {M : Type*} [AddCommGroup M] [Module ℤ M] [Finite M]
    (f : (Fin 2 → ℤ) →ₗ[ℤ] M) (hf : Function.Surjective f) :
    Basis (Fin 2) ℤ (LinearMap.ker f) := by
  letI : Finite ((Fin 2 → ℤ) ⧸ LinearMap.ker f) :=
    finite_quotient_kernel_of_finite_surjective f hf
  exact finiteIndexBasis (LinearMap.ker f)

end Erdos394
