import Wikipedia.HopfProblem.ThreefoldHomologyFinitenessAlgebra
import Mathlib.LinearAlgebra.FreeModule.PID

/-!
# Torsion-freeness in an actual integral exact sequence

An injective incoming map and torsion-free outer modules make the middle
module torsion-free.  No choice of a splitting, no surjectivity of the
outgoing map, and no rank calculation is required.  Finite generation
then gives freeness over the integers.
-/

noncomputable section

universe u

namespace Wikipedia.HopfProblem.ThreefoldHomologyTopCohomologyAlgebra

section IntegralDomain

variable {R : Type*} [CommRing R] [IsDomain R]
variable {A B C : Type u} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
  [Module R A] [Module R B] [Module R C]

/-- An extension of torsion-free modules over a domain is torsion-free, even
when the outgoing map is not onto its stated codomain. -/
theorem torsionFree_of_injective_exact (i : A →ₗ[R] B) (d : B →ₗ[R] C)
    (hi : Function.Injective i) (hex : Function.Exact i d)
    [Module.IsTorsionFree R A] [Module.IsTorsionFree R C] :
    Module.IsTorsionFree R B := by
  apply Module.IsTorsionFree.of_smul_eq_zero
  intro r b hrb
  by_cases hr : r = 0
  · exact Or.inl hr
  right
  have hd : d b = 0 := (smul_eq_zero_iff_right hr).mp (by
    rw [← map_smul, hrb, map_zero])
  obtain ⟨a, rfl⟩ := (hex b).mp hd
  have ha : r • a = 0 := hi (by rw [map_smul, hrb, map_zero])
  have ha₀ : a = 0 := (smul_eq_zero_iff_right hr).mp ha
  rw [ha₀, map_zero]

end IntegralDomain

variable {A B C : Type u} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
  [Module ℤ A] [Module ℤ B] [Module ℤ C]

/-- With finite outer modules, the same actual exact sequence has a free
middle integral module. -/
theorem free_of_injective_exact (i : A →ₗ[ℤ] B) (d : B →ₗ[ℤ] C)
    (hi : Function.Injective i) (hex : Function.Exact i d)
    [Module.Finite ℤ A] [Module.Finite ℤ C]
    [Module.IsTorsionFree ℤ A] [Module.IsTorsionFree ℤ C] :
    Module.Free ℤ B := by
  have := ThreefoldHomologyFinitenessAlgebra.finite_of_exact i d hex
  have := torsionFree_of_injective_exact i d hi hex
  infer_instance

end Wikipedia.HopfProblem.ThreefoldHomologyTopCohomologyAlgebra
