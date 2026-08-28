import Wikipedia.HopfProblem.DegreeCollapseRationalResidue
import Mathlib.Algebra.Category.Grp.Injective
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Extension and lifting for the actual rational coefficient sequence

The rational numbers and their literal quotient by the integer span of
one are injective integer modules. Integral-valued rational functionals
lift through the actual integer inclusion, and quotient-valued functionals
on projective modules lift through the actual rational quotient map.
-/

noncomputable section

open Function

namespace Wikipedia.HopfProblem.DegreeCollapse.RationalResidue

def integralCast : ℤ →ₗ[ℤ] ℚ := (Int.castAddHom ℚ).toIntLinearMap

theorem integralCast_injective : Injective integralCast := Int.cast_injective

theorem residue_surjective : Surjective residue := integers.mkQ_surjective

theorem injective_of_divisible (A : Type*) [AddCommGroup A] [Module ℤ A]
    [DivisibleBy A ℤ] : Module.Injective ℤ A := by
  cases Subsingleton.elim ‹Module ℤ A› (AddCommGroup.toIntModule A)
  exact (Module.Baer.of_divisible A).injective

instance rational_injective : Module.Injective ℤ ℚ := injective_of_divisible ℚ

instance residue_divisible : DivisibleBy Value ℤ :=
  residue_surjective.divisibleBy residue (fun x n ↦ map_zsmul residue n x)

instance residue_injective : Module.Injective ℤ Value := injective_of_divisible Value

theorem exists_integer_lift {M : Type*} [AddCommGroup M] [Module ℤ M]
    (f : M →ₗ[ℤ] ℚ) (hf : ∀ x, residue (f x) = 0) :
    ∃ g : M →ₗ[ℤ] ℤ, integralCast.comp g = f := by
  let e := LinearEquiv.ofInjective integralCast integralCast_injective
  have hr : ∀ x, f x ∈ LinearMap.range integralCast := by
    intro x
    obtain ⟨k, hk⟩ := (residue_eq_zero_iff (f x)).mp (hf x)
    exact ⟨k, hk⟩
  let r := f.codRestrict (LinearMap.range integralCast) hr
  refine ⟨e.symm.toLinearMap.comp r, ?_⟩
  ext x
  exact congrArg Subtype.val (e.apply_symm_apply (r x))

theorem exists_rational_lift {M : Type*} [AddCommGroup M] [Module ℤ M]
    [Module.Projective ℤ M] (f : M →ₗ[ℤ] Value) :
    ∃ g : M →ₗ[ℤ] ℚ, residue.comp g = f :=
  Module.projective_lifting_property residue f residue_surjective

end Wikipedia.HopfProblem.DegreeCollapse.RationalResidue
