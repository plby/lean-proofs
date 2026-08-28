import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# The kernel of the first coordinate of an actual splitting

An additive splitting with first coordinate equal to a specified linear
projection restricts to an integral linear equivalence from its kernel
to the second coordinate. No cancellation of an unknown isomorphism is
used in this restriction.
-/

noncomputable section

namespace NoExoticSixSphere.SplitProjectionKernel

variable {M A B : Type*} [AddCommGroup M] [AddCommGroup A] [AddCommGroup B]
    [Module ℤ M] [Module ℤ A] [Module ℤ B]
    (E : M ≃+ A × B) (p : M →ₗ[ℤ] A) [Module ℤ (LinearMap.ker p)]
    (hp : ∀ a, (E a).1 = p a)

def equiv : LinearMap.ker p ≃ₗ[ℤ] B := by
  let e : LinearMap.ker p ≃+ B :=
    { toFun := fun a ↦ (E a.val).2
      invFun := fun b ↦ ⟨E.symm (0, b), by
        change p (E.symm (0, b)) = 0
        rw [← hp, E.apply_symm_apply]⟩
      left_inv := by
        intro a
        apply Subtype.ext
        apply E.injective
        rw [E.apply_symm_apply]
        apply Prod.ext
        · exact (hp a.val).trans a.property |>.symm
        · rfl
      right_inv := fun b ↦ congrArg Prod.snd (E.apply_symm_apply (0, b))
      map_add' := fun a b ↦ congrArg Prod.snd (E.map_add a.val b.val) }
  exact e.toIntLinearEquiv

theorem equiv_apply (a : LinearMap.ker p) : equiv E p hp a = (E a.val).2 := rfl

end NoExoticSixSphere.SplitProjectionKernel
