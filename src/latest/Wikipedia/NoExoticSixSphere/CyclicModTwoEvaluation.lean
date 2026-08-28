import Wikipedia.NoExoticSixSphere.ModTwoCohomologyEvaluationInjective

/-!
# Evaluation of a mod-two functional on an actual integral generator

An integral marking identifies a functional with its value on the marked
primitive. The forward map is literal evaluation, not an independent
choice of a two-element model for the dual group.
-/

noncomputable section

namespace NoExoticSixSphere.ModTwoCohomologyEvaluation

variable {H : Type} [AddCommGroup H] [Module ℤ H]

/-- A functional on an infinite cyclic group is determined by its actual primitive value. -/
def cyclicFunctionalEquiv (e : H ≃ₗ[ℤ] ℤ) : (H →ₗ[ℤ] ZMod 2) ≃ₗ[ℤ] ZMod 2 :=
  ((e.arrowCongrAddEquiv (LinearEquiv.refl ℤ (ZMod 2))).trans
    (LinearMap.ringLmapEquivSelf ℤ ℤ (ZMod 2)).toAddEquiv).toIntLinearEquiv

theorem cyclicFunctionalEquiv_apply (e : H ≃ₗ[ℤ] ℤ) (φ : H →ₗ[ℤ] ZMod 2) :
    cyclicFunctionalEquiv e φ = φ (e.symm 1) := rfl

end NoExoticSixSphere.ModTwoCohomologyEvaluation
