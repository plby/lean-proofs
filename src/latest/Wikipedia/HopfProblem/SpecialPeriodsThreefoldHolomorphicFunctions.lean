import Wikipedia.HopfProblem.SpecialPeriodsThreefoldConnected
import Mathlib.Geometry.Manifold.Complex
import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions

/-!
# Global holomorphic functions on the actual compact threefold

The compact maximum principle applies to the constructed connected
threefold in its native glued complex atlas. Evaluation identifies its
actual algebra of global holomorphic functions with the complex numbers.
The sphere projection, in contrast, is nonconstant by its proved
surjectivity. No claim about higher sheaf cohomology is made here.
-/

noncomputable section

open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold

attribute [local instance] chartedSpace space_compact space_connected space_isManifold

local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)

/-- Constancy concerns actual maps on the constructed manifold. -/
theorem holomorphic_apply_eq {f : Space → ℂ}
    (hf : ContMDiff IF 𝓘(ℂ) ω f) (x y : Space) : f x = f y :=
  (hf.mdifferentiable (by simp)).apply_eq_of_compactSpace x y

theorem holomorphic_eq_const {f : Space → ℂ}
    (hf : ContMDiff IF 𝓘(ℂ) ω f) : ∃ c : ℂ, f = Function.const Space c :=
  (hf.mdifferentiable (by simp)).exists_eq_const_of_compactSpace

/-- The genuine algebra of global holomorphic functions, with pointwise
operations inherited from Mathlib's bundled manifold maps. -/
abbrev HolomorphicFunction := C^ω⟮IF, Space; ℂ⟯

/-- Evaluation is an algebra homomorphism, not just a vector-space marking. -/
def holomorphicFunctionEval (x : Space) : HolomorphicFunction →ₐ[ℂ] ℂ where
  toFun f := f x
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

@[simp] theorem holomorphicFunctionEval_apply (x : Space) (f : HolomorphicFunction) :
    holomorphicFunctionEval x f = f x := rfl

theorem holomorphicFunctionEval_injective (x : Space) :
    Function.Injective (holomorphicFunctionEval x) := by
  intro f g h
  apply ContMDiffMap.ext
  intro y
  calc
    f y = f x := holomorphic_apply_eq f.contMDiff y x
    _ = g x := h
    _ = g y := holomorphic_apply_eq g.contMDiff x y

theorem holomorphicFunctionEval_surjective (x : Space) :
    Function.Surjective (holomorphicFunctionEval x) := by
  intro c
  exact ⟨ContMDiffMap.const c, rfl⟩

/-- Evaluation at any point identifies the actual holomorphic-function
algebra of the threefold with `ℂ`. -/
def holomorphicFunctionEvalEquiv (x : Space) : HolomorphicFunction ≃ₐ[ℂ] ℂ :=
  AlgEquiv.ofBijective (holomorphicFunctionEval x)
    ⟨holomorphicFunctionEval_injective x, holomorphicFunctionEval_surjective x⟩

@[simp] theorem holomorphicFunctionEvalEquiv_apply (x : Space)
    (f : HolomorphicFunction) : holomorphicFunctionEvalEquiv x f = f x := rfl

@[simp] theorem holomorphicFunctionEvalEquiv_symm_apply (x : Space) (c : ℂ) :
    (holomorphicFunctionEvalEquiv x).symm c = ContMDiffMap.const c := by
  apply (holomorphicFunctionEvalEquiv x).injective
  simp only [AlgEquiv.apply_symm_apply, holomorphicFunctionEvalEquiv_apply]
  rfl

theorem holomorphicFunction_finrank : Module.finrank ℂ HolomorphicFunction = 1 := by
  let x : Space := Classical.choice space_nonempty
  rw [(holomorphicFunctionEvalEquiv x).toLinearEquiv.finrank_eq]
  exact Module.finrank_self ℂ

/-- The map to the sphere is genuinely nonconstant on the same compact
threefold whose complex-valued holomorphic functions are constant. -/
theorem projectionSphere_exists_ne :
    ∃ x y : Space, projectionSphere x ≠ projectionSphere y := by
  obtain ⟨a, b, hab⟩ := exists_pair_ne RiemannSphere
  obtain ⟨x, rfl⟩ := projectionSphere_surjective a
  obtain ⟨y, rfl⟩ := projectionSphere_surjective b
  exact ⟨x, y, hab⟩

theorem projectionSphere_not_constant :
    ¬ ∃ b : RiemannSphere, projectionSphere = Function.const Space b := by
  rintro ⟨b, hb⟩
  obtain ⟨x, y, hxy⟩ := projectionSphere_exists_ne
  apply hxy
  rw [hb]
  rfl

end Wikipedia.HopfProblem.SpecialPeriods.Threefold
