import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.Topology.Homeomorph.Defs

/-!
# Pointed fundamental groups of homeomorphic spaces

The forward homomorphism of this equivalence is exactly the map induced by
the homeomorphism. Its inverse is induced by the inverse homeomorphism,
with the basepoint transported by `symm_apply_apply`.
-/

noncomputable section

namespace Wikipedia.HopfProblem

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- A homeomorphism identifies the actual fundamental groups at corresponding
basepoints, through its induced map on loop classes. -/
def homeomorphFundamentalGroupEquiv (e : X ≃ₜ Y) (x : X) :
    FundamentalGroup X x ≃* FundamentalGroup Y (e x) where
  __ := FundamentalGroup.map ⟨e, e.continuous⟩ x
  invFun := FundamentalGroup.mapOfEq ⟨e.symm, e.symm.continuous⟩
    (e.symm_apply_apply x)
  left_inv γ := by
    rw [FundamentalGroup.mapOfEq_apply]
    obtain ⟨γ⟩ := γ
    apply congrArg Path.Homotopic.Quotient.mk
    ext t
    exact e.symm_apply_apply (γ t)
  right_inv γ := by
    rw [FundamentalGroup.mapOfEq_apply]
    obtain ⟨γ⟩ := γ
    apply congrArg Path.Homotopic.Quotient.mk
    ext t
    exact e.apply_symm_apply (γ t)

@[simp] theorem homeomorphFundamentalGroupEquiv_toMonoidHom (e : X ≃ₜ Y) (x : X) :
    (homeomorphFundamentalGroupEquiv e x).toMonoidHom =
      FundamentalGroup.map ⟨e, e.continuous⟩ x := rfl

@[simp] theorem homeomorphFundamentalGroupEquiv_apply (e : X ≃ₜ Y) (x : X)
    (γ : FundamentalGroup X x) :
    homeomorphFundamentalGroupEquiv e x γ =
      FundamentalGroup.map ⟨e, e.continuous⟩ x γ := rfl

@[simp] theorem homeomorphFundamentalGroupEquiv_symm_apply (e : X ≃ₜ Y) (x : X)
    (γ : FundamentalGroup Y (e x)) :
    (homeomorphFundamentalGroupEquiv e x).symm γ =
      FundamentalGroup.mapOfEq ⟨e.symm, e.symm.continuous⟩
        (e.symm_apply_apply x) γ := rfl

end Wikipedia.HopfProblem
