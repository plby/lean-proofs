import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedInverseLeft

/-!
# The second Hurewicz isomorphism on the original native types

For a simply connected topological space and an actual base point, the
previously constructed native Hurewicz homomorphism is an isomorphism.
Both inverses below are the actual normalized-triangle descent. No CW,
separation, manifold, or higher homotopy comparison hypothesis is used.
-/

noncomputable section

open scoped Topology

namespace Wikipedia.HopfProblem.SecondHurewicz.SimplyConnected

open SingularMayerVietoris

variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]

/-- Integral linear equivalence whose forward map is the original actual
Hurewicz map and whose inverse is the constructed singular-chain descent. -/
def hurewiczLinearEquiv (x : X) : Additive (π_ 2 X x) ≃ₗ[ℤ] SingularHomology X 2 :=
  LinearEquiv.ofLinearMap (hurewiczMap x) (hurewiczInverse x)
    (hurewiczMap_comp_hurewiczInverse x) (hurewiczInverse_comp_hurewiczMap x)

@[simp] theorem hurewiczLinearEquiv_toLinearMap (x : X) :
    (hurewiczLinearEquiv x).toLinearMap = hurewiczMap x := rfl

@[simp] theorem hurewiczLinearEquiv_apply (x : X) (a : Additive (π_ 2 X x)) :
    hurewiczLinearEquiv x a = hurewiczMap x a := rfl

@[simp] theorem hurewiczLinearEquiv_symm_apply (x : X) (c : SingularHomology X 2) :
    (hurewiczLinearEquiv x).symm c = hurewiczInverse x c := rfl

/-- The same isomorphism in Mathlib's original multiplicative notation for
its native second homotopy group. -/
def hurewiczPi2Equiv (x : X) : π_ 2 X x ≃* Multiplicative (SingularHomology X 2) where
  __ := hurewiczPi2 x
  invFun c := Additive.toMul (hurewiczInverse x (Multiplicative.toAdd c))
  left_inv a := congrArg Additive.toMul
    (hurewiczInverse_hurewiczMap x (Additive.ofMul a))
  right_inv c := congrArg Multiplicative.ofAdd
    (hurewiczMap_hurewiczInverse x (Multiplicative.toAdd c))

@[simp] theorem hurewiczPi2Equiv_toMonoidHom (x : X) :
    (hurewiczPi2Equiv x).toMonoidHom = hurewiczPi2 x := rfl

@[simp] theorem hurewiczPi2Equiv_apply (x : X) (a : π_ 2 X x) :
    hurewiczPi2Equiv x a = hurewiczPi2 x a := rfl

@[simp] theorem hurewiczPi2Equiv_symm_apply (x : X)
    (c : Multiplicative (SingularHomology X 2)) :
    (hurewiczPi2Equiv x).symm c =
      Additive.toMul (hurewiczInverse x (Multiplicative.toAdd c)) := rfl

end Wikipedia.HopfProblem.SecondHurewicz.SimplyConnected
