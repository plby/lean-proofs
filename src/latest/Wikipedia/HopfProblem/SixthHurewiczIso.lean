import Wikipedia.HopfProblem.SixthHurewiczInverse

/-!
# The actual sixth Hurewicz isomorphism

The forward maps are the original cubical Hurewicz maps and the inverse
is the constructed singular-chain descent. The connectivity inputs are
actual simple connectedness and triviality of the original native second
through fifth homotopy groups at the chosen base point.
-/

noncomputable section

open scoped Topology

namespace Wikipedia.HopfProblem.SixthHurewicz

open SingularMayerVietoris

variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
variable (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
  [Subsingleton (π_ 4 X x)] [Subsingleton (π_ 5 X x)]

/-- The original sixth Hurewicz map with its genuine constructed linear inverse. -/
def hurewiczLinearEquiv : Additive (π_ 6 X x) ≃ₗ[ℤ] SingularHomology X 6 :=
  LinearEquiv.ofLinearMap (hurewiczMap x) (hurewiczInverse x)
    (hurewiczMap_comp_hurewiczInverse x) (hurewiczInverse_comp_hurewiczMap x)

@[simp] theorem hurewiczLinearEquiv_toLinearMap :
    (hurewiczLinearEquiv x).toLinearMap = hurewiczMap x := rfl

@[simp] theorem hurewiczLinearEquiv_apply (a : Additive (π_ 6 X x)) :
    hurewiczLinearEquiv x a = hurewiczMap x a := rfl

@[simp] theorem hurewiczLinearEquiv_symm_apply (c : SingularHomology X 6) :
    (hurewiczLinearEquiv x).symm c = hurewiczInverse x c := rfl

/-- The same genuine equivalence on Mathlib's actual multiplicative native group. -/
def hurewiczPi6Equiv : π_ 6 X x ≃* Multiplicative (SingularHomology X 6) where
  __ := hurewiczPi6 x
  invFun c := Additive.toMul (hurewiczInverse x (Multiplicative.toAdd c))
  left_inv a := congrArg Additive.toMul
    (hurewiczInverse_hurewiczMap x (Additive.ofMul a))
  right_inv c := congrArg Multiplicative.ofAdd
    (hurewiczMap_hurewiczInverse x (Multiplicative.toAdd c))

@[simp] theorem hurewiczPi6Equiv_toMonoidHom :
    (hurewiczPi6Equiv x).toMonoidHom = hurewiczPi6 x := rfl

@[simp] theorem hurewiczPi6Equiv_apply (a : π_ 6 X x) :
    hurewiczPi6Equiv x a = hurewiczPi6 x a := rfl

@[simp] theorem hurewiczPi6Equiv_symm_apply (c : Multiplicative (SingularHomology X 6)) :
    (hurewiczPi6Equiv x).symm c =
      Additive.toMul (hurewiczInverse x (Multiplicative.toAdd c)) := rfl

end Wikipedia.HopfProblem.SixthHurewicz
