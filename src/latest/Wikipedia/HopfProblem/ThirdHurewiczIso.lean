import Wikipedia.HopfProblem.ThirdHurewiczInverse

/-!
# The actual third Hurewicz isomorphism for a two-connected pointed space

The forward maps below are the original native cubical Hurewicz maps,
and the inverse is the constructed singular-chain descent. The only
connectivity inputs are actual simple connectedness and triviality of
Mathlib's native second homotopy group at the chosen base point.
-/

noncomputable section

open scoped Topology

namespace Wikipedia.HopfProblem.ThirdHurewicz

open SingularMayerVietoris

variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
variable (x : X) [Subsingleton (π_ 2 X x)]

/-- The original actual third Hurewicz map as an integral linear equivalence. -/
def hurewiczLinearEquiv : Additive (π_ 3 X x) ≃ₗ[ℤ] SingularHomology X 3 :=
  LinearEquiv.ofLinearMap (hurewiczMap x) (hurewiczInverse x)
    (hurewiczMap_comp_hurewiczInverse x) (hurewiczInverse_comp_hurewiczMap x)

@[simp] theorem hurewiczLinearEquiv_toLinearMap :
    (hurewiczLinearEquiv x).toLinearMap = hurewiczMap x := rfl

@[simp] theorem hurewiczLinearEquiv_apply (a : Additive (π_ 3 X x)) :
    hurewiczLinearEquiv x a = hurewiczMap x a := rfl

@[simp] theorem hurewiczLinearEquiv_symm_apply (c : SingularHomology X 3) :
    (hurewiczLinearEquiv x).symm c = hurewiczInverse x c := rfl

/-- The same genuine isomorphism on Mathlib's original multiplicative native group. -/
def hurewiczPi3Equiv : π_ 3 X x ≃* Multiplicative (SingularHomology X 3) where
  __ := hurewiczPi3 x
  invFun c := Additive.toMul (hurewiczInverse x (Multiplicative.toAdd c))
  left_inv a := congrArg Additive.toMul
    (hurewiczInverse_hurewiczMap x (Additive.ofMul a))
  right_inv c := congrArg Multiplicative.ofAdd
    (hurewiczMap_hurewiczInverse x (Multiplicative.toAdd c))

@[simp] theorem hurewiczPi3Equiv_toMonoidHom :
    (hurewiczPi3Equiv x).toMonoidHom = hurewiczPi3 x := rfl

@[simp] theorem hurewiczPi3Equiv_apply (a : π_ 3 X x) :
    hurewiczPi3Equiv x a = hurewiczPi3 x a := rfl

@[simp] theorem hurewiczPi3Equiv_symm_apply (c : Multiplicative (SingularHomology X 3)) :
    (hurewiczPi3Equiv x).symm c =
      Additive.toMul (hurewiczInverse x (Multiplicative.toAdd c)) := rfl

end Wikipedia.HopfProblem.ThirdHurewicz
