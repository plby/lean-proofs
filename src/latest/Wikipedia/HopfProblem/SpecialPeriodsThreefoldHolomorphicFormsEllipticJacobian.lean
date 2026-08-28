import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsEllipticJacobianFlat
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsEllipticJacobianLift
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsEllipticJacobianChart

/-!
# The holomorphic, nowhere-zero native elliptic base Jacobian

The preferred charts of the actual root neighborhood and the original
upper half-plane are point-independent. Thus the actual derivative of
the original inverse elliptic chart varies holomorphically, including at
root zero. The local biholomorphism proved in the lift file gives its
nonvanishing without any assumed coordinate-conversion identities.
-/

noncomputable section

open UpperHalfPlane
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicForms.EllipticCover

open Elliptic HolomorphicDifferentialForms

local notation "I₁" => modelWithCornersSelf ℂ ℂ

/-- The genuine native derivative varies holomorphically on the entire
original root domain, with no change to either manifold atlas. -/
theorem baseLift_mfderiv_holomorphic (j : Kind) :
    ContMDiff I₁ 𝓘(ℂ, ℂ →L[ℂ] ℂ) ω
      (FlatDerivative.nativeDerivative (baseLift j)) :=
  FlatDerivative.nativeDerivative_holomorphic_of_constant_charts
    (fun _ _ => rfl) (fun _ _ => rfl) (baseLift j) (baseLift_holomorphic j)

/-- The scalar Jacobian extends holomorphically through root zero. -/
theorem baseJacobian_holomorphic (j : Kind) : ContMDiff I₁ I₁ ω (baseJacobian j) :=
  FlatDerivative.mfderiv_apply_one_holomorphic_of_constant_charts
    (fun _ _ => rfl) (fun _ _ => rfl) (baseLift j) (baseLift_holomorphic j)

/-- In the actual one-dimensional native tangent coordinates, the
differential is multiplication by its genuine scalar Jacobian. -/
theorem mfderiv_baseLift_apply (j : Kind) (z : Root j) (u : ℂ) :
    mfderiv I₁ I₁ (baseLift j) z u = baseJacobian j z * u := by
  let L : ℂ →L[ℂ] ℂ := mfderiv I₁ I₁ (baseLift j) z
  change L u = L 1 * u
  simpa only [smul_eq_mul, mul_one, mul_comm] using L.map_smul u (1 : ℂ)

theorem mfderiv_regularBase_apply (j : Kind) (z : RootStar j) (u : ℂ) :
    mfderiv I₁ I₁ (regularBase j) z u = baseJacobian j z.val * u := by
  have he := congrArg (fun L : ℂ →L[ℂ] ℂ => L u)
    (mfderiv_regularBase_eq_baseLift j z)
  exact he.trans (mfderiv_baseLift_apply j z.val u)

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicForms.EllipticCover
