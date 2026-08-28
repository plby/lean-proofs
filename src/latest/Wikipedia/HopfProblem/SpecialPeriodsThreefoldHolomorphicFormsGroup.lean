import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsGroupCovariance
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsNormalForms

/-!
# Equations (9.8)--(9.10) for genuine global holomorphic forms

The normal forms have been proved for the actual derivative pullback of
each global form. Substitution in the actual all-group covector law gives
the full scalar pullback equations and the derivative-row condition,
without taking either a normal form or a covariance law as an input.
-/

noncomputable section

open scoped ContDiff Manifold Matrix

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicForms.RegularCover

open HolomorphicDifferentialForms (Form)
open PeriodFamilyHolomorphicForms (blockJacobian coordinateVolume)

attribute [local instance] chartedSpace coverChartedSpace cover_isManifold space_isManifold

/-- The full one-form equation uses the literal zero-vector coefficients
because their independence of the fibre vector is already proved. -/
theorem one_group_pullback (θ : Form Model Threefold.Space 1) (g : TriangleGroup)
    (z : TriangleRegularPoint) (ζ v : ComplexPlane₂) (t : ℂ) :
    baseOne θ (g • z) * (groupBaseDerivative g z * t) +
        dotProduct (fibreOne θ (g • z))
          (data.rightBlock g z *ᵥ v + t • (groupRightBlockDerivative g z *ᵥ ζ)) =
      baseOne θ z * t + dotProduct (fibreOne θ z) v := by
  simpa only [TrianglePeriodFamily.Data.complexLift, oneBase_eq_baseOne,
    oneFibre_eq_fibreOne] using one_complexLift_pullback θ g z ζ v t

/-- The derivative-row equation in (9.8) follows by varying the actual
fibre vector in the full pullback identity. -/
theorem fibreOne_group_derivative_covariance (θ : Form Model Threefold.Space 1)
    (g : TriangleGroup) (z : TriangleRegularPoint) :
    fibreOne θ (g • z) ᵥ* groupRightBlockDerivative g z = 0 :=
  PeriodFamilyHolomorphicForms.oneForm_derivative_covariance
    (baseOne θ) (fibreOne θ) (fun z => g • z) (groupBaseDerivative g)
    (data.rightBlock g) (groupRightBlockDerivative g) (one_group_pullback θ g) z

/-- All three equations (9.8), for every actual triangle-group element
and every genuine global holomorphic one-form. -/
theorem oneForm_group_covariance (θ : Form Model Threefold.Space 1)
    (g : TriangleGroup) (z : TriangleRegularPoint) :
    fibreOne θ (g • z) ᵥ* data.rightBlock g z = fibreOne θ z ∧
      baseOne θ (g • z) * groupBaseDerivative g z = baseOne θ z ∧
        fibreOne θ (g • z) ᵥ* groupRightBlockDerivative g z = 0 :=
  ⟨fibreOne_group_covariance θ g z, baseOne_group_covariance θ g z,
    fibreOne_group_derivative_covariance θ g z⟩

/-- The actual two-form has no vertical-area term. Its full scalar
pullback still records the actual base-dependent shear. -/
theorem two_group_pullback (θ : Form Model Threefold.Space 2) (g : TriangleGroup)
    (z : TriangleRegularPoint) (ζ v w : ComplexPlane₂) (t s : ℂ) :
    let v' := data.rightBlock g z *ᵥ v + t • (groupRightBlockDerivative g z *ᵥ ζ)
    let w' := data.rightBlock g z *ᵥ w + s • (groupRightBlockDerivative g z *ᵥ ζ)
    (groupBaseDerivative g z * t) * dotProduct (mixedTwo θ (g • z)) w' -
        (groupBaseDerivative g z * s) * dotProduct (mixedTwo θ (g • z)) v' =
      t * dotProduct (mixedTwo θ z) w - s * dotProduct (mixedTwo θ z) v := by
  have h := two_complexLift_pullback θ g z ζ v w t s
  dsimp only at h ⊢
  simpa only [TrianglePeriodFamily.Data.complexLift, twoVertical_eq_zero,
    twoMixed_eq_mixedTwo, zero_mul, zero_add] using h

/-- The top-form equation (9.10) before evaluation on the ordered basis,
with the actual normal-form coefficient at every fibre vector. -/
theorem top_group_pullback (θ : Form Model Threefold.Space 3) (g : TriangleGroup)
    (z : TriangleRegularPoint) (ζ : ComplexPlane₂) (u v w : Model) :
    baseTop θ (g • z) * coordinateVolume
      (blockJacobian (groupBaseDerivative g z) (data.rightBlock g z)
        (groupRightBlockDerivative g z *ᵥ ζ) u)
      (blockJacobian (groupBaseDerivative g z) (data.rightBlock g z)
        (groupRightBlockDerivative g z *ᵥ ζ) v)
      (blockJacobian (groupBaseDerivative g z) (data.rightBlock g z)
        (groupRightBlockDerivative g z *ᵥ ζ) w) =
      baseTop θ z * coordinateVolume u v w := by
  simpa only [TrianglePeriodFamily.Data.complexLift, top_eq_baseTop] using
    top_complexLift_pullback θ g z ζ u v w

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicForms.RegularCover
