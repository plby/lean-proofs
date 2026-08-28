import Wikipedia.HopfProblem.PeriodFamilyHolomorphicDifferentialFormsCovarianceAction
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicDifferentialFormsCovarianceDerivatives

/-!
# Lemma 9.15 covariance for arbitrary genuine local forms

The only form-invariance hypothesis is equality of actual derivative
pullbacks under the original restricted family map. The native covering
Jacobian is proved from that actual map. Evaluating the already proved
normal forms on this Jacobian gives the full scalar pullback identities,
and hence equations (9.8)--(9.10), with the original right block and its
genuine derivative.
-/

noncomputable section

open scoped ContDiff Manifold Matrix

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicDifferentialForms.Covariance

open SpecialPeriods
open PeriodFamilyHolomorphicForms (blockJacobian coordinateVolume)

attribute [local instance] familyChartedSpace coverChartedSpace family_isManifold cover_isManifold

variable (U : TopologicalSpace.Opens UpperHalfPlane)

/-- Whole-covector invariance with the actual native block derivative written out. -/
theorem nativeCoefficients_complexLift_block {p : ℕ} (θ : Form U p)
    (g : TriangleGroup) (hg : Preserves U g) (hθ : IsInvariant U θ g hg)
    (x : Cover U) (v : Fin p → Model) :
    nativeCoefficients U θ (complexLift U g hg x)
      (fun i => blockJacobian (baseDerivative U g hg x.1) (rightBlock U g x.1)
        (rightBlockDerivative U g x.1 *ᵥ x.2) (v i)) = nativeCoefficients U θ x v := by
  simpa only [complexLift_mfderiv_apply, blockJacobian] using
    nativeCoefficients_complexLift U θ g hg hθ x v

/-- The full one-form pullback identity follows from the genuine native
form invariance and the proved arbitrary-local-form normal form. -/
theorem one_pullback (θ : Form U 1) (g : TriangleGroup) (hg : Preserves U g)
    (hθ : IsInvariant U θ g hg) (z : U) (ζ v : ComplexPlane₂) (t : ℂ) :
    baseOne U θ (baseMap U g hg z) * (baseDerivative U g hg z * t) +
      dotProduct (fibreOne U θ (baseMap U g hg z))
        (rightBlock U g z *ᵥ v + t • (rightBlockDerivative U g z *ᵥ ζ)) =
      baseOne U θ z * t + dotProduct (fibreOne U θ z) v := by
  let J := blockJacobian (baseDerivative U g hg z) (rightBlock U g z)
    (rightBlockDerivative U g z *ᵥ ζ)
  have h := nativeCoefficients_complexLift_block U θ g hg hθ (z, ζ) ![(t, v)]
  change nativeCoefficients U θ (complexLift U g hg (z, ζ))
      (fun i : Fin 1 => J (![(t, v)] i)) =
    nativeCoefficients U θ (z, ζ) ![(t, v)] at h
  have hv : (fun i : Fin 1 => J (![(t, v)] i)) = ![J (t, v)] := by
    funext i
    fin_cases i
    rfl
  rw [hv, HolomorphicDifferentialForms.Coordinates.one_evaluation,
    HolomorphicDifferentialForms.Coordinates.one_evaluation] at h
  change oneBase U θ (complexLift U g hg (z, ζ)) * (baseDerivative U g hg z * t) +
      dotProduct (oneFibre U θ (complexLift U g hg (z, ζ)))
        (rightBlock U g z *ᵥ v + t • (rightBlockDerivative U g z *ᵥ ζ)) =
    oneBase U θ (z, ζ) * t + dotProduct (oneFibre U θ (z, ζ)) v at h
  simpa only [complexLift, oneBase_eq_baseOne, oneFibre_eq_fibreOne] using h

/-- All three equations (9.8), including the vanishing derivative row,
for an arbitrary local form fixed by the actual restricted family map. -/
theorem oneForm_covariance (θ : Form U 1) (g : TriangleGroup) (hg : Preserves U g)
    (hθ : IsInvariant U θ g hg) (z : U) :
    fibreOne U θ (baseMap U g hg z) ᵥ* rightBlock U g z = fibreOne U θ z ∧
      baseOne U θ (baseMap U g hg z) * baseDerivative U g hg z = baseOne U θ z ∧
      fibreOne U θ (baseMap U g hg z) ᵥ* rightBlockDerivative U g z = 0 :=
  PeriodFamilyHolomorphicForms.oneForm_covariance (baseOne U θ) (fibreOne U θ)
    (baseMap U g hg) (baseDerivative U g hg) (rightBlock U g) (rightBlockDerivative U g)
    (one_pullback U θ g hg hθ) z

/-- The actual two-form has its proved vanishing vertical term. The full
pullback still records the actual base-dependent right-block correction. -/
theorem two_pullback (θ : Form U 2) (g : TriangleGroup) (hg : Preserves U g)
    (hθ : IsInvariant U θ g hg) (z : U) (ζ v w : ComplexPlane₂) (t s : ℂ) :
    let v' := rightBlock U g z *ᵥ v + t • (rightBlockDerivative U g z *ᵥ ζ)
    let w' := rightBlock U g z *ᵥ w + s • (rightBlockDerivative U g z *ᵥ ζ)
    (baseDerivative U g hg z * t) * dotProduct (mixedTwo U θ (baseMap U g hg z)) w' -
      (baseDerivative U g hg z * s) * dotProduct (mixedTwo U θ (baseMap U g hg z)) v' =
      t * dotProduct (mixedTwo U θ z) w - s * dotProduct (mixedTwo U θ z) v := by
  let J := blockJacobian (baseDerivative U g hg z) (rightBlock U g z)
    (rightBlockDerivative U g z *ᵥ ζ)
  have h := nativeCoefficients_complexLift_block U θ g hg hθ (z, ζ) ![(t, v), (s, w)]
  change nativeCoefficients U θ (complexLift U g hg (z, ζ))
      (fun i : Fin 2 => J (![(t, v), (s, w)] i)) =
    nativeCoefficients U θ (z, ζ) ![(t, v), (s, w)] at h
  have hv : (fun i : Fin 2 => J (![(t, v), (s, w)] i)) = ![J (t, v), J (s, w)] := by
    funext i
    fin_cases i <;> rfl
  rw [hv, HolomorphicDifferentialForms.Coordinates.two_evaluation,
    HolomorphicDifferentialForms.Coordinates.two_evaluation] at h
  let v' := rightBlock U g z *ᵥ v + t • (rightBlockDerivative U g z *ᵥ ζ)
  let w' := rightBlock U g z *ᵥ w + s • (rightBlockDerivative U g z *ᵥ ζ)
  change twoVertical U θ (complexLift U g hg (z, ζ)) *
      (v' 0 * w' 1 - v' 1 * w' 0) +
      (baseDerivative U g hg z * t) *
        dotProduct (twoMixed U θ (complexLift U g hg (z, ζ))) w' -
      (baseDerivative U g hg z * s) *
        dotProduct (twoMixed U θ (complexLift U g hg (z, ζ))) v' =
    twoVertical U θ (z, ζ) * (v 0 * w 1 - v 1 * w 0) +
      t * dotProduct (twoMixed U θ (z, ζ)) w -
      s * dotProduct (twoMixed U θ (z, ζ)) v at h
  dsimp only [v', w'] at h
  dsimp only
  simpa only [complexLift, twoVertical_eq_zero, twoMixed_eq_mixedTwo,
    zero_mul, zero_add] using h

/-- Equation (9.9) for the actual local mixed coefficient row. -/
theorem twoForm_covariance (θ : Form U 2) (g : TriangleGroup) (hg : Preserves U g)
    (hθ : IsInvariant U θ g hg) (z : U) :
    baseDerivative U g hg z •
      (mixedTwo U θ (baseMap U g hg z) ᵥ* rightBlock U g z) = mixedTwo U θ z := by
  apply PeriodFamilyHolomorphicForms.twoForm_covariance (fun _ : U => 0) (mixedTwo U θ)
    (baseMap U g hg) (baseDerivative U g hg) (rightBlock U g) (rightBlockDerivative U g) ?_ z
  intro z ζ v w t s
  simpa only [zero_mul, zero_add] using two_pullback U θ g hg hθ z ζ v w t s

/-- The genuine top-form pullback evaluates the original ordered coordinate
determinant on the proved native Jacobian of the actual map. -/
theorem three_pullback (θ : Form U 3) (g : TriangleGroup) (hg : Preserves U g)
    (hθ : IsInvariant U θ g hg) (z : U) (ζ : ComplexPlane₂) (u v w : Model) :
    baseTop U θ (baseMap U g hg z) * coordinateVolume
      (blockJacobian (baseDerivative U g hg z) (rightBlock U g z)
        (rightBlockDerivative U g z *ᵥ ζ) u)
      (blockJacobian (baseDerivative U g hg z) (rightBlock U g z)
        (rightBlockDerivative U g z *ᵥ ζ) v)
      (blockJacobian (baseDerivative U g hg z) (rightBlock U g z)
        (rightBlockDerivative U g z *ᵥ ζ) w) =
      baseTop U θ z * coordinateVolume u v w := by
  let J := blockJacobian (baseDerivative U g hg z) (rightBlock U g z)
    (rightBlockDerivative U g z *ᵥ ζ)
  have h := nativeCoefficients_complexLift_block U θ g hg hθ (z, ζ) ![u, v, w]
  change nativeCoefficients U θ (complexLift U g hg (z, ζ))
      (fun i : Fin 3 => J (![u, v, w] i)) = nativeCoefficients U θ (z, ζ) ![u, v, w] at h
  have hv : (fun i : Fin 3 => J (![u, v, w] i)) = ![J u, J v, J w] := by
    funext i
    fin_cases i <;> rfl
  rw [hv, HolomorphicDifferentialForms.Coordinates.top_evaluation,
    HolomorphicDifferentialForms.Coordinates.top_evaluation] at h
  change top U θ (complexLift U g hg (z, ζ)) * coordinateVolume (J u) (J v) (J w) =
    top U θ (z, ζ) * coordinateVolume u v w at h
  simpa only [complexLift, top_eq_baseTop] using h

/-- Equation (9.10), with the actual base Jacobian and original period determinant. -/
theorem threeForm_covariance (θ : Form U 3) (g : TriangleGroup) (hg : Preserves U g)
    (hθ : IsInvariant U θ g hg) (z : U) :
    baseTop U θ (baseMap U g hg z) * baseDerivative U g hg z *
      (rightBlock U g z).det = baseTop U θ z :=
  PeriodFamilyHolomorphicForms.threeForm_covariance (baseTop U θ) (baseMap U g hg)
    (baseDerivative U g hg) (rightBlock U g) (rightBlockDerivative U g)
    (three_pullback U θ g hg hθ) z

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicDifferentialForms.Covariance
