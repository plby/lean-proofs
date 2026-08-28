import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsGroupAction
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsGroupDerivative
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsCoefficients
import Wikipedia.HopfProblem.HolomorphicDifferentialFormsCoordinateEvaluation

/-!
# Actual all-group covariance of the native regular-cover coefficients

The full scalar identities are evaluations of the actual invariant
alternating covectors on the actual block derivative. In particular,
the zero-vector coefficients obey their group laws without assuming
fibre independence or an independently specified form representation.
-/

noncomputable section

open scoped ContDiff Manifold Matrix

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicForms.RegularCover

open HolomorphicDifferentialForms (Form)
open PeriodFamilyHolomorphicForms (blockJacobian coordinateVolume)

attribute [local instance] chartedSpace coverChartedSpace cover_isManifold space_isManifold

local notation "IF" => modelWithCornersSelf ℂ Model

/-- The full genuine covector invariance, now with its proved native
block derivative written out. -/
theorem nativeCoefficients_complexLift_block {p : ℕ} (θ : Form Model Threefold.Space p)
    (g : TriangleGroup) (x : Cover) (v : Fin p → Model) :
    nativeCoefficients θ (data.complexLift g x)
      (fun i => blockJacobian (groupBaseDerivative g x.1) (data.rightBlock g x.1)
        (groupRightBlockDerivative g x.1 *ᵥ x.2) (v i)) =
      nativeCoefficients θ x v := by
  simpa only [complexLift_mfderiv_apply, blockJacobian] using
    nativeCoefficients_complexLift θ g x v

/-- The actual full one-covector pullback, before using fibre independence. -/
theorem one_complexLift_pullback (θ : Form Model Threefold.Space 1) (g : TriangleGroup)
    (z : TriangleRegularPoint) (ζ v : ComplexPlane₂) (t : ℂ) :
    oneBase θ (data.complexLift g (z, ζ)) * (groupBaseDerivative g z * t) +
        dotProduct (oneFibre θ (data.complexLift g (z, ζ)))
          (data.rightBlock g z *ᵥ v + t • (groupRightBlockDerivative g z *ᵥ ζ)) =
      oneBase θ (z, ζ) * t + dotProduct (oneFibre θ (z, ζ)) v := by
  let J := blockJacobian (groupBaseDerivative g z) (data.rightBlock g z)
    (groupRightBlockDerivative g z *ᵥ ζ)
  have h := nativeCoefficients_complexLift_block θ g (z, ζ) ![(t, v)]
  change nativeCoefficients θ (data.complexLift g (z, ζ))
      (fun i : Fin 1 => J (![(t, v)] i)) = nativeCoefficients θ (z, ζ) ![(t, v)] at h
  have hv : (fun i : Fin 1 => J (![(t, v)] i)) = ![J (t, v)] := by
    funext i
    fin_cases i
    rfl
  rw [hv, HolomorphicDifferentialForms.Coordinates.one_evaluation,
    HolomorphicDifferentialForms.Coordinates.one_evaluation] at h
  exact h

/-- The actual full two-covector pullback includes the vertical coefficient
and the complete base-dependent shear column. -/
theorem two_complexLift_pullback (θ : Form Model Threefold.Space 2) (g : TriangleGroup)
    (z : TriangleRegularPoint) (ζ v w : ComplexPlane₂) (t s : ℂ) :
    let v' := data.rightBlock g z *ᵥ v + t • (groupRightBlockDerivative g z *ᵥ ζ)
    let w' := data.rightBlock g z *ᵥ w + s • (groupRightBlockDerivative g z *ᵥ ζ)
    twoVertical θ (data.complexLift g (z, ζ)) * (v' 0 * w' 1 - v' 1 * w' 0) +
        (groupBaseDerivative g z * t) *
          dotProduct (twoMixed θ (data.complexLift g (z, ζ))) w' -
        (groupBaseDerivative g z * s) *
          dotProduct (twoMixed θ (data.complexLift g (z, ζ))) v' =
      twoVertical θ (z, ζ) * (v 0 * w 1 - v 1 * w 0) +
        t * dotProduct (twoMixed θ (z, ζ)) w - s * dotProduct (twoMixed θ (z, ζ)) v := by
  let J := blockJacobian (groupBaseDerivative g z) (data.rightBlock g z)
    (groupRightBlockDerivative g z *ᵥ ζ)
  have h := nativeCoefficients_complexLift_block θ g (z, ζ) ![(t, v), (s, w)]
  change nativeCoefficients θ (data.complexLift g (z, ζ))
      (fun i : Fin 2 => J (![(t, v), (s, w)] i)) =
    nativeCoefficients θ (z, ζ) ![(t, v), (s, w)] at h
  have hv : (fun i : Fin 2 => J (![(t, v), (s, w)] i)) = ![J (t, v), J (s, w)] := by
    funext i
    fin_cases i <;> rfl
  rw [hv, HolomorphicDifferentialForms.Coordinates.two_evaluation,
    HolomorphicDifferentialForms.Coordinates.two_evaluation] at h
  exact h

/-- The top-covector pullback is the actual ordered-coordinate determinant. -/
theorem top_complexLift_pullback (θ : Form Model Threefold.Space 3) (g : TriangleGroup)
    (z : TriangleRegularPoint) (ζ : ComplexPlane₂) (u v w : Model) :
    top θ (data.complexLift g (z, ζ)) * coordinateVolume
      (blockJacobian (groupBaseDerivative g z) (data.rightBlock g z)
        (groupRightBlockDerivative g z *ᵥ ζ) u)
      (blockJacobian (groupBaseDerivative g z) (data.rightBlock g z)
        (groupRightBlockDerivative g z *ᵥ ζ) v)
      (blockJacobian (groupBaseDerivative g z) (data.rightBlock g z)
        (groupRightBlockDerivative g z *ᵥ ζ) w) =
      top θ (z, ζ) * coordinateVolume u v w := by
  let J := blockJacobian (groupBaseDerivative g z) (data.rightBlock g z)
    (groupRightBlockDerivative g z *ᵥ ζ)
  have h := nativeCoefficients_complexLift_block θ g (z, ζ) ![u, v, w]
  change nativeCoefficients θ (data.complexLift g (z, ζ))
      (fun i : Fin 3 => J (![u, v, w] i)) = nativeCoefficients θ (z, ζ) ![u, v, w] at h
  have hv : (fun i : Fin 3 => J (![u, v, w] i)) = ![J u, J v, J w] := by
    funext i
    fin_cases i <;> rfl
  rw [hv, HolomorphicDifferentialForms.Coordinates.top_evaluation,
    HolomorphicDifferentialForms.Coordinates.top_evaluation] at h
  exact h

/-- Every actual fibre row transforms by the original all-word period matrix. -/
theorem oneFibre_complexLift_covariance (θ : Form Model Threefold.Space 1)
    (g : TriangleGroup) (z : TriangleRegularPoint) (ζ : ComplexPlane₂) :
    oneFibre θ (data.complexLift g (z, ζ)) ᵥ* data.rightBlock g z = oneFibre θ (z, ζ) := by
  funext i
  have h := one_complexLift_pullback θ g z ζ (Pi.single i 1) 0
  simpa only [mul_zero, zero_smul, add_zero, zero_add, Matrix.dotProduct_mulVec,
    dotProduct_single_one] using h

/-- Equation (9.8) for the literal zero-vector fibre coefficients. -/
theorem fibreOne_group_covariance (θ : Form Model Threefold.Space 1)
    (g : TriangleGroup) (z : TriangleRegularPoint) :
    fibreOne θ (g • z) ᵥ* data.rightBlock g z = fibreOne θ z := by
  simpa only [TrianglePeriodFamily.Data.complexLift, Matrix.mulVec_zero,
    fibreOne, zeroSection] using oneFibre_complexLift_covariance θ g z 0

/-- Equation (9.8) for the literal zero-vector base coefficient. -/
theorem baseOne_group_covariance (θ : Form Model Threefold.Space 1)
    (g : TriangleGroup) (z : TriangleRegularPoint) :
    baseOne θ (g • z) * groupBaseDerivative g z = baseOne θ z := by
  have h := one_complexLift_pullback θ g z 0 0 1
  simpa only [TrianglePeriodFamily.Data.complexLift, Matrix.mulVec_zero, smul_zero,
    add_zero, dotProduct_zero, mul_one, baseOne, zeroSection] using h

/-- Equation (9.9) for the literal zero-vector mixed coefficients. -/
theorem mixedTwo_group_covariance (θ : Form Model Threefold.Space 2)
    (g : TriangleGroup) (z : TriangleRegularPoint) :
    groupBaseDerivative g z • (mixedTwo θ (g • z) ᵥ* data.rightBlock g z) = mixedTwo θ z := by
  funext i
  have h := two_complexLift_pullback θ g z 0 0 (Pi.single i 1) 1 0
  dsimp only at h
  simpa only [TrianglePeriodFamily.Data.complexLift, Matrix.mulVec_zero,
    smul_zero, add_zero, zero_add, Pi.zero_apply, mul_zero, zero_mul,
    mul_one, one_mul, sub_zero, dotProduct_zero, Matrix.dotProduct_mulVec,
    dotProduct_single_one, Pi.smul_apply, smul_eq_mul, mixedTwo, zeroSection] using h

/-- The zero-vector vertical two-form coefficient transforms by the fibre determinant. -/
theorem verticalTwo_group_covariance (θ : Form Model Threefold.Space 2)
    (g : TriangleGroup) (z : TriangleRegularPoint) :
    verticalTwo θ (g • z) * (data.rightBlock g z).det = verticalTwo θ z := by
  have h := two_complexLift_pullback θ g z 0 (Pi.single (0 : Fin 2) 1)
    (Pi.single (1 : Fin 2) 1) 0 0
  dsimp only at h
  simpa [TrianglePeriodFamily.Data.complexLift, Matrix.det_fin_two, Matrix.mulVec,
    dotProduct, Fin.sum_univ_two, verticalTwo, zeroSection, mul_comm] using h

/-- The full top coefficient has the actual base-Jacobian and fibre-determinant factor. -/
theorem top_complexLift_covariance (θ : Form Model Threefold.Space 3)
    (g : TriangleGroup) (z : TriangleRegularPoint) (ζ : ComplexPlane₂) :
    top θ (data.complexLift g (z, ζ)) * groupBaseDerivative g z *
      (data.rightBlock g z).det = top θ (z, ζ) := by
  have h := top_complexLift_pullback θ g z ζ (1, 0)
    (0, Pi.single (0 : Fin 2) 1) (0, Pi.single (1 : Fin 2) 1)
  simpa only [PeriodFamilyHolomorphicForms.coordinateVolume_blockJacobian,
    PeriodFamilyHolomorphicForms.coordinateVolume_basis, mul_one, mul_assoc] using h

/-- Equation (9.10) for the literal zero-vector top coefficient. -/
theorem baseTop_group_covariance (θ : Form Model Threefold.Space 3)
    (g : TriangleGroup) (z : TriangleRegularPoint) :
    baseTop θ (g • z) * groupBaseDerivative g z * (data.rightBlock g z).det = baseTop θ z := by
  simpa only [TrianglePeriodFamily.Data.complexLift, Matrix.mulVec_zero,
    baseTop, zeroSection] using top_complexLift_covariance θ g z 0

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicForms.RegularCover
