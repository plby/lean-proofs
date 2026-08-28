import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsCuspComparison
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsCuspComparisonDerivative
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsCoefficients
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsEllipticBaseChangeCoefficients

/-!
# Genuine cusp-logarithmic and regular-cover form coefficients

Functoriality applied to the exact global covering diagram identifies the
full genuine pulled-back covectors. The actual comparison derivative scales
the base vector by the triangle width and fixes both fibre vectors. The
coefficient identities therefore hold at the actual regular covering point,
without any use of a fibre-independence or normal-form theorem.
-/

noncomputable section

open scoped ContDiff Manifold Matrix

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicForms.Cusp

open Wikipedia.HopfProblem.HolomorphicDifferentialForms
open Wikipedia.HopfProblem.HolomorphicDifferentialForms.Coordinates

local notation "EL" => ℂ × ComplexPlane₂
local notation "IL" => modelWithCornersSelf ℂ EL

attribute [local instance] Threefold.chartedSpace Threefold.space_isManifold
  RegularCover.coverChartedSpace RegularCover.cover_isManifold

/-- Functoriality identifies the genuine holomorphic forms, not just selected coefficients. -/
theorem logPullback_eq_regularPullback {p : ℕ} (θ : Form EL Threefold.Space p) :
    logPullback θ = pullback toRegularCover toRegularCover_holomorphic
      (RegularCover.globalCoverPullback θ) := by
  change pullback globalLogMap globalLogMap_holomorphic θ = _
  rw [pullback_congr globalLogMap_holomorphic
    (RegularCover.globalCover_holomorphic.comp toRegularCover_holomorphic)
    globalLogMap_eq_regularCover_comp]
  exact pullback_comp toRegularCover toRegularCover_holomorphic
    RegularCover.globalCover RegularCover.globalCover_holomorphic θ

/-- The full actual native covector comparison uses the proved native Jacobian. -/
theorem logCoefficients_eq_regularCoefficients {p : ℕ}
    (θ : Form EL Threefold.Space p) (x : LogDomain) :
    logCoefficients θ x =
      (RegularCover.nativeCoefficients θ (toRegularCover x)).compContinuousLinearMap
        baseWidthLinear := by
  ext v
  rw [logCoefficients_apply, logPullback_eq_regularPullback, pullback_apply]
  change RegularCover.globalCoverPullback θ (toRegularCover x)
      (fun j => mfderiv IL IL toRegularCover x (v j)) =
    RegularCover.nativeCoefficients θ (toRegularCover x)
      (fun j => baseWidthLinear (v j))
  rw [RegularCover.nativeCoefficients_apply, toRegularCover_mfderiv]
  rfl

/-- Evaluation on any tuple of actual tangent vectors in logarithmic coordinates. -/
theorem logCoefficients_regular_apply {p : ℕ} (θ : Form EL Threefold.Space p)
    (x : LogDomain) (v : Fin p → EL) :
    logCoefficients θ x v = RegularCover.nativeCoefficients θ (toRegularCover x)
      (fun j => ((Triangle.width : ℂ) * (v j).1, (v j).2)) := by
  rw [logCoefficients_eq_regularCoefficients]
  rfl

/-- The actual base one-form coefficient gains precisely the cusp width. -/
theorem log_oneBaseCoefficient (θ : Form EL Threefold.Space 1) (x : LogDomain) :
    oneBaseCoefficient (logCoefficients θ x) =
      (Triangle.width : ℂ) * RegularCover.oneBase θ (toRegularCover x) := by
  rw [logCoefficients_eq_regularCoefficients]
  exact EllipticBaseChange.oneBaseCoefficient_pullback _ _

/-- The two actual fibre one-form coefficients are unchanged. -/
theorem log_oneFibreCoefficient (θ : Form EL Threefold.Space 1) (x : LogDomain) :
    oneFibreCoefficient (logCoefficients θ x) =
      RegularCover.oneFibre θ (toRegularCover x) := by
  rw [logCoefficients_eq_regularCoefficients]
  exact EllipticBaseChange.oneFibreCoefficient_pullback _ _

/-- The actual vertical-area coefficient is unchanged. -/
theorem log_twoVerticalCoefficient (θ : Form EL Threefold.Space 2) (x : LogDomain) :
    twoVerticalCoefficient (logCoefficients θ x) =
      RegularCover.twoVertical θ (toRegularCover x) := by
  rw [logCoefficients_eq_regularCoefficients]
  exact EllipticBaseChange.twoVerticalCoefficient_pullback _ _

/-- Both actual mixed two-form coefficients gain precisely one cusp-width factor. -/
theorem log_twoMixedCoefficient (θ : Form EL Threefold.Space 2) (x : LogDomain) :
    twoMixedCoefficient (logCoefficients θ x) =
      (Triangle.width : ℂ) • RegularCover.twoMixed θ (toRegularCover x) := by
  rw [logCoefficients_eq_regularCoefficients]
  exact EllipticBaseChange.twoMixedCoefficient_pullback _ _

theorem log_twoMixedCoefficient_apply (θ : Form EL Threefold.Space 2)
    (x : LogDomain) (i : Fin 2) :
    twoMixedCoefficient (logCoefficients θ x) i =
      (Triangle.width : ℂ) * RegularCover.twoMixed θ (toRegularCover x) i :=
  congrFun (log_twoMixedCoefficient θ x) i

/-- The actual top coefficient also gains exactly one cusp-width factor. -/
theorem log_topCoefficient (θ : Form EL Threefold.Space 3) (x : LogDomain) :
    topCoefficient (logCoefficients θ x) =
      (Triangle.width : ℂ) * RegularCover.top θ (toRegularCover x) := by
  rw [logCoefficients_eq_regularCoefficients]
  exact EllipticBaseChange.topCoefficient_pullback _ _

/-- The full one-form evaluation on a base-plus-fibre vector retains both coefficients. -/
theorem log_one_base_fibre_evaluation (θ : Form EL Threefold.Space 1)
    (x : LogDomain) (i : Fin 2) :
    logCoefficients θ x ![((1, Pi.single i 1) : EL)] =
      (Triangle.width : ℂ) * RegularCover.oneBase θ (toRegularCover x) +
        RegularCover.oneFibre θ (toRegularCover x) i := by
  have hv : ((1, Pi.single i 1) : EL) = basis 0 + basis i.succ := by
    rw [EllipticShear.basis_zero, EllipticShear.basis_succ]
    simp only [Prod.mk_add_mk, add_zero, zero_add]
  rw [hv, (logCoefficients θ x).vecCons_add]
  change oneBaseCoefficient (logCoefficients θ x) +
    oneFibreCoefficient (logCoefficients θ x) i = _
  rw [log_oneBaseCoefficient, log_oneFibreCoefficient]

/-- A zero fibre vector maps to the actual regular zero section. -/
theorem toRegularCover_eq_zeroSection_of_fibre_zero (x : LogDomain) (hx : x.val.2 = 0) :
    toRegularCover x = RegularCover.zeroSection (toRegularCover x).1 := by
  apply Prod.ext
  · rfl
  · exact hx

/-- At the zero fibre vector the comparison uses the literal regular base coefficient. -/
theorem log_oneBaseCoefficient_zero_fibre (θ : Form EL Threefold.Space 1)
    (x : LogDomain) (hx : x.val.2 = 0) :
    oneBaseCoefficient (logCoefficients θ x) =
      (Triangle.width : ℂ) * RegularCover.baseOne θ (toRegularCover x).1 := by
  rw [log_oneBaseCoefficient, toRegularCover_eq_zeroSection_of_fibre_zero x hx]
  rfl

theorem log_twoMixedCoefficient_zero_fibre (θ : Form EL Threefold.Space 2)
    (x : LogDomain) (hx : x.val.2 = 0) :
    twoMixedCoefficient (logCoefficients θ x) =
      (Triangle.width : ℂ) • RegularCover.mixedTwo θ (toRegularCover x).1 := by
  rw [log_twoMixedCoefficient, toRegularCover_eq_zeroSection_of_fibre_zero x hx]
  rfl

theorem log_topCoefficient_zero_fibre (θ : Form EL Threefold.Space 3)
    (x : LogDomain) (hx : x.val.2 = 0) :
    topCoefficient (logCoefficients θ x) =
      (Triangle.width : ℂ) * RegularCover.baseTop θ (toRegularCover x).1 := by
  rw [log_topCoefficient, toRegularCover_eq_zeroSection_of_fibre_zero x hx]
  rfl

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicForms.Cusp
