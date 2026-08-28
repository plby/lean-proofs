import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsCuspComparisonForms
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsNormalForms

/-!
# The actual base coefficients on the full logarithmic cusp cover

Combining the native comparison with the proved regular-family normal forms
removes the fibre vector from the coefficient formulas. All assertions apply
to arbitrary genuine global holomorphic forms and every point of the original
logarithmic cover, including the nonzero fibre vectors used along cusp axes.
-/

noncomputable section

open scoped ContDiff Manifold Matrix

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicForms.Cusp

open Wikipedia.HopfProblem.HolomorphicDifferentialForms
open Wikipedia.HopfProblem.HolomorphicDifferentialForms.Coordinates

local notation "EL" => ℂ × ComplexPlane₂

attribute [local instance] Threefold.chartedSpace Threefold.space_isManifold
  RegularCover.coverChartedSpace RegularCover.cover_isManifold

/-- The genuine logarithmic base one-form coefficient is the actual base coefficient times width. -/
theorem log_oneBaseCoefficient_eq_baseOne (θ : Form EL Threefold.Space 1)
    (x : LogDomain) :
    oneBaseCoefficient (logCoefficients θ x) =
      (Triangle.width : ℂ) * RegularCover.baseOne θ (toRegularCover x).1 := by
  rw [log_oneBaseCoefficient]
  exact congrArg (fun a : ℂ => (Triangle.width : ℂ) * a)
    (RegularCover.oneBase_eq_baseOne θ (toRegularCover x).1 (toRegularCover x).2)

/-- Both genuine logarithmic fibre coefficients are the actual fibre-independent base values. -/
theorem log_oneFibreCoefficient_eq_fibreOne (θ : Form EL Threefold.Space 1)
    (x : LogDomain) :
    oneFibreCoefficient (logCoefficients θ x) =
      RegularCover.fibreOne θ (toRegularCover x).1 :=
  (log_oneFibreCoefficient θ x).trans
    (RegularCover.oneFibre_eq_fibreOne θ (toRegularCover x).1 (toRegularCover x).2)

/-- The actual vertical-area coefficient vanishes throughout the logarithmic cover. -/
theorem log_twoVerticalCoefficient_eq_zero (θ : Form EL Threefold.Space 2)
    (x : LogDomain) : twoVerticalCoefficient (logCoefficients θ x) = 0 :=
  (log_twoVerticalCoefficient θ x).trans
    (RegularCover.twoVertical_eq_zero θ (toRegularCover x).1 (toRegularCover x).2)

/-- The actual mixed coefficients are the base covector times precisely one width factor. -/
theorem log_twoMixedCoefficient_eq_mixedTwo (θ : Form EL Threefold.Space 2)
    (x : LogDomain) :
    twoMixedCoefficient (logCoefficients θ x) =
      (Triangle.width : ℂ) • RegularCover.mixedTwo θ (toRegularCover x).1 := by
  rw [log_twoMixedCoefficient]
  exact congrArg (fun a : ComplexPlane₂ => (Triangle.width : ℂ) • a)
    (RegularCover.twoMixed_eq_mixedTwo θ (toRegularCover x).1 (toRegularCover x).2)

theorem log_twoMixedCoefficient_eq_mixedTwo_apply (θ : Form EL Threefold.Space 2)
    (x : LogDomain) (i : Fin 2) :
    twoMixedCoefficient (logCoefficients θ x) i =
      (Triangle.width : ℂ) * RegularCover.mixedTwo θ (toRegularCover x).1 i :=
  congrFun (log_twoMixedCoefficient_eq_mixedTwo θ x) i

/-- The actual logarithmic top coefficient is the base coefficient times the cusp width. -/
theorem log_topCoefficient_eq_baseTop (θ : Form EL Threefold.Space 3) (x : LogDomain) :
    topCoefficient (logCoefficients θ x) =
      (Triangle.width : ℂ) * RegularCover.baseTop θ (toRegularCover x).1 := by
  rw [log_topCoefficient]
  exact congrArg (fun a : ℂ => (Triangle.width : ℂ) * a)
    (RegularCover.top_eq_baseTop θ (toRegularCover x).1 (toRegularCover x).2)

/-- Along a base-plus-fibre direction, both terms use the same actual base point. -/
theorem log_one_base_fibre_evaluation_normalForm (θ : Form EL Threefold.Space 1)
    (x : LogDomain) (i : Fin 2) :
    logCoefficients θ x ![((1, Pi.single i 1) : EL)] =
      (Triangle.width : ℂ) * RegularCover.baseOne θ (toRegularCover x).1 +
        RegularCover.fibreOne θ (toRegularCover x).1 i := by
  have h := log_one_base_fibre_evaluation θ x i
  have hb : RegularCover.oneBase θ (toRegularCover x) =
      RegularCover.baseOne θ (toRegularCover x).1 :=
    RegularCover.oneBase_eq_baseOne θ (toRegularCover x).1 (toRegularCover x).2
  have hf : RegularCover.oneFibre θ (toRegularCover x) =
      RegularCover.fibreOne θ (toRegularCover x).1 :=
    RegularCover.oneFibre_eq_fibreOne θ (toRegularCover x).1 (toRegularCover x).2
  rw [hb, hf] at h
  exact h

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicForms.Cusp
