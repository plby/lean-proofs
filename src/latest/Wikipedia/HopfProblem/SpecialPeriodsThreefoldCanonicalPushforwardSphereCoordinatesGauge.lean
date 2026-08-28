import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPushforwardSphereCoordinates
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPowersLineBundleBasic
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalLineBundleGauge

/-!
# Comparing the actual sphere cotangent cocycle with the square base twist

The constant sign change in the infinity chart absorbs the minus sign in
the derivative of inversion.  This gives a holomorphic gauge between the
genuine cotangent cocycle and the square of the existing base-twist cocycle.
-/

open Set Topology Bundle TopologicalSpace
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.CanonicalGlobal.SphereCanonical

open RiemannSphere
open HolomorphicFunctionSheaf.SphereH1.NegativeOneFrames

/-- The finite coordinate is unchanged; the infinity coordinate changes sign. -/
noncomputable def chartSign : Bool → ℂˣ
  | false => 1
  | true => -1

@[simp] theorem chartSign_false : chartSign false = 1 := rfl

@[simp] theorem chartSign_true : chartSign true = -1 := rfl

/-- The original cotangent cocycle is holomorphically gauge-equivalent
to the square of the original infinity-ideal base twist. -/
noncomputable def squareGauge :
    CanonicalGlobalLineBundle.Gauge 𝓘(ℂ) data (BaseTwist.data.power 2) where
  baseSet_eq := rfl
  value b _ := chartSign b
  compatible a b p _ := by
    cases a <;> cases b <;>
      simp [chartSign, HolomorphicCharacterBundle.TransitionData.power_transition,
        BaseTwist.data_transition, BaseTwist.transition, data_transition, transition,
        inv_neg, inv_pow]
  holomorphicOn _ := contMDiffOn_const

@[simp] theorem squareGauge_value (b : Bool) (p : RiemannSphere) :
    squareGauge.value b p = chartSign b := rfl

/-- In the actual finite chart the gauge leaves the scalar coefficient unchanged. -/
theorem squareGauge_finiteCoefficient (p : data.core.TotalSpace)
    (hp : p.proj ∈ finiteChart) :
    ((BaseTwist.data.power 2).core.localTriv false (squareGauge.map p)).2 =
      (data.core.localTriv false p).2 := by
  simpa only [squareGauge_value, chartSign_false, Units.val_one, one_mul] using
    squareGauge.map_localCoefficient false p hp

/-- In the actual infinity chart the gauge negates the scalar coefficient. -/
theorem squareGauge_infinityCoefficient (p : data.core.TotalSpace)
    (hp : p.proj ∈ infinityChart) :
    ((BaseTwist.data.power 2).core.localTriv true (squareGauge.map p)).2 =
      -(data.core.localTriv true p).2 := by
  simpa only [squareGauge_value, chartSign_true, Units.val_neg, Units.val_one,
    neg_one_mul] using squareGauge.map_localCoefficient true p hp

/-- The inverse has the same finite-chart coefficient formula. -/
theorem squareGauge_inv_finiteCoefficient (p : (BaseTwist.data.power 2).core.TotalSpace)
    (hp : p.proj ∈ finiteChart) :
    (data.core.localTriv false (squareGauge.invMap p)).2 =
      ((BaseTwist.data.power 2).core.localTriv false p).2 := by
  simpa only [squareGauge_value, chartSign_false, Units.val_one, inv_one, one_mul] using
    squareGauge.invMap_localCoefficient false p hp

/-- The inverse also negates the coefficient on the actual infinity chart. -/
theorem squareGauge_inv_infinityCoefficient (p : (BaseTwist.data.power 2).core.TotalSpace)
    (hp : p.proj ∈ infinityChart) :
    (data.core.localTriv true (squareGauge.invMap p)).2 =
      -((BaseTwist.data.power 2).core.localTriv true p).2 := by
  simpa only [squareGauge_value, chartSign_true, Units.val_neg, Units.val_one,
    inv_neg_one, neg_one_mul] using squareGauge.invMap_localCoefficient true p hp

end Wikipedia.HopfProblem.CanonicalGlobal.SphereCanonical
