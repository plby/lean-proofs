import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsPeriods
import Wikipedia.HopfProblem.HolomorphicDifferentialFormsPeriodLaws

/-!
# Unconditional period laws of actual global forms

The pullback of any global holomorphic form is invariant under the
actual period translations because those translations fix the original
map to the threefold. Thus none of the scalar period laws are additional
assumptions on a global form.
-/

noncomputable section

open scoped ContDiff Manifold Matrix

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicForms.RegularCover

open HolomorphicDifferentialForms (Form)
open HolomorphicDifferentialForms.PeriodLaws
  (IsPeriodInvariant periodTranslation periodTranslation_holomorphic)
open PeriodFamilyHolomorphicForms (periodShift periodDerivative skewPeriod)

attribute [local instance] chartedSpace coverChartedSpace cover_isManifold space_isManifold

/-- The actual derivative pullback satisfies every original period law. -/
theorem globalCoverPullback_isPeriodInvariant {p : ℕ} (θ : Form Model Threefold.Space p) :
    IsPeriodInvariant data.periods (globalCoverPullback θ) := by
  intro ℓ
  apply HolomorphicDifferentialForms.pullback_deck
    globalCover globalCover_holomorphic
    (periodTranslation data.periods ℓ) (periodTranslation_holomorphic data.periods ℓ)
  funext x
  exact globalCover_add_period x.1 ℓ x.2

theorem oneFibre_periodic (θ : Form Model Threefold.Space 1)
    (z : TriangleRegularPoint) (ℓ : Lattice) (ζ : ComplexPlane₂) :
    oneFibre θ (z, ζ + periodShift data.periods z ℓ) = oneFibre θ (z, ζ) :=
  HolomorphicDifferentialForms.PeriodLaws.oneFibre_periodic data.periods
    (globalCoverPullback θ) (globalCoverPullback_isPeriodInvariant θ) z ℓ ζ

theorem oneBase_period_law (θ : Form Model Threefold.Space 1)
    (z : TriangleRegularPoint) (ℓ : Lattice) (ζ : ComplexPlane₂) :
    oneBase θ (z, ζ + periodShift data.periods z ℓ) +
      dotProduct (oneFibre θ (z, ζ + periodShift data.periods z ℓ))
        (periodDerivative data.periods z ℓ) = oneBase θ (z, ζ) :=
  HolomorphicDifferentialForms.PeriodLaws.oneBase_period_law data.periods
    (globalCoverPullback θ) (globalCoverPullback_isPeriodInvariant θ) z ℓ ζ

theorem twoVertical_periodic (θ : Form Model Threefold.Space 2)
    (z : TriangleRegularPoint) (ℓ : Lattice) (ζ : ComplexPlane₂) :
    twoVertical θ (z, ζ + periodShift data.periods z ℓ) = twoVertical θ (z, ζ) :=
  HolomorphicDifferentialForms.PeriodLaws.twoVertical_periodic data.periods
    (globalCoverPullback θ) (globalCoverPullback_isPeriodInvariant θ) z ℓ ζ

theorem twoMixed_period_law (θ : Form Model Threefold.Space 2)
    (z : TriangleRegularPoint) (ℓ : Lattice) (ζ : ComplexPlane₂) :
    twoMixed θ (z, ζ + periodShift data.periods z ℓ) +
      twoVertical θ (z, ζ + periodShift data.periods z ℓ) •
        skewPeriod (periodDerivative data.periods z ℓ) = twoMixed θ (z, ζ) :=
  HolomorphicDifferentialForms.PeriodLaws.twoMixed_period_law data.periods
    (globalCoverPullback θ) (globalCoverPullback_isPeriodInvariant θ) z ℓ ζ

theorem top_periodic (θ : Form Model Threefold.Space 3)
    (z : TriangleRegularPoint) (ℓ : Lattice) (ζ : ComplexPlane₂) :
    top θ (z, ζ + periodShift data.periods z ℓ) = top θ (z, ζ) :=
  HolomorphicDifferentialForms.PeriodLaws.top_periodic data.periods
    (globalCoverPullback θ) (globalCoverPullback_isPeriodInvariant θ) z ℓ ζ

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicForms.RegularCover
