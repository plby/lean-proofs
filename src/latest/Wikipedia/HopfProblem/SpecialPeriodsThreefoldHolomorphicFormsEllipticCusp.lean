import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsEllipticGlobal
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsCusp

/-!
# Cusp orders of the actual whole-plane coefficient extensions

The coefficient extensions across both complete elliptic orbits agree
with the coefficients of the original genuine global form. The actual
filled cusp therefore gives first analytic cusp order for each of them,
without any agreement, factorization, or growth premise.
-/

noncomputable section

open UpperHalfPlane
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicForms.EllipticExtension

open Elliptic HolomorphicDifferentialForms TriangleHolomorphicDifferentials

attribute [local instance] Threefold.chartedSpace Threefold.space_isManifold

/-- Each extended vertical one-form coefficient has first analytic cusp order. -/
theorem fibreOne_hasCuspOrder (θ : Form FamilyModel Threefold.Space 1) (i : Fin 2) :
    HasCuspOrder 1 (fun z => fibreOne θ z i) :=
  Cusp.fibreOne_hasCuspOrder_of_agree_regular θ i _
    (fun z => congrFun (fibreOne_restrict θ z) i)

/-- Each extended mixed two-form coefficient has first analytic cusp order. -/
theorem mixedTwo_hasCuspOrder (θ : Form FamilyModel Threefold.Space 2) (i : Fin 2) :
    HasCuspOrder 1 (fun z => mixedTwo θ z i) :=
  Cusp.mixedTwo_hasCuspOrder_of_agree_regular θ i _
    (fun z => congrFun (mixedTwo_restrict θ z) i)

/-- The extended top-form coefficient has first analytic cusp order. -/
theorem baseTop_hasCuspOrder (θ : Form FamilyModel Threefold.Space 3) :
    HasCuspOrder 1 (baseTop θ) :=
  Cusp.top_hasCuspOrder_of_agree_regular θ _ (baseTop_restrict θ)

/-- After the vertical coefficient vanishes, the extended base one-form
coefficient has first analytic cusp order. -/
theorem baseOne_hasCuspOrder (θ : Form FamilyModel Threefold.Space 1)
    (hc : ∀ z : TriangleRegularPoint, RegularCover.fibreOne θ z = 0) :
    HasCuspOrder 1 (baseOne θ hc) :=
  Cusp.baseOne_hasCuspOrder_of_agree_regular θ _ (baseOne_restrict θ hc)

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicForms.EllipticExtension
