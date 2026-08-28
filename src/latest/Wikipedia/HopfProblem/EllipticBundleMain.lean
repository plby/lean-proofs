import Wikipedia.HopfProblem.EllipticBundleCanonical
import Wikipedia.HopfProblem.EllipticBundleCanonicalFixed
import Wikipedia.HopfProblem.EllipticBundleNormalOrders
import Wikipedia.HopfProblem.EllipticBundleNormalContinuous

/-!
# Bundle orders for the source's chosen elliptic twists

These conclusions concern the already constructed central surfaces and
their actual analytic bundle cores. The twists are the source's specified
ones, and their freeness and admissibility hypotheses have been discharged.
Order is expressed by the least positive analytically trivial tensor-power
degree; no separately constructed Picard-group object is asserted.
-/

noncomputable section

open Set
open scoped ContDiff

namespace Wikipedia.HopfProblem.Elliptic

open HolomorphicCharacterBundle

local notation "IS" => modelWithCornersSelf ℂ ComplexPlane₂

/-- On each of the two actual central surfaces, the canonical power is
analytically trivial precisely at the multiples of three or four. -/
theorem mainCentralCanonical_power_trivial_iff (j : Kind) (n : ℕ) :
    Nonempty (TransitionData.AnalyticTrivialization
      (CanonicalBundle.centralPowerData j j.twist (mainTwist_admissible j) n) IS) ↔ j.order ∣ n :=
  CanonicalBundle.centralPower_analyticTrivialization_iff j j.twist (mainTwist_admissible j) n

/-- The exact canonical order for the source's chosen twist, with no
remaining period, twist, or bundle-identification assumption. -/
theorem mainCentralCanonical_order_isLeast (j : Kind) :
    IsLeast {n : ℕ | 0 < n ∧
      Nonempty (TransitionData.AnalyticTrivialization
        (CanonicalBundle.centralPowerData j j.twist (mainTwist_admissible j) n) IS)} j.order :=
  CanonicalBundle.centralPower_order_isLeast j j.twist (mainTwist_admissible j)

/-- The normal line of the actual central immersion has exactly the same
trivial-power degrees, computed from its genuine tangent quotient. -/
theorem mainCentralNormal_power_trivial_iff (j : Kind) (n : ℕ) :
    Nonempty (TransitionData.AnalyticTrivialization
      (NormalBundle.powerData j j.twist (mainTwist_admissible j) n) IS) ↔ j.order ∣ n :=
  NormalBundle.power_analyticTrivialization_iff j j.twist (mainTwist_admissible j) n

theorem mainCentralNormal_order_isLeast (j : Kind) :
    IsLeast {n : ℕ | 0 < n ∧
      Nonempty (TransitionData.AnalyticTrivialization
        (NormalBundle.powerData j j.twist (mainTwist_admissible j) n) IS)} j.order :=
  NormalBundle.order_isLeast j j.twist (mainTwist_admissible j)

/-- The canonical and normal lines of the source's two actual central
surfaces have exact order three or four, respectively. -/
theorem mainCentral_bundle_orders (j : Kind) :
    IsLeast {n : ℕ | 0 < n ∧
      Nonempty (TransitionData.AnalyticTrivialization
        (CanonicalBundle.centralPowerData j j.twist (mainTwist_admissible j) n) IS)} j.order ∧
    IsLeast {n : ℕ | 0 < n ∧
      Nonempty (TransitionData.AnalyticTrivialization
        (NormalBundle.powerData j j.twist (mainTwist_admissible j) n) IS)} j.order :=
  ⟨mainCentralCanonical_order_isLeast j, mainCentralNormal_order_isLeast j⟩

end Wikipedia.HopfProblem.Elliptic
