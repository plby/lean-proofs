import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsEllipticCover
import Wikipedia.HopfProblem.HolomorphicDifferentialFormsFunctor

/-!
# Genuine differential forms on the actual elliptic root cover

The inherited root-domain product charts are independent of their
centers. Pulling a global form back along the actual holomorphic cover
gives a genuine section of its native alternating cotangent bundle.
Invariance under each actual period translation follows from the proved
equality of the global maps and the genuine derivative chain rule.
-/

noncomputable section

open Function Set Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicForms.EllipticCover

open Elliptic HolomorphicDifferentialForms

local notation "IF" => modelWithCornersSelf ℂ FamilyModel

attribute [local instance] coverChartedSpace Threefold.chartedSpace
  cover_isManifold Threefold.space_isManifold

/-- The native nested-open root charts do not depend on the chosen center. -/
theorem root_chart_eq (j : Kind) (z w : Root j) : chartAt ℂ z = chartAt ℂ w := rfl

/-- Their forward coordinate is the original complex root. -/
theorem root_chart_apply (j : Kind) (z w : Root j) :
    chartAt ℂ z w = rootCoordinate j w := rfl

/-- The actual inherited product charts are independent of their centers,
including the total inverse functions of the partial homeomorphisms. -/
theorem cover_chart_eq (j : Kind) (x y : Cover j) :
    chartAt FamilyModel x = chartAt FamilyModel y := rfl

/-- The native chart keeps the root and both original complex fibre coordinates. -/
theorem cover_chart_apply (j : Kind) (x y : Cover j) :
    chartAt FamilyModel x y = (rootCoordinate j y.1, y.2) := rfl

/-- Pull back every genuine global holomorphic form along the constructed
root-coordinate cover, retaining the actual source tangent bundle. -/
def globalCoverPullback (j : Kind) {p : ℕ} :
    Form FamilyModel Threefold.Space p →ₗ[ℂ] Form FamilyModel (Cover j) p :=
  pullback (globalCover j) (globalCover_holomorphic j)

/-- The pullback covector is given by the actual manifold derivative,
not by separately prescribed coefficient functions. -/
@[simp] theorem globalCoverPullback_apply (j : Kind) {p : ℕ}
    (θ : Form FamilyModel Threefold.Space p) (x : Cover j) :
    globalCoverPullback j θ x =
      (θ (globalCover j x)).compContinuousLinearMap (mfderiv IF IF (globalCover j) x) := rfl

theorem globalCoverPullback_evaluate (j : Kind) {p : ℕ}
    (θ : Form FamilyModel Threefold.Space p) (x : Cover j) (v : Fin p → FamilyModel) :
    globalCoverPullback j θ x v =
      θ (globalCover j x) (fun i => mfderiv IF IF (globalCover j) x (v i)) := rfl

/-- Genuine pullback invariance under every original integral-period translation. -/
theorem globalCoverPullback_periodTranslation (j : Kind) (ℓ : Lattice) {p : ℕ}
    (θ : Form FamilyModel Threefold.Space p) :
    pullback (periodTranslation j ℓ) (periodTranslation_holomorphic j ℓ)
        (globalCoverPullback j θ) = globalCoverPullback j θ :=
  pullback_deck (globalCover j) (globalCover_holomorphic j)
    (periodTranslation j ℓ) (periodTranslation_holomorphic j ℓ)
    (funext (globalCover_periodTranslation j ℓ)) θ

/-- Its pointwise law still contains the derivative of the actual
varying-period translation, so all horizontal correction terms are retained. -/
theorem globalCoverPullback_periodTranslation_apply (j : Kind) (ℓ : Lattice) {p : ℕ}
    (θ : Form FamilyModel Threefold.Space p) (x : Cover j) :
    (globalCoverPullback j θ (periodTranslation j ℓ x)).compContinuousLinearMap
        (mfderiv IF IF (periodTranslation j ℓ) x) = globalCoverPullback j θ x :=
  congrArg (fun η : Form FamilyModel (Cover j) p => η x)
    (globalCoverPullback_periodTranslation j ℓ θ)

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicForms.EllipticCover
