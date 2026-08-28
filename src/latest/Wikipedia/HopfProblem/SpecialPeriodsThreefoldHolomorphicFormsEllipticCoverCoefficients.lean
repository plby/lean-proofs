import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsEllipticCoverForms
import Wikipedia.HopfProblem.HolomorphicDifferentialFormsFlat

/-!
# Native covectors of genuine global forms on the elliptic root cover

The actual preferred charts of the root cover are constant. Hence the
native covectors of the genuine derivative pullback vary holomorphically
as model-space alternating maps. Their zero-section restrictions retain
all fibre covector directions and are holomorphic through root zero.
-/

noncomputable section

open Function Set Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicForms.EllipticCover

open Elliptic HolomorphicDifferentialForms

local notation "I₁" => modelWithCornersSelf ℂ ℂ
local notation "IF" => modelWithCornersSelf ℂ FamilyModel

attribute [local instance] coverChartedSpace Threefold.chartedSpace
  cover_isManifold Threefold.space_isManifold

/-- The actual full native covector of the genuine global-form pullback. -/
def globalCoverNativeCoefficients (j : Kind) {p : ℕ}
    (θ : Form FamilyModel Threefold.Space p) :
    Cover j → FamilyModel [⋀^Fin p]→L[ℂ] ℂ :=
  nativeCoefficients FamilyModel (Cover j) (globalCoverPullback j θ)

/-- The proved constancy of the original charts supplies holomorphicity,
without replacing the source complex structure. -/
theorem globalCoverNativeCoefficients_holomorphic (j : Kind) {p : ℕ}
    (θ : Form FamilyModel Threefold.Space p) :
    ContMDiff IF (modelWithCornersSelf ℂ (FamilyModel [⋀^Fin p]→L[ℂ] ℂ)) ω
      (globalCoverNativeCoefficients j θ) :=
  nativeCoefficients_holomorphic_of_constant_charts FamilyModel (Cover j)
    (cover_chart_eq j) (globalCoverPullback j θ)

/-- These are the original native tangent covectors themselves. -/
theorem globalCoverNativeCoefficients_eq (j : Kind) {p : ℕ}
    (θ : Form FamilyModel Threefold.Space p) (x : Cover j) :
    globalCoverNativeCoefficients j θ x = globalCoverPullback j θ x := by
  ext v
  exact nativeCoefficients_apply FamilyModel (Cover j) (globalCoverPullback j θ) x v

theorem globalCoverNativeCoefficients_evaluate (j : Kind) {p : ℕ}
    (θ : Form FamilyModel Threefold.Space p) (x : Cover j) (v : Fin p → FamilyModel) :
    globalCoverNativeCoefficients j θ x v =
      θ (globalCover j x) (fun i => mfderiv IF IF (globalCover j) x (v i)) := by
  rw [globalCoverNativeCoefficients_eq]
  exact globalCoverPullback_evaluate j θ x v

/-- The native covector law uses the derivative of the actual varying
period translation, including its base-direction correction. -/
theorem globalCoverNativeCoefficients_periodTranslation (j : Kind) (ℓ : Lattice) {p : ℕ}
    (θ : Form FamilyModel Threefold.Space p) (x : Cover j) :
    (globalCoverNativeCoefficients j θ (periodTranslation j ℓ x)).compContinuousLinearMap
        (mfderiv IF IF (periodTranslation j ℓ) x) = globalCoverNativeCoefficients j θ x := by
  rw [globalCoverNativeCoefficients_eq, globalCoverNativeCoefficients_eq]
  exact globalCoverPullback_periodTranslation_apply j ℓ θ x

/-- Restrict the full covector to the zero complex fibre vector. This
retains fibre covector directions; it is not pullback to the one-dimensional base. -/
def globalCoverZeroCoefficients (j : Kind) {p : ℕ}
    (θ : Form FamilyModel Threefold.Space p) :
    Root j → FamilyModel [⋀^Fin p]→L[ℂ] ℂ :=
  globalCoverNativeCoefficients j θ ∘ zeroSection j

@[simp] theorem globalCoverZeroCoefficients_apply (j : Kind) {p : ℕ}
    (θ : Form FamilyModel Threefold.Space p) (z : Root j) :
    globalCoverZeroCoefficients j θ z = globalCoverNativeCoefficients j θ (z, 0) := rfl

/-- The full zero-section coefficient covector is holomorphic on the
actual root domain, which contains root zero. -/
theorem globalCoverZeroCoefficients_holomorphic (j : Kind) {p : ℕ}
    (θ : Form FamilyModel Threefold.Space p) :
    ContMDiff I₁ (modelWithCornersSelf ℂ (FamilyModel [⋀^Fin p]→L[ℂ] ℂ)) ω
      (globalCoverZeroCoefficients j θ) :=
  (globalCoverNativeCoefficients_holomorphic j θ).comp (zeroSection_holomorphic j)

theorem globalCoverZeroCoefficients_holomorphicAt_rootZero (j : Kind) {p : ℕ}
    (θ : Form FamilyModel Threefold.Space p) :
    ContMDiffAt I₁ (modelWithCornersSelf ℂ (FamilyModel [⋀^Fin p]→L[ℂ] ℂ)) ω
      (globalCoverZeroCoefficients j θ) (rootZero j) :=
  globalCoverZeroCoefficients_holomorphic j θ (rootZero j)

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicForms.EllipticCover
