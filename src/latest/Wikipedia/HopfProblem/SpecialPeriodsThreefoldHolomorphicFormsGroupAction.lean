import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsRegularCover

/-!
# Genuine triangle-group invariance on the regular period-vector cover

The complex lift is the original all-word period-family lift. It
intertwines the actual lattice quotient with the actual triangle action,
so its composite with the actual global cover is unchanged. Functoriality
of genuine derivative pullback then gives invariance of every covector.
-/

noncomputable section

open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicForms.RegularCover

open HolomorphicDifferentialForms (Form)

attribute [local instance] chartedSpace coverChartedSpace cover_isManifold space_isManifold

local notation "IF" => modelWithCornersSelf ℂ Model

/-- Every actual complex period-family lift preserves the actual global point. -/
theorem globalCover_complexLift (g : TriangleGroup) (x : Cover) :
    globalCover (data.complexLift g x) = globalCover x := by
  let := data.totalAction
  change regularFamilyInclusion
      (data.quotient (data.periods.quotientMap (data.complexLift g x))) =
    regularFamilyInclusion (data.quotient (data.periods.quotientMap x))
  rw [data.complexLift_quotientMap, data.quotient_smul]

theorem globalCover_comp_complexLift (g : TriangleGroup) :
    globalCover ∘ data.complexLift g = globalCover :=
  funext (globalCover_complexLift g)

/-- The actual pullback form, in every degree, is invariant under every
triangle-group lift, by the actual manifold chain rule. -/
theorem globalCoverPullback_complexLift {p : ℕ} (θ : Form Model Threefold.Space p)
    (g : TriangleGroup) :
    HolomorphicDifferentialForms.pullback (data.complexLift g)
      (data.complexLift_holomorphic g) (globalCoverPullback θ) = globalCoverPullback θ :=
  HolomorphicDifferentialForms.pullback_deck globalCover globalCover_holomorphic
    (data.complexLift g) (data.complexLift_holomorphic g)
    (globalCover_comp_complexLift g) θ

/-- Full native-covector invariance uses the derivative of the literal
complex lift, before any coefficient reconstruction or simplification. -/
theorem nativeCoefficients_complexLift {p : ℕ} (θ : Form Model Threefold.Space p)
    (g : TriangleGroup) (x : Cover) (v : Fin p → Model) :
    nativeCoefficients θ (data.complexLift g x)
        (fun i => mfderiv IF IF (data.complexLift g) x (v i)) =
      nativeCoefficients θ x v := by
  have h := congrArg (fun η : Form Model Cover p => η x v)
    (globalCoverPullback_complexLift θ g)
  change globalCoverPullback θ (data.complexLift g x)
      (fun i => mfderiv IF IF (data.complexLift g) x (v i)) =
    globalCoverPullback θ x v at h
  exact (nativeCoefficients_apply θ _ _).trans
    (h.trans (nativeCoefficients_apply θ x v).symm)

/-- Equality of the whole actual alternating covectors, not just selected
basis evaluations. -/
theorem nativeCoefficients_complexLift_covector {p : ℕ}
    (θ : Form Model Threefold.Space p) (g : TriangleGroup) (x : Cover) :
    (nativeCoefficients θ (data.complexLift g x)).compContinuousLinearMap
      (mfderiv IF IF (data.complexLift g) x) = nativeCoefficients θ x := by
  ext v
  exact nativeCoefficients_complexLift θ g x v

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicForms.RegularCover
