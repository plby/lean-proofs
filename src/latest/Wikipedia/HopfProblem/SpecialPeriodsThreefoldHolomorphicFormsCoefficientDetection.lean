import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsNormalFormEvaluations
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsDetection

/-!
# Detection by the genuine normal-form coefficients

These equivalences concern the entire actual derivative pullback, not
only selected evaluations of a possibly nonzero covector.
-/

noncomputable section

open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicForms.RegularCover

open HolomorphicDifferentialForms (Form)

attribute [local instance] chartedSpace coverChartedSpace cover_isManifold space_isManifold

theorem pullback_eq_zero_iff_nativeCoefficients {p : ℕ}
    (θ : Form Model Threefold.Space p) :
    globalCoverPullback θ = 0 ↔ nativeCoefficients θ = 0 := by
  constructor
  · intro h
    funext x
    ext v
    rw [nativeCoefficients_apply, h]
    rfl
  · intro h
    apply ContMDiffSection.ext
    intro x
    ext v
    change globalCoverPullback θ x v = 0
    calc
      globalCoverPullback θ x v = nativeCoefficients θ x v :=
        (nativeCoefficients_apply θ x v).symm
      _ = 0 := by rw [h]; rfl

theorem pullback_one_eq_zero_iff (θ : Form Model Threefold.Space 1) :
    globalCoverPullback θ = 0 ↔ baseOne θ = 0 ∧ fibreOne θ = 0 := by
  rw [pullback_eq_zero_iff_nativeCoefficients]
  constructor
  · intro h
    constructor
    · funext z
      change HolomorphicDifferentialForms.Coordinates.oneBaseCoefficient
        (nativeCoefficients θ (zeroSection z)) = 0
      rw [h]
      exact map_zero _
    · funext z
      change HolomorphicDifferentialForms.Coordinates.oneFibreCoefficient
        (nativeCoefficients θ (zeroSection z)) = 0
      rw [h]
      exact map_zero _
  · rintro ⟨ha, hc⟩
    funext x
    rcases x with ⟨z, ζ⟩
    apply (HolomorphicDifferentialForms.Coordinates.one_eq_zero_iff _).mpr
    constructor
    · change oneBase θ (z, ζ) = 0
      rw [oneBase_eq_baseOne, ha]
      rfl
    · change oneFibre θ (z, ζ) = 0
      rw [oneFibre_eq_fibreOne, hc]
      rfl

theorem pullback_two_eq_zero_iff (θ : Form Model Threefold.Space 2) :
    globalCoverPullback θ = 0 ↔ mixedTwo θ = 0 := by
  rw [pullback_eq_zero_iff_nativeCoefficients]
  constructor
  · intro h
    funext z
    change HolomorphicDifferentialForms.Coordinates.twoMixedCoefficient
      (nativeCoefficients θ (zeroSection z)) = 0
    rw [h]
    exact map_zero _
  · intro h
    funext x
    rcases x with ⟨z, ζ⟩
    apply (HolomorphicDifferentialForms.Coordinates.two_eq_zero_iff _).mpr
    constructor
    · exact twoVertical_eq_zero θ z ζ
    · change twoMixed θ (z, ζ) = 0
      rw [twoMixed_eq_mixedTwo, h]
      rfl

theorem pullback_three_eq_zero_iff (θ : Form Model Threefold.Space 3) :
    globalCoverPullback θ = 0 ↔ baseTop θ = 0 := by
  rw [pullback_eq_zero_iff_nativeCoefficients]
  constructor
  · intro h
    funext z
    change HolomorphicDifferentialForms.Coordinates.topCoefficient
      (nativeCoefficients θ (zeroSection z)) = 0
    rw [h]
    exact map_zero _
  · intro h
    funext x
    rcases x with ⟨z, ζ⟩
    apply (HolomorphicDifferentialForms.Coordinates.top_eq_zero_iff _).mpr
    change top θ (z, ζ) = 0
    rw [top_eq_baseTop, h]
    rfl

/-- These two actual coefficient functions detect the original global one-form. -/
theorem oneForm_eq_zero_iff_coefficients (θ : Form Model Threefold.Space 1) :
    θ = 0 ↔ baseOne θ = 0 ∧ fibreOne θ = 0 :=
  (globalCoverPullback_eq_zero_iff θ).symm.trans (pullback_one_eq_zero_iff θ)

/-- The mixed coefficient detects the entire original global two-form. -/
theorem twoForm_eq_zero_iff_coefficients (θ : Form Model Threefold.Space 2) :
    θ = 0 ↔ mixedTwo θ = 0 :=
  (globalCoverPullback_eq_zero_iff θ).symm.trans (pullback_two_eq_zero_iff θ)

/-- The top coefficient detects the original global three-form. -/
theorem threeForm_eq_zero_iff_coefficients (θ : Form Model Threefold.Space 3) :
    θ = 0 ↔ baseTop θ = 0 :=
  (globalCoverPullback_eq_zero_iff θ).symm.trans (pullback_three_eq_zero_iff θ)

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicForms.RegularCover
