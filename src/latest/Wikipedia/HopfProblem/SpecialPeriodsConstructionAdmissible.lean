import Wikipedia.HopfProblem.SpecialPeriodsConstructionFunctions
import Wikipedia.HopfProblem.SpecialPeriodsConstructionPeriodMap
import Wikipedia.HopfProblem.SpecialPeriodsConstructionCusp
import Wikipedia.HopfProblem.SpecialPeriodsConstructionDescentBounded

/-!
# One actual imaginary shift makes all constructed periods admissible

The analytic cusp expansion proves divergence of the first imaginary
period and boundedness of beta plus tau.  The discriminant is therefore
negative near the cusp.  Its proved invariance and continuity give genuine
descent to the actual compact triangle quotient, so it is bounded above
globally.  Choosing a negative imaginary constant then constructs the
holomorphic map into the actual admissible period domain.

No discriminant bound, descended discriminant, compactness assumption,
or pointwise negativity is an input to this construction.
-/

noncomputable section

open Filter Set UpperHalfPlane
open scoped Topology ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Construction.PeriodFunctions

variable (F : PeriodFunctions)

/-- The first imaginary period diverges by its constructed analytic cusp
formula, not by a growth assumption. -/
theorem tau_im_tendsto_atTop :
    Tendsto (fun z : ℍ => (F.data.tau z).im) atImInfty atTop := by
  obtain ⟨h, hh, hτ⟩ := F.tau_cusp
  exact tau_im_tendsto_atTop_of_cusp_formula hh hτ

/-- The analytic beta cusp germ gives the upper bound used in the exact
discriminant estimate. -/
theorem beta_add_tau_im_eventually_bounded :
    ∃ M : ℝ, ∀ᶠ z in atImInfty, (F.beta z + (F.data.tau z : ℂ)).im ≤ M := by
  obtain ⟨M, Y, hM⟩ := isBoundedAtImInfty_iff.mp F.beta_cusp.bounded
  refine ⟨M, (UpperHalfPlane.atImInfty_mem _).mpr ⟨Y, ?_⟩⟩
  intro z hz
  exact ((le_abs_self _).trans (Complex.abs_im_le_norm _)).trans (hM z hz)

/-- The actual discriminant tends to negative infinity high in the
original upper half-plane. -/
theorem discriminant_tendsto_atBot :
    Tendsto (fun z => (F.data.periodPoint F.beta z).discriminant) atImInfty atBot :=
  PeriodPoint.tendsto_discriminant_atBot (F.data.periodPoint F.beta)
    (Filter.Eventually.of_forall fun z => (F.data.tau z).im_pos)
    F.tau_im_tendsto_atTop F.beta_add_tau_im_eventually_bounded

/-- **The global discriminant bound.** Actual all-word invariance, actual
continuous descent, and compactness of the constructed quotient discharge
every premise of the compact-descent argument. -/
theorem discriminant_bddAbove :
    BddAbove (range fun z => (F.data.periodPoint F.beta z).discriminant) :=
  bddAbove_range_of_triangle_invariant_tendsto_atBot _
    (continuous_discriminant F.data F.beta_holomorphic)
    (discriminant_invariant F.data F.beta_generators) F.discriminant_tendsto_atBot

/-- Every constant below one proved imaginary threshold works at every
point, exactly as in the source's choice of the additive beta constant. -/
theorem exists_uniform_admissible_shift :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ c : ℂ, c.im < -M → ∀ z : ℍ,
      ((F.data.periodPoint F.beta z).shiftBeta c).Admissible :=
  PeriodPoint.exists_uniform_shift_of_bddAbove (F.data.periodPoint F.beta)
    (fun z => (F.data.tau z).im_pos) F.discriminant_bddAbove

/-- A single genuinely negative imaginary constant is enough. -/
theorem exists_negative_imaginary_shift :
    ∃ M : ℝ, 0 < M ∧ ∀ z : ℍ,
      ((F.data.periodPoint F.beta z).shiftBeta (-((M : ℂ) * Complex.I))).Admissible :=
  PeriodPoint.exists_negative_imaginary_shift_of_bddAbove (F.data.periodPoint F.beta)
    (fun z => (F.data.tau z).im_pos) F.discriminant_bddAbove

/-- The positive height of one constructed downward imaginary shift. -/
def shiftHeight : ℝ := F.exists_negative_imaginary_shift.choose

theorem shiftHeight_pos : 0 < F.shiftHeight :=
  F.exists_negative_imaginary_shift.choose_spec.1

/-- The chosen constant has strictly negative imaginary part. -/
def shiftConstant : ℂ := -((F.shiftHeight : ℂ) * Complex.I)

theorem shiftConstant_im_neg : F.shiftConstant.im < 0 := by
  simpa only [shiftConstant, Complex.neg_im, Complex.mul_im, Complex.ofReal_re,
    Complex.I_im, Complex.ofReal_im, Complex.I_re, mul_one, mul_zero, add_zero,
    neg_lt_zero] using F.shiftHeight_pos

theorem shifted_admissible (z : ℍ) :
    ((F.data.periodPoint F.beta z).shiftBeta F.shiftConstant).Admissible :=
  F.exists_negative_imaginary_shift.choose_spec.2 z

/-- The actual holomorphic admissible period map, constructed after the
global discriminant bound has been proved. -/
def admissiblePeriods : HolomorphicPeriodMap ℂ ℍ :=
  F.data.shiftedPeriodMap F.beta F.beta_holomorphic F.shiftConstant F.shifted_admissible

@[simp] theorem admissiblePeriods_tau (z : ℍ) :
    (F.admissiblePeriods.point z).val.τ = (F.data.tau z : ℂ) := rfl

@[simp] theorem admissiblePeriods_mu (z : ℍ) :
    (F.admissiblePeriods.point z).val.μ = F.data.mu z := rfl

@[simp] theorem admissiblePeriods_beta (z : ℍ) :
    (F.admissiblePeriods.point z).val.β = F.beta z + F.shiftConstant := rfl

/-- Both full period-domain generator laws survive the proved shift. -/
theorem admissiblePeriods_generator₁ (z : ℍ) :
    F.admissiblePeriods.point (Triangle.generatorOneSL • z) =
      (F.admissiblePeriods.point z).step₁ :=
  shiftedPeriodMap_generator₁ F.data F.beta_holomorphic F.shiftConstant
    F.shifted_admissible F.beta_generators z

theorem admissiblePeriods_generator₂ (z : ℍ) :
    F.admissiblePeriods.point (Triangle.generatorTwoSL • z) =
      (F.admissiblePeriods.point z).step₂ :=
  shiftedPeriodMap_generator₂ F.data F.beta_holomorphic F.shiftConstant
    F.shifted_admissible F.beta_generators z

theorem admissiblePeriods_cusp (z : ℍ) :
    F.admissiblePeriods.point (triangleGeometricRepresentation triangleCuspGenerator z) =
      (F.admissiblePeriods.point z).step₀ :=
  shiftedPeriodMap_cusp F.data F.beta_holomorphic F.shiftConstant
    F.shifted_admissible F.beta_generators z

/-- Global strict negativity is a proved property of the constructed map. -/
theorem admissiblePeriods_discriminant_neg (z : ℍ) :
    (F.admissiblePeriods.point z).val.discriminant < 0 :=
  (F.admissiblePeriods.point z).property.2

/-- The shift changes only the analytic beta cusp remainder. -/
theorem admissiblePeriods_beta_cusp : MuTorsor.CuspRegular
    (fun z => (F.admissiblePeriods.point z).val.β +
      (F.admissiblePeriods.point z).val.τ) := by
  obtain ⟨b, hb, hβ⟩ := F.beta_cusp
  exact ⟨fun q => b q + F.shiftConstant, hb.add analyticAt_const,
    beta_add_const_cusp_formula hβ F.shiftConstant⟩

end Wikipedia.HopfProblem.SpecialPeriods.Construction.PeriodFunctions
