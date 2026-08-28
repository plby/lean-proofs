import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalEllipticComparisonBase
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalSectionsUnit

/-!
# The actual quartic elliptic divisor coefficient on the whole root disc

The finite sphere coordinate minus one has its proved fourth-order zero
at the actual order-four elliptic center.  Cancelling that power gives a
holomorphic nowhere-zero unit on the entire original disc.  Dividing by
the square of the actual canonical-section period unit gives the exact
unit relating the squared section coefficient to the pulled-back base
point equation, including at the central zero.
-/

noncomputable section

open Set Filter Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.PowersElliptic

open GlobalEllipticComparison

/-- The centered finite sphere coordinate has an actual analytic unit
factor on a positive-radius ball, by its proved native order four. -/
theorem exists_quartic_unit_ball :
    ∃ (u : ℂ → ℂ) (r : ℝ), 0 < r ∧ r ≤ 1 ∧
      AnalyticOnNhd ℂ u (Metric.ball 0 r) ∧
      (∀ z ∈ Metric.ball 0 r, u z ≠ 0) ∧
      (∀ z ∈ Metric.ball 0 r, discCoordinateExtension .four z - 1 = z ^ 4 * u z) := by
  have ha : AnalyticAt ℂ (fun z => discCoordinateExtension .four z - 1) 0 :=
    (discCoordinateExtension_analyticAt .four).sub analyticAt_const
  obtain ⟨u, hu, hu0, he⟩ :=
    ha.analyticOrderAt_eq_natCast.mp discCoordinateExtension_sub_one_order_four
  have hn : ∀ᶠ z in 𝓝 (0 : ℂ), AnalyticAt ℂ u z ∧ u z ≠ 0 ∧
      discCoordinateExtension .four z - 1 = z ^ 4 * u z := by
    filter_upwards [hu.eventually_analyticAt, hu.continuousAt.eventually_ne hu0, he]
      with z haz hnz hez
    exact ⟨haz, hnz, by simpa only [sub_zero, smul_eq_mul] using hez⟩
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp hn
  refine ⟨u, min r 1, lt_min hr zero_lt_one, min_le_right _ _, ?_, ?_, ?_⟩
  · intro z hz
    exact (hsub (Metric.ball_subset_ball (min_le_left _ _) hz)).1
  · intro z hz
    exact (hsub (Metric.ball_subset_ball (min_le_left _ _) hz)).2.1
  · intro z hz
    exact (hsub (Metric.ball_subset_ball (min_le_left _ _) hz)).2.2

def localQuarticUnit : ℂ → ℂ := exists_quartic_unit_ball.choose

def localQuarticRadius : ℝ := exists_quartic_unit_ball.choose_spec.choose

theorem localQuarticRadius_pos : 0 < localQuarticRadius :=
  exists_quartic_unit_ball.choose_spec.choose_spec.1

theorem localQuarticUnit_analyticOnNhd :
    AnalyticOnNhd ℂ localQuarticUnit (Metric.ball 0 localQuarticRadius) :=
  exists_quartic_unit_ball.choose_spec.choose_spec.2.2.1

theorem localQuarticUnit_ne_zero {z : ℂ} (hz : z ∈ Metric.ball 0 localQuarticRadius) :
    localQuarticUnit z ≠ 0 :=
  exists_quartic_unit_ball.choose_spec.choose_spec.2.2.2.1 z hz

theorem localQuarticUnit_factor {z : ℂ} (hz : z ∈ Metric.ball 0 localQuarticRadius) :
    discCoordinateExtension .four z - 1 = z ^ 4 * localQuarticUnit z :=
  exists_quartic_unit_ball.choose_spec.choose_spec.2.2.2.2 z hz

theorem localQuarticUnit_analyticAt : AnalyticAt ℂ localQuarticUnit 0 :=
  localQuarticUnit_analyticOnNhd 0 (Metric.mem_ball_self localQuarticRadius_pos)

theorem localQuarticUnit_zero_ne_zero : localQuarticUnit 0 ≠ 0 :=
  localQuarticUnit_ne_zero (Metric.mem_ball_self localQuarticRadius_pos)

/-- Away from the actual center the finite coordinate is not the second
elliptic value, since the original punctured lift lies in the regular locus. -/
theorem discCoordinate_four_ne_one (s : Disc) (hs : (s : ℂ) ≠ 0) :
    discCoordinate .four s ≠ 1 := by
  rw [discCoordinate_localBase .four (⟨s, hs⟩ : Elliptic.LogGauge.BaseStar)]
  exact GlobalRegular.upstairsCoordinate_ne_one (EllipticFilling.localBase .four ⟨s, hs⟩)

/-- The removed quartic factor, with its genuine analytic central value. -/
def quarticUnit (s : Disc) : ℂ := by
  classical
  exact if (s : ℂ) = 0 then localQuarticUnit 0 else
    (discCoordinate .four s - 1) / (s : ℂ) ^ 4

theorem quarticUnit_eq_local (s : Disc)
    (hs : (s : ℂ) ∈ Metric.ball 0 localQuarticRadius) :
    quarticUnit s = localQuarticUnit (s : ℂ) := by
  classical
  by_cases hz : (s : ℂ) = 0
  · rw [quarticUnit, if_pos hz, hz]
  · rw [quarticUnit, if_neg hz]
    have hf : discCoordinate .four s - 1 = (s : ℂ) ^ 4 * localQuarticUnit (s : ℂ) := by
      simpa only [discCoordinateExtension_coe] using localQuarticUnit_factor hs
    rw [hf, mul_div_cancel_left₀ _ (pow_ne_zero 4 hz)]

theorem quarticUnit_holomorphicAt_zero :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω quarticUnit Elliptic.discZero := by
  have hu : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω
      (fun s : Disc => localQuarticUnit (s : ℂ)) Elliptic.discZero :=
    localQuarticUnit_analyticAt.contDiffAt.contMDiffAt.comp Elliptic.discZero
      (contMDiff_subtype_val Elliptic.discZero)
  apply hu.congr_of_eventuallyEq
  filter_upwards [continuous_subtype_val.continuousAt
    (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self localQuarticRadius_pos))] with s hs
  exact quarticUnit_eq_local s hs

theorem quarticUnit_holomorphic : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω quarticUnit := by
  intro s
  by_cases hs : (s : ℂ) = 0
  · have he : s = Elliptic.discZero := Subtype.ext hs
    subst s
    exact quarticUnit_holomorphicAt_zero
  · have hh := ((discCoordinate_holomorphic .four s).sub
      (contMDiffAt_const (c := (1 : ℂ)))).div₀
      ((contMDiff_subtype_val s).pow 4) (pow_ne_zero 4 hs)
    apply hh.congr_of_eventuallyEq
    filter_upwards [continuous_subtype_val.continuousAt.eventually_ne hs] with t ht
    simp only [quarticUnit, if_neg ht]
    rfl

theorem quarticUnit_ne_zero (s : Disc) : quarticUnit s ≠ 0 := by
  classical
  by_cases hs : (s : ℂ) = 0
  · rw [quarticUnit, if_pos hs]
    exact localQuarticUnit_zero_ne_zero
  · rw [quarticUnit, if_neg hs]
    exact div_ne_zero (sub_ne_zero.mpr (discCoordinate_four_ne_one s hs)) (pow_ne_zero 4 hs)

/-- The exact quartic equation holds throughout the full original root disc. -/
theorem quarticUnit_factor (s : Disc) :
    discCoordinate .four s - 1 = (s : ℂ) ^ 4 * quarticUnit s := by
  classical
  by_cases hs : (s : ℂ) = 0
  · have he : s = Elliptic.discZero := Subtype.ext hs
    subst s
    have hc : discCoordinate .four Elliptic.discZero = 1 := discCoordinate_zero .four
    simp only [hc, sub_self, Elliptic.discZero_coe,
      zero_pow (by decide : (4 : ℕ) ≠ 0), zero_mul]
  · rw [quarticUnit, if_neg hs]
    field_simp [hs]

/-- The actual unit comparing the squared elliptic canonical coefficient
with the pulled-back finite equation of the base point one. -/
def squaredCoefficientUnit (s : Disc) : ℂ :=
  quarticUnit s / SectionsUnit.specialUnit .four s ^ 2

theorem squaredCoefficientUnit_holomorphic :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω squaredCoefficientUnit := by
  intro s
  exact (quarticUnit_holomorphic s).div₀
    ((SectionsUnit.specialUnit_holomorphic .four s).pow 2)
    (pow_ne_zero 2 (SectionsUnit.specialUnit_ne_zero .four s))

theorem squaredCoefficientUnit_ne_zero (s : Disc) : squaredCoefficientUnit s ≠ 0 :=
  div_ne_zero (quarticUnit_ne_zero s) (pow_ne_zero 2 (SectionsUnit.specialUnit_ne_zero .four s))

/-- Exact equality includes the central point and cancels only the
proved nowhere-zero period unit, never a vanishing section coefficient. -/
theorem squaredCoefficientUnit_factor (s : Disc) :
    discCoordinate .four s - 1 =
      SectionsUnit.specialCoefficient .four s ^ 2 * squaredCoefficientUnit s := by
  rw [quarticUnit_factor, squaredCoefficientUnit, SectionsUnit.specialCoefficient_eq]
  change (s : ℂ) ^ 4 * quarticUnit s =
    ((s : ℂ) ^ 2 * SectionsUnit.specialUnit .four s) ^ 2 *
      (quarticUnit s / SectionsUnit.specialUnit .four s ^ 2)
  field_simp [SectionsUnit.specialUnit_ne_zero .four s]

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.PowersElliptic
