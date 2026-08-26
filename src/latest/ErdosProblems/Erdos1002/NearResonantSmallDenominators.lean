import ErdosProblems.Erdos1002.NearResonantCarrierSeries
import ErdosProblems.Erdos1002.NearResonantPoleDerivatives

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# The two endpoint denominators in the smooth near-resonant tail

The global Ramanujan/carrier argument is naturally indexed by `p > 2`.
This file treats the omitted literal denominators `p = 1,2` directly.  The
Bernoulli mark is bounded by `1/8`, while the exact primitive-pole mass is
`O((a p)⁻¹)`.  Consequently their combined squared `L²(0,1)` mass is at most
`3 / (2a)`.  No Fourier representation of either endpoint is used.
-/

open Filter MeasureTheory Set Finset
open scoped BigOperators ENNReal Real

namespace Erdos1002

noncomputable section

theorem measurable_nearPrimitivePole
    (a ε : ℝ) (p : ℕ) (ha : 0 < a) (haε : a ≤ ε / 4) :
    Measurable (nearPrimitivePole a ε p) := by
  unfold nearPrimitivePole
  apply Measurable.ite (measurableSet_isPrimitiveResonance p)
  · exact (nearW_contDiff a ε ha haε).continuous.measurable.comp
      (measurable_const.mul (measurable_resonanceDelta p))
  · exact measurable_const

theorem measurable_smoothNearLiteralShotTerm
    (N p : ℕ) (a ε : ℝ) (ha : 0 < a) (haε : a ≤ ε / 4) :
    Measurable (smoothNearLiteralShotTerm N p a ε) := by
  unfold smoothNearLiteralShotTerm
  exact ((bernoulliMark_measurable.comp
      (measurable_const.mul (measurable_resonanceDelta p))).complex_ofReal).mul
        (measurable_nearPrimitivePole a ε p ha haε)

/-- The totalized smooth primitive pole is uniformly bounded.  The deleted
inner interval is essential here: it removes the apparent singularity at
`p * delta_p = 0`. -/
theorem norm_nearPrimitivePole_le_two_div
    (a ε : ℝ) (p : ℕ) (alpha : ℝ)
    (ha : 0 < a) (haε : a ≤ ε / 4) :
    ‖nearPrimitivePole a ε p alpha‖ ≤ 2 / a := by
  by_cases hprim : IsPrimitiveResonance p alpha
  · rw [nearPrimitivePole, if_pos hprim]
    calc
      ‖nearW a ε ((p : ℝ) * resonanceDelta p alpha)‖ ≤
          a⁻¹ * ‖nearRho a ε ((p : ℝ) * resonanceDelta p alpha)‖ :=
        norm_nearW_le a ε _ ha haε
      _ ≤ a⁻¹ * 2 := by
        exact mul_le_mul_of_nonneg_left
          (norm_nearRho_le_two a ε _) (inv_nonneg.mpr ha.le)
      _ = 2 / a := by rw [div_eq_mul_inv]; ring
  · rw [nearPrimitivePole, if_neg hprim, norm_zero]
    positivity

/-- The Bernoulli mark contributes its sharp factor `1/8`. -/
theorem norm_smoothNearLiteralShotTerm_le
    (N p : ℕ) (a ε : ℝ) (alpha : ℝ)
    (ha : 0 < a) (haε : a ≤ ε / 4) :
    ‖smoothNearLiteralShotTerm N p a ε alpha‖ ≤ 1 / (4 * a) := by
  unfold smoothNearLiteralShotTerm
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc
    |bernoulliMark ((N : ℝ) * resonanceDelta p alpha)| *
        ‖nearPrimitivePole a ε p alpha‖ ≤
      (1 / 8 : ℝ) * (2 / a) :=
        mul_le_mul (abs_bernoulliMark_le_one_eighth _)
          (norm_nearPrimitivePole_le_two_div a ε p alpha ha haε)
          (norm_nonneg _) (by norm_num)
    _ = 1 / (4 * a) := by field_simp [ha.ne']; ring

private theorem intervalIntegrable_norm_nearPrimitivePole_sq
    (a ε : ℝ) (p : ℕ) (ha : 0 < a) (haε : a ≤ ε / 4) :
    IntervalIntegrable
      (fun alpha : ℝ ↦ ‖nearPrimitivePole a ε p alpha‖ ^ 2)
      volume 0 1 := by
  apply (intervalIntegrable_const
    (c := (2 / a) ^ 2)).mono_fun
  · exact ((measurable_nearPrimitivePole a ε p ha haε).norm.pow_const 2)
      |>.aestronglyMeasurable
  · filter_upwards with alpha
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
      Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _)
      (norm_nearPrimitivePole_le_two_div a ε p alpha ha haε) 2

private theorem intervalIntegrable_norm_smoothNearLiteralShotTerm_sq
    (N p : ℕ) (a ε : ℝ) (ha : 0 < a) (haε : a ≤ ε / 4) :
    IntervalIntegrable
      (fun alpha : ℝ ↦ ‖smoothNearLiteralShotTerm N p a ε alpha‖ ^ 2)
      volume 0 1 := by
  apply (intervalIntegrable_const
    (c := (1 / (4 * a)) ^ 2)).mono_fun
  · exact ((measurable_smoothNearLiteralShotTerm N p a ε ha haε).norm.pow_const 2)
      |>.aestronglyMeasurable
  · filter_upwards with alpha
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
      Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _)
      (norm_smoothNearLiteralShotTerm_le N p a ε alpha ha haε) 2

/-- Exact one-denominator energy reduction to the already proved primitive
pole mass. -/
theorem integral_unit_norm_smoothNearLiteralShotTerm_sq_le
    (N p : ℕ) (a ε : ℝ) (hp : 0 < p)
    (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (hεhalf : ε ≤ 1 / 2) :
    (∫ alpha in (0 : ℝ)..1,
        ‖smoothNearLiteralShotTerm N p a ε alpha‖ ^ 2) ≤
      1 / (2 * a * p) := by
  have hpole := intervalIntegrable_norm_nearPrimitivePole_sq
    a ε p ha haε
  have hshot := intervalIntegrable_norm_smoothNearLiteralShotTerm_sq
    N p a ε ha haε
  calc
    (∫ alpha in (0 : ℝ)..1,
        ‖smoothNearLiteralShotTerm N p a ε alpha‖ ^ 2) ≤
      ∫ alpha in (0 : ℝ)..1,
        (1 / 64 : ℝ) * ‖nearPrimitivePole a ε p alpha‖ ^ 2 := by
          apply intervalIntegral.integral_mono_on (by norm_num) hshot
            (hpole.const_mul (1 / 64 : ℝ))
          intro alpha _halpha
          unfold smoothNearLiteralShotTerm
          rw [norm_mul, mul_pow]
          have hmark :
              ‖(bernoulliMark ((N : ℝ) * resonanceDelta p alpha) : ℂ)‖ ^ 2 ≤
                (1 / 64 : ℝ) := by
            rw [Complex.norm_real, Real.norm_eq_abs]
            calc
              |bernoulliMark ((N : ℝ) * resonanceDelta p alpha)| ^ 2 ≤
                  (1 / 8 : ℝ) ^ 2 :=
                pow_le_pow_left₀ (abs_nonneg _)
                  (abs_bernoulliMark_le_one_eighth
                    ((N : ℝ) * resonanceDelta p alpha)) 2
              _ = 1 / 64 := by norm_num
          exact mul_le_mul_of_nonneg_right hmark (sq_nonneg _)
    _ = (1 / 64 : ℝ) *
        (∫ alpha in (0 : ℝ)..1,
          ‖nearPrimitivePole a ε p alpha‖ ^ 2) := by
      rw [intervalIntegral.integral_const_mul]
    _ ≤ (1 / 64 : ℝ) * (32 / (a * p)) := by
      gcongr
      exact integral_unit_norm_nearPrimitivePole_sq_le
        a ε p hp ha hε haε hεhalf
    _ = 1 / (2 * a * p) := by
      have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
      field_simp [ha.ne', hpR]
      ring

/-- The literal smooth contribution of exactly the omitted denominators
`p=1,2`. -/
def smoothNearLiteralSmallDenominatorSum
    (N : ℕ) (a ε : ℝ) (alpha : ℝ) : ℂ :=
  smoothNearLiteralShotTerm N 1 a ε alpha +
    smoothNearLiteralShotTerm N 2 a ε alpha

theorem smoothNearLiteralSmallDenominatorSum_eq_finset
    (N : ℕ) (a ε : ℝ) (alpha : ℝ) :
    smoothNearLiteralSmallDenominatorSum N a ε alpha =
      ∑ p ∈ Finset.Icc 1 2, smoothNearLiteralShotTerm N p a ε alpha := by
  norm_num [smoothNearLiteralSmallDenominatorSum, Finset.sum_Icc_succ_top]

theorem measurable_smoothNearLiteralSmallDenominatorSum
    (N : ℕ) (a ε : ℝ) (ha : 0 < a) (haε : a ≤ ε / 4) :
    Measurable (smoothNearLiteralSmallDenominatorSum N a ε) := by
  unfold smoothNearLiteralSmallDenominatorSum
  exact (measurable_smoothNearLiteralShotTerm N 1 a ε ha haε).add
    (measurable_smoothNearLiteralShotTerm N 2 a ε ha haε)

private theorem intervalIntegrable_norm_smoothNearLiteralSmallDenominatorSum_sq
    (N : ℕ) (a ε : ℝ) (ha : 0 < a) (haε : a ≤ ε / 4) :
    IntervalIntegrable
      (fun alpha : ℝ ↦
        ‖smoothNearLiteralSmallDenominatorSum N a ε alpha‖ ^ 2)
      volume 0 1 := by
  apply (intervalIntegrable_const
    (c := (1 / (2 * a)) ^ 2)).mono_fun
  · exact ((measurable_smoothNearLiteralSmallDenominatorSum
      N a ε ha haε).norm.pow_const 2).aestronglyMeasurable
  · filter_upwards with alpha
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
      Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    apply pow_le_pow_left₀ (norm_nonneg _)
    unfold smoothNearLiteralSmallDenominatorSum
    calc
      ‖smoothNearLiteralShotTerm N 1 a ε alpha +
          smoothNearLiteralShotTerm N 2 a ε alpha‖ ≤
        ‖smoothNearLiteralShotTerm N 1 a ε alpha‖ +
          ‖smoothNearLiteralShotTerm N 2 a ε alpha‖ := norm_add_le _ _
      _ ≤ 1 / (4 * a) + 1 / (4 * a) := add_le_add
        (norm_smoothNearLiteralShotTerm_le N 1 a ε alpha ha haε)
        (norm_smoothNearLiteralShotTerm_le N 2 a ε alpha ha haε)
      _ = 1 / (2 * a) := by field_simp [ha.ne']; ring

/-- Combined endpoint estimate.  With `a=A/log N`, division by `log N`
makes this contribution `O((A log N)^{-1/2})`. -/
theorem integral_unit_norm_smoothNearLiteralSmallDenominatorSum_sq_le
    (N : ℕ) (a ε : ℝ)
    (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (hεhalf : ε ≤ 1 / 2) :
    (∫ alpha in (0 : ℝ)..1,
        ‖smoothNearLiteralSmallDenominatorSum N a ε alpha‖ ^ 2) ≤
      3 / (2 * a) := by
  let f₁ : ℝ → ℂ := smoothNearLiteralShotTerm N 1 a ε
  let f₂ : ℝ → ℂ := smoothNearLiteralShotTerm N 2 a ε
  have hsum :=
    intervalIntegrable_norm_smoothNearLiteralSmallDenominatorSum_sq
      N a ε ha haε
  have hf₁ : IntervalIntegrable
      (fun alpha : ℝ ↦ ‖f₁ alpha‖ ^ 2) volume 0 1 := by
    dsimp [f₁]
    exact intervalIntegrable_norm_smoothNearLiteralShotTerm_sq
      N 1 a ε ha haε
  have hf₂ : IntervalIntegrable
      (fun alpha : ℝ ↦ ‖f₂ alpha‖ ^ 2) volume 0 1 := by
    dsimp [f₂]
    exact intervalIntegrable_norm_smoothNearLiteralShotTerm_sq
      N 2 a ε ha haε
  have hright : IntervalIntegrable
      (fun alpha : ℝ ↦ 2 *
        (‖f₁ alpha‖ ^ 2 + ‖f₂ alpha‖ ^ 2)) volume 0 1 :=
    (hf₁.add hf₂).const_mul 2
  calc
    (∫ alpha in (0 : ℝ)..1,
        ‖smoothNearLiteralSmallDenominatorSum N a ε alpha‖ ^ 2) ≤
      ∫ alpha in (0 : ℝ)..1,
        2 * (‖f₁ alpha‖ ^ 2 + ‖f₂ alpha‖ ^ 2) := by
          apply intervalIntegral.integral_mono_on (by norm_num) hsum hright
          intro alpha _halpha
          have hadd : ‖f₁ alpha + f₂ alpha‖ ≤
              ‖f₁ alpha‖ + ‖f₂ alpha‖ := norm_add_le _ _
          have hsquare :
              (‖f₁ alpha‖ + ‖f₂ alpha‖) ^ 2 ≤
                2 * (‖f₁ alpha‖ ^ 2 + ‖f₂ alpha‖ ^ 2) := by
            nlinarith [sq_nonneg (‖f₁ alpha‖ - ‖f₂ alpha‖)]
          unfold smoothNearLiteralSmallDenominatorSum
          exact (pow_le_pow_left₀ (norm_nonneg _) hadd 2).trans hsquare
    _ = 2 * ((∫ alpha in (0 : ℝ)..1, ‖f₁ alpha‖ ^ 2) +
        ∫ alpha in (0 : ℝ)..1, ‖f₂ alpha‖ ^ 2) := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_add hf₁ hf₂]
    _ ≤ 2 * (1 / (2 * a * 1) + 1 / (2 * a * 2)) := by
      gcongr
      · simpa [f₁] using!
          (integral_unit_norm_smoothNearLiteralShotTerm_sq_le
            N 1 a ε (by omega) ha hε haε hεhalf)
      · simpa [f₂] using!
          (integral_unit_norm_smoothNearLiteralShotTerm_sq_le
            N 2 a ε (by omega) ha hε haε hεhalf)
    _ = 3 / (2 * a) := by field_simp [ha.ne']; ring

/-! ## Direct hard-cutoff wrapper used by the literal minor shot -/

/-- The part of the literal `p`-th minor shot lying in the near window
`|p delta_p| ≤ ε/4`.  It is written separately so that the two exceptional
denominators can be inserted into the same hard-threshold decomposition as
the `p>2` carrier argument. -/
def nearMinorSmallDenominatorTerm
    (N : ℕ) (A ε : ℝ) (p : ℕ) (alpha : ℝ) : ℂ :=
  if A < Real.log (N : ℝ) *
        |(p : ℝ) * resonanceDelta p alpha| ∧
      |(p : ℝ) * resonanceDelta p alpha| ≤ ε / 4 then
    (primitiveShot N p alpha : ℂ)
  else 0

def nearMinorSmallDenominatorSum
    (N : ℕ) (A ε : ℝ) (alpha : ℝ) : ℂ :=
  nearMinorSmallDenominatorTerm N A ε 1 alpha +
    nearMinorSmallDenominatorTerm N A ε 2 alpha

theorem measurable_nearMinorSmallDenominatorTerm
    (N p : ℕ) (A ε : ℝ) :
    Measurable (nearMinorSmallDenominatorTerm N A ε p) := by
  let x : ℝ → ℝ := fun alpha ↦
    |(p : ℝ) * resonanceDelta p alpha|
  have hx : Measurable x := by
    exact (measurable_const.mul (measurable_resonanceDelta p)).abs
  unfold nearMinorSmallDenominatorTerm
  apply Measurable.ite
  · exact (measurableSet_lt measurable_const (measurable_const.mul hx)).inter
      (measurableSet_le hx measurable_const)
  · exact (measurable_primitiveShot N p).complex_ofReal
  · exact measurable_const

theorem measurable_nearMinorSmallDenominatorSum
    (N : ℕ) (A ε : ℝ) :
    Measurable (nearMinorSmallDenominatorSum N A ε) := by
  unfold nearMinorSmallDenominatorSum
  exact (measurable_nearMinorSmallDenominatorTerm N 1 A ε).add
    (measurable_nearMinorSmallDenominatorTerm N 2 A ε)

/-- On its hard near window, the literal term lies on the plateau of the
smooth cutoff with inner scale `A/(2 log N)`.  Off that window the hard term
is zero, so its squared norm is pointwise dominated by the smooth term. -/
theorem norm_nearMinorSmallDenominatorTerm_sq_le_smooth
    (N p : ℕ) (A ε : ℝ) (alpha : ℝ)
    (hA : 0 < A) (hL : 0 < Real.log (N : ℝ)) (hε : 0 < ε) :
    ‖nearMinorSmallDenominatorTerm N A ε p alpha‖ ^ 2 ≤
      ‖smoothNearLiteralShotTerm N p
        (A / (2 * Real.log (N : ℝ))) ε alpha‖ ^ 2 := by
  let L : ℝ := Real.log (N : ℝ)
  let a : ℝ := A / (2 * L)
  have ha : 0 < a := by dsimp [a, L]; positivity
  by_cases hwindow :
      A < L * |(p : ℝ) * resonanceDelta p alpha| ∧
        |(p : ℝ) * resonanceDelta p alpha| ≤ ε / 4
  · have htwo : 2 * a ≤ |(p : ℝ) * resonanceDelta p alpha| := by
      have hdiv : A / L < |(p : ℝ) * resonanceDelta p alpha| := by
        apply (div_lt_iff₀ (by simpa only [L] using! hL)).2
        simpa only [mul_comm] using! hwindow.1
      have hscale : 2 * a = A / L := by
        dsimp [a]
        field_simp [hL.ne']
      rw [hscale]
      exact hdiv.le
    have hsmooth := smoothNearLiteralShotTerm_eq_primitiveShot_of_plateau
      N p a ε alpha ha hε htwo hwindow.2
    unfold nearMinorSmallDenominatorTerm
    rw [if_pos (by simpa only [L] using! hwindow)]
    rw [show smoothNearLiteralShotTerm N p
      (A / (2 * Real.log (N : ℝ))) ε alpha =
        (primitiveShot N p alpha : ℂ) by simpa only [a, L] using! hsmooth]
  · unfold nearMinorSmallDenominatorTerm
    rw [if_neg (by simpa only [L] using! hwindow), norm_zero,
      zero_pow (by omega : (2 : ℕ) ≠ 0)]
    positivity

private theorem intervalIntegrable_norm_nearMinorSmallDenominatorTerm_sq
    (N p : ℕ) (A ε : ℝ)
    (hA : 0 < A) (hL : 0 < Real.log (N : ℝ))
    (haε : A / (2 * Real.log (N : ℝ)) ≤ ε / 4) :
    IntervalIntegrable
      (fun alpha : ℝ ↦
        ‖nearMinorSmallDenominatorTerm N A ε p alpha‖ ^ 2)
      volume 0 1 := by
  let a : ℝ := A / (2 * Real.log (N : ℝ))
  have ha : 0 < a := by dsimp [a]; positivity
  have hsmooth := intervalIntegrable_norm_smoothNearLiteralShotTerm_sq
    N p a ε ha (by simpa only [a] using! haε)
  apply hsmooth.mono_fun
  · exact ((measurable_nearMinorSmallDenominatorTerm N p A ε).norm.pow_const 2)
      |>.aestronglyMeasurable
  · filter_upwards with alpha
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
      Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    simpa only [a] using!
      norm_nearMinorSmallDenominatorTerm_sq_le_smooth
        N p A ε alpha hA hL (by linarith [haε])

private theorem integral_unit_norm_nearMinorSmallDenominatorTerm_sq_le
    (N p : ℕ) (A ε : ℝ) (hp : 0 < p)
    (hA : 0 < A) (hL : 0 < Real.log (N : ℝ))
    (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2)
    (haε : A / (2 * Real.log (N : ℝ)) ≤ ε / 4) :
    (∫ alpha in (0 : ℝ)..1,
        ‖nearMinorSmallDenominatorTerm N A ε p alpha‖ ^ 2) ≤
      Real.log (N : ℝ) / (A * p) := by
  let a : ℝ := A / (2 * Real.log (N : ℝ))
  have ha : 0 < a := by dsimp [a]; positivity
  have hhard := intervalIntegrable_norm_nearMinorSmallDenominatorTerm_sq
    N p A ε hA hL haε
  have hsmooth := intervalIntegrable_norm_smoothNearLiteralShotTerm_sq
    N p a ε ha (by simpa only [a] using! haε)
  calc
    (∫ alpha in (0 : ℝ)..1,
        ‖nearMinorSmallDenominatorTerm N A ε p alpha‖ ^ 2) ≤
      ∫ alpha in (0 : ℝ)..1,
        ‖smoothNearLiteralShotTerm N p a ε alpha‖ ^ 2 := by
          apply intervalIntegral.integral_mono_on (by norm_num) hhard hsmooth
          intro alpha _halpha
          simpa only [a] using!
            norm_nearMinorSmallDenominatorTerm_sq_le_smooth
              N p A ε alpha hA hL hε
    _ ≤ 1 / (2 * a * p) :=
      integral_unit_norm_smoothNearLiteralShotTerm_sq_le
        N p a ε hp ha hε (by simpa only [a] using! haε) hεhalf
    _ = Real.log (N : ℝ) / (A * p) := by
      have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
      dsimp [a]
      field_simp [hA.ne', hL.ne', hpR]

private theorem nearMinorSmallDenominatorSum_eq_zero_of_outer_le_inner
    (N : ℕ) (A ε : ℝ)
    (hL : 0 < Real.log (N : ℝ))
    (hcut : ε / 4 < A / Real.log (N : ℝ)) :
    nearMinorSmallDenominatorSum N A ε = (fun _alpha : ℝ ↦ 0) := by
  funext alpha
  change nearMinorSmallDenominatorSum N A ε alpha = (0 : ℂ)
  unfold nearMinorSmallDenominatorSum nearMinorSmallDenominatorTerm
  have hzero (p : ℕ) :
      ¬ (A < Real.log (N : ℝ) *
          |(p : ℝ) * resonanceDelta p alpha| ∧
        |(p : ℝ) * resonanceDelta p alpha| ≤ ε / 4) := by
    rintro ⟨hlower, hupper⟩
    have hdiv : A / Real.log (N : ℝ) <
        |(p : ℝ) * resonanceDelta p alpha| := by
      apply (div_lt_iff₀ hL).2
      simpa only [mul_comm] using! hlower
    linarith
  rw [if_neg (hzero 1), if_neg (hzero 2), add_zero]

/-- Uniform hard-cutoff energy bound for the two exceptional denominators.
The proof splits according to whether the hard inner threshold lies inside
the near window; outside it, the near contribution is literally empty. -/
theorem integral_unit_norm_nearMinorSmallDenominatorSum_sq_le
    (N : ℕ) (A ε : ℝ)
    (hA : 0 < A) (hL : 0 < Real.log (N : ℝ))
    (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2) :
    (∫ alpha in (0 : ℝ)..1,
        ‖nearMinorSmallDenominatorSum N A ε alpha‖ ^ 2) ≤
      3 * Real.log (N : ℝ) / A := by
  by_cases hcut : A / Real.log (N : ℝ) ≤ ε / 4
  · have haε : A / (2 * Real.log (N : ℝ)) ≤ ε / 4 := by
      have hhalf : A / (2 * Real.log (N : ℝ)) ≤
          A / Real.log (N : ℝ) := by
        have hAnonneg : 0 ≤ A := hA.le
        have hdenom : Real.log (N : ℝ) ≤
            2 * Real.log (N : ℝ) := by linarith
        exact div_le_div_of_nonneg_left hAnonneg hL hdenom
      exact hhalf.trans hcut
    have h₁ := intervalIntegrable_norm_nearMinorSmallDenominatorTerm_sq
      N 1 A ε hA hL haε
    have h₂ := intervalIntegrable_norm_nearMinorSmallDenominatorTerm_sq
      N 2 A ε hA hL haε
    have hsum : IntervalIntegrable
        (fun alpha : ℝ ↦
          ‖nearMinorSmallDenominatorSum N A ε alpha‖ ^ 2)
        volume 0 1 := by
      have hmeas := (measurable_nearMinorSmallDenominatorSum N A ε).norm.pow_const 2
      apply ((h₁.add h₂).const_mul 2).mono_fun
      · exact hmeas.aestronglyMeasurable
      · filter_upwards with alpha
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
          Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by norm_num)
            (add_nonneg (sq_nonneg _) (sq_nonneg _)))]
        unfold nearMinorSmallDenominatorSum
        have hadd := norm_add_le
          (nearMinorSmallDenominatorTerm N A ε 1 alpha)
          (nearMinorSmallDenominatorTerm N A ε 2 alpha)
        exact (pow_le_pow_left₀ (norm_nonneg _) hadd 2).trans (by
          nlinarith [sq_nonneg
            (‖nearMinorSmallDenominatorTerm N A ε 1 alpha‖ -
              ‖nearMinorSmallDenominatorTerm N A ε 2 alpha‖)])
    calc
      (∫ alpha in (0 : ℝ)..1,
          ‖nearMinorSmallDenominatorSum N A ε alpha‖ ^ 2) ≤
        ∫ alpha in (0 : ℝ)..1, 2 *
          (‖nearMinorSmallDenominatorTerm N A ε 1 alpha‖ ^ 2 +
            ‖nearMinorSmallDenominatorTerm N A ε 2 alpha‖ ^ 2) := by
            apply intervalIntegral.integral_mono_on (by norm_num) hsum
              ((h₁.add h₂).const_mul 2)
            intro alpha _halpha
            unfold nearMinorSmallDenominatorSum
            have hadd := norm_add_le
              (nearMinorSmallDenominatorTerm N A ε 1 alpha)
              (nearMinorSmallDenominatorTerm N A ε 2 alpha)
            exact (pow_le_pow_left₀ (norm_nonneg _) hadd 2).trans (by
              nlinarith [sq_nonneg
                (‖nearMinorSmallDenominatorTerm N A ε 1 alpha‖ -
                  ‖nearMinorSmallDenominatorTerm N A ε 2 alpha‖)])
      _ = 2 *
          ((∫ alpha in (0 : ℝ)..1,
              ‖nearMinorSmallDenominatorTerm N A ε 1 alpha‖ ^ 2) +
            ∫ alpha in (0 : ℝ)..1,
              ‖nearMinorSmallDenominatorTerm N A ε 2 alpha‖ ^ 2) := by
        rw [intervalIntegral.integral_const_mul,
          intervalIntegral.integral_add h₁ h₂]
      _ ≤ 2 * (Real.log (N : ℝ) / (A * 1) +
          Real.log (N : ℝ) / (A * 2)) := by
        gcongr
        · simpa using!
            (integral_unit_norm_nearMinorSmallDenominatorTerm_sq_le
              N 1 A ε (by omega) hA hL hε hεhalf haε)
        · simpa using!
            (integral_unit_norm_nearMinorSmallDenominatorTerm_sq_le
              N 2 A ε (by omega) hA hL hε hεhalf haε)
      _ = 3 * Real.log (N : ℝ) / A := by
        field_simp [hA.ne']
        ring
  · have hzero := nearMinorSmallDenominatorSum_eq_zero_of_outer_le_inner
      N A ε hL (lt_of_not_ge hcut)
    rw [hzero]
    simp only [norm_zero, zero_pow (by omega : (2 : ℕ) ≠ 0),
      intervalIntegral.integral_zero]
    positivity

/-- The preceding hard endpoint estimate in the manuscript normalization.
Its right-hand side tends to zero on the product filter as soon as both
`A` and `N` tend to infinity. -/
theorem integral_unit_norm_nearMinorSmallDenominatorSum_div_log_sq_le
    (N : ℕ) (A ε : ℝ)
    (hA : 0 < A) (hL : 0 < Real.log (N : ℝ))
    (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2) :
    (∫ alpha in (0 : ℝ)..1,
        ‖nearMinorSmallDenominatorSum N A ε alpha /
          (Real.log (N : ℝ) : ℂ)‖ ^ 2) ≤
      3 / (A * Real.log (N : ℝ)) := by
  have henergy := integral_unit_norm_nearMinorSmallDenominatorSum_sq_le
    N A ε hA hL hε hεhalf
  have hfun : (fun alpha : ℝ ↦
      ‖nearMinorSmallDenominatorSum N A ε alpha /
        (Real.log (N : ℝ) : ℂ)‖ ^ 2) =
      (fun alpha : ℝ ↦
        (1 / Real.log (N : ℝ) ^ 2) *
          ‖nearMinorSmallDenominatorSum N A ε alpha‖ ^ 2) := by
    funext alpha
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hL]
    field_simp [hL.ne']
  rw [hfun, intervalIntegral.integral_const_mul]
  calc
    (1 / Real.log (N : ℝ) ^ 2) *
        (∫ alpha in (0 : ℝ)..1,
          ‖nearMinorSmallDenominatorSum N A ε alpha‖ ^ 2) ≤
      (1 / Real.log (N : ℝ) ^ 2) *
        (3 * Real.log (N : ℝ) / A) := by gcongr
    _ = 3 / (A * Real.log (N : ℝ)) := by
      field_simp [hA.ne', hL.ne']

/-- A pointwise bound for one normalized hard endpoint term.  This simpler
`L∞` estimate is sufficient to remove the finite set `p=1,2` uniformly on
the two-parameter product filter. -/
theorem norm_nearMinorSmallDenominatorTerm_div_log_le
    (N p : ℕ) (A ε : ℝ) (alpha : ℝ)
    (hA : 0 < A) (hL : 0 < Real.log (N : ℝ)) :
    ‖nearMinorSmallDenominatorTerm N A ε p alpha /
      (Real.log (N : ℝ) : ℂ)‖ ≤ 1 / A := by
  let L : ℝ := Real.log (N : ℝ)
  by_cases hwindow :
      A < L * |(p : ℝ) * resonanceDelta p alpha| ∧
        |(p : ℝ) * resonanceDelta p alpha| ≤ ε / 4
  · unfold nearMinorSmallDenominatorTerm
    rw [if_pos (by simpa only [L] using! hwindow)]
    by_cases hprim : IsPrimitiveResonance p alpha
    · have hxpos : 0 < |(p : ℝ) * resonanceDelta p alpha| := by
        have hne : |(p : ℝ) * resonanceDelta p alpha| ≠ 0 := by
          intro hzero
          rw [hzero, mul_zero] at hwindow
          linarith
        exact lt_of_le_of_ne (abs_nonneg _) hne.symm
      have hdiv : A / L < |(p : ℝ) * resonanceDelta p alpha| := by
        apply (div_lt_iff₀ (by simpa only [L] using! hL)).2
        simpa only [mul_comm] using! hwindow.1
      have hLpos : 0 < L := by simpa only [L] using! hL
      have hLne : L ≠ 0 := hLpos.ne'
      have hinv : 1 / |(p : ℝ) * resonanceDelta p alpha| ≤ L / A := by
        calc
          1 / |(p : ℝ) * resonanceDelta p alpha| ≤ 1 / (A / L) :=
            one_div_le_one_div_of_le (div_pos hA hLpos)
              hdiv.le
          _ = L / A := by field_simp [hA.ne', hLne]
      have hprimitive :
          ‖(primitiveShot N p alpha : ℂ)‖ ≤ L / A := by
        rw [primitiveShot_of_primitive N p alpha hprim,
          Complex.norm_real, Real.norm_eq_abs, abs_div]
        calc
          |bernoulliMark ((N : ℝ) * resonanceDelta p alpha)| /
                |(p : ℝ) * resonanceDelta p alpha| ≤
              1 / |(p : ℝ) * resonanceDelta p alpha| := by
            gcongr
            exact (abs_bernoulliMark_le_one_eighth _).trans (by norm_num)
          _ ≤ L / A := hinv
      rw [norm_div]
      simp only [Complex.norm_real, Real.norm_eq_abs,
        show |Real.log (N : ℝ)| = Real.log (N : ℝ) from abs_of_pos hL]
      calc
        |primitiveShot N p alpha| / Real.log (N : ℝ) ≤
            (L / A) / L := by
          simpa only [Complex.norm_real, Real.norm_eq_abs, L] using!
            (div_le_div_of_nonneg_right hprimitive hLpos.le)
        _ = 1 / A := by field_simp [hA.ne', hLne]
    · rw [primitiveShot_of_not_primitive N p alpha hprim, Complex.ofReal_zero,
        zero_div, norm_zero]
      positivity
  · unfold nearMinorSmallDenominatorTerm
    rw [if_neg (by simpa only [L] using! hwindow), zero_div, norm_zero]
    positivity

theorem norm_nearMinorSmallDenominatorSum_div_log_le
    (N : ℕ) (A ε : ℝ) (alpha : ℝ)
    (hA : 0 < A) (hL : 0 < Real.log (N : ℝ)) :
    ‖nearMinorSmallDenominatorSum N A ε alpha /
      (Real.log (N : ℝ) : ℂ)‖ ≤ 2 / A := by
  unfold nearMinorSmallDenominatorSum
  rw [add_div]
  calc
    ‖nearMinorSmallDenominatorTerm N A ε 1 alpha /
          (Real.log (N : ℝ) : ℂ) +
        nearMinorSmallDenominatorTerm N A ε 2 alpha /
          (Real.log (N : ℝ) : ℂ)‖ ≤
      ‖nearMinorSmallDenominatorTerm N A ε 1 alpha /
          (Real.log (N : ℝ) : ℂ)‖ +
        ‖nearMinorSmallDenominatorTerm N A ε 2 alpha /
          (Real.log (N : ℝ) : ℂ)‖ := norm_add_le _ _
    _ ≤ 1 / A + 1 / A := add_le_add
      (norm_nearMinorSmallDenominatorTerm_div_log_le
        N 1 A ε alpha hA hL)
      (norm_nearMinorSmallDenominatorTerm_div_log_le
        N 2 A ε alpha hA hL)
    _ = 2 / A := by ring

theorem eLpNorm_nearMinorSmallDenominatorSum_div_log_le
    (N : ℕ) (A ε : ℝ)
    (hA : 0 < A) (hL : 0 < Real.log (N : ℝ)) :
    eLpNorm
        (fun alpha : ℝ ↦ nearMinorSmallDenominatorSum N A ε alpha /
          (Real.log (N : ℝ) : ℂ))
        (2 : ENNReal) uniform01Measure ≤
      ENNReal.ofReal (2 / A) := by
  have hpoint : ∀ᵐ alpha : ℝ ∂uniform01Measure,
      ‖nearMinorSmallDenominatorSum N A ε alpha /
        (Real.log (N : ℝ) : ℂ)‖ ≤ 2 / A :=
    Eventually.of_forall fun alpha ↦
      norm_nearMinorSmallDenominatorSum_div_log_le N A ε alpha hA hL
  simpa using! eLpNorm_le_of_ae_bound (p := (2 : ENNReal)) hpoint

/-- The complete product-filter deletion of the two exceptional near
denominators.  It is uniform in the relative growth of `A` and `N`. -/
theorem tendsto_eLpNorm_nearMinorSmallDenominatorSum_div_log_zero
    (ε : ℝ) :
    Tendsto
      (fun z : ℕ × ℕ ↦
        eLpNorm
          (fun alpha : ℝ ↦
            nearMinorSmallDenominatorSum z.2 (z.1 : ℝ) ε alpha /
              (Real.log (z.2 : ℝ) : ℂ))
          (2 : ENNReal) uniform01Measure)
      ((atTop : Filter ℕ) ×ˢ (atTop : Filter ℕ)) (nhds 0) := by
  have hreal : Tendsto (fun A : ℕ ↦ 2 / (A : ℝ)) atTop (nhds 0) := by
    exact tendsto_natCast_atTop_atTop.const_div_atTop 2
  have henn : Tendsto (fun A : ℕ ↦ ENNReal.ofReal (2 / (A : ℝ)))
      atTop (nhds 0) := by
    have h := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hreal
    simpa using! h
  have hupper : Tendsto
      (fun z : ℕ × ℕ ↦ ENNReal.ofReal (2 / (z.1 : ℝ)))
      ((atTop : Filter ℕ) ×ˢ (atTop : Filter ℕ)) (nhds 0) :=
    henn.comp tendsto_fst
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (show Tendsto (fun _z : ℕ × ℕ ↦ (0 : ENNReal))
        ((atTop : Filter ℕ) ×ˢ (atTop : Filter ℕ)) (nhds 0) from
          tendsto_const_nhds)
      hupper
  · exact Eventually.of_forall fun _z ↦ bot_le
  · have hAevent : ∀ᶠ z : ℕ × ℕ in
        ((atTop : Filter ℕ) ×ˢ (atTop : Filter ℕ)), 1 ≤ z.1 :=
      tendsto_fst.eventually (eventually_ge_atTop 1)
    have hNevent : ∀ᶠ z : ℕ × ℕ in
        ((atTop : Filter ℕ) ×ˢ (atTop : Filter ℕ)), 2 ≤ z.2 :=
      tendsto_snd.eventually (eventually_ge_atTop 2)
    filter_upwards [hAevent, hNevent] with z hA hN
    exact eLpNorm_nearMinorSmallDenominatorSum_div_log_le
      z.2 (z.1 : ℝ) ε (by exact_mod_cast hA)
        (Real.log_pos (by exact_mod_cast hN))

end

end Erdos1002
