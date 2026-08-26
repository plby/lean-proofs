import ErdosProblems.Erdos1002.GaussHeterogeneousFactorialLimit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Heterogeneous Gauss factorial limits at a moving real scale

The resonance process is normalized by `log N`, not by an auxiliary
integer horizon.  This module removes that mismatch.  Tuple times are
arbitrary natural numbers, while the rare-window scale is an independent
real sequence tending to infinity.

The theorem below is an unconditional analytic statement once two purely
deterministic counting limits are supplied: the total tuple density and
the negligible density of tuples with a short chronological gap.
-/

open Filter MeasureTheory Set Finset
open scoped BigOperators ENNReal Topology symmDiff

namespace Erdos1002

noncomputable section

/-! ## Natural-valued chronological families -/

/-- Strict chronological order for a natural-valued tuple. -/
def IsChronologicalNatTuple {r : ℕ} (t : Fin r → ℕ) : Prop :=
  ∀ i k, i < k → t i + 1 ≤ t k

/-- Separation by a prescribed natural gap. -/
def IsSeparatedNatTuple {r : ℕ} (gap : ℕ) (t : Fin r → ℕ) : Prop :=
  ∀ i k, i < k → t i + gap ≤ t k

/-- The long-gap part of an arbitrary finite natural-valued family. -/
def separatedNatTupleFamily {r : ℕ} (gap : ℕ)
    (tuples : Finset (Fin r → ℕ)) : Finset (Fin r → ℕ) := by
  classical
  exact tuples.filter (IsSeparatedNatTuple gap)

/-- The complementary short-gap family. -/
def shortNatTupleFamily {r : ℕ} (gap : ℕ)
    (tuples : Finset (Fin r → ℕ)) : Finset (Fin r → ℕ) := by
  classical
  exact tuples.filter (fun t ↦ ¬ IsSeparatedNatTuple gap t)

@[simp] theorem mem_separatedNatTupleFamily_iff
    {r gap : ℕ} {tuples : Finset (Fin r → ℕ)} {t : Fin r → ℕ} :
    t ∈ separatedNatTupleFamily gap tuples ↔
      t ∈ tuples ∧ IsSeparatedNatTuple gap t := by
  classical
  simp [separatedNatTupleFamily]

@[simp] theorem mem_shortNatTupleFamily_iff
    {r gap : ℕ} {tuples : Finset (Fin r → ℕ)} {t : Fin r → ℕ} :
    t ∈ shortNatTupleFamily gap tuples ↔
      t ∈ tuples ∧ ¬ IsSeparatedNatTuple gap t := by
  classical
  simp [shortNatTupleFamily]

theorem card_shortNatTupleFamily_add_card_separatedNatTupleFamily
    {r gap : ℕ} (tuples : Finset (Fin r → ℕ)) :
    (shortNatTupleFamily gap tuples).card +
      (separatedNatTupleFamily gap tuples).card = tuples.card := by
  classical
  simpa [shortNatTupleFamily, separatedNatTupleFamily, add_comm] using!
    Finset.card_filter_add_card_filter_not
      (s := tuples) (p := IsSeparatedNatTuple gap)

/-! ## Moving-scale exact and digit sums -/

/-- Exact heterogeneous approximation-coordinate tuple sum at an
independent real scale. -/
def gaussMovingHeterogeneousApproximationTupleSum
    {r : ℕ} (scale : ℝ) (lower upper : Fin r → ℝ)
    (tuples : Finset (Fin r → ℕ)) : ℝ :=
  ∑ t ∈ tuples,
    gaussMeasure.real
      (gaussHeterogeneousApproximationTupleEvent scale lower upper t)

/-- One-digit surrogate of the moving-scale exact tuple sum. -/
def gaussMovingHeterogeneousDigitTupleSum
    {r : ℕ} (scale : ℝ) (lower upper : Fin r → ℝ)
    (tuples : Finset (Fin r → ℕ)) : ℝ :=
  ∑ t ∈ tuples,
    gaussMeasure.real
      (gaussHeterogeneousDigitWindowTupleEvent scale lower upper t)

theorem abs_gaussMovingHeterogeneousApproximationTupleSum_sub_digit_le
    {r : ℕ} (scale : ℝ) (lower upper : Fin r → ℝ)
    (tuples : Finset (Fin r → ℕ)) :
    |gaussMovingHeterogeneousApproximationTupleSum
          scale lower upper tuples -
        gaussMovingHeterogeneousDigitTupleSum
          scale lower upper tuples| ≤
      ∑ t ∈ tuples,
        gaussMeasure.real
          (gaussHeterogeneousApproximationTupleEvent
              scale lower upper t ∆
            gaussHeterogeneousDigitWindowTupleEvent
              scale lower upper t) := by
  classical
  unfold gaussMovingHeterogeneousApproximationTupleSum
    gaussMovingHeterogeneousDigitTupleSum
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ t ∈ tuples,
        (gaussMeasure.real
            (gaussHeterogeneousApproximationTupleEvent
              scale lower upper t) -
          gaussMeasure.real
            (gaussHeterogeneousDigitWindowTupleEvent
              scale lower upper t))| ≤
        ∑ t ∈ tuples,
          |gaussMeasure.real
              (gaussHeterogeneousApproximationTupleEvent
                scale lower upper t) -
            gaussMeasure.real
              (gaussHeterogeneousDigitWindowTupleEvent
                scale lower upper t)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro t _ht
      exact abs_measureReal_sub_le_measureReal_symmDiff
        (measurableSet_gaussHeterogeneousApproximationTupleEvent
          scale lower upper t).nullMeasurableSet
        (measurableSet_gaussHeterogeneousDigitWindowTupleEvent
          scale lower upper t).nullMeasurableSet

/-! ## One-point moving-scale asymptotics -/

/-- The heterogeneous product of moving-scale one-point intensities. -/
theorem tendsto_movingGaussHeterogeneousRareDigitProduct
    {r : ℕ} (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (lower upper : Fin r → ℝ)
    (hlower : ∀ i, 0 < lower i)
    (hupper : ∀ i, lower i < upper i) :
    Tendsto
      (fun n : ℕ ↦
        ∏ i, scale n *
          gaussMeasure.real
            (scaledGaussFirstDigitWindow
              (scale n) (lower i) (upper i)))
      atTop
      (𝓝 (∏ i, (upper i - lower i) / Real.log 2)) := by
  apply tendsto_finset_prod Finset.univ
  intro i _hi
  have hmain :=
    tendsto_scaled_gaussFirstDigitBlock_floorCeil
      scale hscale (hlower i) (hupper i)
  apply hmain.congr'
  filter_upwards [hscale.eventually_gt_atTop 0] with n hn
  rw [gaussFirstDigitBlock_floorCeil_eq_scaledWindow
    hn (hlower i) (hupper i)]

/-- A moving-scale tuple-cardinality density times the independent
heterogeneous one-point product. -/
theorem
    tendsto_card_mul_movingGaussHeterogeneousRareDigitProduct_of_density
    {r : ℕ} {density : ℝ}
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (lower upper : Fin r → ℝ)
    (hlower : ∀ i, 0 < lower i)
    (hupper : ∀ i, lower i < upper i)
    (family : ℕ → Finset (Fin r → ℕ))
    (hdensity : Tendsto
      (fun n : ℕ ↦ ((family n).card : ℝ) / (scale n) ^ r)
      atTop (𝓝 density)) :
    Tendsto
      (fun n : ℕ ↦ ((family n).card : ℝ) *
        ∏ i, gaussMeasure.real
          (scaledGaussFirstDigitWindow
            (scale n) (lower i) (upper i)))
      atTop
      (𝓝 (density *
        ∏ i, (upper i - lower i) / Real.log 2)) := by
  have hproduct :=
    tendsto_movingGaussHeterogeneousRareDigitProduct
      scale hscale lower upper hlower hupper
  have hmul := hdensity.mul hproduct
  apply hmul.congr'
  filter_upwards [hscale.eventually_gt_atTop 0] with n hn
  have hsne : scale n ≠ 0 := ne_of_gt hn
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  field_simp [hsne]

/-! ## Pointwise short/long estimates -/

theorem gaussMovingHeterogeneousDigitTupleSum_short_le
    {r gap : ℕ} (hr : 0 < r) {scale : ℝ}
    (lower upper : Fin r → ℝ)
    (tuples : Finset (Fin r → ℕ))
    (hchronological : ∀ t ∈ tuples, IsChronologicalNatTuple t) :
    gaussMovingHeterogeneousDigitTupleSum scale lower upper
        (shortNatTupleFamily gap tuples) ≤
      ((shortNatTupleFamily gap tuples).card : ℝ) *
        (7 ^ (r - 1) *
          ∏ i, gaussMeasure.real
            (scaledGaussFirstDigitWindow
              scale (lower i) (upper i))) := by
  classical
  unfold gaussMovingHeterogeneousDigitTupleSum
  calc
    (∑ t ∈ shortNatTupleFamily gap tuples,
        gaussMeasure.real
          (gaussHeterogeneousDigitWindowTupleEvent
            scale lower upper t)) ≤
        ∑ _t ∈ shortNatTupleFamily gap tuples,
          (7 ^ (r - 1) *
            ∏ i, gaussMeasure.real
              (scaledGaussFirstDigitWindow
                scale (lower i) (upper i))) := by
      apply Finset.sum_le_sum
      intro t ht
      exact gaussMeasure_real_heterogeneousDigitTupleEvent_le
        hr lower upper t
          (hchronological t (mem_shortNatTupleFamily_iff.mp ht).1)
    _ = ((shortNatTupleFamily gap tuples).card : ℝ) *
        (7 ^ (r - 1) *
          ∏ i, gaussMeasure.real
            (scaledGaussFirstDigitWindow
              scale (lower i) (upper i))) := by simp

theorem
    abs_gaussMovingHeterogeneousDigitTupleSum_separated_sub_product_le
    {r gap : ℕ} (hr : 0 < r) (hgap0 : 0 < gap) {scale : ℝ}
    (lower upper : Fin r → ℝ)
    (tuples : Finset (Fin r → ℕ)) :
    |gaussMovingHeterogeneousDigitTupleSum scale lower upper
          (separatedNatTupleFamily gap tuples) -
        ((separatedNatTupleFamily gap tuples).card : ℝ) *
          ∏ i, gaussMeasure.real
            (scaledGaussFirstDigitWindow
              scale (lower i) (upper i))| ≤
      ((separatedNatTupleFamily gap tuples).card : ℝ) *
        (((1 + gaussDigitExponentialRate gap) ^ (r - 1) - 1) *
          ∏ i, gaussMeasure.real
            (scaledGaussFirstDigitWindow
              scale (lower i) (upper i))) := by
  classical
  let p : ℝ :=
    ∏ i, gaussMeasure.real
      (scaledGaussFirstDigitWindow scale (lower i) (upper i))
  let q : ℝ :=
    (1 + gaussDigitExponentialRate gap) ^ (r - 1) - 1
  have hrearrange :
      gaussMovingHeterogeneousDigitTupleSum scale lower upper
            (separatedNatTupleFamily gap tuples) -
          ((separatedNatTupleFamily gap tuples).card : ℝ) * p =
        ∑ t ∈ separatedNatTupleFamily gap tuples,
          (gaussMeasure.real
              (gaussHeterogeneousDigitWindowTupleEvent
                scale lower upper t) - p) := by
    unfold gaussMovingHeterogeneousDigitTupleSum
    simp
  rw [hrearrange]
  calc
    |∑ t ∈ separatedNatTupleFamily gap tuples,
        (gaussMeasure.real
            (gaussHeterogeneousDigitWindowTupleEvent
              scale lower upper t) - p)| ≤
        ∑ t ∈ separatedNatTupleFamily gap tuples,
          |gaussMeasure.real
              (gaussHeterogeneousDigitWindowTupleEvent
                scale lower upper t) - p| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _t ∈ separatedNatTupleFamily gap tuples, q * p := by
      apply Finset.sum_le_sum
      intro t ht
      exact
        abs_gaussMeasure_real_heterogeneousDigitTupleEvent_sub_product_le
          hr lower upper t gap hgap0
            (mem_separatedNatTupleFamily_iff.mp ht).2
    _ = ((separatedNatTupleFamily gap tuples).card : ℝ) *
        (q * p) := by simp

theorem gaussMovingHeterogeneousDigitTupleSum_eq_short_add_separated
    {r : ℕ} (gap : ℕ) {scale : ℝ}
    (lower upper : Fin r → ℝ)
    (tuples : Finset (Fin r → ℕ)) :
    gaussMovingHeterogeneousDigitTupleSum scale lower upper tuples =
      gaussMovingHeterogeneousDigitTupleSum scale lower upper
          (shortNatTupleFamily gap tuples) +
        gaussMovingHeterogeneousDigitTupleSum scale lower upper
          (separatedNatTupleFamily gap tuples) := by
  classical
  unfold gaussMovingHeterogeneousDigitTupleSum
    shortNatTupleFamily separatedNatTupleFamily
  simpa [add_comm] using!
    (Finset.sum_filter_add_sum_filter_not tuples
      (IsSeparatedNatTuple gap)
      (fun t ↦ gaussMeasure.real
        (gaussHeterogeneousDigitWindowTupleEvent
          scale lower upper t))).symm

/-! ## Moving-scale factorial convergence -/

/-- The digit-surrogate factorial limit at an arbitrary real scale. -/
theorem tendsto_gaussMovingHeterogeneousDigitTupleSum
    {r : ℕ} (hr : 0 < r) {density : ℝ}
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (lower upper : Fin r → ℝ)
    (hlower : ∀ i, 0 < lower i)
    (hupper : ∀ i, lower i < upper i)
    (gap : ℕ → ℕ) (hgapTop : Tendsto gap atTop atTop)
    (hgapPos : ∀ᶠ n : ℕ in atTop, 0 < gap n)
    (tuples : ℕ → Finset (Fin r → ℕ))
    (hchronological : ∀ n, ∀ t ∈ tuples n,
      IsChronologicalNatTuple t)
    (htotalDensity : Tendsto
      (fun n : ℕ ↦ ((tuples n).card : ℝ) / (scale n) ^ r)
      atTop (𝓝 density))
    (hshortDensity : Tendsto
      (fun n : ℕ ↦
        ((shortNatTupleFamily (gap n) (tuples n)).card : ℝ) /
          (scale n) ^ r)
      atTop (𝓝 0)) :
    Tendsto
      (fun n : ℕ ↦
        gaussMovingHeterogeneousDigitTupleSum
          (scale n) lower upper (tuples n))
      atTop
      (𝓝 (density *
        ∏ i, (upper i - lower i) / Real.log 2)) := by
  let short : ℕ → Finset (Fin r → ℕ) :=
    fun n ↦ shortNatTupleFamily (gap n) (tuples n)
  let separated : ℕ → Finset (Fin r → ℕ) :=
    fun n ↦ separatedNatTupleFamily (gap n) (tuples n)
  have hmass :=
    tendsto_movingGaussHeterogeneousRareDigitProduct
      scale hscale lower upper hlower hupper
  have hshortWeight :=
    tendsto_card_mul_movingGaussHeterogeneousRareDigitProduct_of_density
      scale hscale lower upper hlower hupper short
        (by simpa only [short] using! hshortDensity)
  have hshortWeight0 :
      Tendsto
        (fun n : ℕ ↦ ((short n).card : ℝ) *
          ∏ i, gaussMeasure.real
            (scaledGaussFirstDigitWindow
              (scale n) (lower i) (upper i)))
        atTop (𝓝 0) := by
    simpa only [zero_mul] using! hshortWeight
  have hshortUpper :
      Tendsto
        (fun n : ℕ ↦ ((short n).card : ℝ) *
          (7 ^ (r - 1) *
            ∏ i, gaussMeasure.real
              (scaledGaussFirstDigitWindow
                (scale n) (lower i) (upper i))))
        atTop (𝓝 0) := by
    have hraw :=
      (tendsto_const_nhds :
        Tendsto (fun _ : ℕ ↦ (7 : ℝ) ^ (r - 1))
          atTop (𝓝 ((7 : ℝ) ^ (r - 1)))).mul hshortWeight0
    have hraw0 :
        Tendsto
          (fun n : ℕ ↦ (7 : ℝ) ^ (r - 1) *
            (((short n).card : ℝ) *
              ∏ i, gaussMeasure.real
                (scaledGaussFirstDigitWindow
                  (scale n) (lower i) (upper i))))
          atTop (𝓝 0) := by
      simpa only [mul_zero] using! hraw
    apply hraw0.congr'
    filter_upwards with n
    ring
  have hshortSum :
      Tendsto
        (fun n : ℕ ↦
          gaussMovingHeterogeneousDigitTupleSum
            (scale n) lower upper (short n))
        atTop (𝓝 0) := by
    apply squeeze_zero'
    · exact Eventually.of_forall fun n ↦
        Finset.sum_nonneg fun _t _ht ↦ measureReal_nonneg
    · filter_upwards with n
      simpa only [short] using!
        gaussMovingHeterogeneousDigitTupleSum_short_le
          hr lower upper (tuples n) (hchronological n)
    · exact hshortUpper
  have hseparatedDensity :
      Tendsto
        (fun n : ℕ ↦ ((separated n).card : ℝ) / (scale n) ^ r)
        atTop (𝓝 density) := by
    have hsub := htotalDensity.sub hshortDensity
    have hsub' :
        Tendsto
          (fun n : ℕ ↦
            ((tuples n).card : ℝ) / (scale n) ^ r -
              ((shortNatTupleFamily (gap n) (tuples n)).card : ℝ) /
                (scale n) ^ r)
          atTop (𝓝 density) := by
      simpa only [sub_zero] using! hsub
    apply hsub'.congr'
    filter_upwards with n
    have hcard :=
      card_shortNatTupleFamily_add_card_separatedNatTupleFamily
        (gap := gap n) (tuples n)
    have hcardReal :
        ((shortNatTupleFamily (gap n) (tuples n)).card : ℝ) +
            ((separatedNatTupleFamily (gap n) (tuples n)).card : ℝ) =
          ((tuples n).card : ℝ) := by
      exact_mod_cast hcard
    dsimp only [short, separated]
    rw [← hcardReal]
    ring
  have hseparatedProduct :=
    tendsto_card_mul_movingGaussHeterogeneousRareDigitProduct_of_density
      scale hscale lower upper hlower hupper separated hseparatedDensity
  have hmix :=
    tendsto_gaussDigitRelativeMixingFactor (r := r) hgapTop
  have herrorUpperRaw := hseparatedDensity.mul (hmix.mul hmass)
  have herrorUpper :
      Tendsto
        (fun n : ℕ ↦ ((separated n).card : ℝ) *
          (((1 + gaussDigitExponentialRate (gap n)) ^ (r - 1) - 1) *
            ∏ i, gaussMeasure.real
              (scaledGaussFirstDigitWindow
                (scale n) (lower i) (upper i))))
        atTop (𝓝 0) := by
    have hzero :
        density * (0 *
          ∏ i, (upper i - lower i) / Real.log 2) = 0 := by
      ring
    rw [hzero] at herrorUpperRaw
    apply herrorUpperRaw.congr'
    filter_upwards [hscale.eventually_gt_atTop 0] with n hn
    have hsne : scale n ≠ 0 := ne_of_gt hn
    dsimp only [separated]
    rw [Finset.prod_mul_distrib]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    field_simp [hsne]
  have hseparatedError :
      Tendsto
        (fun n : ℕ ↦
          gaussMovingHeterogeneousDigitTupleSum
              (scale n) lower upper (separated n) -
            ((separated n).card : ℝ) *
              ∏ i, gaussMeasure.real
                (scaledGaussFirstDigitWindow
                  (scale n) (lower i) (upper i)))
        atTop (𝓝 0) := by
    rw [tendsto_zero_iff_abs_tendsto_zero]
    apply squeeze_zero'
    · exact Eventually.of_forall fun _n ↦ abs_nonneg _
    · filter_upwards [hgapPos] with n hgap
      simpa only [separated] using!
        abs_gaussMovingHeterogeneousDigitTupleSum_separated_sub_product_le
          hr hgap lower upper (tuples n)
    · exact herrorUpper
  have hseparatedSum :
      Tendsto
        (fun n : ℕ ↦
          gaussMovingHeterogeneousDigitTupleSum
            (scale n) lower upper (separated n))
        atTop
        (𝓝 (density *
          ∏ i, (upper i - lower i) / Real.log 2)) := by
    have hadd := hseparatedError.add hseparatedProduct
    have hadd' :
        Tendsto
          (fun n : ℕ ↦
            (gaussMovingHeterogeneousDigitTupleSum
                (scale n) lower upper (separated n) -
              ((separated n).card : ℝ) *
                ∏ i, gaussMeasure.real
                  (scaledGaussFirstDigitWindow
                    (scale n) (lower i) (upper i))) +
              ((separated n).card : ℝ) *
                ∏ i, gaussMeasure.real
                  (scaledGaussFirstDigitWindow
                    (scale n) (lower i) (upper i)))
          atTop
          (𝓝 (density *
            ∏ i, (upper i - lower i) / Real.log 2)) := by
      simpa only [zero_add] using! hadd
    apply hadd'.congr'
    filter_upwards with n
    ring
  have hsum := hshortSum.add hseparatedSum
  have hsum' :
      Tendsto
        (fun n : ℕ ↦
          gaussMovingHeterogeneousDigitTupleSum
              (scale n) lower upper (short n) +
            gaussMovingHeterogeneousDigitTupleSum
              (scale n) lower upper (separated n))
        atTop
        (𝓝 (density *
          ∏ i, (upper i - lower i) / Real.log 2)) := by
    simpa only [zero_add] using! hsum
  apply hsum'.congr'
  filter_upwards with n
  simpa only [short, separated] using!
    (gaussMovingHeterogeneousDigitTupleSum_eq_short_add_separated
      (gap n) lower upper (tuples n)).symm

/-! ## Exact-coordinate replacement and conclusion -/

/-- Fixed positive windows satisfy the replacement large-scale condition
along every real scale tending to infinity. -/
theorem eventually_movingHeterogeneousApproximationWindow_large
    {r : ℕ} (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (lower upper : Fin r → ℝ)
    (hlower : ∀ i, 0 < lower i) :
    ∀ᶠ n : ℕ in atTop,
      ∀ i, 16 * (upper i) ^ 2 ≤ lower i * scale n := by
  have hall :
      ∀ᶠ n : ℕ in atTop,
        ∀ i ∈ (Finset.univ : Finset (Fin r)),
          16 * (upper i) ^ 2 ≤ lower i * scale n := by
    rw [Finset.eventually_all]
    intro i _hi
    have hthreshold :=
      hscale.eventually
        (eventually_ge_atTop
          (16 * (upper i) ^ 2 / lower i : ℝ))
    filter_upwards [hthreshold] with n hn
    calc
      16 * (upper i) ^ 2 =
          lower i * (16 * (upper i) ^ 2 / lower i) := by
        field_simp [ne_of_gt (hlower i)]
      _ ≤ lower i * scale n :=
        mul_le_mul_of_nonneg_left hn (hlower i).le
  filter_upwards [hall] with n hn
  intro i
  exact hn i (Finset.mem_univ i)

/-- The absolutely summed symmetric-difference mass is `o(1)` for every
moving-scale family of bounded factorial density.  Keeping the absolute
error at event level is what permits a later change of measure. -/
theorem
    tendsto_sum_gaussMeasure_real_symmDiff_movingHeterogeneousTuples_zero
    {r : ℕ} (hr : 0 < r) {A density : ℝ}
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (lower upper : Fin r → ℝ)
    (hA : 0 ≤ A)
    (hlower : ∀ i, 0 < lower i)
    (hupper : ∀ i, lower i < upper i)
    (hupperA : ∀ i, upper i ≤ A)
    (tuples : ℕ → Finset (Fin r → ℕ))
    (hchronological : ∀ n, ∀ t ∈ tuples n,
      IsChronologicalNatTuple t)
    (htotalDensity : Tendsto
      (fun n : ℕ ↦ ((tuples n).card : ℝ) / (scale n) ^ r)
      atTop (𝓝 density)) :
    Tendsto
      (fun n : ℕ ↦
        ∑ t ∈ tuples n,
          gaussMeasure.real
            (gaussHeterogeneousApproximationTupleEvent
                (scale n) lower upper t ∆
              gaussHeterogeneousDigitWindowTupleEvent
                (scale n) lower upper t))
      atTop (𝓝 0) := by
  let C : ℝ :=
    (r : ℝ) * 2 *
      (1 + gaussDigitExponentialRate 1) ^ (r - 1) *
      (26 * A ^ 2 / Real.log 2) *
      ((2 * A + 10 * A ^ 2) / Real.log 2) ^ (r - 1)
  let err : ℕ → ℝ := fun n ↦
    ∑ t ∈ tuples n,
      gaussMeasure.real
        (gaussHeterogeneousApproximationTupleEvent
            (scale n) lower upper t ∆
          gaussHeterogeneousDigitWindowTupleEvent
            (scale n) lower upper t)
  have hlarge :=
    eventually_movingHeterogeneousApproximationWindow_large
      scale hscale lower upper hlower
  have hscalePos := hscale.eventually_gt_atTop 0
  have hscaleOne := hscale.eventually (eventually_ge_atTop (1 : ℝ))
  have herrUpper :
      ∀ᶠ n : ℕ in atTop,
        err n ≤
          (((tuples n).card : ℝ) / (scale n) ^ r) *
            (C / scale n) := by
    filter_upwards [hlarge, hscalePos, hscaleOne] with
      n hlargeN hpos hone
    have hraw :=
      sum_gaussMeasure_real_symmDiff_heterogeneousTuples_le_explicit
        hr lower upper (tuples n) 1 (by norm_num) hpos hone hA
          hlower hupper hupperA hlargeN
          (fun t ht i k hik ↦ hchronological n t ht i k hik)
    refine hraw.trans_eq ?_
    dsimp only [C]
    have hsne : scale n ≠ 0 := ne_of_gt hpos
    have hboundary :
        (26 * A ^ 2 / scale n ^ 2) / Real.log 2 =
          (26 * A ^ 2 / Real.log 2) / scale n ^ 2 := by
      field_simp
    have hwindow :
        ((2 * A + 10 * A ^ 2) / scale n) / Real.log 2 =
          ((2 * A + 10 * A ^ 2) / Real.log 2) / scale n := by
      field_simp
    rw [hboundary, hwindow, div_pow]
    have hpow : scale n ^ r = scale n ^ (r - 1) * scale n := by
      conv_lhs => rw [show r = (r - 1) + 1 by omega, pow_succ]
    rw [hpow]
    field_simp [hsne]
  have hCdiv :
      Tendsto (fun n : ℕ ↦ C / scale n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hscale
  have hupperZero := htotalDensity.mul hCdiv
  change Tendsto err atTop (𝓝 0)
  apply squeeze_zero'
  · exact Eventually.of_forall fun n ↦
      Finset.sum_nonneg fun _t _ht ↦ measureReal_nonneg
  · exact herrUpper
  · simpa only [mul_zero] using! hupperZero

/-- The aggregate exact-to-digit difference is `o(1)` for every
moving-scale family of bounded factorial density. -/
theorem
    tendsto_gaussMovingHeterogeneousApproximationTupleSum_sub_digit_zero
    {r : ℕ} (hr : 0 < r) {A density : ℝ}
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (lower upper : Fin r → ℝ)
    (hA : 0 ≤ A)
    (hlower : ∀ i, 0 < lower i)
    (hupper : ∀ i, lower i < upper i)
    (hupperA : ∀ i, upper i ≤ A)
    (tuples : ℕ → Finset (Fin r → ℕ))
    (hchronological : ∀ n, ∀ t ∈ tuples n,
      IsChronologicalNatTuple t)
    (htotalDensity : Tendsto
      (fun n : ℕ ↦ ((tuples n).card : ℝ) / (scale n) ^ r)
      atTop (𝓝 density)) :
    Tendsto
      (fun n : ℕ ↦
        gaussMovingHeterogeneousApproximationTupleSum
            (scale n) lower upper (tuples n) -
          gaussMovingHeterogeneousDigitTupleSum
            (scale n) lower upper (tuples n))
      atTop (𝓝 0) := by
  have herrZero :=
    tendsto_sum_gaussMeasure_real_symmDiff_movingHeterogeneousTuples_zero
      hr scale hscale lower upper hA hlower hupper hupperA
        tuples hchronological htotalDensity
  rw [tendsto_zero_iff_abs_tendsto_zero]
  apply squeeze_zero'
  · exact Eventually.of_forall fun _n ↦ abs_nonneg _
  · filter_upwards with n
    exact
      abs_gaussMovingHeterogeneousApproximationTupleSum_sub_digit_le
        (scale n) lower upper (tuples n)
  · exact herrZero

/-- Uniform-Lebesgue version of the moving exact tuple sum. -/
def uniformMovingHeterogeneousApproximationTupleSum
    {r : ℕ} (scale : ℝ) (lower upper : Fin r → ℝ)
    (tuples : Finset (Fin r → ℕ)) : ℝ :=
  ∑ t ∈ tuples,
    uniform01Measure.real
      (gaussHeterogeneousApproximationTupleEvent scale lower upper t)

/-- Uniform-Lebesgue version of the moving one-digit tuple sum. -/
def uniformMovingHeterogeneousDigitTupleSum
    {r : ℕ} (scale : ℝ) (lower upper : Fin r → ℝ)
    (tuples : Finset (Fin r → ℕ)) : ℝ :=
  ∑ t ∈ tuples,
    uniform01Measure.real
      (gaussHeterogeneousDigitWindowTupleEvent scale lower upper t)

theorem abs_uniformMovingHeterogeneousApproximationTupleSum_sub_digit_le
    {r : ℕ} (scale : ℝ) (lower upper : Fin r → ℝ)
    (tuples : Finset (Fin r → ℕ)) :
    |uniformMovingHeterogeneousApproximationTupleSum
          scale lower upper tuples -
        uniformMovingHeterogeneousDigitTupleSum
          scale lower upper tuples| ≤
      ∑ t ∈ tuples,
        uniform01Measure.real
          (gaussHeterogeneousApproximationTupleEvent
              scale lower upper t ∆
            gaussHeterogeneousDigitWindowTupleEvent
              scale lower upper t) := by
  classical
  unfold uniformMovingHeterogeneousApproximationTupleSum
    uniformMovingHeterogeneousDigitTupleSum
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ t ∈ tuples,
        (uniform01Measure.real
            (gaussHeterogeneousApproximationTupleEvent
              scale lower upper t) -
          uniform01Measure.real
            (gaussHeterogeneousDigitWindowTupleEvent
              scale lower upper t))| ≤
        ∑ t ∈ tuples,
          |uniform01Measure.real
              (gaussHeterogeneousApproximationTupleEvent
                scale lower upper t) -
            uniform01Measure.real
              (gaussHeterogeneousDigitWindowTupleEvent
                scale lower upper t)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro t _ht
      exact abs_measureReal_sub_le_measureReal_symmDiff
        (measurableSet_gaussHeterogeneousApproximationTupleEvent
          scale lower upper t).nullMeasurableSet
        (measurableSet_gaussHeterogeneousDigitWindowTupleEvent
          scale lower upper t).nullMeasurableSet

/-- The moving-scale exact-to-digit replacement remains `o(1)` under the
original uniform Lebesgue law.  This is a consequence of the absolutely
summed Gauss estimate, not a tuplewise informal change of measure. -/
theorem
    tendsto_uniformMovingHeterogeneousApproximationTupleSum_sub_digit_zero
    {r : ℕ} (hr : 0 < r) {A density : ℝ}
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (lower upper : Fin r → ℝ)
    (hA : 0 ≤ A)
    (hlower : ∀ i, 0 < lower i)
    (hupper : ∀ i, lower i < upper i)
    (hupperA : ∀ i, upper i ≤ A)
    (tuples : ℕ → Finset (Fin r → ℕ))
    (hchronological : ∀ n, ∀ t ∈ tuples n,
      IsChronologicalNatTuple t)
    (htotalDensity : Tendsto
      (fun n : ℕ ↦ ((tuples n).card : ℝ) / (scale n) ^ r)
      atTop (𝓝 density)) :
    Tendsto
      (fun n : ℕ ↦
        uniformMovingHeterogeneousApproximationTupleSum
            (scale n) lower upper (tuples n) -
          uniformMovingHeterogeneousDigitTupleSum
            (scale n) lower upper (tuples n))
      atTop (𝓝 0) := by
  let gaussErr : ℕ → ℝ := fun n ↦
    ∑ t ∈ tuples n,
      gaussMeasure.real
        (gaussHeterogeneousApproximationTupleEvent
            (scale n) lower upper t ∆
          gaussHeterogeneousDigitWindowTupleEvent
            (scale n) lower upper t)
  let uniformErr : ℕ → ℝ := fun n ↦
    ∑ t ∈ tuples n,
      uniform01Measure.real
        (gaussHeterogeneousApproximationTupleEvent
            (scale n) lower upper t ∆
          gaussHeterogeneousDigitWindowTupleEvent
            (scale n) lower upper t)
  have hgauss :
      Tendsto gaussErr atTop (𝓝 0) := by
    simpa only [gaussErr] using!
      tendsto_sum_gaussMeasure_real_symmDiff_movingHeterogeneousTuples_zero
        hr scale hscale lower upper hA hlower hupper hupperA
          tuples hchronological htotalDensity
  have hscaled :
      Tendsto (fun n ↦ (2 * Real.log 2) * gaussErr n)
        atTop (𝓝 0) := by
    simpa only [mul_zero] using! tendsto_const_nhds.mul hgauss
  have huniform : Tendsto uniformErr atTop (𝓝 0) := by
    apply squeeze_zero'
    · exact Eventually.of_forall fun n ↦
        Finset.sum_nonneg fun _t _ht ↦ measureReal_nonneg
    · exact Eventually.of_forall fun n ↦ by
        dsimp only [uniformErr, gaussErr]
        calc
          (∑ t ∈ tuples n,
              uniform01Measure.real
                (gaussHeterogeneousApproximationTupleEvent
                    (scale n) lower upper t ∆
                  gaussHeterogeneousDigitWindowTupleEvent
                    (scale n) lower upper t)) ≤
              ∑ t ∈ tuples n,
                (2 * Real.log 2) *
                  gaussMeasure.real
                    (gaussHeterogeneousApproximationTupleEvent
                        (scale n) lower upper t ∆
                      gaussHeterogeneousDigitWindowTupleEvent
                        (scale n) lower upper t) := by
            apply Finset.sum_le_sum
            intro t _ht
            exact uniform01MeasureReal_le_gaussMeasureReal
              ((measurableSet_gaussHeterogeneousApproximationTupleEvent
                (scale n) lower upper t).symmDiff
                (measurableSet_gaussHeterogeneousDigitWindowTupleEvent
                  (scale n) lower upper t))
          _ = (2 * Real.log 2) *
              ∑ t ∈ tuples n,
                gaussMeasure.real
                  (gaussHeterogeneousApproximationTupleEvent
                      (scale n) lower upper t ∆
                    gaussHeterogeneousDigitWindowTupleEvent
                      (scale n) lower upper t) := by
            rw [Finset.mul_sum]
    · exact hscaled
  rw [tendsto_zero_iff_abs_tendsto_zero]
  apply squeeze_zero'
  · exact Eventually.of_forall fun _n ↦ abs_nonneg _
  · filter_upwards with n
    exact
      abs_uniformMovingHeterogeneousApproximationTupleSum_sub_digit_le
        (scale n) lower upper (tuples n)
  · exact huniform

/-- Final heterogeneous factorial limit at a genuinely independent moving
real scale. -/
theorem tendsto_gaussMovingHeterogeneousApproximationTupleSum
    {r : ℕ} (hr : 0 < r) {A density : ℝ}
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (lower upper : Fin r → ℝ)
    (hA : 0 ≤ A)
    (hlower : ∀ i, 0 < lower i)
    (hupper : ∀ i, lower i < upper i)
    (hupperA : ∀ i, upper i ≤ A)
    (gap : ℕ → ℕ) (hgapTop : Tendsto gap atTop atTop)
    (hgapPos : ∀ᶠ n : ℕ in atTop, 0 < gap n)
    (tuples : ℕ → Finset (Fin r → ℕ))
    (hchronological : ∀ n, ∀ t ∈ tuples n,
      IsChronologicalNatTuple t)
    (htotalDensity : Tendsto
      (fun n : ℕ ↦ ((tuples n).card : ℝ) / (scale n) ^ r)
      atTop (𝓝 density))
    (hshortDensity : Tendsto
      (fun n : ℕ ↦
        ((shortNatTupleFamily (gap n) (tuples n)).card : ℝ) /
          (scale n) ^ r)
      atTop (𝓝 0)) :
    Tendsto
      (fun n : ℕ ↦
        gaussMovingHeterogeneousApproximationTupleSum
          (scale n) lower upper (tuples n))
      atTop
      (𝓝 (density *
        ∏ i, (upper i - lower i) / Real.log 2)) := by
  have hreplacement :=
    tendsto_gaussMovingHeterogeneousApproximationTupleSum_sub_digit_zero
      hr scale hscale lower upper hA hlower hupper hupperA
        tuples hchronological htotalDensity
  have hdigit :=
    tendsto_gaussMovingHeterogeneousDigitTupleSum
      hr scale hscale lower upper hlower hupper gap hgapTop hgapPos
        tuples hchronological htotalDensity hshortDensity
  have hadd := hreplacement.add hdigit
  have hadd' :
      Tendsto
        (fun n : ℕ ↦
          (gaussMovingHeterogeneousApproximationTupleSum
              (scale n) lower upper (tuples n) -
            gaussMovingHeterogeneousDigitTupleSum
              (scale n) lower upper (tuples n)) +
            gaussMovingHeterogeneousDigitTupleSum
              (scale n) lower upper (tuples n))
        atTop
        (𝓝 (density *
          ∏ i, (upper i - lower i) / Real.log 2)) := by
    simpa only [zero_add] using! hadd
  apply hadd'.congr'
  filter_upwards with n
  ring

/-! ## Signed windows with prescribed parity -/

/-- Signed exact approximation tuple sum at an independent real scale. -/
def gaussMovingSignedApproximationTupleSum
    {r : ℕ} (scale : ℝ) (signedLower signedUpper : Fin r → ℝ)
    (tuples : Finset (Fin r → ℕ)) : ℝ :=
  ∑ t ∈ tuples,
    gaussMeasure.real
      (gaussSignedApproximationTupleEvent
        scale signedLower signedUpper t)

/-- On a family with prescribed coordinatewise parity, signed windows are
literally the corresponding positive heterogeneous windows. -/
theorem gaussMovingSignedApproximationTupleSum_eq_oriented
    {r : ℕ} (scale : ℝ) (parity : Fin r → Fin 2)
    (signedLower signedUpper : Fin r → ℝ)
    (tuples : Finset (Fin r → ℕ))
    (hparity : ∀ t ∈ tuples, ∀ i,
      t i % 2 = (parity i).1) :
    gaussMovingSignedApproximationTupleSum
        scale signedLower signedUpper tuples =
      gaussMovingHeterogeneousApproximationTupleSum scale
        (gaussPrescribedParityOrientedLower
          parity signedLower signedUpper)
        (gaussPrescribedParityOrientedUpper
          parity signedLower signedUpper)
        tuples := by
  classical
  unfold gaussMovingSignedApproximationTupleSum
    gaussMovingHeterogeneousApproximationTupleSum
  apply Finset.sum_congr rfl
  intro t ht
  have hlower :
      (fun i ↦ gaussParityOrientedLower
          (t i) (signedLower i) (signedUpper i)) =
        gaussPrescribedParityOrientedLower
          parity signedLower signedUpper := by
    funext i
    exact gaussParityOrientedLower_eq_of_mod_two_eq
      (by
        rw [Nat.mod_eq_of_lt (parity i).isLt]
        exact hparity t ht i)
      (signedLower i) (signedUpper i)
  have hupper :
      (fun i ↦ gaussParityOrientedUpper
          (t i) (signedLower i) (signedUpper i)) =
        gaussPrescribedParityOrientedUpper
          parity signedLower signedUpper := by
    funext i
    exact gaussParityOrientedUpper_eq_of_mod_two_eq
      (by
        rw [Nat.mod_eq_of_lt (parity i).isLt]
        exact hparity t ht i)
      (signedLower i) (signedUpper i)
  rw [gaussSignedApproximationTupleEvent_eq_oriented, hlower, hupper]

/-- Signed moving-scale factorial limit.  The parity assumption is exact
and finite at every scale; no asymptotic sign convention is hidden. -/
theorem tendsto_gaussMovingSignedApproximationTupleSum
    {r : ℕ} (hr : 0 < r) {A density : ℝ}
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (signedLower signedUpper : Fin r → ℝ)
    (parity : Fin r → Fin 2)
    (hA : 0 ≤ A)
    (hlower : ∀ i, 0 <
      gaussPrescribedParityOrientedLower
        parity signedLower signedUpper i)
    (hupper : ∀ i,
      gaussPrescribedParityOrientedLower
          parity signedLower signedUpper i <
        gaussPrescribedParityOrientedUpper
          parity signedLower signedUpper i)
    (hupperA : ∀ i,
      gaussPrescribedParityOrientedUpper
        parity signedLower signedUpper i ≤ A)
    (gap : ℕ → ℕ) (hgapTop : Tendsto gap atTop atTop)
    (hgapPos : ∀ᶠ n : ℕ in atTop, 0 < gap n)
    (tuples : ℕ → Finset (Fin r → ℕ))
    (hchronological : ∀ n, ∀ t ∈ tuples n,
      IsChronologicalNatTuple t)
    (hparity : ∀ n, ∀ t ∈ tuples n, ∀ i,
      t i % 2 = (parity i).1)
    (htotalDensity : Tendsto
      (fun n : ℕ ↦ ((tuples n).card : ℝ) / (scale n) ^ r)
      atTop (𝓝 density))
    (hshortDensity : Tendsto
      (fun n : ℕ ↦
        ((shortNatTupleFamily (gap n) (tuples n)).card : ℝ) /
          (scale n) ^ r)
      atTop (𝓝 0)) :
    Tendsto
      (fun n : ℕ ↦
        gaussMovingSignedApproximationTupleSum
          (scale n) signedLower signedUpper (tuples n))
      atTop
      (𝓝 (density *
        ∏ i,
          (gaussPrescribedParityOrientedUpper
              parity signedLower signedUpper i -
            gaussPrescribedParityOrientedLower
              parity signedLower signedUpper i) / Real.log 2)) := by
  have hpositive :=
    tendsto_gaussMovingHeterogeneousApproximationTupleSum
      hr scale hscale
      (gaussPrescribedParityOrientedLower
        parity signedLower signedUpper)
      (gaussPrescribedParityOrientedUpper
        parity signedLower signedUpper)
      hA hlower hupper hupperA gap hgapTop hgapPos tuples
      hchronological htotalDensity hshortDensity
  apply hpositive.congr'
  filter_upwards with n
  exact
    (gaussMovingSignedApproximationTupleSum_eq_oriented
      (scale n) parity signedLower signedUpper
      (tuples n) (hparity n)).symm

end

end Erdos1002
