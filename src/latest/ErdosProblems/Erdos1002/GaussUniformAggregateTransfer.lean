import ErdosProblems.Erdos1002.GaussHeterogeneousMovingScaleAggregate
import ErdosProblems.Erdos1002.GaussTransferCorrelation
import ErdosProblems.Erdos1002.UnitTorusFourierMeasureConvergence

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Aggregate transfer from Gauss to uniform Lebesgue measure

The original probability law in the Erdős problem is uniform Lebesgue
measure, whereas the continued-fraction digit process is stationary under
Gauss measure.  This file carries out that change of measure at the level of
the complete tagged tuple sum.  In particular, no individual canonical-order
density limit is assumed.
-/

open Filter MeasureTheory Set Finset
open scoped BigOperators Topology symmDiff

namespace Erdos1002

noncomputable section

local instance gaussUniformAggregateTransferPropDecidable (P : Prop) :
    Decidable P := Classical.propDecidable P

variable {β : Type*} [Fintype β]

/-- Real-valued form of the exact Lebesgue-to-Gauss change of measure. -/
theorem integral_uniform01_real_eq_integral_gaussLebesguePrefixWeight_mul
    (f : ℝ → ℝ) :
    (∫ x, f x ∂uniform01Measure) =
      ∫ x, gaussLebesguePrefixWeight x * f x ∂gaussMeasure := by
  rw [uniform01Measure_eq_gaussMeasure_withDensity,
    integral_withDensity_eq_integral_toReal_smul
      measurable_lebesgueOverGaussDensity
      (Eventually.of_forall fun _x ↦ ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [gaussMeasure_unit_ae] with x hx
  have hxIcc : x ∈ Icc (0 : ℝ) 1 := ⟨hx.1.le, hx.2⟩
  have hnonneg : 0 ≤ lebesgueOverGaussDensityReal x :=
    (lebesgueOverGaussDensityReal_bounds hxIcc).1.trans'
      (Real.log_pos one_lt_two).le
  change
    (ENNReal.ofReal (lebesgueOverGaussDensityReal x)).toReal • f x =
      gaussLebesguePrefixWeight x * f x
  rw [ENNReal.toReal_ofReal hnonneg]
  simp only [gaussLebesguePrefixWeight, smul_eq_mul]

theorem gaussLebesguePrefixWeight_unit_nonnegative :
    GaussUnitNonnegative gaussLebesguePrefixWeight := by
  intro x hx
  exact (Real.log_pos one_lt_two).le.trans
    (gaussLebesguePrefixWeight_bounds hx).1

theorem gaussLebesguePrefixWeight_unit_upper :
    GaussUnitUpperBound (2 * Real.log 2) gaussLebesguePrefixWeight := by
  intro x hx
  exact (gaussLebesguePrefixWeight_bounds hx).2

theorem gaussLebesguePrefixWeight_unit_lipschitz :
    GaussUnitLipschitzBound (Real.log 2)
      gaussLebesguePrefixWeight := by
  intro x hx y hy
  rw [abs_gaussLebesguePrefixWeight_sub]

theorem integral_gaussLebesguePrefixWeight_eq_one :
    (∫ x, gaussLebesguePrefixWeight x ∂gaussMeasure) = 1 := by
  have h :=
    integral_uniform01_real_eq_integral_gaussLebesguePrefixWeight_mul
      (fun _x : ℝ ↦ (1 : ℝ))
  symm
  simpa only [integral_const, probReal_univ, one_smul,
    mul_one] using! h

/-- A future event pulled back from depth `m` has uniform-Lebesgue mass
exponentially close to its stationary Gauss mass. -/
theorem abs_uniform01Measure_real_gaussOrbit_preimage_sub_gaussMeasure_le
    {H : Set ℝ} (hH : MeasurableSet H) (m : ℕ) :
    |uniform01Measure.real ((gaussOrbit m) ⁻¹' H) -
        gaussMeasure.real H| ≤
      (527 / 540 : ℝ) ^ m * Real.log 2 := by
  let g : ℝ → ℝ := H.indicator (fun _x ↦ (1 : ℝ))
  have hgM : Measurable g := measurable_const.indicator hH
  have hgBound : ∀ y, |g y| ≤ 1 := by
    intro y
    by_cases hyH : y ∈ H <;> simp [g, hyH]
  have hgInt : Integrable g gaussMeasure := by
    apply Integrable.of_bound hgM.aestronglyMeasurable 1
    exact Eventually.of_forall fun y ↦ by
      simpa only [Real.norm_eq_abs] using! hgBound y
  have hchange :
      uniform01Measure.real ((gaussOrbit m) ⁻¹' H) =
        ∫ x, gaussLebesguePrefixWeight x *
          g (gaussOrbit m x) ∂gaussMeasure := by
    rw [← integral_uniform01_real_eq_integral_gaussLebesguePrefixWeight_mul
      (fun x ↦ g (gaussOrbit m x))]
    rw [show (fun x ↦ g (gaussOrbit m x)) =
        ((gaussOrbit m) ⁻¹' H).indicator (fun _x ↦ (1 : ℝ)) by
      funext x
      by_cases hx : gaussOrbit m x ∈ H <;>
        simp [g, hx]]
    exact (integral_indicator_one
      (hH.preimage (measurable_gaussOrbit m))).symm
  have htransfer :=
    integral_mul_comp_gaussOrbit_eq_gaussTransfer_iterate
      measurable_gaussLebesguePrefixWeight hgM
      gaussLebesguePrefixWeight_unit_nonnegative
      gaussLebesguePrefixWeight_unit_upper m
  have hgauss :
      gaussMeasure.real H =
        ∫ y, (1 : ℝ) * g y ∂gaussMeasure := by
    calc
      gaussMeasure.real H = ∫ y, g y ∂gaussMeasure :=
        (integral_indicator_one hH).symm
      _ = ∫ y, (1 : ℝ) * g y ∂gaussMeasure := by
        congr 1
        funext y
        rw [one_mul]
  let Pm : ℝ → ℝ :=
    (gaussTransfer^[m]) gaussLebesguePrefixWeight
  have hPmInt : Integrable Pm gaussMeasure :=
    integrable_gaussTransfer_iterate_of_unit_bounds
      measurable_gaussLebesguePrefixWeight
      gaussLebesguePrefixWeight_unit_nonnegative
      gaussLebesguePrefixWeight_unit_upper m
  have hPmProd : Integrable (fun y ↦ Pm y * g y) gaussMeasure := by
    apply hPmInt.mul_bdd hgM.aestronglyMeasurable
    exact Eventually.of_forall fun y ↦ by
      simpa only [Real.norm_eq_abs] using! hgBound y
  have honeProd : Integrable (fun y ↦ (1 : ℝ) * g y) gaussMeasure := by
    simpa only [one_mul] using! hgInt
  rw [hchange, htransfer, hgauss,
    ← integral_sub hPmProd honeProd]
  change
    |∫ y, Pm y * g y - 1 * g y ∂gaussMeasure| ≤ _
  calc
    |∫ y, Pm y * g y - 1 * g y ∂gaussMeasure| ≤
        ∫ y, |Pm y * g y - 1 * g y| ∂gaussMeasure :=
      abs_integral_le_integral_abs
    _ ≤ ∫ _y, (527 / 540 : ℝ) ^ m * Real.log 2
        ∂gaussMeasure := by
      apply integral_mono_ae (hPmProd.sub honeProd).abs
        (integrable_const _)
      filter_upwards [gaussMeasure_unit_ae] with y hy
      have hycc : y ∈ Icc (0 : ℝ) 1 := ⟨hy.1.le, hy.2⟩
      have hpoint :=
        abs_gaussTransfer_iterate_sub_integral_le
          (Real.log_pos one_lt_two).le
          measurable_gaussLebesguePrefixWeight
          gaussLebesguePrefixWeight_unit_nonnegative
          gaussLebesguePrefixWeight_unit_upper
          gaussLebesguePrefixWeight_unit_lipschitz m hycc
      rw [integral_gaussLebesguePrefixWeight_eq_one] at hpoint
      change |Pm y * g y - 1 * g y| ≤ _
      rw [show Pm y * g y - 1 * g y = (Pm y - 1) * g y by ring,
        abs_mul]
      exact (mul_le_mul hpoint (hgBound y) (abs_nonneg _)
        (mul_nonneg (by positivity)
          (Real.log_pos one_lt_two).le)).trans_eq (mul_one _)
    _ = (527 / 540 : ℝ) ^ m * Real.log 2 := by simp

/-- Uniform Lebesgue measure, like Gauss measure, is supported on the
continued-fraction state interval. -/
theorem uniform01Measure_unit_ae :
    ∀ᵐ x ∂uniform01Measure, x ∈ Ioc (0 : ℝ) 1 := by
  rw [uniform01Measure]
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  exact ⟨hx.1, hx.2.le⟩

/-- The common state-interval restriction in the digit-window event is
also redundant under the original uniform law. -/
theorem uniform01Measure_real_heterogeneousDigitWindowTupleEvent_eq_pure
    {r : ℕ} (hr : 0 < r) (scale : ℝ)
    (lower upper : Fin r → ℝ) (times : Fin r → ℕ) :
    uniform01Measure.real
        (gaussHeterogeneousDigitWindowTupleEvent
          scale lower upper times) =
      uniform01Measure.real
        (gaussHeterogeneousDigitTupleEvent
          scale lower upper times) := by
  let U : Set ℝ := Ioc (0 : ℝ) 1
  let H : Set ℝ := gaussHeterogeneousDigitTupleEvent
    scale lower upper times
  have hset : gaussHeterogeneousDigitWindowTupleEvent
      scale lower upper times = U ∩ H := by
    ext x
    simp only [gaussHeterogeneousDigitWindowTupleEvent,
      gaussHeterogeneousDigitTupleEvent,
      mem_orderedEventIntersection_ofFn_iff,
      gaussDigitWindowAt, mem_inter_iff, Set.mem_preimage, U, H]
    constructor
    · intro hall
      exact ⟨(hall ⟨0, hr⟩).1, fun i ↦ (hall i).2⟩
    · rintro ⟨hxU, hxH⟩ i
      exact ⟨hxU, hxH i⟩
  rw [hset]
  apply measureReal_congr
  filter_upwards [uniform01Measure_unit_ae] with x hx
  change ((x ∈ Ioc (0 : ℝ) 1) ∧ x ∈ H) = (x ∈ H)
  apply propext
  exact and_iff_right hx

/-- A chronological heterogeneous digit tuple is a pullback of a measurable
future event from its first selected depth. -/
theorem gaussHeterogeneousDigitTupleEvent_eq_firstDepth_preimage
    {r : ℕ} (hr : 0 < r) (scale : ℝ)
    (lower upper : Fin r → ℝ) (times : Fin r → ℕ)
    (hchronological : IsChronologicalNatTuple times) :
    gaussHeterogeneousDigitTupleEvent scale lower upper times =
      (gaussOrbit (times ⟨0, hr⟩)) ⁻¹'
        shiftedGaussTailEvent (times ⟨0, hr⟩) times
          (fun i ↦ scaledGaussFirstDigitWindow
            scale (lower i) (upper i)) := by
  have hbase : ∀ i, times ⟨0, hr⟩ ≤ times i := by
    intro i
    by_cases hi : (⟨0, hr⟩ : Fin r) = i
    · subst i
      exact le_rfl
    · have hlt : (⟨0, hr⟩ : Fin r) < i := by
        exact Fin.lt_def.mpr (by
          have hi0 : i.val ≠ 0 := by
            intro hiz
            apply hi
            exact Fin.ext hiz.symm
          exact Nat.pos_of_ne_zero hi0)
      exact (Nat.le_add_right _ 1).trans
        (hchronological ⟨0, hr⟩ i hlt)
  have hpre := shiftedGaussTailEvent_preimage
    (base := times ⟨0, hr⟩) (times := times)
    (events := fun i ↦ scaledGaussFirstDigitWindow
      scale (lower i) (upper i)) hbase
  simpa only [gaussHeterogeneousDigitTupleEvent] using! hpre.symm

/-- Per-tuple uniform-to-Gauss error, controlled only by the first selected
depth.  This is the estimate summed over the complete tagged family below. -/
theorem
    abs_uniform01Measure_real_heterogeneousDigitWindowTupleEvent_sub_gauss_le
    {r : ℕ} (hr : 0 < r) (scale : ℝ)
    (lower upper : Fin r → ℝ) (times : Fin r → ℕ)
    (hchronological : IsChronologicalNatTuple times) :
    |uniform01Measure.real
        (gaussHeterogeneousDigitWindowTupleEvent
          scale lower upper times) -
      gaussMeasure.real
        (gaussHeterogeneousDigitWindowTupleEvent
          scale lower upper times)| ≤
      (527 / 540 : ℝ) ^ (times ⟨0, hr⟩) * Real.log 2 := by
  let H : Set ℝ :=
    shiftedGaussTailEvent (times ⟨0, hr⟩) times
      (fun i ↦ scaledGaussFirstDigitWindow
        scale (lower i) (upper i))
  have hHM : MeasurableSet H :=
    measurableSet_shiftedGaussTailEvent fun i ↦
      measurableSet_scaledGaussFirstDigitWindow
        scale (lower i) (upper i)
  rw [
    uniform01Measure_real_heterogeneousDigitWindowTupleEvent_eq_pure
      hr scale lower upper times,
    gaussMeasure_real_heterogeneousDigitWindowTupleEvent_eq_pure
      hr scale lower upper times,
    gaussHeterogeneousDigitTupleEvent_eq_firstDepth_preimage
      hr scale lower upper times hchronological]
  have hstationary := gaussMeasure_real_gaussOrbit_preimage
    (times ⟨0, hr⟩) hHM
  rw [hstationary]
  exact
    abs_uniform01Measure_real_gaussOrbit_preimage_sub_gaussMeasure_le
      hHM (times ⟨0, hr⟩)

def aggregateUniformMovingHeterogeneousDigitTupleSum
    {r : ℕ} (scale : ℝ)
    (lower upper : β → Fin r → ℝ)
    (tuples : β → Finset (Fin r → ℕ)) : ℝ :=
  ∑ b, uniformMovingHeterogeneousDigitTupleSum
    scale (lower b) (upper b) (tuples b)

def aggregateUniformMovingHeterogeneousApproximationTupleSum
    {r : ℕ} (scale : ℝ)
    (lower upper : β → Fin r → ℝ)
    (tuples : β → Finset (Fin r → ℕ)) : ℝ :=
  ∑ b, uniformMovingHeterogeneousApproximationTupleSum
    scale (lower b) (upper b) (tuples b)

/-- The exact-to-digit symmetric differences are summable over the complete
tagged family.  The proof uses only the aggregate tuple density, not a
density for each tag. -/
theorem
    tendsto_aggregateGaussHeterogeneousApproximationDigitSymmDiff_zero
    {r : ℕ} (hr : 0 < r) {A density : ℝ}
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (lower upper : β → Fin r → ℝ)
    (hA : 0 ≤ A)
    (hlower : ∀ b i, 0 < lower b i)
    (hupper : ∀ b i, lower b i < upper b i)
    (hupperA : ∀ b i, upper b i ≤ A)
    (tuples : ℕ → β → Finset (Fin r → ℕ))
    (hchronological : ∀ n b, ∀ t ∈ tuples n b,
      IsChronologicalNatTuple t)
    (htotalDensity : Tendsto
      (fun n ↦ (aggregateTupleFamilyCard (tuples n) : ℝ) /
        scale n ^ r) atTop (nhds density)) :
    Tendsto
      (fun n ↦ ∑ b, ∑ t ∈ tuples n b,
        gaussMeasure.real
          (gaussHeterogeneousApproximationTupleEvent
              (scale n) (lower b) (upper b) t ∆
            gaussHeterogeneousDigitWindowTupleEvent
              (scale n) (lower b) (upper b) t))
      atTop (nhds 0) := by
  let C : ℝ :=
    (r : ℝ) * 2 *
      (1 + gaussDigitExponentialRate 1) ^ (r - 1) *
      (26 * A ^ 2 / Real.log 2) *
      ((2 * A + 10 * A ^ 2) / Real.log 2) ^ (r - 1)
  have hscalePos := hscale.eventually_gt_atTop 0
  have hscaleOne := hscale.eventually (eventually_ge_atTop (1 : ℝ))
  have hcomponentBound :=
    eventually_component_card_div_scale_le_of_aggregate_tendsto
      scale hscalePos tuples htotalDensity
  have hCdiv : Tendsto (fun n : ℕ ↦ C / scale n)
      atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hscale
  have herrorComponent : ∀ b,
      Tendsto
        (fun n : ℕ ↦
          ∑ t ∈ tuples n b,
            gaussMeasure.real
              (gaussHeterogeneousApproximationTupleEvent
                  (scale n) (lower b) (upper b) t ∆
                gaussHeterogeneousDigitWindowTupleEvent
                  (scale n) (lower b) (upper b) t))
        atTop (nhds 0) := by
    intro b
    let err : ℕ → ℝ := fun n ↦
      ∑ t ∈ tuples n b,
        gaussMeasure.real
          (gaussHeterogeneousApproximationTupleEvent
              (scale n) (lower b) (upper b) t ∆
            gaussHeterogeneousDigitWindowTupleEvent
              (scale n) (lower b) (upper b) t)
    let normalized : ℕ → ℝ := fun n ↦
      ((tuples n b).card : ℝ) / scale n ^ r
    have hlarge :=
      eventually_movingHeterogeneousApproximationWindow_large
        scale hscale (lower b) (upper b) (hlower b)
    have herrUpper : ∀ᶠ n : ℕ in atTop,
        err n ≤ normalized n * (C / scale n) := by
      filter_upwards [hlarge, hscalePos, hscaleOne] with
        n hlargeN hpos hone
      have hraw :=
        sum_gaussMeasure_real_symmDiff_heterogeneousTuples_le_explicit
          hr (lower b) (upper b) (tuples n b) 1 (by norm_num)
            hpos hone hA (hlower b) (hupper b) (hupperA b)
            hlargeN
            (fun t ht i k hik ↦
              hchronological n b t ht i k hik)
      refine hraw.trans_eq ?_
      dsimp only [C, normalized]
      have hsne : scale n ≠ 0 := ne_of_gt hpos
      have hboundary :
          (26 * A ^ 2 / scale n ^ 2) / Real.log 2 =
            (26 * A ^ 2 / Real.log 2) / scale n ^ 2 := by
        field_simp
      have hwindow :
          ((2 * A + 10 * A ^ 2) / scale n) / Real.log 2 =
            ((2 * A + 10 * A ^ 2) / Real.log 2) /
              scale n := by
        field_simp
      rw [hboundary, hwindow, div_pow]
      have hpow : scale n ^ r =
          scale n ^ (r - 1) * scale n := by
        conv_lhs =>
          rw [show r = (r - 1) + 1 by omega, pow_succ]
      rw [hpow]
      field_simp [hsne]
    have hnormalized0 :
        ∀ᶠ n : ℕ in atTop, 0 ≤ normalized n := by
      filter_upwards [hscalePos] with n hn
      dsimp only [normalized]
      positivity
    have hnormalizedBound :
        ∀ᶠ n : ℕ in atTop,
          normalized n ≤ |density| + 1 := by
      filter_upwards [hcomponentBound] with n hn
      exact hn b
    have hupperZero :=
      tendsto_bounded_nonneg_mul_zero normalized
        (fun n ↦ C / scale n)
        (add_nonneg (abs_nonneg density) zero_le_one)
        hnormalized0 hnormalizedBound hCdiv
    change Tendsto err atTop (nhds 0)
    apply squeeze_zero'
    · exact Eventually.of_forall fun n ↦
        Finset.sum_nonneg fun _t _ht ↦ measureReal_nonneg
    · exact herrUpper
    · exact hupperZero
  simpa using! tendsto_finset_sum Finset.univ
    (fun b _hb ↦ herrorComponent b)

/-- Aggregate exact-to-digit replacement under the original uniform law. -/
theorem
    tendsto_aggregateUniformMovingHeterogeneousApproximationTupleSum_sub_digit_zero
    {r : ℕ} (hr : 0 < r) {A density : ℝ}
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (lower upper : β → Fin r → ℝ)
    (hA : 0 ≤ A)
    (hlower : ∀ b i, 0 < lower b i)
    (hupper : ∀ b i, lower b i < upper b i)
    (hupperA : ∀ b i, upper b i ≤ A)
    (tuples : ℕ → β → Finset (Fin r → ℕ))
    (hchronological : ∀ n b, ∀ t ∈ tuples n b,
      IsChronologicalNatTuple t)
    (htotalDensity : Tendsto
      (fun n ↦ (aggregateTupleFamilyCard (tuples n) : ℝ) /
        scale n ^ r) atTop (nhds density)) :
    Tendsto
      (fun n ↦
        aggregateUniformMovingHeterogeneousApproximationTupleSum
            (scale n) lower upper (tuples n) -
          aggregateUniformMovingHeterogeneousDigitTupleSum
            (scale n) lower upper (tuples n))
      atTop (nhds 0) := by
  let gaussErr : ℕ → ℝ := fun n ↦
    ∑ b, ∑ t ∈ tuples n b,
      gaussMeasure.real
        (gaussHeterogeneousApproximationTupleEvent
            (scale n) (lower b) (upper b) t ∆
          gaussHeterogeneousDigitWindowTupleEvent
            (scale n) (lower b) (upper b) t)
  let uniformErr : ℕ → ℝ := fun n ↦
    ∑ b, ∑ t ∈ tuples n b,
      uniform01Measure.real
        (gaussHeterogeneousApproximationTupleEvent
            (scale n) (lower b) (upper b) t ∆
          gaussHeterogeneousDigitWindowTupleEvent
            (scale n) (lower b) (upper b) t)
  have hgauss : Tendsto gaussErr atTop (nhds 0) := by
    simpa only [gaussErr] using!
      tendsto_aggregateGaussHeterogeneousApproximationDigitSymmDiff_zero
        hr scale hscale lower upper hA hlower hupper hupperA
          tuples hchronological htotalDensity
  have hscaled :
      Tendsto (fun n ↦ (2 * Real.log 2) * gaussErr n)
        atTop (nhds 0) := by
    simpa only [mul_zero] using! tendsto_const_nhds.mul hgauss
  have huniform : Tendsto uniformErr atTop (nhds 0) := by
    apply squeeze_zero'
    · exact Eventually.of_forall fun n ↦
        Finset.sum_nonneg fun _b _hb ↦
          Finset.sum_nonneg fun _t _ht ↦ measureReal_nonneg
    · exact Eventually.of_forall fun n ↦ by
        dsimp only [uniformErr, gaussErr]
        calc
          (∑ b, ∑ t ∈ tuples n b,
              uniform01Measure.real
                (gaussHeterogeneousApproximationTupleEvent
                    (scale n) (lower b) (upper b) t ∆
                  gaussHeterogeneousDigitWindowTupleEvent
                    (scale n) (lower b) (upper b) t)) ≤
              ∑ b, ∑ t ∈ tuples n b,
                (2 * Real.log 2) *
                  gaussMeasure.real
                    (gaussHeterogeneousApproximationTupleEvent
                        (scale n) (lower b) (upper b) t ∆
                      gaussHeterogeneousDigitWindowTupleEvent
                        (scale n) (lower b) (upper b) t) := by
            apply Finset.sum_le_sum
            intro b _hb
            apply Finset.sum_le_sum
            intro t _ht
            exact uniform01MeasureReal_le_gaussMeasureReal
              ((measurableSet_gaussHeterogeneousApproximationTupleEvent
                (scale n) (lower b) (upper b) t).symmDiff
                (measurableSet_gaussHeterogeneousDigitWindowTupleEvent
                  (scale n) (lower b) (upper b) t))
          _ = (2 * Real.log 2) *
              ∑ b, ∑ t ∈ tuples n b,
                gaussMeasure.real
                  (gaussHeterogeneousApproximationTupleEvent
                      (scale n) (lower b) (upper b) t ∆
                    gaussHeterogeneousDigitWindowTupleEvent
                      (scale n) (lower b) (upper b) t) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro b _hb
            rw [Finset.mul_sum]
    · exact hscaled
  rw [tendsto_zero_iff_abs_tendsto_zero]
  apply squeeze_zero'
  · exact Eventually.of_forall fun n ↦ abs_nonneg _
  · filter_upwards with n
    change
      |aggregateUniformMovingHeterogeneousApproximationTupleSum
          (scale n) lower upper (tuples n) -
        aggregateUniformMovingHeterogeneousDigitTupleSum
          (scale n) lower upper (tuples n)| ≤ uniformErr n
    unfold aggregateUniformMovingHeterogeneousApproximationTupleSum
      aggregateUniformMovingHeterogeneousDigitTupleSum
    rw [← Finset.sum_sub_distrib]
    calc
      |∑ b,
          (uniformMovingHeterogeneousApproximationTupleSum
              (scale n) (lower b) (upper b) (tuples n b) -
            uniformMovingHeterogeneousDigitTupleSum
              (scale n) (lower b) (upper b) (tuples n b))| ≤
          ∑ b,
            |uniformMovingHeterogeneousApproximationTupleSum
                (scale n) (lower b) (upper b) (tuples n b) -
              uniformMovingHeterogeneousDigitTupleSum
                (scale n) (lower b) (upper b) (tuples n b)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ uniformErr n := by
        dsimp only [uniformErr]
        apply Finset.sum_le_sum
        intro b _hb
        exact
          abs_uniformMovingHeterogeneousApproximationTupleSum_sub_digit_le
            (scale n) (lower b) (upper b) (tuples n b)
  · exact huniform

/-- Absolutely summed uniform-to-Gauss digit error for a tagged family whose
first selected depth is bounded below. -/
theorem
    abs_aggregateUniformMovingHeterogeneousDigitTupleSum_sub_gauss_le
    {r minDepth : ℕ} (hr : 0 < r) (scale : ℝ)
    (lower upper : β → Fin r → ℝ)
    (tuples : β → Finset (Fin r → ℕ))
    (hchronological : ∀ b, ∀ t ∈ tuples b,
      IsChronologicalNatTuple t)
    (hfirst : ∀ b, ∀ t ∈ tuples b,
      minDepth ≤ t ⟨0, hr⟩) :
    |aggregateUniformMovingHeterogeneousDigitTupleSum
          scale lower upper tuples -
        aggregateGaussMovingHeterogeneousDigitTupleSum
          scale lower upper tuples| ≤
      (aggregateTupleFamilyCard tuples : ℝ) *
        ((527 / 540 : ℝ) ^ minDepth * Real.log 2) := by
  unfold aggregateUniformMovingHeterogeneousDigitTupleSum
    aggregateGaussMovingHeterogeneousDigitTupleSum
    uniformMovingHeterogeneousDigitTupleSum
    gaussMovingHeterogeneousDigitTupleSum
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ b,
        ((∑ t ∈ tuples b,
            uniform01Measure.real
              (gaussHeterogeneousDigitWindowTupleEvent
                scale (lower b) (upper b) t)) -
          ∑ t ∈ tuples b,
            gaussMeasure.real
              (gaussHeterogeneousDigitWindowTupleEvent
                scale (lower b) (upper b) t))| ≤
        ∑ b,
          |(∑ t ∈ tuples b,
              uniform01Measure.real
                (gaussHeterogeneousDigitWindowTupleEvent
                  scale (lower b) (upper b) t)) -
            ∑ t ∈ tuples b,
              gaussMeasure.real
                (gaussHeterogeneousDigitWindowTupleEvent
                  scale (lower b) (upper b) t)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ b, ∑ t ∈ tuples b,
        |uniform01Measure.real
            (gaussHeterogeneousDigitWindowTupleEvent
              scale (lower b) (upper b) t) -
          gaussMeasure.real
            (gaussHeterogeneousDigitWindowTupleEvent
              scale (lower b) (upper b) t)| := by
      apply Finset.sum_le_sum
      intro b _hb
      rw [← Finset.sum_sub_distrib]
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ b, ∑ _t ∈ tuples b,
        (527 / 540 : ℝ) ^ minDepth * Real.log 2 := by
      apply Finset.sum_le_sum
      intro b _hb
      apply Finset.sum_le_sum
      intro t ht
      have htuple :=
        abs_uniform01Measure_real_heterogeneousDigitWindowTupleEvent_sub_gauss_le
          hr scale (lower b) (upper b) t
            (hchronological b t ht)
      refine htuple.trans ?_
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_of_le_one (by norm_num) (by norm_num)
          (hfirst b t ht))
        (Real.log_pos one_lt_two).le
    _ = (aggregateTupleFamilyCard tuples : ℝ) *
        ((527 / 540 : ℝ) ^ minDepth * Real.log 2) := by
      unfold aggregateTupleFamilyCard
      simp only [sum_const, nsmul_eq_mul, Nat.cast_sum]
      rw [Finset.sum_mul]

/-- Aggregate digit sums under uniform and Gauss measure have the same
limit whenever the complete tuple count times the transfer decay vanishes. -/
theorem
    tendsto_aggregateUniformMovingHeterogeneousDigitTupleSum_sub_gauss_zero
    {r : ℕ} (hr : 0 < r)
    (scale : ℕ → ℝ)
    (lower upper : β → Fin r → ℝ)
    (tuples : ℕ → β → Finset (Fin r → ℕ))
    (minDepth : ℕ → ℕ)
    (hchronological : ∀ n b, ∀ t ∈ tuples n b,
      IsChronologicalNatTuple t)
    (hfirst : ∀ᶠ n : ℕ in atTop, ∀ b, ∀ t ∈ tuples n b,
      minDepth n ≤ t ⟨0, hr⟩)
    (hdecay : Tendsto
      (fun n ↦ (aggregateTupleFamilyCard (tuples n) : ℝ) *
        ((527 / 540 : ℝ) ^ minDepth n * Real.log 2))
      atTop (nhds 0)) :
    Tendsto
      (fun n ↦
        aggregateUniformMovingHeterogeneousDigitTupleSum
            (scale n) lower upper (tuples n) -
          aggregateGaussMovingHeterogeneousDigitTupleSum
            (scale n) lower upper (tuples n))
      atTop (nhds 0) := by
  rw [tendsto_zero_iff_abs_tendsto_zero]
  apply squeeze_zero'
  · exact Eventually.of_forall fun n ↦ abs_nonneg _
  · filter_upwards [hfirst] with n hn
    exact
      abs_aggregateUniformMovingHeterogeneousDigitTupleSum_sub_gauss_le
        hr (scale n) lower upper (tuples n)
          (hchronological n) hn
  · exact hdecay

/-- Polynomially many tuples are harmless when the first selected depth is
asymptotically a positive multiple of the moving real scale. -/
theorem
    tendsto_aggregateTupleFamilyCard_mul_transferDecay_of_depth_ratio
    {r : ℕ} {density d : ℝ}
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (tuples : ℕ → β → Finset (Fin r → ℕ))
    (htotalDensity : Tendsto
      (fun n ↦ (aggregateTupleFamilyCard (tuples n) : ℝ) /
        scale n ^ r) atTop (nhds density))
    (depth : ℕ → ℕ) (hd : 0 < d)
    (hdepthRatio : Tendsto
      (fun n ↦ (depth n : ℝ) / scale n)
      atTop (nhds d)) :
    Tendsto
      (fun n ↦ (aggregateTupleFamilyCard (tuples n) : ℝ) *
        ((527 / 540 : ℝ) ^ depth n * Real.log 2))
      atTop (nhds 0) := by
  have hscalePos := hscale.eventually_gt_atTop 0
  have hratioLower : ∀ᶠ n : ℕ in atTop,
      d / 2 ≤ (depth n : ℝ) / scale n := by
    have hhalf : d / 2 < d := by linarith
    exact hdepthRatio.eventually (Ioi_mem_nhds hhalf) |>.mono
      fun _n hn ↦ hn.le
  have hdepthCastTop :
      Tendsto (fun n ↦ (depth n : ℝ)) atTop atTop := by
    rw [tendsto_atTop]
    intro B
    have htarget : Tendsto
        (fun n ↦ scale n) atTop atTop := hscale
    have hlarge : ∀ᶠ n : ℕ in atTop,
        max 1 (2 * max B 0 / d) ≤ scale n :=
      htarget.eventually (eventually_ge_atTop _)
    filter_upwards [hratioLower, hlarge] with n hratio hn
    have hspos : 0 < scale n := lt_of_lt_of_le
      (by norm_num) (le_trans (le_max_left _ _) hn)
    have hB0 : 0 ≤ max B 0 := le_max_right _ _
    have hscaleB : 2 * max B 0 / d ≤ scale n :=
      (le_max_right _ _).trans hn
    have hratioNonneg :
        0 ≤ (depth n : ℝ) / scale n := by positivity
    have hprod :
        d / 2 * (2 * max B 0 / d) ≤
          ((depth n : ℝ) / scale n) * scale n := by
      exact mul_le_mul hratio hscaleB
        (by positivity) (by linarith)
    have heq :
        ((depth n : ℝ) / scale n) * scale n = depth n := by
      field_simp
    rw [heq] at hprod
    have hleft :
        d / 2 * (2 * max B 0 / d) = max B 0 := by
      field_simp [ne_of_gt hd]
    rw [hleft] at hprod
    exact (le_max_left B 0).trans hprod
  have hdepthTop : Tendsto depth atTop atTop :=
    tendsto_natCast_atTop_iff.mp hdepthCastTop
  have hdepthPos : ∀ᶠ n : ℕ in atTop, 0 < depth n :=
    hdepthTop.eventually_gt_atTop 0
  have hscaleDivDepth : Tendsto
      (fun n ↦ scale n / (depth n : ℝ))
      atTop (nhds d⁻¹) := by
    have hinv := hdepthRatio.inv₀ (ne_of_gt hd)
    apply hinv.congr'
    filter_upwards [hscalePos, hdepthPos] with n hs hn
    field_simp [ne_of_gt hs, Nat.ne_of_gt hn]
  have hgeometric :=
    tendsto_pow_const_mul_const_pow_of_lt_one r
      (by norm_num : (0 : ℝ) ≤ 527 / 540)
      (by norm_num : (527 / 540 : ℝ) < 1)
  have hdepthGeometric : Tendsto
      (fun n ↦ (depth n : ℝ) ^ r *
        (527 / 540 : ℝ) ^ depth n)
      atTop (nhds 0) :=
    hgeometric.comp hdepthTop
  have hscaleGeometricRaw :=
    (hscaleDivDepth.pow r).mul hdepthGeometric
  have hscaleGeometric : Tendsto
      (fun n ↦ scale n ^ r *
        (527 / 540 : ℝ) ^ depth n)
      atTop (nhds 0) := by
    have hscaleGeometricRaw' : Tendsto
        (fun n ↦
          (scale n / (depth n : ℝ)) ^ r *
            ((depth n : ℝ) ^ r *
              (527 / 540 : ℝ) ^ depth n))
        atTop (nhds 0) := by
      simpa only [mul_zero] using! hscaleGeometricRaw
    apply hscaleGeometricRaw'.congr'
    filter_upwards [hdepthPos] with n hn
    have hdne : (depth n : ℝ) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt hn
    rw [div_pow]
    field_simp [hdne]
  have hproduct :=
    (htotalDensity.mul hscaleGeometric).mul
      (tendsto_const_nhds :
        Tendsto (fun _n : ℕ ↦ Real.log 2)
          atTop (nhds (Real.log 2)))
  have hproduct' : Tendsto
      (fun n ↦
        ((aggregateTupleFamilyCard (tuples n) : ℝ) /
            scale n ^ r) *
          (scale n ^ r *
            (527 / 540 : ℝ) ^ depth n) *
          Real.log 2)
      atTop (nhds 0) := by
    simpa only [mul_zero, zero_mul] using! hproduct
  apply hproduct'.congr'
  filter_upwards [hscalePos] with n hn
  have hsne : scale n ≠ 0 := ne_of_gt hn
  field_simp [hsne]

/-- Aggregate heterogeneous factorial limit under the literal uniform
Lebesgue law. -/
theorem
    tendsto_aggregateUniformMovingHeterogeneousApproximationTupleSum
    {r : ℕ} (hr : 0 < r) {A density common : ℝ}
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (lower upper : β → Fin r → ℝ)
    (hA : 0 ≤ A)
    (hlower : ∀ b i, 0 < lower b i)
    (hupper : ∀ b i, lower b i < upper b i)
    (hupperA : ∀ b i, upper b i ≤ A)
    (hcommon : ∀ b,
      (∏ i, (upper b i - lower b i) / Real.log 2) = common)
    (gap : ℕ → ℕ) (hgapTop : Tendsto gap atTop atTop)
    (hgapPos : ∀ᶠ n : ℕ in atTop, 0 < gap n)
    (tuples : ℕ → β → Finset (Fin r → ℕ))
    (hchronological : ∀ n b, ∀ t ∈ tuples n b,
      IsChronologicalNatTuple t)
    (htotalDensity : Tendsto
      (fun n ↦ (aggregateTupleFamilyCard (tuples n) : ℝ) /
        scale n ^ r) atTop (nhds density))
    (hshortDensity : Tendsto
      (fun n ↦
        (aggregateShortTupleFamilyCard
          (gap := gap n) (tuples n) : ℝ) /
            scale n ^ r)
      atTop (nhds 0))
    (minDepth : ℕ → ℕ)
    (hfirst : ∀ᶠ n : ℕ in atTop, ∀ b, ∀ t ∈ tuples n b,
      minDepth n ≤ t ⟨0, hr⟩)
    (hdecay : Tendsto
      (fun n ↦ (aggregateTupleFamilyCard (tuples n) : ℝ) *
        ((527 / 540 : ℝ) ^ minDepth n * Real.log 2))
      atTop (nhds 0)) :
    Tendsto
      (fun n ↦
        aggregateUniformMovingHeterogeneousApproximationTupleSum
          (scale n) lower upper (tuples n))
      atTop (nhds (density * common)) := by
  have hreplacement :=
    tendsto_aggregateUniformMovingHeterogeneousApproximationTupleSum_sub_digit_zero
      hr scale hscale lower upper hA hlower hupper hupperA
        tuples hchronological htotalDensity
  have htransfer :=
    tendsto_aggregateUniformMovingHeterogeneousDigitTupleSum_sub_gauss_zero
      hr scale lower upper tuples minDepth hchronological hfirst hdecay
  have hgauss :=
    tendsto_aggregateGaussMovingHeterogeneousDigitTupleSum
      hr scale hscale lower upper hlower hupper hcommon
        gap hgapTop hgapPos tuples hchronological
        htotalDensity hshortDensity
  have hsum := (hreplacement.add htransfer).add hgauss
  have hsum' : Tendsto
      (fun n ↦
        (aggregateUniformMovingHeterogeneousApproximationTupleSum
            (scale n) lower upper (tuples n) -
          aggregateUniformMovingHeterogeneousDigitTupleSum
            (scale n) lower upper (tuples n)) +
        (aggregateUniformMovingHeterogeneousDigitTupleSum
            (scale n) lower upper (tuples n) -
          aggregateGaussMovingHeterogeneousDigitTupleSum
            (scale n) lower upper (tuples n)) +
        aggregateGaussMovingHeterogeneousDigitTupleSum
          (scale n) lower upper (tuples n))
      atTop (nhds (density * common)) := by
    simpa only [zero_add] using! hsum
  apply hsum'.congr'
  filter_upwards with n
  ring

/-- Exact orientation identity for the aggregate uniform signed mass. -/
theorem
    aggregateUniformMovingSignedApproximationTupleMassSum_eq_oriented
    {r : ℕ} (scale : ℝ)
    (signedLower signedUpper : β → Fin r → ℝ)
    (parity : β → Fin r → Fin 2)
    (tuples : β → Finset (Fin r → ℕ))
    (hparity : ∀ b, ∀ t ∈ tuples b, ∀ i,
      t i % 2 = (parity b i).1) :
    aggregateUniformMovingSignedApproximationTupleMassSum
        scale signedLower signedUpper tuples =
      aggregateUniformMovingHeterogeneousApproximationTupleSum scale
        (fun b ↦ gaussPrescribedParityOrientedLower
          (parity b) (signedLower b) (signedUpper b))
        (fun b ↦ gaussPrescribedParityOrientedUpper
          (parity b) (signedLower b) (signedUpper b))
        tuples := by
  unfold aggregateUniformMovingSignedApproximationTupleMassSum
    aggregateMovingSignedApproximationTupleMassSum
    movingSignedApproximationTupleMassSum
    aggregateUniformMovingHeterogeneousApproximationTupleSum
    uniformMovingHeterogeneousApproximationTupleSum
  apply Finset.sum_congr rfl
  intro b _hb
  apply Finset.sum_congr rfl
  intro t ht
  have hlower :
      (fun i ↦ gaussParityOrientedLower
          (t i) (signedLower b i) (signedUpper b i)) =
        gaussPrescribedParityOrientedLower
          (parity b) (signedLower b) (signedUpper b) := by
    funext i
    exact gaussParityOrientedLower_eq_of_mod_two_eq
      (by
        rw [Nat.mod_eq_of_lt (parity b i).isLt]
        exact hparity b t ht i)
      (signedLower b i) (signedUpper b i)
  have hupper :
      (fun i ↦ gaussParityOrientedUpper
          (t i) (signedLower b i) (signedUpper b i)) =
        gaussPrescribedParityOrientedUpper
          (parity b) (signedLower b) (signedUpper b) := by
    funext i
    exact gaussParityOrientedUpper_eq_of_mod_two_eq
      (by
        rw [Nat.mod_eq_of_lt (parity b i).isLt]
        exact hparity b t ht i)
      (signedLower b i) (signedUpper b i)
  rw [gaussSignedApproximationTupleEvent_eq_oriented, hlower, hupper]

/-- Literal uniform/Lebesgue signed zero-mode theorem for a tagged family. -/
theorem
    tendsto_aggregateUniformMovingSignedApproximationTupleMassSum
    {r : ℕ} (hr : 0 < r) {A density common : ℝ}
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (signedLower signedUpper : β → Fin r → ℝ)
    (parity : β → Fin r → Fin 2)
    (hA : 0 ≤ A)
    (hlower : ∀ b i, 0 <
      gaussPrescribedParityOrientedLower
        (parity b) (signedLower b) (signedUpper b) i)
    (hupper : ∀ b i,
      gaussPrescribedParityOrientedLower
          (parity b) (signedLower b) (signedUpper b) i <
        gaussPrescribedParityOrientedUpper
          (parity b) (signedLower b) (signedUpper b) i)
    (hupperA : ∀ b i,
      gaussPrescribedParityOrientedUpper
        (parity b) (signedLower b) (signedUpper b) i ≤ A)
    (hcommon : ∀ b,
      (∏ i,
        (gaussPrescribedParityOrientedUpper
              (parity b) (signedLower b) (signedUpper b) i -
          gaussPrescribedParityOrientedLower
              (parity b) (signedLower b) (signedUpper b) i) /
            Real.log 2) = common)
    (gap : ℕ → ℕ) (hgapTop : Tendsto gap atTop atTop)
    (hgapPos : ∀ᶠ n : ℕ in atTop, 0 < gap n)
    (tuples : ℕ → β → Finset (Fin r → ℕ))
    (hchronological : ∀ n b, ∀ t ∈ tuples n b,
      IsChronologicalNatTuple t)
    (hparity : ∀ n b, ∀ t ∈ tuples n b, ∀ i,
      t i % 2 = (parity b i).1)
    (htotalDensity : Tendsto
      (fun n ↦ (aggregateTupleFamilyCard (tuples n) : ℝ) /
        scale n ^ r) atTop (nhds density))
    (hshortDensity : Tendsto
      (fun n ↦
        (aggregateShortTupleFamilyCard
          (gap := gap n) (tuples n) : ℝ) /
            scale n ^ r)
      atTop (nhds 0))
    (minDepth : ℕ → ℕ)
    (hfirst : ∀ᶠ n : ℕ in atTop, ∀ b, ∀ t ∈ tuples n b,
      minDepth n ≤ t ⟨0, hr⟩)
    (hdecay : Tendsto
      (fun n ↦ (aggregateTupleFamilyCard (tuples n) : ℝ) *
        ((527 / 540 : ℝ) ^ minDepth n * Real.log 2))
      atTop (nhds 0)) :
    Tendsto
      (fun n ↦
        aggregateUniformMovingSignedApproximationTupleMassSum
          (scale n) signedLower signedUpper (tuples n))
      atTop (nhds (density * common)) := by
  let lower : β → Fin r → ℝ := fun b ↦
    gaussPrescribedParityOrientedLower
      (parity b) (signedLower b) (signedUpper b)
  let upper : β → Fin r → ℝ := fun b ↦
    gaussPrescribedParityOrientedUpper
      (parity b) (signedLower b) (signedUpper b)
  have hpositive :=
    tendsto_aggregateUniformMovingHeterogeneousApproximationTupleSum
      hr scale hscale lower upper hA hlower hupper hupperA hcommon
        gap hgapTop hgapPos tuples hchronological
        htotalDensity hshortDensity minDepth hfirst hdecay
  apply hpositive.congr'
  filter_upwards with n
  exact
    (aggregateUniformMovingSignedApproximationTupleMassSum_eq_oriented
      (scale n) signedLower signedUpper parity (tuples n)
        (hparity n)).symm

end

end Erdos1002
