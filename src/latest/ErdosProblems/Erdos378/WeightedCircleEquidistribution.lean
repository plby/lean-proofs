/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos378.CircleEquidistribution
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Group.AddCircle
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Weighted Weyl equidistribution on the unit circle

This file turns cancellation of all nonzero Fourier modes of finite weighted
point sets into convergence of their weighted centered fractional parts.  The
only discontinuity of the fractional-part coordinate is handled by a
continuous one-sided smoothing and a shrinking metric ball around zero.
-/

open Filter MeasureTheory Set
open scoped Topology BigOperators ENNReal NNReal

namespace Erdos378
namespace WeightedCircleEquidistribution

open CircleEquidistribution

noncomputable section

variable {A : Type*}

example (c : ℝ≥0) (μ : FiniteMeasure UnitCircle) :
    FiniteMeasure UnitCircle := c • μ

def finiteDirac (z : UnitCircle) : FiniteMeasure UnitCircle :=
  ⟨Measure.dirac z, by infer_instance⟩

@[simp, norm_cast] lemma coe_finiteDirac (z : UnitCircle) :
    (finiteDirac z : Measure UnitCircle) = Measure.dirac z := rfl

def weightedDirac (c : ℝ≥0) (z : UnitCircle) : FiniteMeasure UnitCircle :=
  c • finiteDirac z

@[simp, norm_cast] lemma coe_weightedDirac (c : ℝ≥0) (z : UnitCircle) :
    (weightedDirac c z : Measure UnitCircle) = c • Measure.dirac z := rfl

def weightedPointMeasure (s : Finset A) (w : A → ℝ≥0)
    (x : A → UnitCircle) : FiniteMeasure UnitCircle :=
  ∑ a ∈ s, weightedDirac (w a) (x a)

lemma weightedPointMeasure_mass (s : Finset A) (w : A → ℝ≥0)
    (x : A → UnitCircle) :
    (weightedPointMeasure s w x).mass = ∑ a ∈ s, w a := by
  apply ENNReal.coe_injective
  rw [FiniteMeasure.ennreal_mass]
  simp [weightedPointMeasure]

lemma integral_weightedPointMeasure (s : Finset A) (w : A → ℝ≥0)
    (x : A → UnitCircle) (f : UnitCircle → ℂ) :
    ∫ z, f z ∂(weightedPointMeasure s w x : Measure UnitCircle) =
      ∑ a ∈ s, (w a : ℝ) • f (x a) := by
  rw [weightedPointMeasure, FiniteMeasure.toMeasure_sum]
  rw [integral_finsetSum_measure]
  · apply Finset.sum_congr rfl
    intro a ha
    rw [coe_weightedDirac, integral_smul_nnreal_measure, integral_dirac]
    rfl
  · intro a ha
    rw [coe_weightedDirac]
    exact (integrable_dirac (by simp)).smul_measure (by simp)

lemma integral_weightedPointMeasure_real (s : Finset A) (w : A → ℝ≥0)
    (x : A → UnitCircle) (f : UnitCircle → ℝ) :
    ∫ z, f z ∂(weightedPointMeasure s w x : Measure UnitCircle) =
      ∑ a ∈ s, (w a : ℝ) * f (x a) := by
  rw [weightedPointMeasure, FiniteMeasure.toMeasure_sum]
  rw [integral_finsetSum_measure]
  · apply Finset.sum_congr rfl
    intro a ha
    rw [coe_weightedDirac, integral_smul_nnreal_measure, integral_dirac]
    rfl
  · intro a ha
    rw [coe_weightedDirac]
    exact (integrable_dirac (by simp)).smul_measure (by simp)

def totalWeight (s : Finset A) (w : A → ℝ≥0) : ℝ≥0 :=
  ∑ a ∈ s, w a

def normalizedWeightedPointMeasure (s : Finset A) (w : A → ℝ≥0)
    (x : A → UnitCircle) : ProbabilityMeasure UnitCircle :=
  (weightedPointMeasure s w x).normalize

lemma weightedPointMeasure_ne_zero {s : Finset A} {w : A → ℝ≥0}
    {x : A → UnitCircle} (hW : totalWeight s w ≠ 0) :
    weightedPointMeasure s w x ≠ 0 := by
  rw [← FiniteMeasure.mass_nonzero_iff, weightedPointMeasure_mass]
  exact hW

lemma integral_normalizedWeightedPointMeasure
    {s : Finset A} {w : A → ℝ≥0} {x : A → UnitCircle}
    (hW : totalWeight s w ≠ 0) (f : UnitCircle → ℂ) :
    ∫ z, f z ∂(normalizedWeightedPointMeasure s w x : Measure UnitCircle) =
      ((totalWeight s w : ℝ) : ℂ)⁻¹ *
        ∑ a ∈ s, ((w a : ℝ) : ℂ) * f (x a) := by
  let mu := weightedPointMeasure s w x
  have hmu : mu ≠ 0 := weightedPointMeasure_ne_zero hW
  change ∫ z, f z ∂(mu.normalize : Measure UnitCircle) = _
  rw [← mu.average_eq_integral_normalize hmu f, average_eq]
  rw [integral_weightedPointMeasure]
  have hmass : mu.mass = totalWeight s w := by
    exact weightedPointMeasure_mass s w x
  rw [show (mu : Measure UnitCircle).real Set.univ = (totalWeight s w : ℝ) by
    simpa [hmass]]
  rw [Complex.real_smul, Complex.ofReal_inv]
  simp_rw [Complex.real_smul]

lemma integral_normalizedWeightedPointMeasure_real
    {s : Finset A} {w : A → ℝ≥0} {x : A → UnitCircle}
    (hW : totalWeight s w ≠ 0) (f : UnitCircle → ℝ) :
    ∫ z, f z ∂(normalizedWeightedPointMeasure s w x : Measure UnitCircle) =
      (totalWeight s w : ℝ)⁻¹ *
        ∑ a ∈ s, (w a : ℝ) * f (x a) := by
  let mu := weightedPointMeasure s w x
  have hmu : mu ≠ 0 := weightedPointMeasure_ne_zero hW
  change ∫ z, f z ∂(mu.normalize : Measure UnitCircle) = _
  rw [← mu.average_eq_integral_normalize hmu f, average_eq]
  rw [integral_weightedPointMeasure_real]
  have hmass : mu.mass = totalWeight s w := by
    exact weightedPointMeasure_mass s w x
  rw [show (mu : Measure UnitCircle).real Set.univ = (totalWeight s w : ℝ) by
    simpa [hmass]]
  simp only [smul_eq_mul]

def unitCoord (z : UnitCircle) : ℝ :=
  (AddCircle.equivIco (1 : ℝ) 0 z : ℝ)

def centeredCoord (z : UnitCircle) : ℝ := unitCoord z - 1 / 2

lemma unitCoord_mem_Ico (z : UnitCircle) : unitCoord z ∈ Ico (0 : ℝ) 1 :=
  by simpa [unitCoord] using (AddCircle.equivIco (1 : ℝ) 0 z).property

lemma unitCoord_nonneg (z : UnitCircle) : 0 ≤ unitCoord z :=
  (unitCoord_mem_Ico z).1

lemma unitCoord_lt_one (z : UnitCircle) : unitCoord z < 1 :=
  (unitCoord_mem_Ico z).2

lemma coe_unitCoord (z : UnitCircle) :
    ((unitCoord z : ℝ) : UnitCircle) = z := by
  exact AddCircle.coe_equivIco

lemma unitCoord_coe (t : ℝ) :
    unitCoord (t : UnitCircle) = Int.fract t := by
  simpa [unitCoord] using
    (AddCircle.coe_equivIco_mk_apply (p := (1 : ℝ)) t)

lemma unitCoord_coe_of_mem_Ico {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) :
    unitCoord (t : UnitCircle) = t := by
  simpa [unitCoord] using
    (AddCircle.equivIco_coe_of_mem (p := (1 : ℝ)) (a := (0 : ℝ))
      (show t ∈ Ico (0 : ℝ) (0 + 1) by simpa using ht))

lemma measurable_unitCoord : Measurable unitCoord := by
  exact (AddCircle.measurableEquivIco (1 : ℝ) 0).measurable.subtype_val

lemma measurable_centeredCoord : Measurable centeredCoord :=
  measurable_unitCoord.sub measurable_const

lemma norm_centeredCoord_le (z : UnitCircle) : ‖centeredCoord z‖ ≤ 1 / 2 := by
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> dsimp only [centeredCoord] <;>
    linarith [unitCoord_nonneg z, unitCoord_lt_one z]

lemma integrable_centeredCoord (mu : Measure UnitCircle) [IsFiniteMeasure mu] :
    Integrable centeredCoord mu :=
  Integrable.of_bound measurable_centeredCoord.aestronglyMeasurable (1 / 2)
    (Eventually.of_forall norm_centeredCoord_le)

lemma integral_centeredCoord_unitHaar :
    ∫ z : UnitCircle, centeredCoord z ∂AddCircle.haarAddCircle = 0 := by
  have hvol : (volume : Measure UnitCircle) = AddCircle.haarAddCircle := by
    simpa using (AddCircle.volume_eq_smul_haarAddCircle (T := (1 : ℝ)))
  rw [← hvol, ← AddCircle.integral_preimage (T := (1 : ℝ)) 0 centeredCoord]
  simp only [zero_add]
  have hcongr :
      (∫ x in Ioc (0 : ℝ) 1, centeredCoord (x : UnitCircle)) =
        ∫ x in Ioc (0 : ℝ) 1, x - 1 / 2 := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc,
      ae_restrict_of_ae ((volume : Measure ℝ).ae_ne (1 : ℝ))] with x hx hxne
    have hx0 : 0 < x := hx.1
    have hx1 : x < 1 := hx.2.lt_of_ne hxne
    have hfract : Int.fract x = x := by
      rw [Int.fract_eq_self]
      exact ⟨hx0.le, hx1⟩
    simp [centeredCoord, unitCoord_coe, hfract]
  rw [hcongr]
  rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  have hid : IntervalIntegrable (fun x : ℝ ↦ x) volume 0 1 :=
    continuous_id.intervalIntegrable 0 1
  have hc : IntervalIntegrable (fun _x : ℝ ↦ (1 / 2 : ℝ)) volume 0 1 :=
    intervalIntegrable_const
  calc
    (∫ x : ℝ in (0 : ℝ)..1, x - 1 / 2) =
        (∫ x : ℝ in (0 : ℝ)..1, x) -
          ∫ _x : ℝ in (0 : ℝ)..1, (1 / 2 : ℝ) :=
      intervalIntegral.integral_sub hid hc
    _ = 0 := by
      rw [integral_id, intervalIntegral.integral_const]
      norm_num

def smoothCoord (delta : ℝ) (z : UnitCircle) : ℝ :=
  AddCircle.liftIco (1 : ℝ) 0
    (fun u ↦ max u (1 - (1 - delta) * u / delta)) z

lemma smoothCoord_apply (delta : ℝ) (z : UnitCircle) :
    smoothCoord delta z =
      max (unitCoord z) (1 - (1 - delta) * unitCoord z / delta) := by
  unfold smoothCoord
  calc
    AddCircle.liftIco (1 : ℝ) 0
        (fun u ↦ max u (1 - (1 - delta) * u / delta)) z =
      AddCircle.liftIco (1 : ℝ) 0
        (fun u ↦ max u (1 - (1 - delta) * u / delta))
          (unitCoord z : UnitCircle) := by rw [coe_unitCoord]
    _ = _ := AddCircle.liftIco_zero_coe_apply (unitCoord_mem_Ico z)

lemma continuous_smoothCoord {delta : ℝ} (hdelta0 : 0 < delta)
    (hdelta1 : delta ≤ 1) : Continuous (smoothCoord delta) := by
  apply AddCircle.liftIco_zero_continuous
  · norm_num
    exact div_nonneg (sub_nonneg.mpr hdelta1) hdelta0.le
  · fun_prop

lemma unitCoord_le_smoothCoord (delta : ℝ) (z : UnitCircle) :
    unitCoord z ≤ smoothCoord delta z := by
  rw [smoothCoord_apply]
  exact le_max_left _ _

lemma smoothCoord_eq_unitCoord_of_le {delta : ℝ} (hdelta0 : 0 < delta)
    {z : UnitCircle} (hz : delta ≤ unitCoord z) :
    smoothCoord delta z = unitCoord z := by
  rw [smoothCoord_apply, max_eq_left]
  rw [← sub_nonneg]
  rw [show unitCoord z -
      (1 - (1 - delta) * unitCoord z / delta) =
        (unitCoord z - delta) / delta by
      field_simp
      ring]
  exact div_nonneg (sub_nonneg.mpr hz) hdelta0.le

lemma smoothCoord_le_one {delta : ℝ} (hdelta0 : 0 < delta)
    (hdelta1 : delta ≤ 1) (z : UnitCircle) :
    smoothCoord delta z ≤ 1 := by
  rw [smoothCoord_apply, max_le_iff]
  constructor
  · exact (unitCoord_lt_one z).le
  · have hq : 0 ≤ (1 - delta) * unitCoord z / delta :=
      div_nonneg (mul_nonneg (sub_nonneg.mpr hdelta1)
        (unitCoord_nonneg z)) hdelta0.le
    linarith

lemma unitCoord_lt_imp_mem_closedBall {delta : ℝ} (hdelta : delta ≤ 1 / 2)
    {z : UnitCircle} (hz : unitCoord z < delta) :
    z ∈ Metric.closedBall (0 : UnitCircle) delta := by
  rw [Metric.mem_closedBall, dist_zero_right, ← coe_unitCoord z]
  have huhalf : |unitCoord z| ≤ |(1 : ℝ)| / 2 := by
    rw [abs_of_nonneg (unitCoord_nonneg z), abs_one]
    linarith
  rw [(AddCircle.norm_coe_eq_abs_iff (p := (1 : ℝ)) (by norm_num)).2 huhalf]
  rw [abs_of_nonneg (unitCoord_nonneg z)]
  exact hz.le

lemma volume_sphere_unitCircle (z : UnitCircle) (delta : ℝ) :
    (volume : Measure UnitCircle) (Metric.sphere z delta) = 0 := by
  rw [← Metric.closedBall_sdiff_ball]
  rw [measure_sdiff Metric.ball_subset_closedBall
    measurableSet_ball.nullMeasurableSet (measure_ne_top _ _)]
  rw [measure_congr AddCircle.closedBall_ae_eq_ball, tsub_self]

lemma unitHaar_frontier_closedBall (delta : ℝ) :
    (unitHaar : Measure UnitCircle)
        (frontier (Metric.closedBall (0 : UnitCircle) delta)) = 0 := by
  have hvol : (volume : Measure UnitCircle) = AddCircle.haarAddCircle := by
    simpa using (AddCircle.volume_eq_smul_haarAddCircle (T := (1 : ℝ)))
  change AddCircle.haarAddCircle
      (frontier (Metric.closedBall (0 : UnitCircle) delta)) = 0
  rw [← hvol]
  exact measure_mono_null Metric.frontier_closedBall_subset_sphere
    (volume_sphere_unitCircle 0 delta)

lemma unitHaar_closedBall {delta : ℝ} (hdelta0 : 0 ≤ delta)
    (hdelta : delta ≤ 1 / 2) :
    (unitHaar : Measure UnitCircle)
        (Metric.closedBall (0 : UnitCircle) delta) = ENNReal.ofReal (2 * delta) := by
  have hvol : (volume : Measure UnitCircle) = AddCircle.haarAddCircle := by
    simpa using (AddCircle.volume_eq_smul_haarAddCircle (T := (1 : ℝ)))
  change AddCircle.haarAddCircle
      (Metric.closedBall (0 : UnitCircle) delta) = _
  rw [← hvol, AddCircle.volume_closedBall]
  congr 1
  rw [min_eq_right]
  linarith

lemma smoothCoord_sub_unitCoord_norm_le_indicator {delta : ℝ}
    (hdelta0 : 0 < delta) (hdeltaHalf : delta ≤ 1 / 2) (z : UnitCircle) :
    ‖smoothCoord delta z - unitCoord z‖ ≤
      (Metric.closedBall (0 : UnitCircle) delta).indicator (fun _ ↦ (1 : ℝ)) z := by
  classical
  by_cases hzball : z ∈ Metric.closedBall (0 : UnitCircle) delta
  · rw [Set.indicator_of_mem hzball, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr (unitCoord_le_smoothCoord delta z))]
    linarith [smoothCoord_le_one hdelta0 (hdeltaHalf.trans (by norm_num)) z,
      unitCoord_nonneg z]
  · rw [Set.indicator_of_notMem hzball]
    have hzcoord : delta ≤ unitCoord z := by
      by_contra h
      exact hzball (unitCoord_lt_imp_mem_closedBall hdeltaHalf (lt_of_not_ge h))
    rw [smoothCoord_eq_unitCoord_of_le hdelta0 hzcoord, sub_self, norm_zero]

lemma integrable_unitCoord (mu : Measure UnitCircle) [IsFiniteMeasure mu] :
    Integrable unitCoord mu := by
  apply Integrable.of_bound measurable_unitCoord.aestronglyMeasurable 1
  exact Eventually.of_forall fun z ↦ by
    rw [Real.norm_eq_abs, abs_of_nonneg (unitCoord_nonneg z)]
    exact (unitCoord_lt_one z).le

lemma integrable_smoothCoord {delta : ℝ} (hdelta0 : 0 < delta)
    (hdelta1 : delta ≤ 1) (mu : Measure UnitCircle) [IsFiniteMeasure mu] :
    Integrable (smoothCoord delta) mu := by
  apply Integrable.of_bound
    (continuous_smoothCoord hdelta0 hdelta1).aestronglyMeasurable 1
  exact Eventually.of_forall fun z ↦ by
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · exact smoothCoord_le_one hdelta0 hdelta1 z
    · exact (unitCoord_nonneg z).trans
        (unitCoord_le_smoothCoord delta z)

lemma norm_integral_smoothCoord_sub_unitCoord_le {delta : ℝ}
    (hdelta0 : 0 < delta) (hdeltaHalf : delta ≤ 1 / 2)
    (mu : Measure UnitCircle) [IsFiniteMeasure mu] :
    ‖(∫ z, smoothCoord delta z ∂mu) - ∫ z, unitCoord z ∂mu‖ ≤
      mu.real (Metric.closedBall (0 : UnitCircle) delta) := by
  rw [← integral_sub (integrable_smoothCoord hdelta0
      (hdeltaHalf.trans (by norm_num)) mu)
    (integrable_unitCoord mu)]
  calc
    _ ≤ ∫ z, (Metric.closedBall (0 : UnitCircle) delta).indicator
        (fun _ ↦ (1 : ℝ)) z ∂mu :=
      norm_integral_le_of_norm_le
        ((integrable_const (1 : ℝ)).integrableOn.integrable_indicator
          measurableSet_closedBall)
        (Eventually.of_forall
          (smoothCoord_sub_unitCoord_norm_le_indicator hdelta0 hdeltaHalf))
    _ = _ := integral_indicator_one measurableSet_closedBall

lemma integral_centeredCoord_eq (mu : ProbabilityMeasure UnitCircle) :
    ∫ z, centeredCoord z ∂(mu : Measure UnitCircle) =
      (∫ z, unitCoord z ∂(mu : Measure UnitCircle)) - 1 / 2 := by
  unfold centeredCoord
  rw [integral_sub (integrable_unitCoord _) (integrable_const _)]
  simp

lemma integral_unitCoord_unitHaar :
    ∫ z : UnitCircle, unitCoord z ∂AddCircle.haarAddCircle = 1 / 2 := by
  have h := integral_centeredCoord_eq unitHaar
  have h' :
      (∫ z : UnitCircle, centeredCoord z ∂AddCircle.haarAddCircle) =
        (∫ z : UnitCircle, unitCoord z ∂AddCircle.haarAddCircle) - 1 / 2 := by
    simpa [unitHaar] using h
  rw [integral_centeredCoord_unitHaar] at h'
  linarith

/-- Weak convergence to Haar measure controls the discontinuous coordinate,
because its only discontinuity is the Haar-null point `0`. -/
theorem tendsto_integral_centeredCoord_of_tendsto_unitHaar
    {I : Type*} {F : Filter I} (mu : I → ProbabilityMeasure UnitCircle)
    (hmu : Tendsto mu F (nhds unitHaar)) :
    Tendsto (fun i ↦ ∫ z, centeredCoord z ∂(mu i : Measure UnitCircle))
      F (nhds 0) := by
  rw [Metric.tendsto_nhds]
  intro epsilon hepsilon
  let delta : ℝ := min (epsilon / 20) (1 / 4)
  have hdelta0 : 0 < delta := by
    dsimp only [delta]
    exact lt_min (div_pos hepsilon (by norm_num)) (by norm_num)
  have hdeltaE : delta ≤ epsilon / 20 := min_le_left _ _
  have hdeltaHalf : delta ≤ 1 / 2 :=
    (min_le_right _ _).trans (by norm_num)
  let f : BoundedContinuousFunction UnitCircle ℝ :=
    BoundedContinuousFunction.mkOfCompact
      ⟨smoothCoord delta,
        continuous_smoothCoord hdelta0 (hdeltaHalf.trans (by norm_num))⟩
  have hsmooth : Tendsto
      (fun i ↦ ∫ z, smoothCoord delta z ∂(mu i : Measure UnitCircle)) F
      (nhds (∫ z, smoothCoord delta z ∂(unitHaar : Measure UnitCircle))) := by
    simpa only [f, BoundedContinuousFunction.mkOfCompact_apply,
      ContinuousMap.coe_mk] using
      (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hmu f)
  let E : Set UnitCircle := Metric.closedBall 0 delta
  have hballENN : Tendsto (fun i ↦ (mu i : Measure UnitCircle) E) F
      (nhds ((unitHaar : Measure UnitCircle) E)) := by
    apply ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hmu
    simpa only [E] using unitHaar_frontier_closedBall delta
  have hballReal : Tendsto (fun i ↦ (mu i : Measure UnitCircle).real E) F
      (nhds (2 * delta)) := by
    have hfinite : (unitHaar : Measure UnitCircle) E ≠ ∞ := measure_ne_top _ _
    have ht := (ENNReal.tendsto_toReal hfinite).comp hballENN
    convert ht using 1
    · funext i
      rfl
    · rw [show (unitHaar : Measure UnitCircle) E = ENNReal.ofReal (2 * delta) by
          simpa only [E] using unitHaar_closedBall hdelta0.le hdeltaHalf]
      rw [ENNReal.toReal_ofReal (by positivity)]
  have hsmoothEventually := hsmooth.eventually
    (Metric.ball_mem_nhds _ (show 0 < epsilon / 4 by linarith))
  have hballEventually := hballReal.eventually
    (Metric.ball_mem_nhds _ (show 0 < delta by exact hdelta0))
  filter_upwards [hsmoothEventually, hballEventually] with i hi hballi
  rw [Real.dist_eq] at hi hballi
  rw [dist_zero_right, Real.norm_eq_abs]
  rw [integral_centeredCoord_eq]
  have hmuBall : (mu i : Measure UnitCircle).real E < 3 * delta := by
    rw [abs_lt] at hballi
    linarith
  have hleft := norm_integral_smoothCoord_sub_unitCoord_le
    hdelta0 hdeltaHalf (mu i : Measure UnitCircle)
  have hhaar := norm_integral_smoothCoord_sub_unitCoord_le
    hdelta0 hdeltaHalf (unitHaar : Measure UnitCircle)
  have hhaarBall : (unitHaar : Measure UnitCircle).real E = 2 * delta := by
    rw [measureReal_def]
    rw [show (unitHaar : Measure UnitCircle) E = ENNReal.ofReal (2 * delta) by
      simpa only [E] using unitHaar_closedBall hdelta0.le hdeltaHalf]
    rw [ENNReal.toReal_ofReal (by positivity)]
  have hunitHaar :
      (∫ z : UnitCircle, unitCoord z ∂(unitHaar : Measure UnitCircle)) = 1 / 2 :=
    integral_unitCoord_unitHaar
  rw [← hunitHaar]
  let A : ℝ := ∫ z, unitCoord z ∂(mu i : Measure UnitCircle)
  let B : ℝ := ∫ z, smoothCoord delta z ∂(mu i : Measure UnitCircle)
  let C : ℝ := ∫ z, smoothCoord delta z ∂(unitHaar : Measure UnitCircle)
  let D : ℝ := ∫ z, unitCoord z ∂(unitHaar : Measure UnitCircle)
  change |A - D| < epsilon
  have hleft' : ‖A - B‖ < 3 * delta := by
    dsimp only [A, B]
    rw [norm_sub_rev]
    exact hleft.trans_lt (by simpa only [E] using hmuBall)
  have hmiddle : ‖B - C‖ < epsilon / 4 := by
    simpa only [B, C, Real.norm_eq_abs] using hi
  have hhaar' : ‖C - D‖ ≤ 2 * delta := by
    dsimp only [C, D]
    exact hhaar.trans_eq hhaarBall
  calc
    |A - D| ≤ ‖A - B‖ + ‖B - C‖ + ‖C - D‖ := by
      rw [← Real.norm_eq_abs]
      calc
        ‖A - D‖ = ‖(A - B) + ((B - C) + (C - D))‖ := by
          congr 1
          ring
        _ ≤ ‖A - B‖ + ‖(B - C) + (C - D)‖ := norm_add_le _ _
        _ ≤ ‖A - B‖ + (‖B - C‖ + ‖C - D‖) :=
          add_le_add le_rfl (norm_add_le (B - C) (C - D))
        _ = _ := by ring
    _ < 3 * delta + epsilon / 4 + 2 * delta := by
      linarith
    _ < epsilon := by linarith

/-- A weighted Weyl criterion in the exact form used for prime intervals. -/
def normalizedFourierAverage (s : Finset A) (w : A → ℝ≥0)
    (x : A → UnitCircle) (h : ℤ) : ℂ :=
  ((totalWeight s w : ℝ) : ℂ)⁻¹ *
    ∑ a ∈ s, ((w a : ℝ) : ℂ) * fourier h (x a)

def normalizedCenteredAverage (s : Finset A) (w : A → ℝ≥0)
    (x : A → UnitCircle) : ℝ :=
  (totalWeight s w : ℝ)⁻¹ *
    ∑ a ∈ s, (w a : ℝ) * centeredCoord (x a)

theorem tendsto_weightedCenteredAverage_of_fourier
    {I : Type*} {F : Filter I}
    (s : I → Finset A) (w : I → A → ℝ≥0) (x : I → A → UnitCircle)
    (hweight : ∀ᶠ i in F, totalWeight (s i) (w i) ≠ 0)
    (hmode : ∀ h : ℤ, h ≠ 0 → Tendsto
      (fun i ↦ normalizedFourierAverage (s i) (w i) (x i) h)
      F (nhds 0)) :
    Tendsto (fun i ↦ normalizedCenteredAverage (s i) (w i) (x i))
      F (nhds 0) := by
  let mu : I → ProbabilityMeasure UnitCircle := fun i ↦
    normalizedWeightedPointMeasure (s i) (w i) (x i)
  have hfourier : ∀ h : ℤ, h ≠ 0 →
      Tendsto (fun i ↦ ∫ z, fourier h z ∂(mu i : Measure UnitCircle))
        F (nhds 0) := by
    intro h hh
    apply (hmode h hh).congr'
    filter_upwards [hweight] with i hi
    simpa only [normalizedFourierAverage, mu] using
      (integral_normalizedWeightedPointMeasure (x := x i) hi (fourier h)).symm
  have hmu : Tendsto mu F (nhds unitHaar) :=
    tendsto_unitHaar_of_fourier mu hfourier
  have hcenter := tendsto_integral_centeredCoord_of_tendsto_unitHaar mu hmu
  apply hcenter.congr'
  filter_upwards [hweight] with i hi
  simpa only [normalizedCenteredAverage, mu] using
    integral_normalizedWeightedPointMeasure_real (x := x i) hi centeredCoord

end

end WeightedCircleEquidistribution
end Erdos378
