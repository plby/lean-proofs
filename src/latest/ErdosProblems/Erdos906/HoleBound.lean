import ErdosProblems.Erdos906.RandomFock
import ErdosProblems.Erdos906.CircleLogTail
import ErdosProblems.Erdos906.CircleNormGap
import ErdosProblems.Erdos906.Jensen
import ErdosProblems.Erdos906.DiskBasis

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open Complex MeasureTheory Metric Real Set
open scoped ENNReal

namespace CofiniteDerivatives

noncomputable section

/-- The deterministic compact-error bound at the center of a disk. -/
def centerUpperConstant (c : ℂ) : ℝ :=
  (‖c‖ + ‖c‖ ^ 2) / 2

/-- The nonnegative logarithmic deficit at a fixed complex point. -/
def pointwiseLogDeficit (n : ℕ) (ω : ℕ → ℂ) (z : ℂ) : ℝ :=
  max (pointwisePotential n z -
    Real.log ‖randomFockDeriv n ω z‖ - pointwiseSaddleLoss n) 0

/-- The sample-point pair obtained from a coefficient sequence and an angle. -/
def circleSampleMap (c : ℂ) (r : ℝ) (p : (ℕ → ℂ) × ℝ) : (ℕ → ℂ) × ℂ :=
  (p.1, circleMap c r p.2)

/-- The nonnegative logarithmic deficit on the circle centered at `c` with radius `r`. -/
def circleLogDeficit (n : ℕ) (c : ℂ) (r : ℝ) (ω : ℕ → ℂ) (θ : ℝ) : ℝ :=
  pointwiseLogDeficit n ω (circleMap c r θ)

theorem measurable_pointwisePotential (n : ℕ) : Measurable (pointwisePotential n) := by
  unfold pointwisePotential
  exact measurable_const.add (measurable_id.norm.mul_const (Real.sqrt n))

theorem measurable_pointwiseLogDeficit (n : ℕ) :
    Measurable (fun p : (ℕ → ℂ) × ℂ ↦ pointwiseLogDeficit n p.1 p.2) := by
  unfold pointwiseLogDeficit
  have hpotential : Measurable (fun p : (ℕ → ℂ) × ℂ ↦ pointwisePotential n p.2) :=
    (measurable_pointwisePotential n).comp measurable_snd
  exact ((hpotential.sub (measurable_randomFockDeriv n).norm.log).sub measurable_const).max
    measurable_const

theorem measurable_circleSampleMap (c : ℂ) (r : ℝ) : Measurable (circleSampleMap c r) := by
  have hfst : Measurable (fun p : (ℕ → ℂ) × ℝ ↦ p.1) := measurable_fst
  exact Measurable.prodMk hfst ((measurable_circleMap c r).comp measurable_snd)

/-- The circle logarithmic deficit is jointly measurable in the sample and angle. -/
theorem measurable_circleLogDeficit (n : ℕ) (c : ℂ) (r : ℝ) :
    Measurable (fun p : (ℕ → ℂ) × ℝ ↦ circleLogDeficit n c r p.1 p.2) := by
  change Measurable
    ((fun p : (ℕ → ℂ) × ℂ ↦ pointwiseLogDeficit n p.1 p.2) ∘ circleSampleMap c r)
  exact (measurable_pointwiseLogDeficit n).comp (measurable_circleSampleMap c r)

theorem circleLogDeficit_nonneg (n : ℕ) (c : ℂ) (r : ℝ) (ω : ℕ → ℂ) (θ : ℝ) :
    0 ≤ circleLogDeficit n c r ω θ :=
  le_max_right _ _

/-- On a saddle-ready circle, every angular section has the exponential tail used by
`measure_event_le_two_mul_exp_neg_eighth_of_circleLogAverage`. -/
theorem P_circleLogDeficit_tail
    (n : ℕ) (c : ℂ) (r δ M : ℝ)
    (hn : PointwiseSaddleReady n δ M)
    (hnorm : ∀ θ, δ ≤ ‖circleMap c r θ‖ ∧ ‖circleMap c r θ‖ ≤ M)
    (θ s : ℝ) (hs : 0 ≤ s) :
    P {ω | s < circleLogDeficit n c r ω θ} ≤
      ENNReal.ofReal (Real.exp (-s / 2)) := by
  let z := circleMap c r θ
  have hx : 1 ≤ ‖z‖ * Real.sqrt n :=
    hn.1.trans <| mul_le_mul_of_nonneg_right (hnorm θ).1 (Real.sqrt_nonneg _)
  have hzn : ‖z‖ ≤ Real.sqrt n := (hnorm θ).2.trans hn.2
  have hset : {ω | s < circleLogDeficit n c r ω θ} =
      {ω | pointwisePotential n z - Real.log ‖randomFockDeriv n ω z‖ >
        s + pointwiseSaddleLoss n} := by
    ext ω
    change s < max
      (pointwisePotential n z - Real.log ‖randomFockDeriv n ω z‖ -
        pointwiseSaddleLoss n) 0 ↔ _
    simp only [lt_max_iff]
    constructor
    · rintro (h | h)
      · exact lt_sub_iff_add_lt.mp h
      · exact (not_lt_of_ge hs h).elim
    · intro h
      exact Or.inl (lt_sub_iff_add_lt.mpr h)
  rw [hset]
  calc
    P {ω | pointwisePotential n z - Real.log ‖randomFockDeriv n ω z‖ >
        s + pointwiseSaddleLoss n} ≤ ENNReal.ofReal (Real.exp (-2 * s)) :=
      P_pointwise_log_lowerTail n z s hx hzn
    _ ≤ ENNReal.ofReal (Real.exp (-s / 2)) := by
      apply ENNReal.ofReal_le_ofReal
      exact Real.exp_monotone (by linarith)

/-- The uniform exponential section tail makes the circle deficit integrable under the
product of the coefficient law and angular volume. -/
theorem integrable_circleLogDeficit
    (n : ℕ) (c : ℂ) (r δ M : ℝ)
    (hn : PointwiseSaddleReady n δ M)
    (hnorm : ∀ θ, δ ≤ ‖circleMap c r θ‖ ∧ ‖circleMap c r θ‖ ≤ M) :
    Integrable (Function.uncurry (circleLogDeficit n c r))
      (P.prod (volume.restrict (Ioc 0 (2 * Real.pi)))) := by
  let ν : Measure ℝ := volume.restrict (Ioc 0 (2 * Real.pi))
  let Y : (ℕ → ℂ) × ℝ → ℝ := Function.uncurry (circleLogDeficit n c r)
  have hY : Measurable Y := measurable_circleLogDeficit n c r
  have hY_nonneg : ∀ p, 0 ≤ Y p := fun p ↦ circleLogDeficit_nonneg n c r p.1 p.2
  have hlintegral : (∫⁻ p, ENNReal.ofReal (Y p) ∂P.prod ν) < ∞ := by
    rw [lintegral_eq_lintegral_meas_lt (P.prod ν)
      (Filter.Eventually.of_forall hY_nonneg) hY.aemeasurable]
    have hlevel (s : ℝ) (hs : s ∈ Ioi 0) :
        P.prod ν {p | s < Y p} ≤
          ENNReal.ofReal (Real.exp (-s / 2)) * ν univ := by
      have hset : MeasurableSet {p | s < Y p} :=
        measurableSet_lt measurable_const hY
      rw [Measure.prod_apply_symm hset]
      calc
        (∫⁻ θ, P ((fun ω ↦ (ω, θ)) ⁻¹' {p | s < Y p}) ∂ν) ≤
            ∫⁻ _θ, ENNReal.ofReal (Real.exp (-s / 2)) ∂ν := by
          apply lintegral_mono
          intro θ
          change P {ω | s < circleLogDeficit n c r ω θ} ≤ _
          exact P_circleLogDeficit_tail n c r δ M hn hnorm θ s hs.le
        _ = ENNReal.ofReal (Real.exp (-s / 2)) * ν univ :=
          lintegral_const _
    calc
      (∫⁻ s in Ioi 0, P.prod ν {p | s < Y p} ∂volume) ≤
          ∫⁻ s in Ioi 0,
            ENNReal.ofReal (Real.exp (-s / 2)) * ν univ ∂volume := by
        apply setLIntegral_mono' measurableSet_Ioi
        intro s hs
        exact hlevel s hs
      _ = (∫⁻ s in Ioi 0, ENNReal.ofReal (Real.exp (-s / 2)) ∂volume) * ν univ := by
        exact lintegral_mul_const' (ν univ)
          (fun s ↦ ENNReal.ofReal (Real.exp (-s / 2))) (measure_ne_top ν univ)
      _ < ∞ := by
        have hexp_int : Integrable (fun s : ℝ ↦ Real.exp (-s / 2))
            (volume.restrict (Ioi 0)) := by
          apply (integrableOn_exp_mul_Ioi (a := -(1 / 2 : ℝ)) (by norm_num) 0).congr
          filter_upwards [] with s
          congr 1
          ring
        have hexp_lt :
            (∫⁻ s in Ioi 0, ENNReal.ofReal (Real.exp (-s / 2)) ∂volume) < ∞ := by
          exact hexp_int.lintegral_lt_top
        exact ENNReal.mul_lt_top hexp_lt (measure_lt_top ν univ)
  refine ⟨hY.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hY_nonneg)]
  exact hlintegral

/-- The deterministic pointwise potential gains exactly `sqrt n` times the norm circle gap. -/
theorem circleAverage_pointwisePotential_sub_center (n : ℕ) (c : ℂ) (r : ℝ) :
    circleAverage (pointwisePotential n) c r - pointwisePotential n c =
      Real.sqrt n * normCircleGap c r := by
  have hnorm : CircleIntegrable (fun z : ℂ ↦ ‖z‖ * Real.sqrt n) c r := by
    simpa only [smul_eq_mul, mul_comm] using!
      (circleIntegrable_norm c r).const_fun_smul (a := Real.sqrt n)
  have hmul : circleAverage (fun z : ℂ ↦ ‖z‖ * Real.sqrt n) c r =
      Real.sqrt n * circleAverage (fun z : ℂ ↦ ‖z‖) c r := by
    simpa only [mul_comm] using! circleAverage_mul_norm (Real.sqrt n) c r
  rw [show pointwisePotential n = fun z : ℂ ↦
      Real.log (Real.sqrt (Nat.factorial n : ℝ)) + ‖z‖ * Real.sqrt n by
    rfl]
  rw [circleAverage_fun_add (circleIntegrable_const _ c r) hnorm,
    circleAverage_const, hmul]
  simp only [normCircleGap]
  ring

/-- Every sample path obeys the compact deterministic logarithmic upper bound at the center. -/
theorem log_norm_randomFockDeriv_sub_pointwisePotential_le_centerUpperConstant
    (n : ℕ) (ω : ℕ → ℂ) (c : ℂ) (hn : n ≠ 0) :
    Real.log ‖randomFockDeriv n ω c‖ - pointwisePotential n c ≤
      centerUpperConstant c := by
  simpa only [randomFockDeriv, randomFock, centerUpperConstant] using!
    log_norm_iteratedDeriv_fockFunction_sub_potential_le
      (fun k ↦ clipDisk (ω k)) (fun k ↦ norm_clipDisk_le_one (ω k))
      n c ‖c‖ hn le_rfl

/-- For every sample path, the angular logarithmic deficit is interval-integrable. -/
theorem intervalIntegrable_circleLogDeficit
    (n : ℕ) (c : ℂ) (r : ℝ) (ω : ℕ → ℂ) :
    IntervalIntegrable (circleLogDeficit n c r ω) volume 0 (2 * Real.pi) := by
  have hpotential : CircleIntegrable (pointwisePotential n) c r := by
    apply ContinuousOn.circleIntegrable'
    exact (continuous_const.add (continuous_norm.mul continuous_const)).continuousOn
  have hlog : CircleIntegrable
      (fun z : ℂ ↦ Real.log ‖randomFockDeriv n ω z‖) c r :=
    MeromorphicOn.circleIntegrable_log_norm fun z _ ↦
      (analyticOnNhd_randomFockDeriv n ω).meromorphicOn z (by simp)
  have hraw : CircleIntegrable (fun z : ℂ ↦
      pointwisePotential n z - Real.log ‖randomFockDeriv n ω z‖ -
        pointwiseSaddleLoss n) c r :=
    (hpotential.sub hlog).sub (circleIntegrable_const _ c r)
  have hmax : CircleIntegrable (fun z : ℂ ↦ max
      (pointwisePotential n z - Real.log ‖randomFockDeriv n ω z‖ -
        pointwiseSaddleLoss n) 0) c r :=
    ⟨hraw.1.sup integrableOn_zero, hraw.2.sup integrableOn_zero⟩
  simpa only [CircleIntegrable, circleLogDeficit] using! hmax

/-- The deterministic threshold for the large circle-average event. -/
def holeThreshold (n : ℕ) (c : ℂ) (r : ℝ) : ℝ :=
  Real.sqrt n * normCircleGap c r - centerUpperConstant c - pointwiseSaddleLoss n

/-- The event that the random derivative has no zero in the outer open disk. -/
def randomFockHoleEvent (n : ℕ) (c : ℂ) (R : ℝ) : Set (ℕ → ℂ) :=
  {ω | ∀ z ∈ ball c R, randomFockDeriv n ω z ≠ 0}

/-- The measurable event where the circle deficit average exceeds its deterministic threshold. -/
def largeCircleDeficitEvent (n : ℕ) (c : ℂ) (r : ℝ) : Set (ℕ → ℂ) :=
  {ω | holeThreshold n c r ≤ circleLogAverage (circleLogDeficit n c r) ω}

theorem measurableSet_largeCircleDeficitEvent (n : ℕ) (c : ℂ) (r : ℝ) :
    MeasurableSet (largeCircleDeficitEvent n c r) := by
  exact measurableSet_le measurable_const
    (measurable_circleLogAverage _ (measurable_circleLogDeficit n c r))

/-- A zero-free outer disk forces a large average logarithmic deficit on every enclosed circle. -/
theorem holeEvent_subset_largeCircleDeficitEvent
    (n : ℕ) (c : ℂ) {r R : ℝ} (hr : 0 < r)
    (hclosed : closedBall c r ⊆ ball c R) (hn : n ≠ 0) :
    randomFockHoleEvent n c R ⊆ largeCircleDeficitEvent n c r := by
  intro ω hω
  have hzero : ∀ z ∈ closedBall c |r|, randomFockDeriv n ω z ≠ 0 := by
    intro z hz
    apply hω z
    apply hclosed
    simpa only [abs_of_pos hr] using! hz
  have hJensen : diskLogStat (randomFockDeriv n ω) c r = 0 :=
    diskLogStat_eq_zero_of_entire_zeroFree
      (analyticOnNhd_randomFockDeriv n ω) hzero
  have hlog_average :
      circleAverage (fun z : ℂ ↦ Real.log ‖randomFockDeriv n ω z‖) c r =
        Real.log ‖randomFockDeriv n ω c‖ := by
    simpa only [diskLogStat, sub_eq_zero] using! hJensen
  let raw : ℂ → ℝ := fun z ↦
    pointwisePotential n z - Real.log ‖randomFockDeriv n ω z‖ - pointwiseSaddleLoss n
  let positive : ℂ → ℝ := fun z ↦ max (raw z) 0
  have hpotential : CircleIntegrable (pointwisePotential n) c r := by
    apply ContinuousOn.circleIntegrable'
    exact (continuous_const.add (continuous_norm.mul continuous_const)).continuousOn
  have hlog : CircleIntegrable
      (fun z : ℂ ↦ Real.log ‖randomFockDeriv n ω z‖) c r :=
    MeromorphicOn.circleIntegrable_log_norm fun z _ ↦
      (analyticOnNhd_randomFockDeriv n ω).meromorphicOn z (by simp)
  have hdiff : CircleIntegrable (fun z : ℂ ↦
      pointwisePotential n z - Real.log ‖randomFockDeriv n ω z‖) c r := by
    exact hpotential.sub hlog
  have hraw : CircleIntegrable raw c r := by
    exact hdiff.sub (circleIntegrable_const _ c r)
  have hpositive : CircleIntegrable positive c r := by
    exact ⟨hraw.1.sup integrableOn_zero, hraw.2.sup integrableOn_zero⟩
  have hraw_average :
      circleAverage raw c r = circleAverage (pointwisePotential n) c r -
        circleAverage (fun z : ℂ ↦ Real.log ‖randomFockDeriv n ω z‖) c r -
          pointwiseSaddleLoss n := by
    calc
      circleAverage raw c r = circleAverage (fun z : ℂ ↦
          (pointwisePotential n z - Real.log ‖randomFockDeriv n ω z‖) -
            pointwiseSaddleLoss n) c r := rfl
      _ = circleAverage (fun z : ℂ ↦
          pointwisePotential n z - Real.log ‖randomFockDeriv n ω z‖) c r -
            circleAverage (fun _ : ℂ ↦ pointwiseSaddleLoss n) c r :=
        circleAverage_fun_sub hdiff (circleIntegrable_const _ c r)
      _ = circleAverage (pointwisePotential n) c r -
          circleAverage (fun z : ℂ ↦ Real.log ‖randomFockDeriv n ω z‖) c r -
            pointwiseSaddleLoss n := by
        rw [circleAverage_fun_sub hpotential hlog, circleAverage_const]
  have hcenter :=
    log_norm_randomFockDeriv_sub_pointwisePotential_le_centerUpperConstant n ω c hn
  have ht_raw : holeThreshold n c r ≤ circleAverage raw c r := by
    rw [hraw_average, hlog_average]
    rw [holeThreshold, ← circleAverage_pointwisePotential_sub_center n c r]
    linarith
  have hraw_positive : circleAverage raw c r ≤ circleAverage positive c r := by
    apply circleAverage_mono hraw hpositive
    intro z _
    exact le_max_left _ _
  have hpositive_eq :
      circleAverage positive c r = circleLogAverage (circleLogDeficit n c r) ω := by
    rfl
  change holeThreshold n c r ≤ circleLogAverage (circleLogDeficit n c r) ω
  rw [← hpositive_eq]
  exact ht_raw.trans hraw_positive

/-- For a saddle-ready circle whose threshold is at least eight, the outer measure of the
zero-free outer-disk event has the exponential circle-log bound. -/
theorem P_outerMeasure_holeEvent_le_two_mul_exp_neg_eighth
    (n : ℕ) (c : ℂ) {r R δ M : ℝ}
    (hr : 0 < r) (hrR : r < R)
    (hn : PointwiseSaddleReady n δ M)
    (hnorm : ∀ z ∈ sphere c r, δ ≤ ‖z‖ ∧ ‖z‖ ≤ M)
    (ht : 8 ≤ holeThreshold n c r) :
    P.toOuterMeasure (randomFockHoleEvent n c R) ≤
      ENNReal.ofReal (2 * Real.exp (-holeThreshold n c r / 8)) := by
  have hn0 : n ≠ 0 := by
    intro hnzero
    subst n
    norm_num [PointwiseSaddleReady] at hn
  have hcircle : ∀ θ, δ ≤ ‖circleMap c r θ‖ ∧ ‖circleMap c r θ‖ ≤ M := by
    intro θ
    exact hnorm (circleMap c r θ) (circleMap_mem_sphere c hr.le θ)
  have hlarge :
      P (largeCircleDeficitEvent n c r) ≤
        ENNReal.ofReal (2 * Real.exp (-holeThreshold n c r / 8)) := by
    apply measure_event_le_two_mul_exp_neg_eighth_of_circleLogAverage
      P (circleLogDeficit n c r) (largeCircleDeficitEvent n c r)
      (holeThreshold n c r)
    · exact measurable_circleLogDeficit n c r
    · exact circleLogDeficit_nonneg n c r
    · exact integrable_circleLogDeficit n c r δ M hn hcircle
    · exact measurableSet_largeCircleDeficitEvent n c r
    · exact ht
    · intro ω hω
      exact hω
    · exact P_circleLogDeficit_tail n c r δ M hn hcircle
  rw [Measure.toOuterMeasure_apply]
  exact (measure_mono
    (holeEvent_subset_largeCircleDeficitEvent n c hr
      (closedBall_subset_ball hrR) hn0)).trans hlarge

end

end CofiniteDerivatives
