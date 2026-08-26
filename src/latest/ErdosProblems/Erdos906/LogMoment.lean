import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Layercake

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set
open scoped ENNReal

namespace CofiniteDerivatives

variable {Ω : Type*} [MeasurableSpace Ω]

/-- An exponential upper tail turns a large event-restricted first moment into an
exponentially small event.  The constants are normalized for the tail
`μ {ω | s < Y ω} ≤ exp (-s / 2)`.

The integral hypothesis is stated in `ℝ≥0∞`, so it remains useful before integrability of
`Y` has been established. -/
theorem measure_event_le_two_mul_exp_neg_quarter_of_le_logMoment
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : Ω → ℝ) (E : Set Ω) (t : ℝ)
    (hY : Measurable Y) (_hY_nonneg : ∀ ω, 0 ≤ Y ω) (hE : MeasurableSet E)
    (ht : 4 ≤ t)
    (htail : ∀ s : ℝ, 0 ≤ s →
      μ {ω | s < Y ω} ≤ ENNReal.ofReal (Real.exp (-s / 2)))
    (hmoment : ENNReal.ofReal t * μ E ≤
      ∫⁻ ω in E, ENNReal.ofReal (Y ω) ∂μ) :
    μ E ≤ ENNReal.ofReal (2 * Real.exp (-t / 4)) := by
  let u := t / 2
  let Z : Ω → ℝ := fun ω ↦ max (Y ω - u) 0
  have hu : 0 ≤ u := by dsimp [u]; linarith
  have hZ_nonneg : ∀ ω, 0 ≤ Z ω := fun ω ↦ by simp [Z]
  have hZ : Measurable Z := by
    exact (hY.sub measurable_const).max measurable_const
  have hpoint : ∀ ω, ENNReal.ofReal (Y ω) ≤
      ENNReal.ofReal u + ENNReal.ofReal (Z ω) := by
    intro ω
    rw [← ENNReal.ofReal_add hu (hZ_nonneg ω)]
    apply ENNReal.ofReal_le_ofReal
    dsimp [Z]
    by_cases h : Y ω ≤ u
    · simp [h]
    · rw [max_eq_left (sub_nonneg.mpr (le_of_not_ge h))]
      linarith
  have hmoment_upper : (∫⁻ ω in E, ENNReal.ofReal (Y ω) ∂μ) ≤
      ENNReal.ofReal u * μ E + ∫⁻ ω, ENNReal.ofReal (Z ω) ∂μ := by
    calc
      (∫⁻ ω in E, ENNReal.ofReal (Y ω) ∂μ) ≤
          ∫⁻ ω in E, (ENNReal.ofReal u + ENNReal.ofReal (Z ω)) ∂μ :=
        setLIntegral_mono' hE fun ω _ ↦ hpoint ω
      _ = ENNReal.ofReal u * μ E + ∫⁻ ω in E, ENNReal.ofReal (Z ω) ∂μ := by
        rw [lintegral_add_left measurable_const]
        simp
      _ ≤ ENNReal.ofReal u * μ E + ∫⁻ ω, ENNReal.ofReal (Z ω) ∂μ := by
        exact add_le_add_right
          (setLIntegral_le_lintegral E (fun ω ↦ ENNReal.ofReal (Z ω))) _
  have htail_Z : ∀ s : ℝ, 0 < s →
      μ {ω | s < Z ω} ≤ ENNReal.ofReal (Real.exp (-(s + u) / 2)) := by
    intro s hs
    have hsets : {ω | s < Z ω} = {ω | s + u < Y ω} := by
      ext ω
      simp only [Z, mem_ofPred_eq]
      rw [lt_max_iff]
      constructor
      · rintro (h | h)
        · linarith
        · linarith
      · intro h
        left
        linarith
    rw [hsets]
    exact htail (s + u) (by linarith)
  have hZ_lintegral : (∫⁻ ω, ENNReal.ofReal (Z ω) ∂μ) ≤
      ENNReal.ofReal (2 * Real.exp (-u / 2)) := by
    rw [lintegral_eq_lintegral_meas_lt μ (Filter.Eventually.of_forall hZ_nonneg) hZ.aemeasurable]
    have hexp_eq : (fun s : ℝ ↦ Real.exp (-(s + u) / 2)) =
        fun s ↦ Real.exp (-u / 2) * Real.exp (-(1 / 2) * s) := by
      funext s
      rw [← Real.exp_add]
      congr 1
      ring
    have hexp_integrable : Integrable (fun s : ℝ ↦ Real.exp (-(s + u) / 2))
        (volume.restrict (Ioi 0)) := by
      rw [hexp_eq]
      exact (integrableOn_exp_mul_Ioi (by norm_num : -(1 / 2 : ℝ) < 0) 0).const_mul _
    have hexp_integral : (∫ s : ℝ in Ioi 0, Real.exp (-(s + u) / 2)) =
        2 * Real.exp (-u / 2) := by
      rw [hexp_eq, integral_const_mul,
        integral_exp_mul_Ioi (by norm_num : -(1 / 2 : ℝ) < 0)]
      norm_num
      ring
    calc
      (∫⁻ s in Ioi 0, μ {ω | s < Z ω} ∂volume) ≤
          ∫⁻ s in Ioi 0, ENNReal.ofReal (Real.exp (-(s + u) / 2)) ∂volume := by
        apply setLIntegral_mono' measurableSet_Ioi
        intro s hs
        exact htail_Z s hs
      _ = ENNReal.ofReal (2 * Real.exp (-u / 2)) := by
        calc
          (∫⁻ s in Ioi 0, ENNReal.ofReal (Real.exp (-(s + u) / 2)) ∂volume) =
              ENNReal.ofReal (∫ s : ℝ in Ioi 0, Real.exp (-(s + u) / 2)) :=
            (ofReal_integral_eq_lintegral_ofReal hexp_integrable
              (Filter.Eventually.of_forall fun _ ↦ Real.exp_nonneg _)).symm
          _ = ENNReal.ofReal (2 * Real.exp (-u / 2)) := congrArg ENNReal.ofReal hexp_integral
  have hmain : ENNReal.ofReal t * μ E ≤
      ENNReal.ofReal u * μ E + ENNReal.ofReal (2 * Real.exp (-u / 2)) :=
    hmoment.trans (hmoment_upper.trans (by gcongr))
  have hhalf : ENNReal.ofReal u * μ E ≤
      ENNReal.ofReal (2 * Real.exp (-u / 2)) := by
    have ht_eq : ENNReal.ofReal t = ENNReal.ofReal u + ENNReal.ofReal u := by
      rw [← ENNReal.ofReal_add hu hu]
      congr 1
      dsimp [u]
      ring
    rw [ht_eq, add_mul] at hmain
    exact ENNReal.le_of_add_le_add_left (by finiteness) hmain
  have hu_pos : 0 < u := by dsimp [u]; linarith
  have hprob : μ E ≤ ENNReal.ofReal ((2 * Real.exp (-u / 2)) / u) := by
    rw [ENNReal.ofReal_div_of_pos hu_pos]
    exact (ENNReal.le_div_iff_mul_le
      (Or.inl (ENNReal.ofReal_pos.2 hu_pos).ne')
      (Or.inl ENNReal.ofReal_ne_top)).2 <| by
      simpa [mul_comm] using! hhalf
  calc
    μ E ≤ ENNReal.ofReal ((2 * Real.exp (-u / 2)) / u) := hprob
    _ ≤ ENNReal.ofReal (2 * Real.exp (-t / 4)) := by
      apply ENNReal.ofReal_le_ofReal
      have hu_one : 1 ≤ u := by
        calc
          (1 : ℝ) ≤ 2 := by norm_num
          _ ≤ u := by dsimp [u]; linarith
      have hnum_nonneg : 0 ≤ 2 * Real.exp (-u / 2) :=
        mul_nonneg (by norm_num) (Real.exp_nonneg _)
      have hexp_arg : -u / 2 = -t / 4 := by
        dsimp [u]
        ring
      calc
        (2 * Real.exp (-u / 2)) / u ≤ 2 * Real.exp (-u / 2) :=
          div_le_self hnum_nonneg hu_one
        _ = 2 * Real.exp (-t / 4) := by rw [hexp_arg]

end CofiniteDerivatives
