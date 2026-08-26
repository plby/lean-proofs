import ErdosProblems.Erdos1002.NearResonantLiteralParameters

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Converting iterated `L²` smallness to probability deletion

The final assembly uses the nested limit `A → ∞` followed by `N → ∞`, not
a uniform product filter.  This file records the exact Chebyshev conversion
in that order so no interchange of the two limits is implicit.
-/

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace Erdos1002

noncomputable section

variable {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
  {μ : Measure α}

/-- Real-valued Chebyshev inequality in the exact form used below. -/
theorem measureReal_norm_ge_le_sq_div_of_eLpNorm_two_le
    {f : α → E} (hf : AEStronglyMeasurable f μ)
    {r s : ℝ} (hr : 0 < r) (hs : 0 ≤ s)
    (hnorm : eLpNorm f (2 : ENNReal) μ ≤ ENNReal.ofReal s) :
    μ.real {x | r ≤ ‖f x‖} ≤ (s / r) ^ 2 := by
  have hcheb := mul_meas_ge_le_pow_eLpNorm'
    μ (p := (2 : ENNReal)) (by norm_num) (by norm_num)
      hf (ENNReal.ofReal r)
  norm_num only [ENNReal.toReal_ofNat, ENNReal.rpow_two] at hcheb
  have hset : {x | ENNReal.ofReal r ≤ ‖f x‖ₑ} = {x | r ≤ ‖f x‖} := by
    ext x
    simp only [Set.mem_setOf_eq]
    rw [← ofReal_norm_eq_enorm]
    exact ENNReal.ofReal_le_ofReal_iff (norm_nonneg _)
  rw [hset] at hcheb
  have hnormSq : eLpNorm f (2 : ENNReal) μ ^ 2 ≤
      (ENNReal.ofReal s) ^ 2 := pow_le_pow_left' hnorm 2
  have hENN :
      (ENNReal.ofReal r) ^ 2 * μ {x | r ≤ ‖f x‖} ≤
        (ENNReal.ofReal s) ^ 2 := hcheb.trans hnormSq
  have hrightTop : (ENNReal.ofReal s) ^ 2 ≠ ∞ := by finiteness
  have hreal := ENNReal.toReal_mono hrightTop hENN
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal hr.le, ENNReal.toReal_ofReal hs] at hreal
  have hdiv : μ.real {x | r ≤ ‖f x‖} ≤ s ^ 2 / r ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hr)).2
    simpa only [measureReal_def, mul_comm] using! hreal
  calc
    μ.real {x | r ≤ ‖f x‖} ≤ s ^ 2 / r ^ 2 := hdiv
    _ = (s / r) ^ 2 := by field_simp [hr.ne']

/-- Nested `L²` smallness implies precisely the nested probability
deletion premise used by `FinalAssembly`. -/
theorem iterated_probabilityDeletion_of_iterated_eLpNorm_two
    (F : ℕ → ℕ → α → E)
    (hF : ∀ᶠ A : ℕ in atTop, ∀ᶠ N : ℕ in atTop,
      AEStronglyMeasurable (F A N) μ)
    (hsmall : ∀ η > 0, ∀ᶠ A : ℕ in atTop, ∀ᶠ N : ℕ in atTop,
      eLpNorm (F A N) (2 : ENNReal) μ ≤ ENNReal.ofReal η) :
    ∀ r > 0, ∀ δ > 0,
      ∀ᶠ A : ℕ in atTop, ∀ᶠ N : ℕ in atTop,
        μ.real {x | r ≤ ‖F A N x‖} < δ := by
  intro r hr δ hδ
  let η : ℝ := r * min 1 δ / 2
  have hη : 0 < η := by
    dsimp [η]
    positivity
  have hbound := hsmall η hη
  filter_upwards [hbound, hF] with A hinner hmeasurable
  filter_upwards [hinner, hmeasurable] with N hnorm hmeasurableN
  have hcheb := measureReal_norm_ge_le_sq_div_of_eLpNorm_two_le
    hmeasurableN hr hη.le hnorm
  have hratio : (η / r) ^ 2 < δ := by
    dsimp [η]
    rw [mul_div_assoc, mul_div_cancel_left₀ _ hr.ne']
    by_cases hδone : δ ≤ 1
    · rw [min_eq_right hδone]
      nlinarith [sq_nonneg δ]
    · rw [min_eq_left (le_of_not_ge hδone)]
      nlinarith
  exact hcheb.trans_lt hratio

/-- Probability deletion for the actual literal smooth near shot. -/
theorem iterated_probabilityDeletion_normalizedSmoothNearLiteralShotTail
    (ε : ℝ) (hε : 0 < ε) (hεhalf : ε < 1 / 2) :
    ∀ r > 0, ∀ δ > 0,
      ∀ᶠ A : ℕ in atTop, ∀ᶠ N : ℕ in atTop,
        uniform01Measure.real
          {alpha | r ≤
            ‖normalizedSmoothNearLiteralShotTail N (A : ℝ) ε alpha‖} < δ := by
  apply iterated_probabilityDeletion_of_iterated_eLpNorm_two
    (μ := uniform01Measure)
    (fun A N ↦ normalizedSmoothNearLiteralShotTail N (A : ℝ) ε)
  · filter_upwards [eventually_ge_atTop 1] with A hA
    have hlog : Tendsto (fun N : ℕ ↦ Real.log (N : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have hratio : Tendsto
        (fun N : ℕ ↦ (A : ℝ) / Real.log (N : ℝ)) atTop (nhds 0) :=
      hlog.const_div_atTop (A : ℝ)
    have hsmall : ∀ᶠ N : ℕ in atTop,
        (A : ℝ) / Real.log (N : ℝ) < ε / 4 :=
      hratio.eventually_lt_const (by positivity)
    have hscale : ∀ᶠ N : ℕ in atTop,
        0 < Real.log (N : ℝ) ∧
          (A : ℝ) / Real.log (N : ℝ) ≤ ε / 4 := by
      filter_upwards [eventually_ge_atTop 2, hsmall] with N hN hsmallN
      exact ⟨Real.log_pos (by exact_mod_cast hN), hsmallN.le⟩
    filter_upwards [hscale] with N hscaleN
    have hApos : 0 < (A : ℝ) := by exact_mod_cast (show 0 < A by omega)
    have hLpos := hscaleN.1
    have ha : 0 < (A : ℝ) / (2 * Real.log (N : ℝ)) := by positivity
    have hhalf :
        (A : ℝ) / (2 * Real.log (N : ℝ)) =
          ((A : ℝ) / Real.log (N : ℝ)) / 2 := by
      field_simp [hLpos.ne']
    have haε : (A : ℝ) / (2 * Real.log (N : ℝ)) ≤ ε / 4 := by
      rw [hhalf]
      linarith [div_nonneg hApos.le hLpos.le]
    unfold normalizedSmoothNearLiteralShotTail
    exact (measurable_smoothNearLiteralShotTail N
      ((A : ℝ) / (2 * Real.log (N : ℝ))) ε 2 N ha haε).div_const _
      |>.aestronglyMeasurable
  · intro η hη
    exact iterated_eventually_eLpNorm_normalizedSmoothNearLiteralShotTail_lt
      ε η hε hεhalf hη

end

end Erdos1002
