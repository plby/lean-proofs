import ErdosProblems.Erdos1166.Erdos1166Core

namespace Erdos1166.HLOZScreeningAssembly

open Filter Asymptotics MeasureTheory Set
open scoped BigOperators ENNReal

variable {Ω ι : Type*}

/-- The history after `n` screenings: at each step we intersect the preceding
history with the next screening event. -/
def screeningHistory (base : Set Ω) (screen : ℕ → Set Ω) : ℕ → Set Ω
  | 0 => base
  | n + 1 => screeningHistory base screen n ∩ screen n

@[simp] theorem screeningHistory_zero (base : Set Ω) (screen : ℕ → Set Ω) :
    screeningHistory base screen 0 = base := rfl

@[simp] theorem screeningHistory_succ (base : Set Ω) (screen : ℕ → Set Ω) (n : ℕ) :
    screeningHistory base screen (n + 1) =
      screeningHistory base screen n ∩ screen n := rfl

theorem screeningHistory_succ_subset (base : Set Ω) (screen : ℕ → Set Ω) (n : ℕ) :
    screeningHistory base screen (n + 1) ⊆ screeningHistory base screen n :=
  inter_subset_left

variable [MeasurableSpace Ω]

/-- A stage event is obtained from the preceding history, and its measure is
bounded by a conditional cost times the preceding measure, plus an exceptional
error. Writing the conditional estimate in this multiplied-out form avoids
all division-by-zero issues. -/
structure StageBound (μ : Measure Ω) (q error : ℝ≥0∞)
    (previous next : Set Ω) : Prop where
  nested : next ⊆ previous
  measure_le : μ next ≤ q * μ previous + error

/-- A multiplied-out conditional bound on the next intersection gives a
`StageBound` for the recursively defined history. -/
theorem stageBound_screeningHistory (μ : Measure Ω)
    (base : Set Ω) (screen : ℕ → Set Ω) (n : ℕ) (q error : ℝ≥0∞)
    (hmeasure : μ (screeningHistory base screen (n + 1)) ≤
      q * μ (screeningHistory base screen n) + error) :
    StageBound μ q error (screeningHistory base screen n)
      (screeningHistory base screen (n + 1)) :=
  ⟨screeningHistory_succ_subset base screen n, hmeasure⟩

/-- Three successive conditional estimates multiply their main costs. -/
theorem three_stage_measure_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    {q e₁ e₂ e₃ : ℝ≥0∞} {E₀ E₁ E₂ E₃ : Set Ω}
    (h₁ : StageBound μ q e₁ E₀ E₁)
    (h₂ : StageBound μ q e₂ E₁ E₂)
    (h₃ : StageBound μ q e₃ E₂ E₃) :
    μ E₃ ≤ q ^ 3 + q ^ 2 * e₁ + q * e₂ + e₃ := by
  calc
    μ E₃ ≤ q * μ E₂ + e₃ := h₃.measure_le
    _ ≤ q * (q * μ E₁ + e₂) + e₃ := by gcongr; exact h₂.measure_le
    _ ≤ q * (q * (q * μ E₀ + e₁) + e₂) + e₃ := by
      gcongr
      exact h₁.measure_le
    _ ≤ q * (q * (q * 1 + e₁) + e₂) + e₃ := by
      gcongr
      exact prob_le_one
    _ = q ^ 3 + q ^ 2 * e₁ + q * e₂ + e₃ := by ring

/-- Recursive-history form of `three_stage_measure_le`. -/
theorem screeningHistory_three_measure_le
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (base : Set Ω) (screen : ℕ → Set Ω) {q : ℝ≥0∞}
    (error : Fin 3 → ℝ≥0∞)
    (hstage : ∀ i : Fin 3,
      μ (screeningHistory base screen (i + 1)) ≤
        q * μ (screeningHistory base screen i) + error i) :
    μ (screeningHistory base screen 3) ≤
      q ^ 3 + q ^ 2 * error 0 + q * error 1 + error 2 := by
  exact three_stage_measure_le μ
    (stageBound_screeningHistory μ base screen 0 q (error 0) (hstage 0))
    (stageBound_screeningHistory μ base screen 1 q (error 1) (hstage 1))
    (stageBound_screeningHistory μ base screen 2 q (error 2) (hstage 2))

/-- Equal exceptional errors at the three stages contribute at most a
geometrically weighted error. -/
theorem three_stage_measure_le_common_error (μ : Measure Ω) [IsProbabilityMeasure μ]
    {q error : ℝ≥0∞} {E₀ E₁ E₂ E₃ : Set Ω}
    (h₁ : StageBound μ q error E₀ E₁)
    (h₂ : StageBound μ q error E₁ E₂)
    (h₃ : StageBound μ q error E₂ E₃) :
    μ E₃ ≤ q ^ 3 + (q ^ 2 + q + 1) * error := by
  calc
    μ E₃ ≤ q ^ 3 + q ^ 2 * error + q * error + error :=
      three_stage_measure_le μ h₁ h₂ h₃
    _ = q ^ 3 + (q ^ 2 + q + 1) * error := by ring

/-- A finite grid of parameter choices costs only its cardinality. The
distinguished set `bad` collects all exceptional estimates that were removed
before the three clean screening stages. -/
theorem finite_grid_three_stage
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (grid : Finset ι) (bad target : Set Ω)
    (E₀ E₁ E₂ E₃ : ι → Set Ω) {q error badError : ℝ≥0∞}
    (hcover : target ⊆ bad ∪ ⋃ a ∈ grid, E₃ a)
    (hbad : μ bad ≤ badError)
    (h₁ : ∀ a ∈ grid, StageBound μ q error (E₀ a) (E₁ a))
    (h₂ : ∀ a ∈ grid, StageBound μ q error (E₁ a) (E₂ a))
    (h₃ : ∀ a ∈ grid, StageBound μ q error (E₂ a) (E₃ a)) :
    μ target ≤ badError + grid.card * (q ^ 3 + (q ^ 2 + q + 1) * error) := by
  calc
    μ target ≤ μ (bad ∪ ⋃ a ∈ grid, E₃ a) := measure_mono hcover
    _ ≤ μ bad + μ (⋃ a ∈ grid, E₃ a) := measure_union_le _ _
    _ ≤ badError + ∑ a ∈ grid, μ (E₃ a) := by
      gcongr
      exact measure_biUnion_finset_le grid E₃
    _ ≤ badError + ∑ _a ∈ grid, (q ^ 3 + (q ^ 2 + q + 1) * error) := by
      gcongr with a ha
      exact three_stage_measure_le_common_error μ (h₁ a ha) (h₂ a ha) (h₃ a ha)
    _ = badError + grid.card * (q ^ 3 + (q ^ 2 + q + 1) * error) := by
      simp only [Finset.sum_const, nsmul_eq_mul]

/-- The exact no-exception form used for the main `m^{-κ}` contribution. -/
theorem finite_grid_three_stage_zero_error
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (grid : Finset ι) (target : Set Ω)
    (E₀ E₁ E₂ E₃ : ι → Set Ω) {q : ℝ≥0∞}
    (hcover : target ⊆ ⋃ a ∈ grid, E₃ a)
    (h₁ : ∀ a ∈ grid, StageBound μ q 0 (E₀ a) (E₁ a))
    (h₂ : ∀ a ∈ grid, StageBound μ q 0 (E₁ a) (E₂ a))
    (h₃ : ∀ a ∈ grid, StageBound μ q 0 (E₂ a) (E₃ a)) :
    μ target ≤ grid.card * q ^ 3 := by
  have h := finite_grid_three_stage μ grid ∅ target E₀ E₁ E₂ E₃
      (q := q) (error := 0) (badError := 0)
      (by simpa using hcover) (by simp) h₁ h₂ h₃
  simpa using h

/-- If each of the three stage costs has the concrete form `C * rate`,
the final estimate has rate cubed. -/
theorem finite_grid_three_stage_cubic_rate
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (grid : Finset ι) (target : Set Ω)
    (E₀ E₁ E₂ E₃ : ι → Set Ω) {C rate : ℝ≥0∞}
    (hcover : target ⊆ ⋃ a ∈ grid, E₃ a)
    (h₁ : ∀ a ∈ grid, StageBound μ (C * rate) 0 (E₀ a) (E₁ a))
    (h₂ : ∀ a ∈ grid, StageBound μ (C * rate) 0 (E₁ a) (E₂ a))
    (h₃ : ∀ a ∈ grid, StageBound μ (C * rate) 0 (E₂ a) (E₃ a)) :
    μ target ≤ grid.card * C ^ 3 * rate ^ 3 := by
  calc
    μ target ≤ grid.card * (C * rate) ^ 3 :=
      finite_grid_three_stage_zero_error μ grid target E₀ E₁ E₂ E₃
        hcover h₁ h₂ h₃
    _ = grid.card * C ^ 3 * rate ^ 3 := by ring

/-- Cubing the inverse-power stage cost gives exactly the exponent `3κ`. -/
theorem ennreal_inverse_rpow_cube (x : ℝ≥0∞) (κ : ℝ) :
    (x ^ (-κ)) ^ 3 = x ^ (-(3 * κ)) := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  congr 1
  ring

/-- Source-shaped specialization: three `m^{-κ}` screening costs and a fixed
finite parameter grid give a constant multiple of `m^{-3κ}`. -/
theorem finite_grid_three_stage_inverse_power
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (grid : Finset ι) (target : Set Ω)
    (E₀ E₁ E₂ E₃ : ι → Set Ω) (m : ℕ) {C : ℝ≥0∞} {κ : ℝ}
    (hcover : target ⊆ ⋃ a ∈ grid, E₃ a)
    (h₁ : ∀ a ∈ grid,
      StageBound μ (C * (m : ℝ≥0∞) ^ (-κ)) 0 (E₀ a) (E₁ a))
    (h₂ : ∀ a ∈ grid,
      StageBound μ (C * (m : ℝ≥0∞) ^ (-κ)) 0 (E₁ a) (E₂ a))
    (h₃ : ∀ a ∈ grid,
      StageBound μ (C * (m : ℝ≥0∞) ^ (-κ)) 0 (E₂ a) (E₃ a)) :
    μ target ≤ grid.card * C ^ 3 * (m : ℝ≥0∞) ^ (-(3 * κ)) := by
  simpa only [ennreal_inverse_rpow_cube] using
    finite_grid_three_stage_cubic_rate μ grid target E₀ E₁ E₂ E₃
      hcover h₁ h₂ h₃

/-! ### Absorbing the harmless factors in the source estimate -/

/-- Any fixed real power of a logarithm is eventually bounded by an
arbitrarily small positive power. This is the standard device for absorbing
polylogarithmic losses into a chosen power slack. -/
theorem eventually_log_rpow_le_rpow {p ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ m : ℕ in atTop,
      Real.log (m : ℝ) ^ p ≤ (m : ℝ) ^ ε := by
  have hsmall :=
    (isLittleO_log_rpow_rpow_atTop p hε).comp_tendsto
      (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [hsmall.eventuallyLE, eventually_ge_atTop 1] with m hm hm1
  have hm1real : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  change ‖Real.log (m : ℝ) ^ p‖ ≤ ‖(m : ℝ) ^ ε‖ at hm
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (Real.log_nonneg hm1real) p),
    Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) ε)] at hm
  exact hm

/-- Consequently, a polylogarithmic multiplier on `m⁻ᵃ` can be absorbed by
losing any prescribed positive amount from the exponent. -/
theorem eventually_polylog_mul_rpow_neg_le {p a ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ m : ℕ in atTop,
      Real.log (m : ℝ) ^ p * (m : ℝ) ^ (-a) ≤
        (m : ℝ) ^ (-(a - ε)) := by
  filter_upwards [eventually_log_rpow_le_rpow (p := p) hε,
    eventually_ge_atTop 1] with m hlog hm1
  calc
    Real.log (m : ℝ) ^ p * (m : ℝ) ^ (-a) ≤
        (m : ℝ) ^ ε * (m : ℝ) ^ (-a) := by
      gcongr
    _ = (m : ℝ) ^ (ε + -a) :=
      (Real.rpow_add (by positivity : (0 : ℝ) < m) ε (-a)).symm
    _ = (m : ℝ) ^ (-(a - ε)) := by ring_nf

/-- The stretched-log exceptional errors in HLOZ are eventually smaller than
every inverse polynomial. -/
theorem eventually_exp_neg_log_sq_le_rpow_neg {c a : ℝ}
    (hc : 0 < c) (_ha : 0 ≤ a) :
    ∀ᶠ m : ℕ in atTop,
      Real.exp (-c * Real.log (m : ℝ) ^ 2) ≤ (m : ℝ) ^ (-a) := by
  have hthreshold : ∀ᶠ x : ℝ in atTop, a / c ≤ Real.log x :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (a / c))
  have hthresholdNat :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hthreshold
  filter_upwards [hthresholdNat, eventually_ge_atTop 1] with m hlog hm1
  have hlog0 : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg (by exact_mod_cast hm1)
  have hc0 : 0 ≤ c := hc.le
  have hmul : a * Real.log (m : ℝ) ≤ c * Real.log (m : ℝ) ^ 2 := by
    have : a ≤ c * Real.log (m : ℝ) := by
      simpa [mul_comm] using (div_le_iff₀ hc).mp hlog
    nlinarith
  rw [Real.rpow_def_of_pos (by positivity : (0 : ℝ) < m)]
  apply Real.exp_le_exp.mpr
  nlinarith

end Erdos1166.HLOZScreeningAssembly
