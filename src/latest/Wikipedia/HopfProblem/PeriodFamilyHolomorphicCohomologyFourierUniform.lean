import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyFourierContinuity

/-!
# Locally uniform Fourier ellipticity for a genuine period family

At any base point, the actual symbol has a positive lower bound by its proved
real-linear injectivity.  Operator-norm continuity retains half this bound on
one open neighborhood, simultaneously for every real frequency.  Restricting
to the original integer frequencies gives a locally uniform positive spectral
gap.  None of these statements assumes a family ellipticity estimate.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.Fourier

open Set Topology Filter
open PeriodTorusLineBundleClassification

/-- A single operator-norm estimate controls all vectors, not just a fixed one. -/
theorem lowerBound_of_norm_sub_le {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A A₀ : E →L[ℝ] F) (c : ℝ)
    (h₀ : ∀ v, c * ‖v‖ ≤ ‖A₀ v‖) (hnear : ‖A - A₀‖ ≤ c / 2) (v : E) :
    (c / 2) * ‖v‖ ≤ ‖A v‖ := by
  have hdiff : ‖(A - A₀) v‖ ≤ (c / 2) * ‖v‖ :=
    ((A - A₀).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right hnear (norm_nonneg v))
  have htri : ‖A₀ v‖ ≤ ‖A v‖ + ‖(A - A₀) v‖ := by
    simpa only [sub_apply, sub_sub_cancel] using
      norm_sub_le (A v) ((A - A₀) v)
  nlinarith [h₀ v]

variable {V B : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [TopologicalSpace B] [ChartedSpace V B] (P : HolomorphicPeriodMap V B)

/-- A genuinely uniform lower bound on one open neighborhood, valid for every
real frequency in the original period coordinates. -/
theorem exists_open_uniform_symbol_lowerBound (b : B) :
    ∃ (U : Set B) (c : ℝ), IsOpen U ∧ b ∈ U ∧ 0 < c ∧
      ∀ b' ∈ U, ∀ v : Fin 4 → ℝ, c * ‖v‖ ≤ ‖dolbeaultSymbol (P.point b') v‖ := by
  obtain ⟨c, hc, hbound⟩ := dolbeaultSymbol_exists_pos_lowerBound (P.point b)
  let U : Set B := {b' | ‖symbolOperator (P.point b') - symbolOperator (P.point b)‖ < c / 2}
  have hU : IsOpen U := isOpen_lt
    (((continuous_symbolOperator P).sub continuous_const).norm) continuous_const
  have hb : b ∈ U := by
    simpa only [U, mem_ofPred_eq, sub_self, norm_zero] using half_pos hc
  refine ⟨U, c / 2, hU, hb, half_pos hc, ?_⟩
  intro b' hb' v
  exact lowerBound_of_norm_sub_le (symbolOperator (P.point b'))
    (symbolOperator (P.point b)) c hbound (le_of_lt hb') v

/-- Neighborhood-filter form of the uniform real-frequency estimate. -/
theorem exists_eventually_uniform_symbol_lowerBound (b : B) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ b' in 𝓝 b, ∀ v : Fin 4 → ℝ,
      c * ‖v‖ ≤ ‖dolbeaultSymbol (P.point b') v‖ := by
  obtain ⟨U, c, hU, hb, hc, hbound⟩ := exists_open_uniform_symbol_lowerBound P b
  refine ⟨c, hc, ?_⟩
  filter_upwards [hU.mem_nhds hb] with b' hb'
  exact hbound b' hb'

/-- The same lower bound keeps the genuine integer-frequency norm. -/
theorem exists_open_uniform_integer_lowerBound (b : B) :
    ∃ (U : Set B) (c : ℝ), IsOpen U ∧ b ∈ U ∧ 0 < c ∧
      ∀ b' ∈ U, ∀ k : Fin 4 → ℤ,
        c * ‖k‖ ≤ ‖dolbeaultSymbol (P.point b') (integerFrequency k)‖ := by
  obtain ⟨U, c, hU, hb, hc, hbound⟩ := exists_open_uniform_symbol_lowerBound P b
  refine ⟨U, c, hU, hb, hc, fun b' hb' k => ?_⟩
  simpa only [integerFrequency_norm] using hbound b' hb' (integerFrequency k)

/-- All nonzero integer modes have one common positive gap near the base point. -/
theorem exists_open_uniform_integer_gap (b : B) :
    ∃ (U : Set B) (c : ℝ), IsOpen U ∧ b ∈ U ∧ 0 < c ∧
      ∀ b' ∈ U, ∀ k : Fin 4 → ℤ, k ≠ 0 →
        c ≤ ‖dolbeaultSymbol (P.point b') (integerFrequency k)‖ := by
  obtain ⟨U, c, hU, hb, hc, hbound⟩ := exists_open_uniform_integer_lowerBound P b
  refine ⟨U, c, hU, hb, hc, fun b' hb' k hk => ?_⟩
  calc
    c = c * 1 := (mul_one c).symm
    _ ≤ c * ‖k‖ := mul_le_mul_of_nonneg_left (one_le_norm_integerVector hk) hc.le
    _ ≤ ‖dolbeaultSymbol (P.point b') (integerFrequency k)‖ := hbound b' hb' k

/-- Neighborhood-filter form of the locally uniform nonzero-mode gap. -/
theorem exists_eventually_uniform_integer_gap (b : B) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ b' in 𝓝 b, ∀ k : Fin 4 → ℤ, k ≠ 0 →
      c ≤ ‖dolbeaultSymbol (P.point b') (integerFrequency k)‖ := by
  obtain ⟨U, c, hU, hb, hc, hgap⟩ := exists_open_uniform_integer_gap P b
  refine ⟨c, hc, ?_⟩
  filter_upwards [hU.mem_nhds hb] with b' hb'
  exact hgap b' hb'

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.Fourier
