import ErdosProblems.Erdos1166.Erdos1166HLOZPairingScreeningBridge

namespace Erdos1166.HLOZProp47Parameters

open Filter MeasureTheory Set
open scoped ENNReal

open HLOZPairing
open HLOZPairing.ScreeningBridge
open HLOZScreeningAssembly

/-! ### A concrete choice satisfying HLOZ (4.26)--(4.28) -/

/-- The preliminary near-favourite exponent `κ₁` from HLOZ (4.9). -/
noncomputable def kappaOne : ℝ := 17 / 50

/-- The discretization cutoff `κ₂` in HLOZ (4.26). -/
noncomputable def kappaTwo : ℝ := 27 / 80

/-- The mesh size.  This is `κ₂ / 324`, as required by the paper's
description `δ = κ₂ / N` for a sufficiently large natural `N`. -/
noncomputable def delta : ℝ := 1 / 960

/-- The exponent left after the two `δ` losses in HLOZ (4.28). -/
noncomputable def kappa : ℝ := kappaTwo - 2 * delta

theorem kappaOne_between_one_third_and_seven_twentieths :
    (1 : ℝ) / 3 < kappaOne ∧ kappaOne < (7 : ℝ) / 20 := by
  norm_num [kappaOne]

theorem kappaTwo_between_one_third_and_kappaOne :
    (1 : ℝ) / 3 < kappaTwo ∧ kappaTwo < kappaOne := by
  norm_num [kappaTwo, kappaOne]

theorem delta_pos : 0 < delta := by
  norm_num [delta]

theorem delta_eq_kappaTwo_div_three_hundred_twenty_four :
    delta = kappaTwo / 324 := by
  norm_num [delta, kappaTwo]

/-- The exact strict chain imposed in HLOZ (4.26). -/
theorem exponent_parameter_chain :
    kappaOne > kappaTwo + 2 * delta ∧
      kappaTwo + 2 * delta > (1 : ℝ) / 3 + 4 * delta := by
  norm_num [kappaOne, kappaTwo, delta]

theorem kappa_eq : kappa = (161 : ℝ) / 480 := by
  norm_num [kappa, kappaTwo, delta]

theorem kappa_gt_one_third : (1 : ℝ) / 3 < kappa := by
  norm_num [kappa_eq]

/-- Three screenings give the summable exponent `161/160`. -/
theorem three_kappa_eq : 3 * kappa = (161 : ℝ) / 160 := by
  norm_num [kappa_eq]

theorem one_lt_three_kappa : 1 < 3 * kappa := by
  norm_num [three_kappa_eq]

/-! ### The finite `Λ` grid from HLOZ (4.27) -/

/-- An index for the full 960-point distance mesh
`Λ ∩ (0,1] = {δ,2δ,...,960δ}` used in (4.36)--(4.37). -/
abbrev AlphaIndex := Fin 960

/-- The real exponent represented by a grid index. -/
noncomputable def alphaValue (j : AlphaIndex) : ℝ := (j.1 + 1) * delta

/-- `Λ ∩ [0,1]`, represented without a noncomputable real-valued finset. -/
def alphaGrid : Finset AlphaIndex := Finset.univ

@[simp] theorem card_alphaGrid : alphaGrid.card = 960 := by
  simp [alphaGrid]

theorem alphaValue_pos (j : AlphaIndex) : 0 < alphaValue j := by
  have hj : (0 : ℝ) < (j.1 : ℝ) + 1 := by positivity
  exact mul_pos hj delta_pos

theorem alphaValue_le_one (j : AlphaIndex) : alphaValue j ≤ 1 := by
  have hjNat : j.1 + 1 ≤ 960 := Nat.succ_le_iff.mpr j.2
  have hj : (j.1 : ℝ) + 1 ≤ 960 := by exact_mod_cast hjNat
  rw [alphaValue, delta]
  norm_num
  linarith

theorem alphaValue_is_delta_multiple (j : AlphaIndex) :
    ∃ n : ℕ, 1 ≤ n ∧ n ≤ 960 ∧ alphaValue j = n * delta := by
  refine ⟨j.1 + 1, Nat.succ_le_succ (Nat.zero_le _),
    Nat.succ_le_iff.mpr j.2, ?_⟩
  simp [alphaValue]

/-- The 324-point submesh `Λ₀ = Λ ∩ (0,κ₂]` used inside
the Lemma 4.10 near-favourite screening.  It is not the full distance grid
over which Proposition 4.7 takes its three finite unions. -/
abbrev ScreeningAlphaIndex := Fin 324

noncomputable def screeningAlphaValue (j : ScreeningAlphaIndex) : ℝ :=
  (j.1 + 1) * delta

def screeningAlphaGrid : Finset ScreeningAlphaIndex := Finset.univ

@[simp] theorem card_screeningAlphaGrid : screeningAlphaGrid.card = 324 := by
  simp [screeningAlphaGrid]

theorem screeningAlphaValue_pos (j : ScreeningAlphaIndex) :
    0 < screeningAlphaValue j := by
  have hj : (0 : ℝ) < (j.1 : ℝ) + 1 := by positivity
  exact mul_pos hj delta_pos

theorem screeningAlphaValue_le_kappaTwo (j : ScreeningAlphaIndex) :
    screeningAlphaValue j ≤ kappaTwo := by
  have hjNat : j.1 + 1 ≤ 324 := Nat.succ_le_iff.mpr j.2
  have hj : (j.1 : ℝ) + 1 ≤ 324 := by exact_mod_cast hjNat
  rw [screeningAlphaValue, delta, kappaTwo]
  norm_num
  linarith

/-- A parameter choice for each of the three screening rounds. -/
abbrev AlphaTriple := AlphaIndex × AlphaIndex × AlphaIndex

/-- The finite union used after iterating (4.36)--(4.37) three times. -/
def screeningTripleGrid : Finset AlphaTriple := Finset.univ

@[simp] theorem card_screeningTripleGrid : screeningTripleGrid.card = 960 ^ 3 := by
  norm_num [screeningTripleGrid, AlphaTriple, AlphaIndex]

/-! ### Absorption of the source's harmless analytic errors -/

/-- A polylogarithmic loss accompanied by one extra `δ` of inverse-power
decay is eventually absorbed into the target exponent `3κ`. -/
theorem eventually_polylog_error_absorbed (p : ℝ) :
    ∀ᶠ m : ℕ in atTop,
      Real.log (m : ℝ) ^ p * (m : ℝ) ^ (-(3 * kappa + delta)) ≤
        (m : ℝ) ^ (-(3 * kappa)) := by
  simpa only [add_sub_cancel_right] using
    (eventually_polylog_mul_rpow_neg_le
      (p := p) (a := 3 * kappa + delta) (ε := delta) delta_pos)

/-- The `exp (-c (log m)^2)` errors in Lemma 4.10 and Propositions 4.8--4.9
are eventually smaller than the target inverse power. -/
theorem eventually_exponential_error_absorbed {c : ℝ} (hc : 0 < c) :
    ∀ᶠ m : ℕ in atTop,
      Real.exp (-c * Real.log (m : ℝ) ^ 2) ≤
        (m : ℝ) ^ (-(3 * kappa)) := by
  apply eventually_exp_neg_log_sq_le_rpow_neg hc
  linarith [one_lt_three_kappa]

/-- Both analytic error types can be discarded simultaneously after a
deterministic level. -/
theorem eventually_all_source_errors_absorbed (p : ℝ) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ m : ℕ in atTop,
      Real.log (m : ℝ) ^ p * (m : ℝ) ^ (-(3 * kappa + delta)) ≤
          (m : ℝ) ^ (-(3 * kappa)) ∧
        Real.exp (-c * Real.log (m : ℝ) ^ 2) ≤
          (m : ℝ) ^ (-(3 * kappa)) :=
  (eventually_polylog_error_absorbed p).and
    (eventually_exponential_error_absorbed hc)

/-! ### Source-facing closure of Proposition 4.7 -/

/-- With the concrete parameters and finite grid fixed above, the only
remaining inputs are the source-specific event cover and the three
single-stage estimates corresponding to HLOZ (4.36)--(4.37).  All exponent
inequalities and grid-cardinality obligations are discharged internally. -/
theorem hlozPlanarConclusion_of_prop47_single_stage_estimates
    (A B : ℕ)
    (bad : ℕ → Fin 6 → Set (ℕ → Site))
    (E₀ E₁ E₂ E₃ : ℕ → Fin 6 → AlphaTriple → Set (ℕ → Site))
    (hcover : ∀ m i,
      firstFourPairingEvent m i ⊆
        bad m i ∪ ⋃ a ∈ screeningTripleGrid, E₃ m i a)
    (hbad : ∀ m i,
      simpleRandomWalkLaw (bad m i) ≤
        sourceExceptionalRateWithPrefactor m B kappa)
    (h₁ : ∀ m i a, a ∈ screeningTripleGrid →
      StageBound simpleRandomWalkLaw (sourceStageRate m A kappa)
        (sourceExceptionalRateWithPrefactor m B kappa) (E₀ m i a) (E₁ m i a))
    (h₂ : ∀ m i a, a ∈ screeningTripleGrid →
      StageBound simpleRandomWalkLaw (sourceStageRate m A kappa)
        (sourceExceptionalRateWithPrefactor m B kappa) (E₁ m i a) (E₂ m i a))
    (h₃ : ∀ m i a, a ∈ screeningTripleGrid →
      StageBound simpleRandomWalkLaw (sourceStageRate m A kappa)
        (sourceExceptionalRateWithPrefactor m B kappa) (E₂ m i a) (E₃ m i a)) :
    HLOZPlanarConclusion := by
  apply hlozPlanarConclusion_of_prefactored_source_screenings
      A B (960 ^ 3) kappa one_lt_three_kappa
      (fun _m _i ↦ screeningTripleGrid) bad E₀ E₁ E₂ E₃
  · intro m i
    simp
  · exact hcover
  · exact hbad
  · exact h₁
  · exact h₂
  · exact h₃

/-- A compact wrapper for the two source estimates on the two sides of
`κ₂`.  Keeping this as a named predicate also prevents elaboration of the
full stage-bound expression six times in downstream source interfaces. -/
def BranchedStageBound (alpha : ℝ) (m A B : ℕ)
    (previous next : Set (ℕ → Site)) : Prop :=
  (alpha ≤ kappaTwo →
    StageBound simpleRandomWalkLaw (sourceStageRate m A kappa)
      (sourceExceptionalRateWithPrefactor m B kappa) previous next) ∧
  (kappaTwo < alpha →
    StageBound simpleRandomWalkLaw (sourceStageRate m A kappa)
      (sourceExceptionalRateWithPrefactor m B kappa) previous next)

theorem BranchedStageBound.stage {alpha : ℝ} {m A B : ℕ}
    {previous next : Set (ℕ → Site)}
    (h : BranchedStageBound alpha m A B previous next) :
    StageBound simpleRandomWalkLaw (sourceStageRate m A kappa)
      (sourceExceptionalRateWithPrefactor m B kappa) previous next := by
  rcases le_or_gt alpha kappaTwo with hle | hgt
  · exact h.1 hle
  · exact h.2 hgt

/-- Full-grid, source-facing closure with the correct eventual and
prefactored error interface.  The 960-point distance grid is fixed here;
callers may discharge each displayed `StageBound` from a
`BranchedStageBound`, using the low (`α≤κ₂`) or high (`α>κ₂`) source
estimate as appropriate. -/
theorem hlozPlanarConclusion_of_eventually_prop47_single_stage_estimates
    (A B : ℕ)
    (bad : ℕ → Fin 6 → Set (ℕ → Site))
    (E₀ E₁ E₂ E₃ : ℕ → Fin 6 → AlphaTriple → Set (ℕ → Site))
    (hcover : ∀ m i, firstFourPairingEvent m i ⊆
      bad m i ∪ ⋃ a ∈ screeningTripleGrid, E₃ m i a)
    (hsource : ∀ᶠ m : ℕ in atTop, ∀ i : Fin 6,
      simpleRandomWalkLaw (bad m i) ≤
          sourceExceptionalRateWithPrefactor m B kappa ∧
      (∀ a ∈ screeningTripleGrid,
        StageBound simpleRandomWalkLaw (sourceStageRate m A kappa)
          (sourceExceptionalRateWithPrefactor m B kappa) (E₀ m i a) (E₁ m i a)) ∧
      (∀ a ∈ screeningTripleGrid,
        StageBound simpleRandomWalkLaw (sourceStageRate m A kappa)
          (sourceExceptionalRateWithPrefactor m B kappa) (E₁ m i a) (E₂ m i a)) ∧
      (∀ a ∈ screeningTripleGrid,
        StageBound simpleRandomWalkLaw (sourceStageRate m A kappa)
          (sourceExceptionalRateWithPrefactor m B kappa) (E₂ m i a) (E₃ m i a))) :
    HLOZPlanarConclusion := by
  apply hlozPlanarConclusion_of_eventually_prefactored_source_screenings
      A B (960 ^ 3) kappa one_lt_three_kappa
      (fun _m _i ↦ screeningTripleGrid) bad E₀ E₁ E₂ E₃
  · intro m i
    simp
  · exact hcover
  · exact hsource

end Erdos1166.HLOZProp47Parameters
