import ErdosProblems.Erdos1002.IteratedLpDeletion
import ErdosProblems.Erdos1002.NearResonantLowerTransitionMarked

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Exact assembly of the complete minor resonance shot

The literal minor shot is split into four normalized physical functions:
the two endpoint denominators, the smooth near shot, the lower transition,
and the sharp-minus-smooth fixed-away remainder.  The final union bound is
proved with the nested order of limits used by `FinalAssembly`.
-/

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace Erdos1002

noncomputable section

open MultivariateFactorialMomentMethod

def normalizedNearMinorSmallDenominatorSum
    (N : ℕ) (A ε : ℝ) (alpha : ℝ) : ℂ :=
  nearMinorSmallDenominatorSum N A ε alpha / Real.log (N : ℝ)

def normalizedNearMinorLowerTransitionSum
    (N : ℕ) (A ε : ℝ) (alpha : ℝ) : ℂ :=
  nearMinorLowerTransitionSum N A ε alpha / Real.log (N : ℝ)

def normalizedFixedAwayMinorRemainder
    (N : ℕ) (A ε : ℝ) (alpha : ℝ) : ℂ :=
  (minorFixedAwaySharpSum N (ε / 4) alpha -
      nearMinorUpperTransitionSum N A ε alpha) /
    Real.log (N : ℝ)

def normalizedComplexMinorResonanceShotSum
    (N : ℕ) (A : ℝ) (alpha : ℝ) : ℂ :=
  complexMinorResonanceShotSum N A alpha / Real.log (N : ℝ)

theorem normalizedComplexMinorResonanceShotSum_eq_cast
    (N : ℕ) (A alpha : ℝ) :
    normalizedComplexMinorResonanceShotSum N A alpha =
      (normalizedMinorResonanceShotSum N A alpha : ℂ) := by
  unfold normalizedComplexMinorResonanceShotSum
    normalizedMinorResonanceShotSum
  rw [complexMinorResonanceShotSum_eq_cast]
  push_cast
  rfl

/-- Exact four-piece normalized decomposition. -/
theorem normalizedComplexMinorResonanceShotSum_eq_components
    (N : ℕ) (A ε alpha : ℝ)
    (hN : 2 ≤ N) (hL : 0 < Real.log (N : ℝ))
    (hAquarter : A < Real.log (N : ℝ) * (ε / 4)) :
    normalizedComplexMinorResonanceShotSum N A alpha =
      normalizedNearMinorSmallDenominatorSum N A ε alpha +
        normalizedSmoothNearLiteralShotTail N A ε alpha -
        normalizedNearMinorLowerTransitionSum N A ε alpha +
        normalizedFixedAwayMinorRemainder N A ε alpha := by
  unfold normalizedComplexMinorResonanceShotSum
    normalizedNearMinorSmallDenominatorSum
    normalizedNearMinorLowerTransitionSum
    normalizedFixedAwayMinorRemainder
    normalizedSmoothNearLiteralShotTail
  rw [complexMinorResonanceShotSum_eq_hardNear_add_fixedAway
    N A ε alpha hN hL hAquarter]
  rw [nearMinorHardNearSum_eq_endpoint_add_smooth_sub_transitions]
  ring

/-- For fixed `A` and positive near-window width, the exact near/far split
is valid for every sufficiently large natural cutoff. -/
theorem eventually_minorComponentSplit_admissible
    (A ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      2 ≤ N ∧ 0 < Real.log (N : ℝ) ∧
        A < Real.log (N : ℝ) * (ε / 4) := by
  have hlog : Tendsto (fun N : ℕ ↦ Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hratio : Tendsto (fun N : ℕ ↦ A / Real.log (N : ℝ))
      atTop (nhds 0) := hlog.const_div_atTop A
  have hsmall : ∀ᶠ N : ℕ in atTop,
      A / Real.log (N : ℝ) < ε / 4 :=
    hratio.eventually_lt_const (by positivity)
  filter_upwards [eventually_ge_atTop 2, hsmall] with N hN hsmallN
  have hL : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast hN)
  exact ⟨hN, hL, by
    apply (div_lt_iff₀ hL).mp hsmallN |>.trans_eq
    ring⟩

/-- The endpoint denominators vanish in probability in the required
iterated limit.  In fact their event is eventually empty by the pointwise
`2/A` bound. -/
theorem iterated_probabilityDeletion_normalizedNearMinorSmallDenominatorSum
    (ε : ℝ) :
    ∀ r > 0, ∀ δ > 0,
      ∀ᶠ A : ℕ in atTop, ∀ᶠ N : ℕ in atTop,
        uniform01Measure.real
          {alpha | r ≤
            ‖normalizedNearMinorSmallDenominatorSum
              N (A : ℝ) ε alpha‖} < δ := by
  intro r hr δ hδ
  have hratio : Tendsto (fun A : ℕ ↦ 2 / (A : ℝ)) atTop (nhds 0) :=
    tendsto_natCast_atTop_atTop.const_div_atTop 2
  have hsmall : ∀ᶠ A : ℕ in atTop, 2 / (A : ℝ) < r :=
    hratio.eventually_lt_const hr
  filter_upwards [hsmall, eventually_ge_atTop 1] with A hAr hA
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hApos : 0 < (A : ℝ) := by exact_mod_cast (show 0 < A by omega)
  have hL : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast hN)
  have hempty :
      {alpha | r ≤ ‖normalizedNearMinorSmallDenominatorSum
        N (A : ℝ) ε alpha‖} = (∅ : Set ℝ) := by
    ext alpha
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    apply not_le_of_gt
    exact (norm_nearMinorSmallDenominatorSum_div_log_le
      N (A : ℝ) ε alpha hApos hL).trans_lt hAr
  rw [hempty, measureReal_empty]
  exact hδ

/-- Four probability deletions combine to delete the literal real minor
shot.  The proof uses the exact physical identity above and three explicit
applications of the union bound. -/
theorem minorProbabilityDeletion_of_component_deletions
    (ε : ℝ) (hε : 0 < ε)
    (hsmall : ∀ r > 0, ∀ δ > 0,
      ∀ᶠ A : ℕ in atTop, ∀ᶠ N : ℕ in atTop,
        uniform01Measure.real
          {alpha | r ≤ ‖normalizedNearMinorSmallDenominatorSum
            N (A : ℝ) ε alpha‖} < δ)
    (hsmooth : ∀ r > 0, ∀ δ > 0,
      ∀ᶠ A : ℕ in atTop, ∀ᶠ N : ℕ in atTop,
        uniform01Measure.real
          {alpha | r ≤ ‖normalizedSmoothNearLiteralShotTail
            N (A : ℝ) ε alpha‖} < δ)
    (hlower : ∀ r > 0, ∀ δ > 0,
      ∀ᶠ A : ℕ in atTop, ∀ᶠ N : ℕ in atTop,
        uniform01Measure.real
          {alpha | r ≤ ‖normalizedNearMinorLowerTransitionSum
            N (A : ℝ) ε alpha‖} < δ)
    (hfixed : ∀ r > 0, ∀ δ > 0,
      ∀ᶠ A : ℕ in atTop, ∀ᶠ N : ℕ in atTop,
        uniform01Measure.real
          {alpha | r ≤ ‖normalizedFixedAwayMinorRemainder
            N (A : ℝ) ε alpha‖} < δ) :
    ∀ r > 0, ∀ δ > 0,
      ∀ᶠ A : ℕ in atTop, ∀ᶠ N : ℕ in atTop,
        uniform01Measure.real
          {alpha | r ≤ ‖normalizedMinorResonanceShotSum
            N (A : ℝ) alpha‖} < δ := by
  intro r hr δ hδ
  have hsA := hsmall (r / 4) (by positivity) (δ / 4) (by positivity)
  have hmA := hsmooth (r / 4) (by positivity) (δ / 4) (by positivity)
  have hlA := hlower (r / 4) (by positivity) (δ / 4) (by positivity)
  have hfA := hfixed (r / 4) (by positivity) (δ / 4) (by positivity)
  filter_upwards [hsA, hmA, hlA, hfA] with A hsN hmN hlN hfN
  have hadmissible := eventually_minorComponentSplit_admissible
    (A : ℝ) ε hε
  filter_upwards [hsN, hmN, hlN, hfN, hadmissible] with
      N hs hm hl hf hadm
  let U : Set ℝ := {alpha | r ≤
    ‖normalizedComplexMinorResonanceShotSum N (A : ℝ) alpha‖}
  let S : Set ℝ := {alpha | r / 4 ≤
    ‖normalizedNearMinorSmallDenominatorSum N (A : ℝ) ε alpha‖}
  let M : Set ℝ := {alpha | r / 4 ≤
    ‖normalizedSmoothNearLiteralShotTail N (A : ℝ) ε alpha‖}
  let Lw : Set ℝ := {alpha | r / 4 ≤
    ‖normalizedNearMinorLowerTransitionSum N (A : ℝ) ε alpha‖}
  let F : Set ℝ := {alpha | r / 4 ≤
    ‖normalizedFixedAwayMinorRemainder N (A : ℝ) ε alpha‖}
  have hsubset : U ⊆ S ∪ (M ∪ (Lw ∪ F)) := by
    intro alpha hU
    by_cases hS : r / 4 ≤
        ‖normalizedNearMinorSmallDenominatorSum N (A : ℝ) ε alpha‖
    · exact Or.inl hS
    by_cases hM : r / 4 ≤
        ‖normalizedSmoothNearLiteralShotTail N (A : ℝ) ε alpha‖
    · exact Or.inr (Or.inl hM)
    by_cases hLw : r / 4 ≤
        ‖normalizedNearMinorLowerTransitionSum N (A : ℝ) ε alpha‖
    · exact Or.inr (Or.inr (Or.inl hLw))
    by_cases hF : r / 4 ≤
        ‖normalizedFixedAwayMinorRemainder N (A : ℝ) ε alpha‖
    · exact Or.inr (Or.inr (Or.inr hF))
    · have hdecomp := normalizedComplexMinorResonanceShotSum_eq_components
        N (A : ℝ) ε alpha hadm.1 hadm.2.1 hadm.2.2
      have htri :
          ‖normalizedComplexMinorResonanceShotSum N (A : ℝ) alpha‖ ≤
            ‖normalizedNearMinorSmallDenominatorSum N (A : ℝ) ε alpha‖ +
            ‖normalizedSmoothNearLiteralShotTail N (A : ℝ) ε alpha‖ +
            ‖normalizedNearMinorLowerTransitionSum N (A : ℝ) ε alpha‖ +
            ‖normalizedFixedAwayMinorRemainder N (A : ℝ) ε alpha‖ := by
        rw [hdecomp]
        calc
          ‖normalizedNearMinorSmallDenominatorSum N (A : ℝ) ε alpha +
              normalizedSmoothNearLiteralShotTail N (A : ℝ) ε alpha -
              normalizedNearMinorLowerTransitionSum N (A : ℝ) ε alpha +
              normalizedFixedAwayMinorRemainder N (A : ℝ) ε alpha‖ ≤
            ‖normalizedNearMinorSmallDenominatorSum N (A : ℝ) ε alpha +
              normalizedSmoothNearLiteralShotTail N (A : ℝ) ε alpha -
              normalizedNearMinorLowerTransitionSum N (A : ℝ) ε alpha‖ +
              ‖normalizedFixedAwayMinorRemainder N (A : ℝ) ε alpha‖ :=
            norm_add_le _ _
          _ ≤ (‖normalizedNearMinorSmallDenominatorSum N (A : ℝ) ε alpha +
              normalizedSmoothNearLiteralShotTail N (A : ℝ) ε alpha‖ +
              ‖normalizedNearMinorLowerTransitionSum N (A : ℝ) ε alpha‖) +
              ‖normalizedFixedAwayMinorRemainder N (A : ℝ) ε alpha‖ := by
            gcongr
            exact norm_sub_le _ _
          _ ≤ (‖normalizedNearMinorSmallDenominatorSum N (A : ℝ) ε alpha‖ +
              ‖normalizedSmoothNearLiteralShotTail N (A : ℝ) ε alpha‖ +
              ‖normalizedNearMinorLowerTransitionSum N (A : ℝ) ε alpha‖) +
              ‖normalizedFixedAwayMinorRemainder N (A : ℝ) ε alpha‖ := by
            gcongr
            exact norm_add_le _ _
      dsimp [U] at hU
      have hslt := lt_of_not_ge hS
      have hmlt := lt_of_not_ge hM
      have hllt := lt_of_not_ge hLw
      have hflt := lt_of_not_ge hF
      linarith
  have hrealSet :
      {alpha | r ≤ ‖normalizedMinorResonanceShotSum N (A : ℝ) alpha‖} = U := by
    ext alpha
    dsimp [U]
    rw [normalizedComplexMinorResonanceShotSum_eq_cast,
      Complex.norm_real, Real.norm_eq_abs]
  rw [hrealSet]
  calc
    uniform01Measure.real U ≤
        uniform01Measure.real (S ∪ (M ∪ (Lw ∪ F))) :=
      measureReal_mono hsubset
    _ ≤ uniform01Measure.real S +
        uniform01Measure.real (M ∪ (Lw ∪ F)) := measureReal_union_le _ _
    _ ≤ uniform01Measure.real S +
        (uniform01Measure.real M +
          uniform01Measure.real (Lw ∪ F)) := by
      gcongr
      exact measureReal_union_le _ _
    _ ≤ uniform01Measure.real S +
        (uniform01Measure.real M +
          (uniform01Measure.real Lw + uniform01Measure.real F)) := by
      gcongr
      exact measureReal_union_le _ _
    _ < δ := by
      dsimp only [S, M, Lw, F]
      linarith

/-- The sole marked-process input needed to delete every lower transition
layer.  It refers only to the literal resonance count vector on the
explicit annular grid. -/
def LowerTransitionActualGridFactorialLimits : Prop :=
  ∀ (A : ℕ), 0 < A → ∀ m (k : AnnularGridIndex (m + 1) → ℕ),
    Tendsto
      (fun N ↦ mixedFactorialMoment
        (markedResonanceCountVectorLaw N N
          (annularGridCell ((A : ℝ) / 2) (A : ℝ) (m + 1))
          (fun i ↦ measurableSet_annularGridCell
            ((A : ℝ) / 2) (A : ℝ) (m + 1) i)) k)
      atTop
      (nhds (∏ i,
        (annularGridCellPoissonRate
          ((A : ℝ) / 2) (A : ℝ) (m + 1) i : ℝ) ^ (k i)))

private theorem tendsto_lowerTransitionTailMajorant_nat
    {R : ℝ} (hR : 0 < R) :
    Tendsto
      (fun A : ℕ ↦
        ((1 / (Real.pi ^ 2 / 6)) *
          (1 / (16 * (A : ℝ)))) / R ^ 2)
      atTop (nhds 0) := by
  let C : ℝ := ((1 / (Real.pi ^ 2 / 6)) * (1 / 16)) / R ^ 2
  have h := tendsto_natCast_atTop_atTop.const_div_atTop C
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with A hA
  have hAne : (A : ℝ) ≠ 0 := by exact_mod_cast (show A ≠ 0 by omega)
  dsimp [C]
  field_simp [hAne, hR.ne', Real.pi_ne_zero]

/-- The marked-grid factorial limits imply the exact nested probability
deletion of the literal lower residual, including the bridge from the
push-forward law back to the physical complex sum. -/
theorem lowerTransitionProbabilityDeletion_of_actualGridFactorialLimits
    (ε : ℝ) (hε : 0 < ε)
    (hFac : LowerTransitionActualGridFactorialLimits) :
    ∀ r > 0, ∀ δ > 0,
      ∀ᶠ A : ℕ in atTop, ∀ᶠ N : ℕ in atTop,
        uniform01Measure.real
          {alpha | r ≤ ‖normalizedNearMinorLowerTransitionSum
            N (A : ℝ) ε alpha‖} < δ := by
  intro r hr δ hδ
  have hmajorReal := tendsto_lowerTransitionTailMajorant_nat hr
  have hmajorENN : Tendsto
      (fun A : ℕ ↦ ENNReal.ofReal
        (((1 / (Real.pi ^ 2 / 6)) *
          (1 / (16 * (A : ℝ)))) / r ^ 2))
      atTop (nhds 0) := by
    simpa using! ENNReal.continuous_ofReal.continuousAt.tendsto.comp hmajorReal
  have hmajorSmall : ∀ᶠ A : ℕ in atTop,
      ENNReal.ofReal
          (((1 / (Real.pi ^ 2 / 6)) *
            (1 / (16 * (A : ℝ)))) / r ^ 2) <
        ENNReal.ofReal δ :=
    (tendsto_order.1 hmajorENN).2 _ (by simp [hδ])
  filter_upwards [hmajorSmall, eventually_ge_atTop 1] with A hmajorA hA
  have hApos : 0 < (A : ℝ) := by exact_mod_cast (show 0 < A by omega)
  have hlim := limsup_lowerTransitionMarkedLaw_tail_le_of_actualGridFactorialMoments
    hApos hr (hFac A (by omega))
  have hlawEventually : ∀ᶠ N : ℕ in atTop,
      (lowerTransitionMarkedLaw N (A : ℝ) : Measure ℝ)
          {x : ℝ | r ≤ |x|} < ENNReal.ofReal δ :=
    eventually_lt_of_limsup_lt (hlim.trans_lt hmajorA)
  have hscale := eventually_lowerTransition_scale_admissible
    (A : ℝ) ε hε
  filter_upwards [hlawEventually, hscale] with N hlaw hscaleN
  have htailMeas : MeasurableSet {x : ℝ | r ≤ |x|} :=
    isClosed_Ici.preimage continuous_abs |>.measurableSet
  have hlawEq :
      (lowerTransitionMarkedLaw N (A : ℝ) : Measure ℝ)
          {x : ℝ | r ≤ |x|} =
        uniform01Measure
          {alpha | r ≤ |lowerTransitionMarkedFunctionalReal
            N (A : ℝ) alpha|} := by
    unfold lowerTransitionMarkedLaw uniform01
    exact ProbabilityMeasure.map_apply'
      ⟨uniform01Measure, inferInstance⟩
      (measurable_lowerTransitionMarkedFunctionalReal N (A : ℝ)).aemeasurable
      htailMeas
  have hphysicalSet :
      {alpha | r ≤ ‖normalizedNearMinorLowerTransitionSum
        N (A : ℝ) ε alpha‖} =
      {alpha | r ≤ |lowerTransitionMarkedFunctionalReal
        N (A : ℝ) alpha|} := by
    ext alpha
    simp only [Set.mem_setOf_eq]
    rw [normalizedNearMinorLowerTransitionSum,
      norm_nearMinorLowerTransitionSum_div_log_eq_abs_markedFunctional
        N (A : ℝ) ε alpha hApos hscaleN.1 hε hscaleN.2]
  rw [hphysicalSet, measureReal_def, ← hlawEq]
  exact (ENNReal.toReal_lt_toReal (measure_ne_top _ _)
    ENNReal.ofReal_ne_top).2 hlaw |>.trans_eq
      (ENNReal.toReal_ofReal hδ.le)

/-- After inserting the already proved endpoint and smooth deletions, only
the lower-transition and fixed-away remainder estimates remain. -/
theorem minorProbabilityDeletion_of_lower_and_fixedAway
    (ε : ℝ) (hε : 0 < ε) (hεhalf : ε < 1 / 2)
    (hlower : ∀ r > 0, ∀ δ > 0,
      ∀ᶠ A : ℕ in atTop, ∀ᶠ N : ℕ in atTop,
        uniform01Measure.real
          {alpha | r ≤ ‖normalizedNearMinorLowerTransitionSum
            N (A : ℝ) ε alpha‖} < δ)
    (hfixed : ∀ r > 0, ∀ δ > 0,
      ∀ᶠ A : ℕ in atTop, ∀ᶠ N : ℕ in atTop,
        uniform01Measure.real
          {alpha | r ≤ ‖normalizedFixedAwayMinorRemainder
            N (A : ℝ) ε alpha‖} < δ) :
    ∀ r > 0, ∀ δ > 0,
      ∀ᶠ A : ℕ in atTop, ∀ᶠ N : ℕ in atTop,
        uniform01Measure.real
          {alpha | r ≤ ‖normalizedMinorResonanceShotSum
            N (A : ℝ) alpha‖} < δ := by
  exact minorProbabilityDeletion_of_component_deletions ε hε
    (iterated_probabilityDeletion_normalizedNearMinorSmallDenominatorSum ε)
    (iterated_probabilityDeletion_normalizedSmoothNearLiteralShotTail
      ε hε hεhalf)
    hlower hfixed

/-- After the actual marked-grid factorial limits have been supplied, the
complete minor deletion is reduced to the single fixed-away remainder.
This is the paper-facing interface for the two genuinely independent
inputs: marked Poisson convergence and the Ramanujan square-function
estimate. -/
theorem minorProbabilityDeletion_of_actualGridFactorialLimits_and_fixedAway
    (ε : ℝ) (hε : 0 < ε) (hεhalf : ε < 1 / 2)
    (hFac : LowerTransitionActualGridFactorialLimits)
    (hfixed : ∀ r > 0, ∀ δ > 0,
      ∀ᶠ A : ℕ in atTop, ∀ᶠ N : ℕ in atTop,
        uniform01Measure.real
          {alpha | r ≤ ‖normalizedFixedAwayMinorRemainder
            N (A : ℝ) ε alpha‖} < δ) :
    ∀ r > 0, ∀ δ > 0,
      ∀ᶠ A : ℕ in atTop, ∀ᶠ N : ℕ in atTop,
        uniform01Measure.real
          {alpha | r ≤ ‖normalizedMinorResonanceShotSum
            N (A : ℝ) alpha‖} < δ := by
  exact minorProbabilityDeletion_of_lower_and_fixedAway ε hε hεhalf
    (lowerTransitionProbabilityDeletion_of_actualGridFactorialLimits
      ε hε hFac)
    hfixed

end

end Erdos1002
