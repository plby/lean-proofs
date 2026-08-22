/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZPositiveInterfacePairMultiplicity
import ErdosProblems.Erdos1165.HLOZPositiveInterfacePairSourceCapMonotone
import ErdosProblems.Erdos1165.HLOZPositiveInterfacePairSupportActualDeltaAtom
import ErdosProblems.Erdos1165.HLOZVariableDeltaHistoryCapSummation

/-!
# Harmonic summation of exact positive-interface pair histories

The local pair comparison pays its history-dependent number of honest raised
ranks on the source side.  Reindexing those ranks by their numerical endpoint
increment and using exact rank atoms loses only the corresponding harmonic
factor globally.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.HLOZPositiveInterfacePairHarmonic

open LazyDecomposition
open HLOZPositiveInterfacePairActualDeltaWalkCap
open HLOZPositiveInterfacePairMultiplicity
open HLOZPositiveInterfacePairSourceCapMonotone
open HLOZPositiveInterfacePairSupportActualDeltaAtom
open HLOZPositiveInterfacePairSupportActualDeltaWalkCap
open HLOZPositiveInterfacePairSupportFiber
open HLOZPositiveInterfacePairWeightedScreen
open HLOZSharpProductNumerics
open HLOZSourceOrientedThetaSourceActualDeltaProduct
open HLOZVariableDeltaHistoryCapSummation

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- External pair histories for which at least one exact source cap is
nonempty.  Restricting to active histories makes the uniform multiplicity
bound a structural fact rather than an empty-cap side condition. -/
abbrev PositiveInterfaceExternalPairActiveHistory
    (t : DominoTiling) (o : Orientation)
    (m k externalThreshold width shell : ℕ)
    (threshold : ℕ → ℕ) (bound : ℕ) (event : Set WalkPath) :=
  {eta : PositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold width shell //
    0 < eta.1.1.initial.1.length + 2 * eta.1.1.retainedCount +
        eta.1.1.tail.1.length ∧
      PositiveInterfaceExternalPairArithmetic eta 0 ∧
      ∃ cap s, s ∈ event ∧
        s ∈ positiveInterfaceExternalPairSourceCap eta cap threshold bound}

private noncomputable def activeHistoryDeltaEquiv
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold width shell : ℕ}
    {threshold : ℕ → ℕ} {bound : ℕ} {event : Set WalkPath}
    (history : PositiveInterfaceExternalPairActiveHistory t o m k
      externalThreshold width shell threshold bound event) :
    SourceActualDeltaIndex (PositiveInterfaceExternalPairFiber history.1) ≃
      Fin (positiveInterfaceExternalPairRankMultiplicity history.1) :=
  positiveInterfaceExternalPairActualDeltaEquiv history.1

private theorem activeHistory_fixedPrefix_pos
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold width shell : ℕ}
    {threshold : ℕ → ℕ} {bound : ℕ} {event : Set WalkPath}
    (history : PositiveInterfaceExternalPairActiveHistory t o m k
      externalThreshold width shell threshold bound event) :
    0 < history.1.1.1.initial.1.length +
      2 * history.1.1.1.retainedCount + history.1.1.1.tail.1.length := by
  exact history.2.1

private theorem activeHistory_multiplicity_le
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold width shell : ℕ}
    {threshold : ℕ → ℕ} {bound : ℕ} {event : Set WalkPath}
    (history : PositiveInterfaceExternalPairActiveHistory t o m k
      externalThreshold width shell threshold bound event) :
    positiveInterfaceExternalPairRankMultiplicity history.1 ≤ 2 * bound + 1 := by
  rcases history.2.2.2 with ⟨cap, s, _hsevent, hs⟩
  exact rankMultiplicity_le_two_mul_bound_add_one_of_mem_sourceCap
    history.1 cap threshold bound hs

private theorem arithmetic_change_cap
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold width shell cap cap' : ℕ}
    {eta : PositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold width shell}
    (h : PositiveInterfaceExternalPairArithmetic eta cap) :
    PositiveInterfaceExternalPairArithmetic eta cap' :=
  { external_pos := h.external_pos
    width_ge_four := h.width_ge_four
    window_ratio := h.window_ratio
    boundary_lt := h.boundary_lt }

private theorem activeHistory_arithmetic
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold width shell : ℕ}
    {threshold : ℕ → ℕ} {bound : ℕ} {event : Set WalkPath}
    (history : PositiveInterfaceExternalPairActiveHistory t o m k
      externalThreshold width shell threshold bound event) (cap : ℕ) :
    PositiveInterfaceExternalPairArithmetic history.1 cap :=
  arithmetic_change_cap history.2.2.1

/-- Reindex a finite actual-increment sum as a numerical sum supported below
the history's rank multiplicity. -/
private theorem actualDelta_tsum_eq_numerical_tsum
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold width shell : ℕ}
    (eta : PositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold width shell)
    (f : SourceActualDeltaIndex (PositiveInterfaceExternalPairFiber eta) →
      ℝ≥0∞) :
    (∑' delta, f delta) =
      ∑' d : ℕ,
        if h : d < positiveInterfaceExternalPairRankMultiplicity eta then
          f ((positiveInterfaceExternalPairActualDeltaEquiv eta).symm ⟨d, h⟩)
        else 0 := by
  classical
  let e := positiveInterfaceExternalPairActualDeltaEquiv eta
  calc
    (∑' delta, f delta) = ∑' i : Fin
        (positiveInterfaceExternalPairRankMultiplicity eta), f (e.symm i) :=
      (e.symm.tsum_eq f).symm
    _ = ∑ i : Fin (positiveInterfaceExternalPairRankMultiplicity eta),
        f (e.symm i) := tsum_fintype _
    _ = ∑ d ∈ Finset.range
        (positiveInterfaceExternalPairRankMultiplicity eta),
          if h : d < positiveInterfaceExternalPairRankMultiplicity eta then
            f (e.symm ⟨d, h⟩)
          else 0 := by
      rw [Finset.sum_fin_eq_sum_range]
    _ = ∑' d : ℕ,
        if h : d < positiveInterfaceExternalPairRankMultiplicity eta then
          f (e.symm ⟨d, h⟩)
        else 0 := by
      rw [tsum_eq_sum (s := Finset.range
        (positiveInterfaceExternalPairRankMultiplicity eta))]
      intro d hd
      have hnot : ¬d < positiveInterfaceExternalPairRankMultiplicity eta := by
        simpa only [Finset.mem_range] using hd
      simp only [hnot, ↓reduceDIte]

/-- The generic variable-rank history data furnished by the exact pair
source caps and support-preserving replacement caps. -/
noncomputable def positiveInterfaceExternalPairVariableDeltaData
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold width shell : ℕ}
    (hm : 1 < m) (hk : 0 < k)
    (threshold : ℕ → ℕ) (bound : ℕ) (event : Set WalkPath)
    (event_cover : ∀ s ∈ event,
      ∃ eta : PositiveInterfaceExternalPairSupportedIndex t o m k
          externalThreshold width shell,
        ∃ cap : ℕ,
          0 < eta.1.1.initial.1.length + 2 * eta.1.1.retainedCount +
              eta.1.1.tail.1.length ∧
            PositiveInterfaceExternalPairArithmetic eta cap ∧
            s ∈ positiveInterfaceExternalPairSourceCap eta cap threshold bound) :
    VariableDeltaHistoryCapData
      (History := PositiveInterfaceExternalPairActiveHistory t o m k
        externalThreshold width shell threshold bound event)
      simpleRandomWalk event
      (ENNReal.ofReal (sharpRankConstant * sharpInterfaceCost threshold shell))
      (2 * bound + 1) where
  multiplicity := fun history ↦
    positiveInterfaceExternalPairRankMultiplicity history.1
  multiplicity_pos := by
    intro history
    unfold positiveInterfaceExternalPairRankMultiplicity
    omega
  multiplicity_le := activeHistory_multiplicity_le
  sourceCap := fun cap history ↦
    positiveInterfaceExternalPairSourceCap history.1 cap threshold bound
  rankCap := fun cap d history ↦
    if h : d < positiveInterfaceExternalPairRankMultiplicity history.1 then
      positiveInterfaceExternalPairSupportActualDeltaCap history.1 cap
        ((activeHistoryDeltaEquiv history).symm ⟨d, h⟩)
    else ∅
  rankAtom := fun d history ↦
    positiveInterfaceExternalPairRankAtom t o m k externalThreshold width
      shell d history.1
  event_subset := by
    intro s hs
    rcases event_cover s hs with ⟨eta, cap, hpos, harith, hcap⟩
    let history : PositiveInterfaceExternalPairActiveHistory t o m k
        externalThreshold width shell threshold bound event :=
      ⟨eta, hpos, arithmetic_change_cap harith, cap, s, hs, hcap⟩
    exact Set.mem_iUnion.mpr ⟨history, Set.mem_iUnion.mpr ⟨cap, hcap⟩⟩
  source_monotone := by
    intro history
    exact monotone_positiveInterfaceExternalPairSourceCap history.1 threshold
      bound
  cap_le := by
    intro cap history
    have hlocal :=
      rankMultiplicity_mul_simpleRandomWalk_sourceCap_le_supportActualDelta_sum
        history.1 (by omega) hk
          (activeHistory_fixedPrefix_pos history)
          cap threshold bound (activeHistory_arithmetic history cap)
    rw [actualDelta_tsum_eq_numerical_tsum history.1] at hlocal
    calc
      _ ≤ ENNReal.ofReal (sharpRankConstant * sharpInterfaceCost threshold shell) *
          ∑' d : ℕ,
            if h : d < positiveInterfaceExternalPairRankMultiplicity
                history.1 then
              simpleRandomWalk
                (positiveInterfaceExternalPairSupportActualDeltaCap history.1
                  cap ((activeHistoryDeltaEquiv history).symm ⟨d, h⟩))
            else 0 := by
        simpa only [ENNReal.ofReal_natCast, activeHistoryDeltaEquiv] using hlocal
      _ = _ := by
        congr 1
        apply tsum_congr
        intro d
        by_cases hd : d < positiveInterfaceExternalPairRankMultiplicity
            history.1
        · simp only [hd, ↓reduceDIte]
        · simp only [hd, ↓reduceDIte]
  measurable_rankCap := by
    intro cap d history
    split
    next h =>
      exact measurableSet_positiveInterfaceExternalPairSupportActualDeltaCap
        history.1 cap ((activeHistoryDeltaEquiv history).symm ⟨d, h⟩)
    next _ => exact MeasurableSet.empty
  rankCap_subset_rankAtom := by
    intro cap d history
    split
    next h =>
      have hsubset :=
        positiveInterfaceExternalPairSupportActualDeltaCap_subset_rankAtom
          history.1 hm hk cap (activeHistory_arithmetic history cap)
            ((activeHistoryDeltaEquiv history).symm ⟨d, h⟩)
      simpa only [activeHistoryDeltaEquiv,
        positiveInterfaceExternalPairActualDeltaEquiv_symm_val] using hsubset
    next _ => exact Set.empty_subset _
  disjoint_rankAtom := by
    intro d history history' hne
    have heta : history.1 ≠ history'.1 := by
      intro heq
      exact hne (Subtype.ext heq)
    exact pairwise_disjoint_positiveInterfaceExternalPairRankAtom
      t o m k externalThreshold width shell d heta

/-- Global harmonic payment for any event covered by the positive-prefix
pair source caps. -/
theorem simpleRandomWalk_event_le_variableDeltaHarmonic
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold width shell : ℕ}
    (hm : 1 < m) (hk : 0 < k)
    (threshold : ℕ → ℕ) (bound : ℕ) (event : Set WalkPath)
    (event_cover : ∀ s ∈ event,
      ∃ eta : PositiveInterfaceExternalPairSupportedIndex t o m k
          externalThreshold width shell,
        ∃ cap : ℕ,
          0 < eta.1.1.initial.1.length + 2 * eta.1.1.retainedCount +
              eta.1.1.tail.1.length ∧
            PositiveInterfaceExternalPairArithmetic eta cap ∧
            s ∈ positiveInterfaceExternalPairSourceCap eta cap threshold bound) :
    simpleRandomWalk event ≤
      variableDeltaHarmonic (2 * bound + 1) *
        ENNReal.ofReal (sharpRankConstant * sharpInterfaceCost threshold shell) := by
  exact (positiveInterfaceExternalPairVariableDeltaData hm hk threshold bound
    event event_cover).measure_event_le

/-- The path-local balanced carrier: a path is admitted only when one exact
pair source cap covering it carries all arithmetic needed for the
support-preserving adjacent-row comparison.  This is the useful interface
for splitting raw growth histories into balanced and exceptional parts; no
global assertion about unrelated external histories is required. -/
def positiveInterfaceExternalPairBalancedSourceEvent
    (t : DominoTiling) (o : Orientation)
    (m k externalThreshold width shell : ℕ)
    (threshold : ℕ → ℕ) (bound : ℕ) : Set WalkPath :=
  {s | ∃ eta : PositiveInterfaceExternalPairSupportedIndex t o m k
        externalThreshold width shell,
      ∃ cap : ℕ,
        0 < eta.1.1.initial.1.length + 2 * eta.1.1.retainedCount +
            eta.1.1.tail.1.length ∧
          PositiveInterfaceExternalPairArithmetic eta cap ∧
          s ∈ positiveInterfaceExternalPairSourceCap eta cap threshold bound}

/-- The balanced pair-source carrier has the same harmonic payment as an
arbitrary locally covered event. -/
theorem simpleRandomWalk_positiveInterfaceExternalPairBalancedSourceEvent_le
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold width shell : ℕ}
    (hm : 1 < m) (hk : 0 < k)
    (threshold : ℕ → ℕ) (bound : ℕ) :
    simpleRandomWalk
        (positiveInterfaceExternalPairBalancedSourceEvent t o m k
          externalThreshold width shell threshold bound) ≤
      variableDeltaHarmonic (2 * bound + 1) *
        ENNReal.ofReal (sharpRankConstant * sharpInterfaceCost threshold shell) := by
  apply simpleRandomWalk_event_le_variableDeltaHarmonic hm hk threshold bound
  intro s hs
  exact hs

end

end Erdos1165.HLOZPositiveInterfacePairHarmonic
