/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Variable-delta summation over countable stopped histories

The number of honest replacement ranks may depend on the retained history.
The local comparison pays this multiplicity on its source side.  Regrouping
the replacement pieces by their numerical increment then loses only the
harmonic sum up to a uniform multiplicity bound, rather than the bound itself.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.HLOZVariableDeltaHistoryCapSummation

noncomputable section

/-- The ENNReal harmonic factor used by the variable-delta summation. -/
def variableDeltaHarmonic (M : ℕ) : ℝ≥0∞ :=
  ∑ d ∈ Finset.range M, ((d + 1 : ℕ) : ℝ≥0∞)⁻¹

/-- The history-summation factor is exactly the ordinary finite harmonic
number, embedded into `ENNReal`. -/
theorem variableDeltaHarmonic_eq_ofReal_harmonic (M : ℕ) :
    variableDeltaHarmonic M = ENNReal.ofReal (harmonic M : ℝ) := by
  unfold variableDeltaHarmonic harmonic
  rw [Rat.cast_sum]
  rw [ENNReal.ofReal_sum_of_nonneg]
  · apply Finset.sum_congr rfl
    intro d hd
    simp only [Rat.cast_inv, Rat.cast_natCast]
    rw [ENNReal.ofReal_inv_of_pos (by positivity)]
    have hbase : ENNReal.ofReal ((d : ℝ) + 1) =
        ((d + 1 : ℕ) : ℝ≥0∞) := by
      rw [← Nat.cast_add_one, ENNReal.ofReal_natCast]
    simpa only [Nat.cast_add, Nat.cast_one] using
      congrArg (fun x : ℝ≥0∞ ↦ x⁻¹) hbase.symm
  · intro d hd
    positivity

/-- Logarithmic upper bound for the variable-rank loss. -/
theorem variableDeltaHarmonic_le_one_add_log (M : ℕ) :
    variableDeltaHarmonic M ≤ ENNReal.ofReal (1 + Real.log (M : ℝ)) := by
  rw [variableDeltaHarmonic_eq_ofReal_harmonic]
  exact ENNReal.ofReal_mono (harmonic_le_one_add_log M)

/-- Cap-level data for a history-dependent finite set of numerical endpoint
increments.  At each fixed numerical increment, the enclosing rank atoms are
pairwise disjoint across histories. -/
structure VariableDeltaHistoryCapData
    {Omega History : Type*} [MeasurableSpace Omega] [Countable History]
    (mu : Measure Omega) (event : Set Omega) (q : ℝ≥0∞) (M : ℕ) where
  multiplicity : History → ℕ
  multiplicity_pos : ∀ history, 0 < multiplicity history
  multiplicity_le : ∀ history, multiplicity history ≤ M
  sourceCap : ℕ → History → Set Omega
  rankCap : ℕ → ℕ → History → Set Omega
  rankAtom : ℕ → History → Set Omega
  event_subset : event ⊆ ⋃ history, ⋃ cap, sourceCap cap history
  source_monotone : ∀ history, Monotone fun cap ↦ sourceCap cap history
  cap_le : ∀ cap history,
    (multiplicity history : ℝ≥0∞) * mu (sourceCap cap history) ≤
      q * ∑' d : ℕ,
        if h : d < multiplicity history then mu (rankCap cap d history)
        else 0
  measurable_rankCap : ∀ cap d history,
    MeasurableSet (rankCap cap d history)
  rankCap_subset_rankAtom : ∀ cap d history,
    rankCap cap d history ⊆ rankAtom d history
  disjoint_rankAtom : ∀ d, Pairwise fun history history' ↦
    Disjoint (rankAtom d history) (rankAtom d history')

namespace VariableDeltaHistoryCapData

def sourceHistory
    {Omega History : Type*} [MeasurableSpace Omega] [Countable History]
    {mu : Measure Omega} {event : Set Omega} {q : ℝ≥0∞} {M : ℕ}
    (data : VariableDeltaHistoryCapData (History := History) mu event q M)
    (history : History) : Set Omega :=
  ⋃ cap, data.sourceCap cap history

def rankHistory
    {Omega History : Type*} [MeasurableSpace Omega] [Countable History]
    {mu : Measure Omega} {event : Set Omega} {q : ℝ≥0∞} {M : ℕ}
    (data : VariableDeltaHistoryCapData (History := History) mu event q M)
    (d : ℕ) (history : History) : Set Omega :=
  ⋃ cap, data.rankCap cap d history

theorem measurable_rankHistory
    {Omega History : Type*} [MeasurableSpace Omega] [Countable History]
    {mu : Measure Omega} {event : Set Omega} {q : ℝ≥0∞} {M : ℕ}
    (data : VariableDeltaHistoryCapData (History := History) mu event q M)
    (d : ℕ) (history : History) :
    MeasurableSet (data.rankHistory d history) := by
  exact MeasurableSet.iUnion fun cap ↦ data.measurable_rankCap cap d history

theorem rankHistory_subset_rankAtom
    {Omega History : Type*} [MeasurableSpace Omega] [Countable History]
    {mu : Measure Omega} {event : Set Omega} {q : ℝ≥0∞} {M : ℕ}
    (data : VariableDeltaHistoryCapData (History := History) mu event q M)
    (d : ℕ) (history : History) :
    data.rankHistory d history ⊆ data.rankAtom d history := by
  intro omega homega
  rcases Set.mem_iUnion.mp homega with ⟨cap, hcap⟩
  exact data.rankCap_subset_rankAtom cap d history hcap

theorem disjoint_rankHistory
    {Omega History : Type*} [MeasurableSpace Omega] [Countable History]
    {mu : Measure Omega} {event : Set Omega} {q : ℝ≥0∞} {M : ℕ}
    (data : VariableDeltaHistoryCapData (History := History) mu event q M)
    (d : ℕ) : Pairwise fun history history' ↦
    Disjoint (data.rankHistory d history) (data.rankHistory d history') := by
  intro history history' hne
  exact (data.disjoint_rankAtom d hne).mono
    (data.rankHistory_subset_rankAtom d history)
    (data.rankHistory_subset_rankAtom d history')

private theorem sourceHistory_le_inverse_sum
    {Omega History : Type*} [MeasurableSpace Omega] [Countable History]
    {mu : Measure Omega} {event : Set Omega} {q : ℝ≥0∞} {M : ℕ}
    (data : VariableDeltaHistoryCapData (History := History) mu event q M)
    (history : History) :
    mu (data.sourceHistory history) ≤
      q * ∑' d : ℕ,
        if h : d < data.multiplicity history then
          (data.multiplicity history : ℝ≥0∞)⁻¹ *
            mu (data.rankHistory d history)
        else 0 := by
  have hpos : (data.multiplicity history : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (data.multiplicity_pos history))
  have htop : (data.multiplicity history : ℝ≥0∞) ≠ ∞ := by simp
  have hlim := tendsto_measure_iUnion_atTop
    (μ := mu) (data.source_monotone history)
  apply le_of_tendsto hlim
  filter_upwards [] with cap
  have hweighted :
      (data.multiplicity history : ℝ≥0∞) *
          mu (data.sourceCap cap history) ≤
        q * ∑' d : ℕ,
          if h : d < data.multiplicity history then
            mu (data.rankHistory d history)
          else 0 := by
    exact (data.cap_le cap history).trans <| by
      apply mul_le_mul le_rfl
      · apply ENNReal.tsum_le_tsum
        intro d
        split
        next h =>
          exact measure_mono (Set.subset_iUnion
            (fun cap ↦ data.rankCap cap d history) cap)
        next _ => exact le_rfl
      · exact bot_le
      · exact bot_le
  calc
    mu (data.sourceCap cap history) =
        (data.multiplicity history : ℝ≥0∞)⁻¹ *
          ((data.multiplicity history : ℝ≥0∞) *
            mu (data.sourceCap cap history)) := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel hpos htop, one_mul]
    _ ≤ (data.multiplicity history : ℝ≥0∞)⁻¹ *
        (q * ∑' d : ℕ,
        if h : d < data.multiplicity history then
          mu (data.rankHistory d history)
        else 0) := mul_le_mul le_rfl hweighted bot_le bot_le
    _ = q * ((data.multiplicity history : ℝ≥0∞)⁻¹ *
        ∑' d : ℕ,
          if h : d < data.multiplicity history then
            mu (data.rankHistory d history)
          else 0) := by ac_rfl
    _ = q * ∑' d : ℕ,
          (data.multiplicity history : ℝ≥0∞)⁻¹ *
            (if h : d < data.multiplicity history then
              mu (data.rankHistory d history)
            else 0) := by
      rw [ENNReal.tsum_mul_left]
    _ = q * ∑' d : ℕ,
          if h : d < data.multiplicity history then
            (data.multiplicity history : ℝ≥0∞)⁻¹ *
              mu (data.rankHistory d history)
          else 0 := by
      congr 1
      apply tsum_congr
      intro d
      split <;> simp_all

private theorem fixedDelta_weighted_rank_sum_le
    {Omega History : Type*} [MeasurableSpace Omega] [Countable History]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {event : Set Omega} {q : ℝ≥0∞} {M : ℕ}
    (data : VariableDeltaHistoryCapData (History := History) mu event q M)
    (d : ℕ) :
    (∑' history : History,
      if h : d < data.multiplicity history then
        (data.multiplicity history : ℝ≥0∞)⁻¹ *
          mu (data.rankHistory d history)
      else 0) ≤
      ((d + 1 : ℕ) : ℝ≥0∞)⁻¹ := by
  calc
    (∑' history : History,
        if h : d < data.multiplicity history then
          (data.multiplicity history : ℝ≥0∞)⁻¹ *
            mu (data.rankHistory d history)
        else 0) ≤
      ∑' history : History,
        ((d + 1 : ℕ) : ℝ≥0∞)⁻¹ *
          mu (data.rankHistory d history) := by
      apply ENNReal.tsum_le_tsum
      intro history
      split
      next h =>
        apply mul_le_mul
        · exact ENNReal.inv_le_inv.mpr (by exact_mod_cast h)
        · exact le_rfl
        · exact bot_le
        · exact bot_le
      next _ => exact bot_le
    _ = ((d + 1 : ℕ) : ℝ≥0∞)⁻¹ *
        ∑' history : History, mu (data.rankHistory d history) := by
      rw [ENNReal.tsum_mul_left]
    _ ≤ ((d + 1 : ℕ) : ℝ≥0∞)⁻¹ := by
      apply mul_le_of_le_one_right
      · exact bot_le
      · rw [← measure_iUnion (data.disjoint_rankHistory d)
            (data.measurable_rankHistory d)]
        calc
          mu (⋃ history, data.rankHistory d history) ≤ mu Set.univ :=
            measure_mono (Set.subset_univ _)
          _ = 1 := measure_univ

/-- Global variable-delta summation.  The only loss from histories carrying
different finite increment sets is the harmonic factor through `M`. -/
theorem measure_event_le
    {Omega History : Type*} [MeasurableSpace Omega] [Countable History]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (event : Set Omega) (q : ℝ≥0∞) (M : ℕ)
    (data : VariableDeltaHistoryCapData
      (History := History) mu event q M) :
    mu event ≤ variableDeltaHarmonic M * q := by
  calc
    mu event ≤ mu (⋃ history, data.sourceHistory history) :=
      measure_mono (by
        intro omega homega
        rcases Set.mem_iUnion.mp (data.event_subset homega) with
          ⟨history, hhistory⟩
        exact Set.mem_iUnion.mpr ⟨history, hhistory⟩)
    _ ≤ ∑' history, mu (data.sourceHistory history) := measure_iUnion_le _
    _ ≤ ∑' history, q * ∑' d : ℕ,
          if h : d < data.multiplicity history then
            (data.multiplicity history : ℝ≥0∞)⁻¹ *
              mu (data.rankHistory d history)
          else 0 := ENNReal.tsum_le_tsum data.sourceHistory_le_inverse_sum
    _ = q * ∑' d : ℕ, ∑' history : History,
          if h : d < data.multiplicity history then
            (data.multiplicity history : ℝ≥0∞)⁻¹ *
              mu (data.rankHistory d history)
          else 0 := by
      rw [ENNReal.tsum_mul_left]
      congr 1
      exact ENNReal.tsum_comm
    _ ≤ q * ∑' d : ℕ,
          if d < M then ((d + 1 : ℕ) : ℝ≥0∞)⁻¹ else 0 := by
      apply mul_le_mul le_rfl
      · apply ENNReal.tsum_le_tsum
        intro d
        by_cases hd : d < M
        · rw [if_pos hd]
          exact data.fixedDelta_weighted_rank_sum_le d
        · rw [if_neg hd]
          calc
            (∑' history : History,
              if h : d < data.multiplicity history then
                (data.multiplicity history : ℝ≥0∞)⁻¹ *
                  mu (data.rankHistory d history)
              else 0) ≤ ∑' _history : History, (0 : ℝ≥0∞) := by
                apply ENNReal.tsum_le_tsum
                intro history
                have hnot : ¬d < data.multiplicity history := fun h ↦
                  hd (h.trans_le (data.multiplicity_le history))
                simp only [hnot, dite_false]
                exact le_rfl
            _ = 0 := by simp
      · exact bot_le
      · exact bot_le
    _ = variableDeltaHarmonic M * q := by
      rw [mul_comm]
      unfold variableDeltaHarmonic
      rw [tsum_eq_sum (s := Finset.range M)]
      · congr 1
        apply Finset.sum_congr rfl
        intro d hd
        rw [Finset.mem_range] at hd
        rw [if_pos hd]
      · intro d hd
        rw [if_neg]
        simpa only [Finset.mem_range] using hd

end VariableDeltaHistoryCapData

end

end Erdos1165.HLOZVariableDeltaHistoryCapSummation
