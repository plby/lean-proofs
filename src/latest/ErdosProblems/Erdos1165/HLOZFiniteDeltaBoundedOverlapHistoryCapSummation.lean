/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZBoundedOverlapHistorySummation

/-!
# Finite-delta summation with bounded history overlap

Increasing source caps may be paid by finitely many replacement ranks even
when the enclosing rank atoms are not disjoint.  A uniform pointwise overlap
bound replaces disjointness at the cost of that multiplicity.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.HLOZFiniteDeltaBoundedOverlapHistoryCapSummation

open HLOZBoundedOverlapHistorySummation

noncomputable section

/-- Cap-level finite-rank payment data with a uniform overlap bound on the
enclosing rank atoms. -/
structure FiniteDeltaBoundedOverlapHistoryCapData
    {Omega History Delta : Type*} [MeasurableSpace Omega]
    [Countable History] [Fintype Delta]
    (mu : Measure Omega) (event : Set Omega) (q : ℝ≥0∞) (N : ℕ) where
  sourceCap : ℕ → History → Set Omega
  rankCap : ℕ → Delta → History → Set Omega
  rankAtom : Delta → History → Set Omega
  event_subset : event ⊆ ⋃ history, ⋃ cap, sourceCap cap history
  source_monotone : ∀ history, Monotone fun cap ↦ sourceCap cap history
  cap_le : ∀ cap history,
    mu (sourceCap cap history) ≤
      q * ∑' delta, mu (rankCap cap delta history)
  measurable_rankCap : ∀ cap delta history,
    MeasurableSet (rankCap cap delta history)
  rankCap_subset_rankAtom : ∀ cap delta history,
    rankCap cap delta history ⊆ rankAtom delta history
  rankAtom_overlap : ∀ delta omega,
    (({history | omega ∈ rankAtom delta history}.encard : ℕ∞) : ℝ≥0∞) ≤
      (N : ℝ≥0∞)

namespace FiniteDeltaBoundedOverlapHistoryCapData

def sourceHistory
    {Omega History Delta : Type*} [MeasurableSpace Omega]
    [Countable History] [Fintype Delta]
    {mu : Measure Omega} {event : Set Omega} {q : ℝ≥0∞} {N : ℕ}
    (data : FiniteDeltaBoundedOverlapHistoryCapData
      (History := History) (Delta := Delta) mu event q N)
    (history : History) : Set Omega :=
  ⋃ cap, data.sourceCap cap history

def rankHistory
    {Omega History Delta : Type*} [MeasurableSpace Omega]
    [Countable History] [Fintype Delta]
    {mu : Measure Omega} {event : Set Omega} {q : ℝ≥0∞} {N : ℕ}
    (data : FiniteDeltaBoundedOverlapHistoryCapData
      (History := History) (Delta := Delta) mu event q N)
    (delta : Delta) (history : History) : Set Omega :=
  ⋃ cap, data.rankCap cap delta history

theorem measurable_rankHistory
    {Omega History Delta : Type*} [MeasurableSpace Omega]
    [Countable History] [Fintype Delta]
    {mu : Measure Omega} {event : Set Omega} {q : ℝ≥0∞} {N : ℕ}
    (data : FiniteDeltaBoundedOverlapHistoryCapData
      (History := History) (Delta := Delta) mu event q N)
    (delta : Delta) (history : History) :
    MeasurableSet (data.rankHistory delta history) := by
  exact MeasurableSet.iUnion fun cap ↦
    data.measurable_rankCap cap delta history

theorem rankHistory_subset_rankAtom
    {Omega History Delta : Type*} [MeasurableSpace Omega]
    [Countable History] [Fintype Delta]
    {mu : Measure Omega} {event : Set Omega} {q : ℝ≥0∞} {N : ℕ}
    (data : FiniteDeltaBoundedOverlapHistoryCapData
      (History := History) (Delta := Delta) mu event q N)
    (delta : Delta) (history : History) :
    data.rankHistory delta history ⊆ data.rankAtom delta history := by
  intro omega homega
  rcases Set.mem_iUnion.mp homega with ⟨cap, hcap⟩
  exact data.rankCap_subset_rankAtom cap delta history hcap

theorem rankHistory_overlap
    {Omega History Delta : Type*} [MeasurableSpace Omega]
    [Countable History] [Fintype Delta]
    {mu : Measure Omega} {event : Set Omega} {q : ℝ≥0∞} {N : ℕ}
    (data : FiniteDeltaBoundedOverlapHistoryCapData
      (History := History) (Delta := Delta) mu event q N)
    (delta : Delta) (omega : Omega) :
    (({history | omega ∈ data.rankHistory delta history}.encard : ℕ∞) :
        ℝ≥0∞) ≤ (N : ℝ≥0∞) := by
  apply le_trans _ (data.rankAtom_overlap delta omega)
  exact_mod_cast Set.encard_le_encard <| by
    intro history hhistory
    exact data.rankHistory_subset_rankAtom delta history hhistory

theorem sourceHistory_le
    {Omega History Delta : Type*} [MeasurableSpace Omega]
    [Countable History] [Fintype Delta]
    {mu : Measure Omega} {event : Set Omega} {q : ℝ≥0∞} {N : ℕ}
    (data : FiniteDeltaBoundedOverlapHistoryCapData
      (History := History) (Delta := Delta) mu event q N)
    (history : History) :
    mu (data.sourceHistory history) ≤
      q * ∑' delta, mu (data.rankHistory delta history) := by
  have hlim := tendsto_measure_iUnion_atTop
    (μ := mu) (data.source_monotone history)
  apply le_of_tendsto hlim
  filter_upwards [] with cap
  calc
    mu (data.sourceCap cap history) ≤
        q * ∑' delta, mu (data.rankCap cap delta history) :=
      data.cap_le cap history
    _ ≤ q * ∑' delta, mu (data.rankHistory delta history) := by
      apply mul_le_mul_of_nonneg_left
      · apply ENNReal.tsum_le_tsum
        intro delta
        exact measure_mono (Set.subset_iUnion
          (fun cap ↦ data.rankCap cap delta history) cap)
      · exact bot_le

/-- Global finite-delta bounded-overlap summation. -/
theorem measure_event_le
    {Omega History Delta : Type*} [MeasurableSpace Omega]
    [Countable History] [Fintype Delta]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (event : Set Omega) (q : ℝ≥0∞) (N : ℕ)
    (data : FiniteDeltaBoundedOverlapHistoryCapData
      (History := History) (Delta := Delta) mu event q N) :
    mu event ≤ q * ((Fintype.card Delta : ℕ) : ℝ≥0∞) * (N : ℝ≥0∞) := by
  calc
    mu event ≤ mu (⋃ history, data.sourceHistory history) := by
      apply measure_mono
      intro omega homega
      rcases Set.mem_iUnion.mp (data.event_subset homega) with
        ⟨history, hhistory⟩
      exact Set.mem_iUnion.mpr ⟨history, hhistory⟩
    _ ≤ ∑' history, mu (data.sourceHistory history) := measure_iUnion_le _
    _ ≤ ∑' history, q * ∑' delta,
        mu (data.rankHistory delta history) :=
      ENNReal.tsum_le_tsum data.sourceHistory_le
    _ = q * ∑' delta, ∑' history,
        mu (data.rankHistory delta history) := by
      rw [ENNReal.tsum_mul_left]
      congr 1
      exact ENNReal.tsum_comm
    _ ≤ q * ∑' _delta : Delta, (N : ℝ≥0∞) := by
      apply mul_le_mul_of_nonneg_left
      apply ENNReal.tsum_le_tsum
      intro delta
      exact tsum_measure_le_of_overlap_probability mu
        (data.rankHistory delta) N (data.measurable_rankHistory delta)
          (data.rankHistory_overlap delta)
      exact bot_le
    _ = q * ((Fintype.card Delta : ℕ) : ℝ≥0∞) * (N : ℝ≥0∞) := by
      rw [tsum_fintype]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ac_rfl

end FiniteDeltaBoundedOverlapHistoryCapData

end

end Erdos1165.HLOZFiniteDeltaBoundedOverlapHistoryCapSummation
