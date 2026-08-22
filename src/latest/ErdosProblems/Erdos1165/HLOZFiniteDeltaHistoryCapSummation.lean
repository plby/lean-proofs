/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.HLOZShellZeroDeltaIndexedCapScreen

/-!
# Finite-delta summation over countable stopped histories

This is the shell-independent global summation used by source-slot payments.
For each retained history, increasing source caps are compared with a finite
sum of fixed-rank pieces.  Pieces at one fixed delta lie inside pairwise
disjoint full stopped rank atoms.  No disjointness across distinct deltas is
required; its only cost is `Fintype.card Delta`.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.HLOZFiniteDeltaHistoryCapSummation

open HLOZShellZeroDeltaIndexedCapScreen

noncomputable section

/-- Cap-level data for a finite endpoint-increment payment over a countable
history partition.  The enclosing `rankAtom` is allowed to be larger than the
cap piece; it exists solely to prove disjointness at each fixed delta. -/
structure FiniteDeltaHistoryCapData
    {Omega History Delta : Type*} [MeasurableSpace Omega]
    [Countable History] [Fintype Delta]
    (mu : Measure Omega) (event : Set Omega) (q : ℝ≥0∞) where
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
  disjoint_rankAtom : ∀ delta, Pairwise fun history history' ↦
    Disjoint (rankAtom delta history) (rankAtom delta history')

def FiniteDeltaHistoryCapData.sourceHistory
    {Omega History Delta : Type*} [MeasurableSpace Omega]
    [Countable History] [Fintype Delta]
    {mu : Measure Omega} {event : Set Omega} {q : ℝ≥0∞}
    (data : FiniteDeltaHistoryCapData
      (History := History) (Delta := Delta) mu event q)
    (history : History) : Set Omega :=
  ⋃ cap, data.sourceCap cap history

def FiniteDeltaHistoryCapData.rankHistory
    {Omega History Delta : Type*} [MeasurableSpace Omega]
    [Countable History] [Fintype Delta]
    {mu : Measure Omega} {event : Set Omega} {q : ℝ≥0∞}
    (data : FiniteDeltaHistoryCapData
      (History := History) (Delta := Delta) mu event q)
    (delta : Delta) (history : History) : Set Omega :=
  ⋃ cap, data.rankCap cap delta history

theorem FiniteDeltaHistoryCapData.measurable_rankHistory
    {Omega History Delta : Type*} [MeasurableSpace Omega]
    [Countable History] [Fintype Delta]
    {mu : Measure Omega} {event : Set Omega} {q : ℝ≥0∞}
    (data : FiniteDeltaHistoryCapData
      (History := History) (Delta := Delta) mu event q)
    (delta : Delta) (history : History) :
    MeasurableSet (data.rankHistory delta history) := by
  exact MeasurableSet.iUnion fun cap ↦
    data.measurable_rankCap cap delta history

theorem FiniteDeltaHistoryCapData.rankHistory_subset_rankAtom
    {Omega History Delta : Type*} [MeasurableSpace Omega]
    [Countable History] [Fintype Delta]
    {mu : Measure Omega} {event : Set Omega} {q : ℝ≥0∞}
    (data : FiniteDeltaHistoryCapData
      (History := History) (Delta := Delta) mu event q)
    (delta : Delta) (history : History) :
    data.rankHistory delta history ⊆ data.rankAtom delta history := by
  intro omega homega
  rcases Set.mem_iUnion.mp homega with ⟨cap, hcap⟩
  exact data.rankCap_subset_rankAtom cap delta history hcap

theorem FiniteDeltaHistoryCapData.disjoint_rankHistory
    {Omega History Delta : Type*} [MeasurableSpace Omega]
    [Countable History] [Fintype Delta]
    {mu : Measure Omega} {event : Set Omega} {q : ℝ≥0∞}
    (data : FiniteDeltaHistoryCapData
      (History := History) (Delta := Delta) mu event q)
    (delta : Delta) : Pairwise fun history history' ↦
    Disjoint (data.rankHistory delta history)
      (data.rankHistory delta history') := by
  intro history history' hne
  exact (data.disjoint_rankAtom delta hne).mono
    (data.rankHistory_subset_rankAtom delta history)
    (data.rankHistory_subset_rankAtom delta history')

theorem FiniteDeltaHistoryCapData.sourceHistory_le
    {Omega History Delta : Type*} [MeasurableSpace Omega]
    [Countable History] [Fintype Delta]
    {mu : Measure Omega} {event : Set Omega} {q : ℝ≥0∞}
    (data : FiniteDeltaHistoryCapData
      (History := History) (Delta := Delta) mu event q)
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

noncomputable def FiniteDeltaHistoryCapData.toCertificate
    {Omega History Delta : Type*} [MeasurableSpace Omega]
    [Countable History] [Fintype Delta]
    {mu : Measure Omega} {event : Set Omega} {q : ℝ≥0∞}
    (data : FiniteDeltaHistoryCapData
      (History := History) (Delta := Delta) mu event q) :
    DeltaIndexedReplacementCertificate
      (Index := History) (Delta := Delta) mu event q where
  sourceAtom := data.sourceHistory
  rankPiece := data.rankHistory
  source_subset := by
    intro omega homega
    rcases Set.mem_iUnion.mp (data.event_subset homega) with
      ⟨history, hhistory⟩
    exact Set.mem_iUnion.mpr ⟨history, hhistory⟩
  atom_le := data.sourceHistory_le
  measurable_rankPiece := data.measurable_rankHistory
  disjoint_rankPiece := data.disjoint_rankHistory

/-- Global finite-delta summation.  Fixed-delta stopped atoms are used only
for disjointness, so different replacement ranks may overlap arbitrarily. -/
theorem FiniteDeltaHistoryCapData.measure_event_le
    {Omega History Delta : Type*} [MeasurableSpace Omega]
    [Countable History] [Fintype Delta]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (event : Set Omega) (q : ℝ≥0∞)
    (data : FiniteDeltaHistoryCapData
      (History := History) (Delta := Delta) mu event q) :
    mu event ≤ (Fintype.card Delta : ℝ≥0∞) * q := by
  exact measure_le_rankMultiplicity_mul_of_deltaIndexedCertificate
    mu event q data.toCertificate

end


end Erdos1165.HLOZFiniteDeltaHistoryCapSummation
