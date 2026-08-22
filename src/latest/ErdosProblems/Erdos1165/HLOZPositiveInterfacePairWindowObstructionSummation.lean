/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZFiniteDeltaBoundedOverlapHistoryCapSummation
import ErdosProblems.Erdos1165.HLOZPositiveInterfacePairSingleDeletionOverlap
import ErdosProblems.Erdos1165.HLOZPositiveInterfacePairSourceCapMonotone

/-!
# Global summation of bad adjacent-window pair histories

The local bad-window comparison has three honest endpoint increments.  Its
observable replacement atoms remember an exact source history up to survival
or deletion of the exposed base.  The resulting `2 * (R + 1)` overlap bound
therefore gives a global exponentially small payment.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.HLOZPositiveInterfacePairWindowObstructionSummation

open ExternalProposition44
open HLOZFiniteDeltaBoundedOverlapHistoryCapSummation
open HLOZPathEvents
open HLOZPositiveInterfacePairActualDeltaWalkCap
open HLOZPositiveInterfacePairSingleDeletionAtom
open HLOZPositiveInterfacePairSingleDeletionOverlap
open HLOZPositiveInterfacePairSourceCapMonotone
open HLOZPositiveInterfacePairSupportFiber
open HLOZPositiveInterfacePairWindowTailObservableCap
open HLOZPositiveInterfacePairWindowTailProduct
open HLOZPositiveInterfacePairWindowTailSingleton
open HLOZPositiveInterfacePairWindowTailSingletonWalkCap
open HLOZPositiveInterfacePhysicalWindowRatio
open HLOZProposition48Candidates
open HLOZShellZeroReplacementWindows
open HLOZSourceOrientedThetaBalance
open HLOZSourceOrientedThetaCreationSlots
open HLOZSourceOrientedThetaProduct
open HLOZSourceOrientedThetaSourceActualDeltaProduct
open LazyDecomposition
open ScreeningInstantiation
open SmallWindow
open TilingOrientedRetainedDominoEndpoint
open TilingSpatialInsertionFiber

noncomputable section

abbrev DominoTiling := Tilings.Tiling

attribute [local instance] Classical.propDecidable

/-- Two consecutive accepted physical deficit rows fit inside the first
below-level strip whose width is their full distance from level `m`. -/
theorem positiveInterfacePairWindow_subset_thetaFailureWindow
    {m width i shell : ℕ} (hwidth : 0 < width)
    (hfit : (shell + 2) * width ≤ m) :
    positiveInterfacePairWindow m width i shell ⊆
      thetaFailureWindow m ((shell + 2) * width) i := by
  intro v hv
  rw [positiveInterfacePairWindow, Finset.mem_union] at hv
  rw [thetaFailureWindow, Finset.mem_union]
  left
  rw [mem_shellZeroSourceFailureWindow]
  rcases hv with hv | hv
  · rw [mem_acceptedPhysicalDeficitFailureWindow] at hv
    have hdeficit : m - (i + v) < (shell + 2) * width := by
      rw [← Nat.div_lt_iff_lt_mul hwidth, hv.2]
      omega
    omega
  · rw [mem_acceptedPhysicalDeficitFailureWindow] at hv
    have hdeficit : m - (i + v) < (shell + 2) * width := by
      rw [← Nat.div_lt_iff_lt_mul hwidth, hv.2]
      omega
    omega

/-- The cap-independent hypotheses carried by one pointed bad-window source
history. -/
def BadWindowPointedConditions
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold shell : ℕ} (R : ℕ)
    (p : PositiveInterfaceExternalPairPointedIndex t o m k
      externalThreshold (shellWidth48 m) shell) : Prop :=
  p.1.1.1.retainedCount ≤ R ∧
    0 < p.1.1.1.initial.1.length + 2 * p.1.1.1.retainedCount +
      p.1.1.1.tail.1.length ∧
    m / 2 ≤ Fintype.card
      (TilingCoordinatesAt t p.1.1.1.start p.1.1.1.retained p.2.1) ∧
    Fintype.card
      (TilingCoordinatesAt t p.1.1.1.start p.1.1.1.retained p.2.1) ≤ m ∧
    (shell + 2) * shellWidth48 m ≤ m ∧
    ¬windowMass
          (Fintype.card
            (TilingCoordinatesAt t p.1.1.1.start p.1.1.1.retained p.2.1))
          (acceptedPhysicalDeficitFailureWindow m (shellWidth48 m)
            (Fintype.card
              (TilingCoordinatesAt t p.1.1.1.start p.1.1.1.retained p.2.1))
            (shell + 1)) ≤
        positiveInterfaceRatioConstant * windowMass
          (Fintype.card
            (TilingCoordinatesAt t p.1.1.1.start p.1.1.1.retained p.2.1))
          (acceptedPhysicalDeficitFailureWindow m (shellWidth48 m)
            (Fintype.card
              (TilingCoordinatesAt t p.1.1.1.start p.1.1.1.retained p.2.1))
            shell)

/-- Pointed histories on which the singleton bad-window comparison applies. -/
abbrev PositiveInterfaceExternalPairBadWindowHistory
    (t : DominoTiling) (o : Orientation)
    (m k externalThreshold shell R : ℕ) :=
  {p : PositiveInterfaceExternalPairPointedIndex t o m k
      externalThreshold (shellWidth48 m) shell //
    BadWindowPointedConditions R p}

private theorem badWindowHistory_retained_le
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold shell R : ℕ}
    (history : PositiveInterfaceExternalPairBadWindowHistory t o m k
      externalThreshold shell R) :
    history.1.1.1.1.retainedCount ≤ R := history.2.1

private theorem badWindowHistory_fixed_pos
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold shell R : ℕ}
    (history : PositiveInterfaceExternalPairBadWindowHistory t o m k
      externalThreshold shell R) :
    0 < history.1.1.1.1.initial.1.length +
      2 * history.1.1.1.1.retainedCount +
        history.1.1.1.1.tail.1.length := history.2.2.1

/-- Generic finite-rank bounded-overlap data for a covered bad-window event. -/
noncomputable def badWindowBoundedOverlapData
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold shell R : ℕ}
    (hm : 1 < m) (hk : 0 < k)
    (threshold : ℕ → ℕ) (bound : ℕ) (event : Set WalkPath)
    (harithmetic : HLOZShellZeroReplacementWindows.ShellZeroWindowArithmeticAt m)
    (hwidthFour : 4 ≤ shellWidth48 m)
    (hwidthDeviation : 24 * (shellWidth48 m : ℝ) ≤ geometricDeviation m)
    (hdeviationLevel : geometricDeviation m ≤ (m : ℝ))
    (event_cover : ∀ s ∈ event,
      ∃ eta : PositiveInterfaceExternalPairSupportedIndex t o m k
          externalThreshold (shellWidth48 m) shell,
        ∃ cap : ℕ, ∃ b : PositiveInterfaceExternalPairCoordinate eta,
          BadWindowPointedConditions R ⟨eta, b⟩ ∧
            s ∈ positiveInterfaceExternalPairSourceCap eta cap threshold bound) :
    FiniteDeltaBoundedOverlapHistoryCapData
      (History := PositiveInterfaceExternalPairBadWindowHistory t o m k
        externalThreshold shell R)
      (Delta := Fin 3) simpleRandomWalk event
      (ENNReal.ofReal (2 * Real.exp (-17 * balanceRateScale m)))
      (2 * (R + 1)) where
  sourceCap := fun cap history ↦
    positiveInterfaceExternalPairSourceCap history.1.1 cap threshold bound
  rankCap := fun cap delta history ↦
    singletonPairObservableActualDeltaCap history.1.1 history.1.2 cap
      threshold bound
      ((singletonPairActualDeltaEquiv history.1.1 history.1.2).symm delta)
  rankAtom := fun delta history ↦
    positiveInterfaceExternalPairSingleDeletionRankAtom t o m k
      externalThreshold (shellWidth48 m) shell delta history.1.1 history.1.2
  event_subset := by
    intro s hs
    rcases event_cover s hs with ⟨eta, cap, b, hconditions, hcap⟩
    let history : PositiveInterfaceExternalPairBadWindowHistory t o m k
        externalThreshold shell R := ⟨⟨eta, b⟩, hconditions⟩
    exact Set.mem_iUnion.mpr ⟨history, Set.mem_iUnion.mpr ⟨cap, hcap⟩⟩
  source_monotone := by
    intro history
    exact monotone_positiveInterfaceExternalPairSourceCap history.1.1
      threshold bound
  cap_le := by
    intro cap history
    have hlocal :=
      simpleRandomWalk_sourceCap_le_exp_mul_observableSingletonSum
        history.1.1 history.1.2 (by omega) hk
          (badWindowHistory_fixed_pos history) cap threshold bound harithmetic
          hwidthFour history.2.2.2.1 history.2.2.2.2.1
          history.2.2.2.2.2.1 hwidthDeviation hdeviationLevel
          history.2.2.2.2.2.2
    calc
      simpleRandomWalk
          (positiveInterfaceExternalPairSourceCap history.1.1 cap threshold
            bound) ≤
        ENNReal.ofReal (2 * Real.exp (-17 * balanceRateScale m)) *
          ∑' delta : SourceActualDeltaIndex
              (singletonPairFiber history.1.1 history.1.2),
            simpleRandomWalk
              (singletonPairObservableActualDeltaCap history.1.1 history.1.2
                cap threshold bound delta) := hlocal
      _ = ENNReal.ofReal (2 * Real.exp (-17 * balanceRateScale m)) *
          ∑' delta : Fin 3,
            simpleRandomWalk
              (singletonPairObservableActualDeltaCap history.1.1 history.1.2
                cap threshold bound
                  ((singletonPairActualDeltaEquiv history.1.1
                    history.1.2).symm delta)) := by
        congr 1
        exact ((singletonPairActualDeltaEquiv history.1.1
          history.1.2).symm.tsum_eq _).symm
  measurable_rankCap := by
    intro cap delta history
    exact measurableSet_singletonPairObservableActualDeltaCap history.1.1
      history.1.2 cap threshold bound
        ((singletonPairActualDeltaEquiv history.1.1 history.1.2).symm delta)
  rankCap_subset_rankAtom := by
    intro cap delta history
    have hsubset :=
      singletonPairObservableActualDeltaCap_subset_singleDeletionRankAtom
        history.1.1 history.1.2 hm hk
          (badWindowHistory_fixed_pos history) cap threshold bound
          ((singletonPairActualDeltaEquiv history.1.1 history.1.2).symm delta)
    simpa only [singletonPairActualDeltaEquiv_symm_val] using hsubset
  rankAtom_overlap := by
    intro delta s
    have h := singleDeletionRankAtom_fiber_encard_le
      (fun history : PositiveInterfaceExternalPairBadWindowHistory t o m k
        externalThreshold shell R ↦ history.1)
      Subtype.val_injective R badWindowHistory_retained_le delta s
    exact_mod_cast h

/-- A covered bad-window event has the expected exponential mass bound, with
three endpoint increments and `2 * (R + 1)` source-history overlap. -/
theorem simpleRandomWalk_badWindowEvent_le
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold shell R : ℕ}
    (hm : 1 < m) (hk : 0 < k)
    (threshold : ℕ → ℕ) (bound : ℕ) (event : Set WalkPath)
    (harithmetic : HLOZShellZeroReplacementWindows.ShellZeroWindowArithmeticAt m)
    (hwidthFour : 4 ≤ shellWidth48 m)
    (hwidthDeviation : 24 * (shellWidth48 m : ℝ) ≤ geometricDeviation m)
    (hdeviationLevel : geometricDeviation m ≤ (m : ℝ))
    (event_cover : ∀ s ∈ event,
      ∃ eta : PositiveInterfaceExternalPairSupportedIndex t o m k
          externalThreshold (shellWidth48 m) shell,
        ∃ cap : ℕ, ∃ b : PositiveInterfaceExternalPairCoordinate eta,
          BadWindowPointedConditions R ⟨eta, b⟩ ∧
            s ∈ positiveInterfaceExternalPairSourceCap eta cap threshold bound) :
    simpleRandomWalk event ≤
      ENNReal.ofReal (2 * Real.exp (-17 * balanceRateScale m)) *
        (3 : ℝ≥0∞) * (2 * (R + 1) : ℕ) := by
  exact (badWindowBoundedOverlapData hm hk threshold bound event harithmetic
    hwidthFour hwidthDeviation hdeviationLevel event_cover).measure_event_le
      simpleRandomWalk event
      (ENNReal.ofReal (2 * Real.exp (-17 * balanceRateScale m)))
      (2 * (R + 1))

/-! ## Proposition 4.4 candidate-budget overlap -/

/-- The cap-independent bad-window hypotheses, with the exposed base charged
to the code-local Proposition 4.4 candidate family instead of to all retained
bases. -/
def CandidateBadWindowPointedConditions
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold shell : ℕ} (B : ℕ)
    (p : PositiveInterfaceExternalPairPointedIndex t o m k
      externalThreshold (shellWidth48 m) shell) : Prop :=
  orientedDominoEndpoint t o p.2.1.1 ∈
      orientedThetaCodeEndpointCandidateSites44 t o m p.1.1.1 ∧
    (orientedThetaCodeEndpointCandidateSites44 t o m p.1.1.1).card ≤ B ∧
    0 < p.1.1.1.initial.1.length + 2 * p.1.1.1.retainedCount +
      p.1.1.1.tail.1.length ∧
    m / 2 ≤ Fintype.card
      (TilingCoordinatesAt t p.1.1.1.start p.1.1.1.retained p.2.1) ∧
    Fintype.card
      (TilingCoordinatesAt t p.1.1.1.start p.1.1.1.retained p.2.1) ≤ m ∧
    (shell + 2) * shellWidth48 m ≤ m ∧
    ¬windowMass
          (Fintype.card
            (TilingCoordinatesAt t p.1.1.1.start p.1.1.1.retained p.2.1))
          (acceptedPhysicalDeficitFailureWindow m (shellWidth48 m)
            (Fintype.card
              (TilingCoordinatesAt t p.1.1.1.start p.1.1.1.retained p.2.1))
            (shell + 1)) ≤
        positiveInterfaceRatioConstant * windowMass
          (Fintype.card
            (TilingCoordinatesAt t p.1.1.1.start p.1.1.1.retained p.2.1))
          (acceptedPhysicalDeficitFailureWindow m (shellWidth48 m)
            (Fintype.card
              (TilingCoordinatesAt t p.1.1.1.start p.1.1.1.retained p.2.1))
            shell)

/-- Pointed bad-window histories whose bases range over a bounded high-count
candidate family. -/
abbrev PositiveInterfaceExternalPairCandidateBadWindowHistory
    (t : DominoTiling) (o : Orientation)
    (m k externalThreshold shell B : ℕ) :=
  {p : PositiveInterfaceExternalPairPointedIndex t o m k
      externalThreshold (shellWidth48 m) shell //
    CandidateBadWindowPointedConditions B p}

private theorem candidateBadWindowHistory_fixed_pos
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold shell B : ℕ}
    (history : PositiveInterfaceExternalPairCandidateBadWindowHistory t o m k
      externalThreshold shell B) :
    0 < history.1.1.1.1.initial.1.length +
      2 * history.1.1.1.1.retainedCount +
        history.1.1.1.1.tail.1.length := history.2.2.2.1

/-- Bounded-overlap summation data using the Proposition 4.4 candidate budget
`B`.  The overlap is `2 * B`, independent of the physical cutoff time. -/
noncomputable def candidateBadWindowBoundedOverlapData
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold shell B : ℕ}
    (hm : 1 < m) (hk : 0 < k)
    (threshold : ℕ → ℕ) (bound : ℕ) (event : Set WalkPath)
    (harithmetic : HLOZShellZeroReplacementWindows.ShellZeroWindowArithmeticAt m)
    (hwidthFour : 4 ≤ shellWidth48 m)
    (hwidthDeviation : 24 * (shellWidth48 m : ℝ) ≤ geometricDeviation m)
    (hdeviationLevel : geometricDeviation m ≤ (m : ℝ))
    (event_cover : ∀ s ∈ event,
      ∃ eta : PositiveInterfaceExternalPairSupportedIndex t o m k
          externalThreshold (shellWidth48 m) shell,
        ∃ cap : ℕ, ∃ b : PositiveInterfaceExternalPairCoordinate eta,
          CandidateBadWindowPointedConditions B ⟨eta, b⟩ ∧
            s ∈ positiveInterfaceExternalPairSourceCap eta cap threshold bound) :
    FiniteDeltaBoundedOverlapHistoryCapData
      (History := PositiveInterfaceExternalPairCandidateBadWindowHistory t o m k
        externalThreshold shell B)
      (Delta := Fin 3) simpleRandomWalk event
      (ENNReal.ofReal (2 * Real.exp (-17 * balanceRateScale m)))
      (2 * B) where
  sourceCap := fun cap history ↦
    positiveInterfaceExternalPairSourceCap history.1.1 cap threshold bound
  rankCap := fun cap delta history ↦
    singletonPairObservableActualDeltaCap history.1.1 history.1.2 cap
      threshold bound
      ((singletonPairActualDeltaEquiv history.1.1 history.1.2).symm delta)
  rankAtom := fun delta history ↦
    positiveInterfaceExternalPairSingleDeletionRankAtom t o m k
      externalThreshold (shellWidth48 m) shell delta history.1.1 history.1.2
  event_subset := by
    intro s hs
    rcases event_cover s hs with ⟨eta, cap, b, hconditions, hcap⟩
    let history : PositiveInterfaceExternalPairCandidateBadWindowHistory
        t o m k externalThreshold shell B := ⟨⟨eta, b⟩, hconditions⟩
    exact Set.mem_iUnion.mpr ⟨history, Set.mem_iUnion.mpr ⟨cap, hcap⟩⟩
  source_monotone := by
    intro history
    exact monotone_positiveInterfaceExternalPairSourceCap history.1.1
      threshold bound
  cap_le := by
    intro cap history
    have hlocal :=
      simpleRandomWalk_sourceCap_le_exp_mul_observableSingletonSum
        history.1.1 history.1.2 (by omega) hk
          (candidateBadWindowHistory_fixed_pos history) cap threshold bound
          harithmetic hwidthFour history.2.2.2.2.1
          history.2.2.2.2.2.1 history.2.2.2.2.2.2.1
          hwidthDeviation hdeviationLevel history.2.2.2.2.2.2.2
    calc
      simpleRandomWalk
          (positiveInterfaceExternalPairSourceCap history.1.1 cap threshold
            bound) ≤
        ENNReal.ofReal (2 * Real.exp (-17 * balanceRateScale m)) *
          ∑' delta : SourceActualDeltaIndex
              (singletonPairFiber history.1.1 history.1.2),
            simpleRandomWalk
              (singletonPairObservableActualDeltaCap history.1.1 history.1.2
                cap threshold bound delta) := hlocal
      _ = ENNReal.ofReal (2 * Real.exp (-17 * balanceRateScale m)) *
          ∑' delta : Fin 3,
            simpleRandomWalk
              (singletonPairObservableActualDeltaCap history.1.1 history.1.2
                cap threshold bound
                  ((singletonPairActualDeltaEquiv history.1.1
                    history.1.2).symm delta)) := by
        congr 1
        exact ((singletonPairActualDeltaEquiv history.1.1
          history.1.2).symm.tsum_eq _).symm
  measurable_rankCap := by
    intro cap delta history
    exact measurableSet_singletonPairObservableActualDeltaCap history.1.1
      history.1.2 cap threshold bound
        ((singletonPairActualDeltaEquiv history.1.1 history.1.2).symm delta)
  rankCap_subset_rankAtom := by
    intro cap delta history
    have hsubset :=
      singletonPairObservableActualDeltaCap_subset_singleDeletionRankAtom
        history.1.1 history.1.2 hm hk
          (candidateBadWindowHistory_fixed_pos history) cap threshold bound
          ((singletonPairActualDeltaEquiv history.1.1 history.1.2).symm delta)
    simpa only [singletonPairActualDeltaEquiv_symm_val] using hsubset
  rankAtom_overlap := by
    intro delta s
    have h := singleDeletionRankAtom_endpointCandidate_fiber_encard_le
      (fun history : PositiveInterfaceExternalPairCandidateBadWindowHistory
        t o m k externalThreshold shell B ↦ history.1)
      Subtype.val_injective B (fun history ↦ history.2.1)
      (fun history ↦ history.2.2.1) delta s
    exact_mod_cast h

/-- A covered bad-window event has the sharp one-coordinate tail and the
code-local Proposition 4.4 overlap budget. -/
theorem simpleRandomWalk_candidateBadWindowEvent_le
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold shell B : ℕ}
    (hm : 1 < m) (hk : 0 < k)
    (threshold : ℕ → ℕ) (bound : ℕ) (event : Set WalkPath)
    (harithmetic : HLOZShellZeroReplacementWindows.ShellZeroWindowArithmeticAt m)
    (hwidthFour : 4 ≤ shellWidth48 m)
    (hwidthDeviation : 24 * (shellWidth48 m : ℝ) ≤ geometricDeviation m)
    (hdeviationLevel : geometricDeviation m ≤ (m : ℝ))
    (event_cover : ∀ s ∈ event,
      ∃ eta : PositiveInterfaceExternalPairSupportedIndex t o m k
          externalThreshold (shellWidth48 m) shell,
        ∃ cap : ℕ, ∃ b : PositiveInterfaceExternalPairCoordinate eta,
          CandidateBadWindowPointedConditions B ⟨eta, b⟩ ∧
            s ∈ positiveInterfaceExternalPairSourceCap eta cap threshold bound) :
    simpleRandomWalk event ≤
      ENNReal.ofReal (2 * Real.exp (-17 * balanceRateScale m)) *
        (3 : ℝ≥0∞) * (2 * B : ℕ) := by
  exact (candidateBadWindowBoundedOverlapData hm hk threshold bound event
    harithmetic hwidthFour hwidthDeviation hdeviationLevel
    event_cover).measure_event_le simpleRandomWalk event
      (ENNReal.ofReal (2 * Real.exp (-17 * balanceRateScale m))) (2 * B)

/-! ## Strong low-count payment -/

/-- The cap-independent hypotheses for a low external-count bad-window
history.  The physical cutoff still bounds source-history overlap, while the
coordinate mass receives the stronger square-root exponential tail. -/
def LowBadWindowPointedConditions
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold shell : ℕ} (R : ℕ)
    (p : PositiveInterfaceExternalPairPointedIndex t o m k
      externalThreshold (shellWidth48 m) shell) : Prop :=
  p.1.1.1.retainedCount ≤ R ∧
    0 < p.1.1.1.initial.1.length + 2 * p.1.1.1.retainedCount +
      p.1.1.1.tail.1.length ∧
    Fintype.card
        (TilingCoordinatesAt t p.1.1.1.start p.1.1.1.retained p.2.1) <
      hlozThickLevel44 m ∧
    (shell + 2) * shellWidth48 m ≤ m

/-- Pointed bad-window histories on the low external-count side. -/
abbrev PositiveInterfaceExternalPairLowBadWindowHistory
    (t : DominoTiling) (o : Orientation)
    (m k externalThreshold shell R : ℕ) :=
  {p : PositiveInterfaceExternalPairPointedIndex t o m k
      externalThreshold (shellWidth48 m) shell //
    LowBadWindowPointedConditions R p}

private theorem lowBadWindowHistory_fixed_pos
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold shell R : ℕ}
    (history : PositiveInterfaceExternalPairLowBadWindowHistory t o m k
      externalThreshold shell R) :
    0 < history.1.1.1.1.initial.1.length +
      2 * history.1.1.1.1.retainedCount +
        history.1.1.1.1.tail.1.length := history.2.2.1

/-- Bounded-overlap summation data for the low-count half of the bad-window
event. -/
noncomputable def lowBadWindowBoundedOverlapData
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold shell R : ℕ}
    (hm : 1 < m) (hk : 0 < k)
    (threshold : ℕ → ℕ) (bound : ℕ) (event : Set WalkPath)
    (hwidthPos : 0 < shellWidth48 m)
    (hcombinedWidth : ((((shell + 2) * shellWidth48 m : ℕ) : ℝ)) ≤
      (m : ℝ) / 10)
    (hthreshold0 : 0 ≤ hlozThickThresholdReal44 m)
    (hdom : ((((shell + 2) * shellWidth48 m : ℕ) : ℝ)) +
        thetaLowDeviation m ≤
      (16 / 15 : ℝ) * (m : ℝ) ^ (4 / 5 : ℝ))
    (htheta : thetaLowDeviation m ≤
      (m + (shell + 2) * shellWidth48 m : ℕ))
    (event_cover : ∀ s ∈ event,
      ∃ eta : PositiveInterfaceExternalPairSupportedIndex t o m k
          externalThreshold (shellWidth48 m) shell,
        ∃ cap : ℕ, ∃ b : PositiveInterfaceExternalPairCoordinate eta,
          LowBadWindowPointedConditions R ⟨eta, b⟩ ∧
            s ∈ positiveInterfaceExternalPairSourceCap eta cap threshold bound) :
    FiniteDeltaBoundedOverlapHistoryCapData
      (History := PositiveInterfaceExternalPairLowBadWindowHistory t o m k
        externalThreshold shell R)
      (Delta := Fin 3) simpleRandomWalk event
      (ENNReal.ofReal (2 * Real.exp (-17 * thetaLowRateScale m)))
      (2 * (R + 1)) where
  sourceCap := fun cap history ↦
    positiveInterfaceExternalPairSourceCap history.1.1 cap threshold bound
  rankCap := fun cap delta history ↦
    singletonPairObservableActualDeltaCap history.1.1 history.1.2 cap
      threshold bound
      ((singletonPairActualDeltaEquiv history.1.1 history.1.2).symm delta)
  rankAtom := fun delta history ↦
    positiveInterfaceExternalPairSingleDeletionRankAtom t o m k
      externalThreshold (shellWidth48 m) shell delta history.1.1 history.1.2
  event_subset := by
    intro s hs
    rcases event_cover s hs with ⟨eta, cap, b, hconditions, hcap⟩
    let history : PositiveInterfaceExternalPairLowBadWindowHistory
        t o m k externalThreshold shell R := ⟨⟨eta, b⟩, hconditions⟩
    exact Set.mem_iUnion.mpr ⟨history, Set.mem_iUnion.mpr ⟨cap, hcap⟩⟩
  source_monotone := by
    intro history
    exact monotone_positiveInterfaceExternalPairSourceCap history.1.1
      threshold bound
  cap_le := by
    intro cap history
    let i := Fintype.card (TilingCoordinatesAt t history.1.1.1.1.start
      history.1.1.1.1.retained history.1.2.1)
    have hi : 0 < i := by
      dsimp only [i]
      exact card_tilingCoordinatesAt_pos t history.1.1.1.1.start
        history.1.1.1.1.retained history.1.2.1
    have hwindowMass :
        windowMass i
            (positiveInterfacePairWindow m (shellWidth48 m) i shell) ≤
          Real.exp (-17 * thetaLowRateScale m) := by
      calc
        windowMass i
            (positiveInterfacePairWindow m (shellWidth48 m) i shell) ≤
          windowMass i
            (thetaFailureWindow m ((shell + 2) * shellWidth48 m) i) := by
            unfold windowMass
            exact Finset.sum_le_sum_of_subset_of_nonneg
              (positiveInterfacePairWindow_subset_thetaFailureWindow
                hwidthPos history.2.2.2.2)
              (fun _ _ _ ↦ NegativeBinomial.hlozMass_nonneg _ _)
        _ ≤ Real.exp (-17 * thetaLowRateScale m) :=
          thetaFailureWindowMass_le_low_cost (by omega) hi hcombinedWidth
            history.2.2.2.1 hthreshold0 hdom htheta
    have hscreen : singletonPairWindowScreenMass history.1.1 history.1.2 cap ≤
        2 * Real.exp (-17 * thetaLowRateScale m) :=
      (singletonPairWindowScreenMass_le_two_mul_windowMass
        history.1.1 cap history.1.2).trans
          (by simpa only [i] using
            mul_le_mul_of_nonneg_left hwindowMass (by norm_num))
    have hlocal :=
      simpleRandomWalk_sourceCap_le_mul_observableSingletonSum_of_screenMass_le
        history.1.1 history.1.2 (by omega) hk
          (lowBadWindowHistory_fixed_pos history) cap threshold bound
          (2 * Real.exp (-17 * thetaLowRateScale m)) (by positivity) hscreen
    calc
      simpleRandomWalk
          (positiveInterfaceExternalPairSourceCap history.1.1 cap threshold
            bound) ≤
        ENNReal.ofReal (2 * Real.exp (-17 * thetaLowRateScale m)) *
          ∑' delta : SourceActualDeltaIndex
              (singletonPairFiber history.1.1 history.1.2),
            simpleRandomWalk
              (singletonPairObservableActualDeltaCap history.1.1 history.1.2
                cap threshold bound delta) := hlocal
      _ = ENNReal.ofReal (2 * Real.exp (-17 * thetaLowRateScale m)) *
          ∑' delta : Fin 3,
            simpleRandomWalk
              (singletonPairObservableActualDeltaCap history.1.1 history.1.2
                cap threshold bound
                  ((singletonPairActualDeltaEquiv history.1.1
                    history.1.2).symm delta)) := by
        congr 1
        exact ((singletonPairActualDeltaEquiv history.1.1
          history.1.2).symm.tsum_eq _).symm
  measurable_rankCap := by
    intro cap delta history
    exact measurableSet_singletonPairObservableActualDeltaCap history.1.1
      history.1.2 cap threshold bound
        ((singletonPairActualDeltaEquiv history.1.1 history.1.2).symm delta)
  rankCap_subset_rankAtom := by
    intro cap delta history
    have hsubset :=
      singletonPairObservableActualDeltaCap_subset_singleDeletionRankAtom
        history.1.1 history.1.2 hm hk
          (lowBadWindowHistory_fixed_pos history) cap threshold bound
          ((singletonPairActualDeltaEquiv history.1.1 history.1.2).symm delta)
    simpa only [singletonPairActualDeltaEquiv_symm_val] using hsubset
  rankAtom_overlap := by
    intro delta s
    have h := singleDeletionRankAtom_fiber_encard_le
      (fun history : PositiveInterfaceExternalPairLowBadWindowHistory
        t o m k externalThreshold shell R ↦ history.1)
      Subtype.val_injective R (fun history ↦ history.2.1) delta s
    exact_mod_cast h

/-- A covered low-count bad-window event has the square-root exponential
tail, with only the physical cutoff overlap factor remaining. -/
theorem simpleRandomWalk_lowBadWindowEvent_le
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold shell R : ℕ}
    (hm : 1 < m) (hk : 0 < k)
    (threshold : ℕ → ℕ) (bound : ℕ) (event : Set WalkPath)
    (hwidthPos : 0 < shellWidth48 m)
    (hcombinedWidth : ((((shell + 2) * shellWidth48 m : ℕ) : ℝ)) ≤
      (m : ℝ) / 10)
    (hthreshold0 : 0 ≤ hlozThickThresholdReal44 m)
    (hdom : ((((shell + 2) * shellWidth48 m : ℕ) : ℝ)) +
        thetaLowDeviation m ≤
      (16 / 15 : ℝ) * (m : ℝ) ^ (4 / 5 : ℝ))
    (htheta : thetaLowDeviation m ≤
      (m + (shell + 2) * shellWidth48 m : ℕ))
    (event_cover : ∀ s ∈ event,
      ∃ eta : PositiveInterfaceExternalPairSupportedIndex t o m k
          externalThreshold (shellWidth48 m) shell,
        ∃ cap : ℕ, ∃ b : PositiveInterfaceExternalPairCoordinate eta,
          LowBadWindowPointedConditions R ⟨eta, b⟩ ∧
            s ∈ positiveInterfaceExternalPairSourceCap eta cap threshold bound) :
    simpleRandomWalk event ≤
      ENNReal.ofReal (2 * Real.exp (-17 * thetaLowRateScale m)) *
        (3 : ℝ≥0∞) * (2 * (R + 1) : ℕ) := by
  exact (lowBadWindowBoundedOverlapData hm hk threshold bound event hwidthPos
    hcombinedWidth hthreshold0 hdom htheta event_cover).measure_event_le
      simpleRandomWalk event
      (ENNReal.ofReal (2 * Real.exp (-17 * thetaLowRateScale m)))
      (2 * (R + 1))

end

end Erdos1165.HLOZPositiveInterfacePairWindowObstructionSummation
