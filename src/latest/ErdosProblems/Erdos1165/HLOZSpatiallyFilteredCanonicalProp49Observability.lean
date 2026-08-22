/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors.
-/

import ErdosProblems.Erdos1165.HLOZPrefixedCanonicalSourceProp49Observability
import ErdosProblems.Erdos1165.HLOZSpatiallyFilteredCanonicalSourceProp49

/-!
# Stopped observability for spatially filtered Prop. 4.9 histories

The spatial atom filter is a proposition about the fixed trace index.  It
therefore changes which histories have candidates, but not the physical
narrow cylinders.  This module proves that the resulting some-candidate event
is observable on every fixed old-creation atom.
-/

open MeasureTheory Set

namespace Erdos1165.HLOZSpatiallyFilteredCanonicalProp49Observability

open HLOZFilteredOrientedAllCreationStoppedCandidateFamily
open HLOZGapFixedPair
open HLOZOrientedAllCreationStoppedCandidateFamily
open HLOZPathEvents HLOZPrefixedCanonicalSourceLowRecovery
open HLOZPrefixedCanonicalSourceProp49Observability
open HLOZPrefixedCanonicalSourceProp49Refinement
open HLOZPrefixedProp49CandidateWindowRatio
open HLOZShellZeroExternalWindow HLOZShellZeroReplacementWindows
open HLOZSpatiallyFilteredCanonicalSourceProp49
open HLOZStoppedHistoryCandidateFuture
open LazyDecomposition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

private theorem isMeasurableAtStopping_iUnion_const
    {ι : Sort*} [Countable ι] {n : ℕ} {A : ι → Set StepPath}
    (hA : ∀ i, IsMeasurableAtStopping (fun _ : StepPath ↦ n) (A i)) :
    IsMeasurableAtStopping (fun _ : StepPath ↦ n) (⋃ i, A i) := by
  apply isMeasurableAtStopping_const_of_measurableSet
  apply MeasurableSet.iUnion
  intro i
  have hi := hA i n
  have heq : A i ∩ {ω | (fun _ : StepPath ↦ n) ω = n} = A i := by
    ext omega
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, and_true]
  rw [heq] at hi
  exact hi

/-- One spatially eligible candidate's complete cap-union is observable at
the fixed creation time. -/
theorem sourceProp49CandidateNear_fixedCreation_observable
    {t : DominoTiling} {o : Orientation} {m k n : ℕ}
    (eta : SourceSupportedIndex t o m k) (a : GapScale)
    (candidate : Point) (hcandidate : candidate ∈ eta.1.2) (low : ℕ) :
    IsMeasurableAtStopping (fun _ : StepPath ↦ n)
      { ω | ThresholdCreation (trajectory ω) m k n ∧
        trajectory ω ∈ sourceProp49CandidateNear eta a low candidate } := by
  have heq :
      { ω | ThresholdCreation (trajectory ω) m k n ∧
          trajectory ω ∈ sourceProp49CandidateNear eta a low candidate } =
        ⋃ cap,
          { ω | ThresholdCreation (trajectory ω) m k n ∧
            trajectory ω ∈ sourceProp49ScreenedFiber
              eta a candidate hcandidate low cap } := by
    have hnearEq : sourceProp49CandidateNear eta a low candidate =
        sourceProp49Near eta a candidate hcandidate low := by
      simp only [sourceProp49CandidateNear, hcandidate, dite_true]
    rw [hnearEq, sourceProp49Near]
    ext omega
    constructor
    · rintro ⟨hcreation, hcap⟩
      rcases Set.mem_iUnion.mp hcap with ⟨cap, hcap⟩
      exact Set.mem_iUnion_of_mem cap ⟨hcreation, hcap⟩
    · intro hcap
      rcases Set.mem_iUnion.mp hcap with ⟨cap, hcreation, hcap⟩
      exact ⟨hcreation, Set.mem_iUnion_of_mem cap hcap⟩
  rw [heq]
  apply isMeasurableAtStopping_iUnion_const
  intro cap
  exact sourceProp49ScreenedFiber_fixedCreation_observable
    eta a candidate hcandidate low cap

private theorem creation_inter_someCandidate_eq_iUnion
    {t : DominoTiling} {o : Orientation} {m k n : ℕ}
    (a : GapScale) (low : ℕ) (previous : Set WalkPath)
    (hprevious : MeasurableSet previous)
    (hm : 1 < m) (hk : 0 < k)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)) :
    let family := spatiallyFilteredCandidateFamily (t := t) (o := o) a low
      previous hprevious hm hk hwindow harithmetic hexternalArithmetic
    { ω | ThresholdCreation (trajectory ω) m k n ∧
        trajectory ω ∈ family.someCandidate } =
      ⋃ eta : SourceSupportedIndex t o m k,
        ⋃ _heligible : SourceProp49EligibleInPrevious previous eta,
          ⋃ candidate : Point, ⋃ _hcandidate : candidate ∈ eta.1.2,
            { ω | ThresholdCreation (trajectory ω) m k n ∧
              trajectory ω ∈
                sourceProp49CandidateNear eta a low candidate } := by
  let data := spatiallyFilteredCoordinateData (t := t) (o := o) a low
    previous hprevious hm hk hwindow harithmetic hexternalArithmetic
  let family := data.family
  change { ω | ThresholdCreation (trajectory ω) m k n ∧
      trajectory ω ∈ family.someCandidate } = _
  ext omega
  constructor
  · rintro ⟨hcreation, hsome⟩
    unfold StoppedHistoryCandidateFamily.someCandidate at hsome
    rcases Set.mem_iUnion.mp hsome with ⟨history, hhistory⟩
    rcases Set.mem_iUnion.mp hhistory with ⟨candidate, hcandidate⟩
    rcases Set.mem_iUnion.mp hcandidate with ⟨hcandidate, hpiece, hnear⟩
    cases history with
    | none =>
        simp [family, data, FilteredOrientedAllCreationLowCoordinateData.family,
          filteredHistoryCandidates] at hcandidate
    | some eta =>
        have heligible : SourceProp49EligibleInPrevious previous eta ∧
            candidate ∈ eta.1.2 := by
          change candidate ∈ filteredHistoryCandidates t o m k
            (SourceSupportAt t o m)
            (SourceProp49EligibleInPrevious previous) (some eta) at hcandidate
          exact (mem_filteredHistoryCandidates_some_iff t o m k
            (SourceSupportAt t o m)
            (SourceProp49EligibleInPrevious previous) eta candidate).mp
              hcandidate
        exact Set.mem_iUnion_of_mem eta <|
          Set.mem_iUnion_of_mem heligible.1 <|
            Set.mem_iUnion_of_mem candidate <|
              Set.mem_iUnion_of_mem heligible.2 ⟨hcreation, hnear⟩
  · intro hright
    rcases Set.mem_iUnion.mp hright with ⟨eta, heta⟩
    rcases Set.mem_iUnion.mp heta with ⟨heligible, heta⟩
    rcases Set.mem_iUnion.mp heta with ⟨candidate, heta⟩
    rcases Set.mem_iUnion.mp heta with ⟨hcandidate, hcreation, hnear⟩
    have hatom := sourceProp49CandidateNear_subset_atom
      eta a low candidate hcandidate hnear
    have hpiece : trajectory omega ∈ historyPiece t o m k
        (SourceSupportAt t o m) previous (some eta) :=
      ⟨heligible.atom_subset hatom, hatom⟩
    have hcandidate' : candidate ∈ filteredHistoryCandidates t o m k
        (SourceSupportAt t o m)
        (SourceProp49EligibleInPrevious previous) (some eta) :=
      (mem_filteredHistoryCandidates_some_iff t o m k
        (SourceSupportAt t o m)
        (SourceProp49EligibleInPrevious previous) eta candidate).2
          ⟨heligible, hcandidate⟩
    refine ⟨hcreation, Set.mem_iUnion_of_mem (some eta) ?_⟩
    exact Set.mem_iUnion_of_mem candidate <|
      Set.mem_iUnion_of_mem hcandidate' ⟨hpiece, hnear⟩

/-- The complete spatially filtered candidate union is observable at any
fixed rank-`k` creation clock. -/
theorem spatiallyFilteredCandidateFamily_fixedCreation_observable
    {t : DominoTiling} {o : Orientation} {m k n : ℕ}
    (a : GapScale) (low : ℕ) (previous : Set WalkPath)
    (hprevious : MeasurableSet previous)
    (hm : 1 < m) (hk : 0 < k)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)) :
    let family := spatiallyFilteredCandidateFamily (t := t) (o := o) a low
      previous hprevious hm hk hwindow harithmetic hexternalArithmetic
    IsMeasurableAtStopping (fun _ : StepPath ↦ n)
      { ω | ThresholdCreation (trajectory ω) m k n ∧
        trajectory ω ∈ family.someCandidate } := by
  dsimp only
  rw [creation_inter_someCandidate_eq_iUnion a low previous hprevious hm hk
    hwindow harithmetic hexternalArithmetic]
  apply isMeasurableAtStopping_iUnion_const
  intro eta
  apply isMeasurableAtStopping_iUnion_const
  intro heligible
  apply isMeasurableAtStopping_iUnion_const
  intro candidate
  apply isMeasurableAtStopping_iUnion_const
  intro hcandidate
  exact sourceProp49CandidateNear_fixedCreation_observable eta a candidate
    hcandidate low

end

end Erdos1165.HLOZSpatiallyFilteredCanonicalProp49Observability
