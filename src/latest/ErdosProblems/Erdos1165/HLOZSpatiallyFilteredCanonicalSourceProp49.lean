/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors.
-/

import ErdosProblems.Erdos1165.HLOZPrefixedCanonicalSourceProp49MeshFactor

/-!
# Spatially filtered canonical Proposition 4.9 histories

A rank-two or rank-three past event fixes a spatial mesh history.  Source-good
atoms in other mesh cells must remain in the ambient stopped partition, but
cannot be assigned candidates for this row.  Thus the required atom-in-past
condition belongs in the per-atom eligibility predicate, not as a global
premise on every source-good atom.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.HLOZSpatiallyFilteredCanonicalSourceProp49

open HLOZFilteredOrientedAllCreationStoppedCandidateFamily
open HLOZMeshCandidateFutureFactor
open HLOZMeshCandidatePolynomialNumerics
open HLOZNoLazyInitialBudgetMixedTransitionFactors
open HLOZOrientedAllCreationStoppedCandidateFamily
open HLOZPathEvents HLOZPrefixedCanonicalSourceAtomRecovery
open HLOZPrefixedCanonicalSourceLowRecovery
open HLOZPrefixedCanonicalSourceProp49Data
open HLOZPrefixedCanonicalSourceProp49Refinement
open HLOZPrefixedProp49CandidateWindowRatio HLOZProposition48Candidates
open HLOZShellZeroExternalWindow HLOZShellZeroReplacementWindows
open HLOZStoppedHistoryCandidateFuture
open LazyDecomposition
open TilingOrientedAllCreationStoppedCoordinate

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- Source-good eligibility localized to one actual spatial past. -/
structure SourceProp49EligibleInPrevious
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (previous : Set WalkPath) (eta : SourceSupportedIndex t o m k) : Prop where
  source : SourceProp49EligibleHistory eta
  atom_subset :
    orientedAllCreationSupportTraceAtom t o m k (SourceSupportAt t o m)
      eta.1.1 eta.1.2 ⊆ previous

set_option linter.unusedVariables false in
private theorem zero_not_mem_sourceWindow
    {m : ℕ} (hm : 1 < m) :
    0 ∉ shellZeroSourceTotalWindow m (shellWidth48 m) := by
  simp only [mem_shellZeroSourceTotalWindow]
  omega

/-- Prefix-correct coordinate data with the spatial past condition inside
the good-history filter. -/
noncomputable def spatiallyFilteredCoordinateData
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (a : GapScale) (low : ℕ) (previous : Set WalkPath)
    (hprevious : MeasurableSet previous)
    (hm : 1 < m) (hk : 0 < k)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)) :
    FilteredOrientedAllCreationLowCoordinateData t o m k
      (initialBudget48 m) previous
      (prop49CandidateRatioEnvelope prop49WindowRatioConstant m a) where
  supportAt := SourceSupportAt t o m
  supportData := SourceSupportData t o m k
  previous_measurable := hprevious
  ratio_ne_top := prop49CandidateRatioEnvelope_ne_top _ _ _
  eligible := SourceProp49EligibleInPrevious previous
  eligible_card := fun _ heligible ↦ heligible.source.card_le
  near := fun eta candidate ↦ sourceProp49CandidateNear eta a low candidate
  near_measurable := fun eta candidate ↦
    measurableSet_sourceProp49CandidateNear eta a low candidate
  refinement := by
    intro eta candidate heligible hcandidate
    let cert := sourceRecoveryCertificate eta candidate hcandidate low
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)
      (prop49NarrowTotalWindow m a) hm hk
      (zero_not_mem_sourceWindow hm)
    apply cert.refinement
    · intro s hs
      exact ⟨heligible.atom_subset hs, hs⟩
    · intro cap
      exact heligible.source.good.acceptedRatioData a candidate hcandidate
        low hm hk hwindow harithmetic hexternalArithmetic cap
    · exact monotone_sourceProp49ScreenedFiber eta a candidate hcandidate low
    · intro s hs
      have hnear : s ∈ sourceProp49Near eta a candidate hcandidate low := by
        simpa only [sourceProp49CandidateNear, hcandidate, dite_true] using
          hs.2.2
      exact hnear

/-- The stopped family partitions the whole past.  Spatially irrelevant
source atoms are the required empty-candidate histories. -/
noncomputable def spatiallyFilteredCandidateFamily
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (a : GapScale) (low : ℕ) (previous : Set WalkPath)
    (hprevious : MeasurableSet previous)
    (hm : 1 < m) (hk : 0 < k)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)) :
    StoppedHistoryCandidateFamily
      (History t o m k (SourceSupportAt t o m)) Point previous
      (initialBudget48 m)
      (prop49CandidateRatioEnvelope prop49WindowRatioConstant m a) :=
  (spatiallyFilteredCoordinateData (t := t) (o := o) a low previous
    hprevious hm hk hwindow
    harithmetic hexternalArithmetic).family

/-- The complete spatially filtered candidate union is ordinarily
measurable. -/
theorem measurableSet_spatiallyFilteredCandidateFamily
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (a : GapScale) (low : ℕ) (previous : Set WalkPath)
    (hprevious : MeasurableSet previous)
    (hm : 1 < m) (hk : 0 < k)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)) :
    MeasurableSet
      (spatiallyFilteredCandidateFamily (t := t) (o := o) a low previous
        hprevious hm hk hwindow harithmetic
        hexternalArithmetic).someCandidate := by
  let data := spatiallyFilteredCoordinateData (t := t) (o := o) a low
    previous hprevious hm hk hwindow harithmetic hexternalArithmetic
  unfold StoppedHistoryCandidateFamily.someCandidate
  apply MeasurableSet.iUnion
  intro history
  apply MeasurableSet.iUnion
  intro candidate
  apply MeasurableSet.iUnion
  intro hcandidate
  apply (data.family.piece_measurable history).inter
  cases history with
  | none => exact MeasurableSet.empty
  | some eta => exact data.near_measurable eta candidate

/-- Literal containment in the spatially eligible candidate union. -/
theorem next_subset_spatiallyFilteredCandidate
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (a : GapScale) (low : ℕ) (previous next : Set WalkPath)
    (hprevious : MeasurableSet previous)
    (hm : 1 < m) (hk : 0 < k)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    (hnext : ∀ s ∈ next,
      ∃ (eta : SourceSupportedIndex t o m k) (candidate : Point),
        s ∈ historyPiece t o m k (SourceSupportAt t o m) previous
          (some eta) ∧
        SourceProp49EligibleInPrevious previous eta ∧
        candidate ∈ eta.1.2 ∧
        s ∈ sourceProp49CandidateNear eta a low candidate) :
    next ⊆ (spatiallyFilteredCandidateFamily (t := t) (o := o) a low
      previous hprevious hm hk hwindow harithmetic
      hexternalArithmetic).someCandidate := by
  exact (spatiallyFilteredCoordinateData (t := t) (o := o) a low previous
    hprevious hm hk hwindow harithmetic
    hexternalArithmetic).next_subset_someCandidate hnext

/-- Final row-local mesh datum once its fixed-clock future decomposition is
supplied.  The candidate ratio remains the literal Proposition 4.9 envelope. -/
noncomputable def spatiallyFilteredMeshLowCoordinateData
    {Index : Type} [Countable Index]
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (a : GapScale) (low : ℕ) (previous next : Set WalkPath)
    (hprevious : MeasurableSet previous)
    (hm : 1 < m) (hk : 0 < k)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    (creation : CountableMeshCreationData Index
      (spatiallyFilteredCandidateFamily (t := t) (o := o) a low previous
        hprevious hm hk hwindow harithmetic hexternalArithmetic).someCandidate
      next m k a) :
    FirstStripMeshLowCoordinateData prop49WindowRatioConstant m k a
      previous next where
  History := History t o m k (SourceSupportAt t o m)
  Candidate := Point
  Index := Index
  candidateRatio := prop49CandidateRatioEnvelope
    prop49WindowRatioConstant m a
  candidate := spatiallyFilteredCandidateFamily (t := t) (o := o) a low
    previous hprevious hm hk hwindow harithmetic hexternalArithmetic
  creation := creation
  ratio_le := le_rfl

end

end Erdos1165.HLOZSpatiallyFilteredCanonicalSourceProp49
