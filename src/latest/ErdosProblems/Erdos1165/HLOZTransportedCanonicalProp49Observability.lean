/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors.
-/

import ErdosProblems.Erdos1165.HLOZSourceTransportFixedCreationObservability
import ErdosProblems.Erdos1165.HLOZThetaOneSourceShift
import ErdosProblems.Erdos1165.HLOZTransportedCanonicalProp49Row

/-!
# Stopped observability of reflected Proposition 4.9 rows

This module specializes the generic filtration-preserving reflection theorem
to the concrete canonical Proposition 4.9 family.  It closes the fixed-clock
observability seam for opposite column rows.  Checker rows are intentionally
excluded because their physical first increment changes the target clock.
-/

open MeasureTheory Set

namespace Erdos1165.HLOZTransportedCanonicalProp49Observability

open HLOZPathEvents
open HLOZNoLazyMeshCandidateCreation
open HLOZPrefixedCanonicalSourceProp49MeshFactor
open HLOZPrefixedCanonicalSourceProp49Observability
open HLOZPrefixedProp49CandidateWindowRatio
open HLOZShellZeroExternalWindow HLOZShellZeroReplacementWindows
open HLOZSourceEndpointTransportTable
open HLOZSourceTransportFixedCreationObservability
open HLOZSourceTransportStoppedCandidateFamily
open HLOZSpatialAdapter
open HLOZStoppedCandidatePreviousRestriction
open HLOZStoppedHistoryCandidateFuture
open HLOZTransportedCanonicalProp49Row
open LazyDecomposition ScreeningInstantiation

noncomputable section

abbrev DominoTiling := Tilings.Tiling

set_option linter.defProp false in
noncomputable def targetAmbientPastData
    (t : DominoTiling) (o : Orientation) (cls : DominantEndpointClass)
    (m k : ℕ) (a : GapScale) (low : ℕ)
    (hm : 1 < m) (hk : 0 < k)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)) :
    CanonicalSourceProp49PastData (TargetTiling t cls)
      (TargetOrientation t o cls) m k a low Set.univ where
  previous_measurable := MeasurableSet.univ
  atom_subset_previous := fun _eta _heligible ↦ subset_univ _
  m_gt_one := hm
  rank_pos := hk
  window := hwindow
  shell_arithmetic := harithmetic
  external_arithmetic := hexternalArithmetic

theorem targetAmbientPastData_candidateFamily
    (t : DominoTiling) (o : Orientation) (cls : DominantEndpointClass)
    (m k : ℕ) (a : GapScale) (low : ℕ)
    (hm : 1 < m) (hk : 0 < k)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)) :
    (targetAmbientPastData t o cls m k a low hm hk hwindow harithmetic
      hexternalArithmetic).candidateFamily =
      targetAmbientFamily t o cls m k a low hm hk hwindow harithmetic
        hexternalArithmetic :=
  rfl

/-- A canonical source-table row is the target candidate event itself. -/
theorem transportedAmbientSomeCandidate_canonical
    (t : DominoTiling) (o : Orientation)
    (m k : ℕ) (a : GapScale) (low : ℕ)
    (hm : 1 < m) (hk : 0 < k)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)) :
    (transportedAmbientFamily t o .canonical m k a low hm hk hwindow
      harithmetic hexternalArithmetic).someCandidate =
      (targetAmbientPastData t o .canonical m k a low hm hk hwindow
        harithmetic hexternalArithmetic).candidateFamily.someCandidate := by
  change
    (stoppedHistoryCandidateFamilySourceTransport t .canonical
      (targetAmbientFamily t o .canonical m k a low hm hk hwindow
        harithmetic hexternalArithmetic)
      (targetAmbientNear_measurable t o .canonical m k a low hm hk hwindow
        harithmetic hexternalArithmetic)).someCandidate = _
  have htransport :=
    StoppedHistoryCandidateFamily.someCandidate_sourceTransport t .canonical
      (targetAmbientFamily t o .canonical m k a low hm hk hwindow harithmetic
        hexternalArithmetic)
      (targetAmbientNear_measurable t o .canonical m k a low hm hk hwindow
        harithmetic hexternalArithmetic)
  rw [htransport, targetAmbientPastData_candidateFamily]
  rfl

/-- Canonical rows inherit the canonical stopped-observability theorem
without any transport argument. -/
theorem transportedAmbientCandidate_fixedCreation_observable_canonical
    (t : DominoTiling) (o : Orientation)
    (m k n : ℕ) (a : GapScale) (low : ℕ)
    (hm : 1 < m) (hk : 0 < k)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)) :
    IsMeasurableAtStopping (fun _ : StepPath ↦ n)
      { ω | ThresholdCreation (trajectory ω) m k n ∧
        trajectory ω ∈
          (transportedAmbientFamily t o .canonical m k a low hm hk hwindow
            harithmetic hexternalArithmetic).someCandidate } := by
  rw [transportedAmbientSomeCandidate_canonical]
  exact candidateFamily_fixedCreation_observable
    (n := n) (targetAmbientPastData t o .canonical m k a low hm hk hwindow
      harithmetic hexternalArithmetic)

/-- The ambient opposite-column some-candidate event is the literal reflected
preimage of the target canonical candidate event. -/
theorem transportedAmbientSomeCandidate_column
    (t : DominoTiling) (ht : t = .evenColumns ∨ t = .oddColumns)
    (o : Orientation) (m k : ℕ) (a : GapScale) (low : ℕ)
    (hm : 1 < m) (hk : 0 < k)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)) :
    (transportedAmbientFamily t o .opposite m k a low hm hk hwindow
      harithmetic hexternalArithmetic).someCandidate =
      HLOZSourceTransportCoordinateMass.sourceTransportPreimage t .opposite
        ((targetAmbientPastData t o .opposite m k a low hm hk hwindow
          harithmetic hexternalArithmetic).candidateFamily.someCandidate) := by
  rcases ht with rfl | rfl
  · change
      (stoppedHistoryCandidateFamilySourceTransport .evenColumns .opposite
        (targetAmbientFamily .evenColumns o .opposite m k a low hm hk hwindow
          harithmetic hexternalArithmetic)
        (targetAmbientNear_measurable .evenColumns o .opposite m k a low hm hk
          hwindow harithmetic hexternalArithmetic)).someCandidate = _
    rw [targetAmbientPastData_candidateFamily]
    exact
      StoppedHistoryCandidateFamily.someCandidate_sourceTransport
        (t := (.evenColumns : DominoTiling)) .opposite
        (targetAmbientFamily .evenColumns o .opposite m k a low hm hk hwindow
          harithmetic hexternalArithmetic)
        (targetAmbientNear_measurable .evenColumns o .opposite m k a low hm hk
          hwindow harithmetic hexternalArithmetic)
  · change
      (stoppedHistoryCandidateFamilySourceTransport .oddColumns .opposite
        (targetAmbientFamily .oddColumns o .opposite m k a low hm hk hwindow
          harithmetic hexternalArithmetic)
        (targetAmbientNear_measurable .oddColumns o .opposite m k a low hm hk
          hwindow harithmetic hexternalArithmetic)).someCandidate = _
    rw [targetAmbientPastData_candidateFamily]
    exact
      StoppedHistoryCandidateFamily.someCandidate_sourceTransport
        (t := (.oddColumns : DominoTiling)) .opposite
        (targetAmbientFamily .oddColumns o .opposite m k a low hm hk hwindow
          harithmetic hexternalArithmetic)
        (targetAmbientNear_measurable .oddColumns o .opposite m k a low hm hk
          hwindow harithmetic hexternalArithmetic)

/-- An opposite-column ambient candidate row is observable on every fixed
rank-`k` creation atom. -/
theorem transportedAmbientCandidate_fixedCreation_observable_column
    (t : DominoTiling) (ht : t = .evenColumns ∨ t = .oddColumns)
    (o : Orientation) (m k n : ℕ) (a : GapScale) (low : ℕ)
    (hm : 1 < m) (hk : 0 < k)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)) :
    IsMeasurableAtStopping (fun _ : StepPath ↦ n)
      { ω | ThresholdCreation (trajectory ω) m k n ∧
        trajectory ω ∈
          (transportedAmbientFamily t o .opposite m k a low hm hk hwindow
            harithmetic hexternalArithmetic).someCandidate } := by
  let data := targetAmbientPastData t o .opposite m k a low hm hk hwindow
    harithmetic hexternalArithmetic
  have htarget := candidateFamily_fixedCreation_observable (n := n) data
  have htarget' : IsMeasurableAtStopping (fun _ : StepPath ↦ n)
      (trajectory ⁻¹' {s : WalkPath | ThresholdCreation s m k n ∧
        s ∈ data.candidateFamily.someCandidate}) := by
    change IsMeasurableAtStopping (fun _ : StepPath ↦ n)
      (trajectory ⁻¹' {s : WalkPath | ThresholdCreation s m k n ∧
        s ∈ data.candidateFamily.someCandidate}) at htarget
    exact htarget
  have hreflected :=
    isMeasurableAtStopping_const_sourceTransportPreimage_column t ht htarget'
  have heq :
      trajectory ⁻¹'
          (HLOZSourceTransportCoordinateMass.sourceTransportPreimage t
            .opposite {s : WalkPath | ThresholdCreation s m k n ∧
              s ∈ data.candidateFamily.someCandidate}) =
        { ω | ThresholdCreation (trajectory ω) m k n ∧
          trajectory ω ∈
            (transportedAmbientFamily t o .opposite m k a low hm hk hwindow
              harithmetic hexternalArithmetic).someCandidate } := by
    ext ω
    rcases ht with rfl | rfl
    · rw [transportedAmbientSomeCandidate_column .evenColumns
          (Or.inl rfl) o m k a low hm hk hwindow harithmetic
          hexternalArithmetic]
      simp only [HLOZSourceTransportCoordinateMass.sourceTransportPreimage,
        HLOZSourceEndpointTransportTable.sourceTransportPath,
        Set.mem_preimage, Set.mem_ofPred_eq]
      rw [HLOZThetaOneSourceShift.thresholdCreation_horizontalReflectPath]
      omega
    · rw [transportedAmbientSomeCandidate_column .oddColumns
          (Or.inr rfl) o m k a low hm hk hwindow harithmetic
          hexternalArithmetic]
      simp only [HLOZSourceTransportCoordinateMass.sourceTransportPreimage,
        HLOZSourceEndpointTransportTable.sourceTransportPath,
        Set.mem_preimage, Set.mem_ofPred_eq]
      rw [HLOZThetaOneSourceShift.thresholdCreation_horizontalReflectPath]
      omega
  rw [← heq]
  exact hreflected

/-- Restricting an ambient row to the all-path past changes neither its
candidate support nor its some-candidate event. -/
theorem candidateFamily_univ_someCandidate
    (t : DominoTiling) (o : Orientation) (cls : DominantEndpointClass)
    (m k : ℕ) (a : GapScale) (low : ℕ)
    (hm : 1 < m) (hk : 0 < k)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)) :
    (candidateFamily t o cls m k a low Set.univ MeasurableSet.univ hm hk
      hwindow harithmetic hexternalArithmetic).someCandidate =
      (transportedAmbientFamily t o cls m k a low hm hk hwindow harithmetic
        hexternalArithmetic).someCandidate := by
  classical
  ext s
  simp only [StoppedHistoryCandidateFamily.someCandidate, candidateFamily,
    restrictToPrevious, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_univ,
    true_and, candidatesInPrevious]
  constructor
  · rintro ⟨h, x, hx, hs⟩
    exact ⟨h, x, by simpa using hx, hs⟩
  · rintro ⟨h, x, hx, hs⟩
    exact ⟨h, x, by simpa using hx, hs⟩

/-- Rank-one opposite-column rows therefore need no consumer-supplied
candidate observability premise. -/
theorem candidateFamily_univ_fixedCreation_observable_column
    (t : DominoTiling) (ht : t = .evenColumns ∨ t = .oddColumns)
    (o : Orientation) (m k n : ℕ) (a : GapScale) (low : ℕ)
    (hm : 1 < m) (hk : 0 < k)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)) :
    IsMeasurableAtStopping (fun _ : StepPath ↦ n)
      { ω | ThresholdCreation (trajectory ω) m k n ∧
        trajectory ω ∈
          (candidateFamily t o .opposite m k a low Set.univ
            MeasurableSet.univ hm hk hwindow harithmetic
              hexternalArithmetic).someCandidate } := by
  rw [candidateFamily_univ_someCandidate]
  exact transportedAmbientCandidate_fixedCreation_observable_column t ht o
    m k n a low hm hk hwindow harithmetic hexternalArithmetic

/-- Rank-one canonical rows likewise have a premise-free stopped-past
observable candidate atom. -/
theorem candidateFamily_univ_fixedCreation_observable_canonical
    (t : DominoTiling) (o : Orientation)
    (m k n : ℕ) (a : GapScale) (low : ℕ)
    (hm : 1 < m) (hk : 0 < k)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)) :
    IsMeasurableAtStopping (fun _ : StepPath ↦ n)
      { ω | ThresholdCreation (trajectory ω) m k n ∧
        trajectory ω ∈
          (candidateFamily t o .canonical m k a low Set.univ
            MeasurableSet.univ hm hk hwindow harithmetic
              hexternalArithmetic).someCandidate } := by
  rw [candidateFamily_univ_someCandidate]
  exact transportedAmbientCandidate_fixedCreation_observable_canonical t o
    m k n a low hm hk hwindow harithmetic hexternalArithmetic

/-- Exact rank-one atom form consumed by the raw mesh-creation adapter. -/
theorem candidateFamily_univ_firstCandidatePastAtom_observable_canonical
    (t : DominoTiling) (o : Orientation)
    (m n : ℕ) (a : GapScale) (low : ℕ)
    (hm : 1 < m)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)) :
    IsMeasurableAtStopping (fun _ : StepPath ↦ n)
      (trajectory ⁻¹' firstCandidatePastAtom
        (candidateFamily t o .canonical m 1 a low Set.univ
          MeasurableSet.univ hm (by omega) hwindow harithmetic
            hexternalArithmetic).someCandidate m n) := by
  change IsMeasurableAtStopping (fun _ : StepPath ↦ n)
    { ω | ThresholdCreation (trajectory ω) m 1 n ∧
      trajectory ω ∈
        (candidateFamily t o .canonical m 1 a low Set.univ
          MeasurableSet.univ hm (by omega) hwindow harithmetic
            hexternalArithmetic).someCandidate }
  exact candidateFamily_univ_fixedCreation_observable_canonical t o m 1 n a low
    hm (by omega) hwindow harithmetic hexternalArithmetic

/-- Opposite-column rank-one atom form consumed by the same adapter. -/
theorem candidateFamily_univ_firstCandidatePastAtom_observable_column
    (t : DominoTiling) (ht : t = .evenColumns ∨ t = .oddColumns)
    (o : Orientation) (m n : ℕ) (a : GapScale) (low : ℕ)
    (hm : 1 < m)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)) :
    IsMeasurableAtStopping (fun _ : StepPath ↦ n)
      (trajectory ⁻¹' firstCandidatePastAtom
        (candidateFamily t o .opposite m 1 a low Set.univ
          MeasurableSet.univ hm (by omega) hwindow harithmetic
            hexternalArithmetic).someCandidate m n) := by
  change IsMeasurableAtStopping (fun _ : StepPath ↦ n)
    { ω | ThresholdCreation (trajectory ω) m 1 n ∧
      trajectory ω ∈
        (candidateFamily t o .opposite m 1 a low Set.univ
          MeasurableSet.univ hm (by omega) hwindow harithmetic
            hexternalArithmetic).someCandidate }
  exact candidateFamily_univ_fixedCreation_observable_column t ht o m 1 n a low
    hm (by omega) hwindow harithmetic hexternalArithmetic

end

end Erdos1165.HLOZTransportedCanonicalProp49Observability
