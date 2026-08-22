/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors.
-/

import ErdosProblems.Erdos1165.HLOZCountableMeshCreationRestriction
import ErdosProblems.Erdos1165.HLOZCheckerPrefixedStoppedCandidateFamily
import ErdosProblems.Erdos1165.HLOZPrefixedCanonicalSourceProp49Refinement
import ErdosProblems.Erdos1165.HLOZSourceTransportStoppedCandidateFamily
import ErdosProblems.Erdos1165.HLOZStoppedCandidatePreviousRestriction

/-!
# One transported canonical Proposition 4.9 source row

Canonical and opposite dominant endpoints are handled by the same canonical
conditional product after applying the finite source transport table.  This
module performs that literal complete-path pullback, then restricts the
ambient stopped partition to the actual spatial past.  It does not identify
an original retained trace with a checker-recentered or reflected trace.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.HLOZTransportedCanonicalProp49Row

open HLOZCountableMeshCreationRestriction
open HLOZCheckerPrefixedStoppedCandidateFamily
open HLOZMeshCandidateFutureFactor
open HLOZMeshCandidatePolynomialNumerics
open HLOZNoLazyInitialBudgetMixedTransitionFactors
open HLOZPathEvents HLOZPrefixedCanonicalSourceLowRecovery
open HLOZPrefixedCanonicalSourceProp49Data
open HLOZPrefixedCanonicalSourceProp49Refinement
open HLOZPrefixedProp49CandidateWindowRatio HLOZProposition48Candidates
open HLOZShellZeroExternalWindow HLOZShellZeroReplacementWindows
open HLOZSourceEndpointTransportTable
open HLOZSourceTransportStoppedCandidateFamily
open HLOZStoppedCandidatePreviousRestriction
open HLOZStoppedHistoryCandidateFuture
open LazyDecomposition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

abbrev TargetTiling (t : DominoTiling) (cls : DominantEndpointClass) :=
  sourceTransportTargetTiling t cls

abbrev TargetOrientation (t : DominoTiling) (o : Orientation)
    (cls : DominantEndpointClass) :=
  sourceTransportTargetOrientation t o cls

abbrev TargetHistory (t : DominoTiling) (o : Orientation)
    (cls : DominantEndpointClass) (m k : ℕ) :=
  HLOZOrientedAllCreationStoppedCandidateFamily.History
    (TargetTiling t cls) (TargetOrientation t o cls) m k
    (SourceSupportAt (TargetTiling t cls) (TargetOrientation t o cls) m)

/-- Checker opposite rows retain the deleted physical first direction.
Canonical and reflected-column rows need no additional history coordinate. -/
abbrev TransportedHistory (t : DominoTiling) (o : Orientation)
    (cls : DominantEndpointClass) (m k : ℕ) :=
  match cls, t with
  | .opposite, .checker _ => CheckerPrefixedHistory (TargetHistory t o cls m k)
  | _, _ => TargetHistory t o cls m k

noncomputable instance transportedHistory_countable
    (t : DominoTiling) (o : Orientation)
    (cls : DominantEndpointClass) (m k : ℕ) :
    Countable (TransportedHistory t o cls m k) := by
  cases cls <;> cases t <;> simp only [TransportedHistory] <;> infer_instance

/-- The canonical conditional family on the target source, before restricting
to a spatial past on the original path. -/
noncomputable def targetAmbientFamily
    (t : DominoTiling) (o : Orientation) (cls : DominantEndpointClass)
    (m k : ℕ) (a : GapScale) (low : ℕ)
    (hm : 1 < m) (hk : 0 < k)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)) :
    StoppedHistoryCandidateFamily (TargetHistory t o cls m k) Point Set.univ
      (initialBudget48 m)
      (prop49CandidateRatioEnvelope prop49WindowRatioConstant m a) :=
  sourceProp49StoppedHistoryCandidateFamily a low Set.univ MeasurableSet.univ
    (fun _ _ ↦ subset_univ _) hm hk hwindow harithmetic hexternalArithmetic

theorem targetAmbientNear_measurable
    (t : DominoTiling) (o : Orientation) (cls : DominantEndpointClass)
    (m k : ℕ) (a : GapScale) (low : ℕ)
    (hm : 1 < m) (hk : 0 < k)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    (h : TargetHistory t o cls m k) (x : Point) :
    MeasurableSet ((targetAmbientFamily t o cls m k a low hm hk hwindow
      harithmetic hexternalArithmetic).near h x) := by
  cases h with
  | none => exact MeasurableSet.empty
  | some eta =>
      exact measurableSet_sourceProp49CandidateNear eta a low x

/-- Exact complete-path pullback of the canonical target row. -/
noncomputable def transportedAmbientFamily
    (t : DominoTiling) (o : Orientation) (cls : DominantEndpointClass)
    (m k : ℕ) (a : GapScale) (low : ℕ)
    (hm : 1 < m) (hk : 0 < k)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)) :
    StoppedHistoryCandidateFamily (TransportedHistory t o cls m k) Point Set.univ
      (initialBudget48 m)
      (prop49CandidateRatioEnvelope prop49WindowRatioConstant m a) := by
  cases cls with
  | canonical =>
      simpa only [TransportedHistory,
          HLOZSourceTransportCoordinateMass.sourceTransportPreimage,
          preimage_univ] using
        stoppedHistoryCandidateFamilySourceTransport t .canonical
          (targetAmbientFamily t o .canonical m k a low hm hk hwindow harithmetic
            hexternalArithmetic)
          (targetAmbientNear_measurable t o .canonical m k a low hm hk hwindow
            harithmetic hexternalArithmetic)
  | opposite =>
      cases t with
      | checker d =>
          exact checkerPrefixedFamily
            (targetAmbientFamily (.checker d) o .opposite m k a low hm hk hwindow
              harithmetic hexternalArithmetic)
            (targetAmbientNear_measurable (.checker d) o .opposite m k a low hm hk
              hwindow harithmetic hexternalArithmetic)
      | evenColumns =>
          simpa only [TransportedHistory,
              HLOZSourceTransportCoordinateMass.sourceTransportPreimage,
              preimage_univ] using
            stoppedHistoryCandidateFamilySourceTransport .evenColumns .opposite
              (targetAmbientFamily .evenColumns o .opposite m k a low hm hk hwindow
                harithmetic hexternalArithmetic)
              (targetAmbientNear_measurable .evenColumns o .opposite m k a low hm hk
                hwindow harithmetic hexternalArithmetic)
      | oddColumns =>
          simpa only [TransportedHistory,
              HLOZSourceTransportCoordinateMass.sourceTransportPreimage,
              preimage_univ] using
            stoppedHistoryCandidateFamilySourceTransport .oddColumns .opposite
              (targetAmbientFamily .oddColumns o .opposite m k a low hm hk hwindow
                harithmetic hexternalArithmetic)
              (targetAmbientNear_measurable .oddColumns o .opposite m k a low hm hk
                hwindow harithmetic hexternalArithmetic)

/-- Every near event of the correctly normalized ambient row is measurable. -/
theorem transportedAmbientNear_measurable
    (t : DominoTiling) (o : Orientation) (cls : DominantEndpointClass)
    (m k : ℕ) (a : GapScale) (low : ℕ)
    (hm : 1 < m) (hk : 0 < k)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    (h : TransportedHistory t o cls m k) (x : Point) :
    MeasurableSet ((transportedAmbientFamily t o cls m k a low hm hk hwindow
      harithmetic hexternalArithmetic).near h x) := by
  cases cls with
  | canonical =>
      change MeasurableSet
        (HLOZSourceTransportCoordinateMass.sourceTransportPreimage t .canonical
          ((targetAmbientFamily t o .canonical m k a low hm hk hwindow
            harithmetic hexternalArithmetic).near h x))
      exact (targetAmbientNear_measurable t o .canonical m k a low hm hk hwindow
        harithmetic hexternalArithmetic h x).preimage
          (measurable_sourceTransportPath t .canonical)
  | opposite =>
      cases t with
      | checker d =>
          cases h with
          | none => exact MeasurableSet.empty
          | some dh =>
              exact
                HLOZCheckerPrefixedCylinderTransport.measurableSet_checkerPrefixedPreimage
                  (targetAmbientNear_measurable (.checker d) o .opposite m k a low
                    hm hk hwindow harithmetic hexternalArithmetic dh.2 x) dh.1
      | evenColumns =>
          change MeasurableSet
            (HLOZSourceTransportCoordinateMass.sourceTransportPreimage
              .evenColumns .opposite
              ((targetAmbientFamily .evenColumns o .opposite m k a low hm hk
                hwindow harithmetic hexternalArithmetic).near h x))
          exact (targetAmbientNear_measurable .evenColumns o .opposite m k a low
            hm hk hwindow harithmetic hexternalArithmetic h x).preimage
              (measurable_sourceTransportPath .evenColumns .opposite)
      | oddColumns =>
          change MeasurableSet
            (HLOZSourceTransportCoordinateMass.sourceTransportPreimage
              .oddColumns .opposite
              ((targetAmbientFamily .oddColumns o .opposite m k a low hm hk
                hwindow harithmetic hexternalArithmetic).near h x))
          exact (targetAmbientNear_measurable .oddColumns o .opposite m k a low
            hm hk hwindow harithmetic hexternalArithmetic h x).preimage
              (measurable_sourceTransportPath .oddColumns .opposite)

/-- One source row on the actual original-path past.  Histories whose full
transported atom is not absorbed by `previous` remain as empty-candidate
pieces, so the pieces still partition all of `previous`. -/
noncomputable def candidateFamily
    (t : DominoTiling) (o : Orientation) (cls : DominantEndpointClass)
    (m k : ℕ) (a : GapScale) (low : ℕ)
    (previous : Set WalkPath) (hprevious : MeasurableSet previous)
    (hm : 1 < m) (hk : 0 < k)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)) :
    StoppedHistoryCandidateFamily (TransportedHistory t o cls m k) Point previous
      (initialBudget48 m)
      (prop49CandidateRatioEnvelope prop49WindowRatioConstant m a) :=
  restrictToPrevious
    (transportedAmbientFamily t o cls m k a low hm hk hwindow harithmetic
      hexternalArithmetic) previous hprevious

/-- Measurability of the complete candidate union in one transported row. -/
theorem measurableSet_candidateFamily
    (t : DominoTiling) (o : Orientation) (cls : DominantEndpointClass)
    (m k : ℕ) (a : GapScale) (low : ℕ)
    (previous : Set WalkPath) (hprevious : MeasurableSet previous)
    (hm : 1 < m) (hk : 0 < k)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)) :
    MeasurableSet ((candidateFamily t o cls m k a low previous hprevious hm hk
      hwindow harithmetic hexternalArithmetic).someCandidate) := by
  unfold StoppedHistoryCandidateFamily.someCandidate
  apply MeasurableSet.iUnion
  intro h
  apply MeasurableSet.iUnion
  intro x
  apply MeasurableSet.iUnion
  intro _hx
  apply (candidateFamily t o cls m k a low previous hprevious hm hk hwindow
    harithmetic hexternalArithmetic).piece_measurable h |>.inter
  exact transportedAmbientNear_measurable t o cls m k a low hm hk hwindow
    harithmetic hexternalArithmetic h x

/-- A literal transported target witness enters the original-path row.  This
is the exact deterministic interface needed by an all-source cover theorem. -/
theorem mem_candidateFamily_someCandidate
    (t : DominoTiling) (o : Orientation) (cls : DominantEndpointClass)
    (m k : ℕ) (a : GapScale) (low : ℕ)
    (previous : Set WalkPath) (hprevious : MeasurableSet previous)
    (hm : 1 < m) (hk : 0 < k)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    (h : TransportedHistory t o cls m k) (x : Point)
    (hpiece : (transportedAmbientFamily t o cls m k a low hm hk hwindow
      harithmetic hexternalArithmetic).piece h ⊆ previous)
    {s : WalkPath}
    (hsPiece : s ∈ (transportedAmbientFamily t o cls m k a low hm hk hwindow
      harithmetic hexternalArithmetic).piece h)
    (hx : x ∈ (transportedAmbientFamily t o cls m k a low hm hk hwindow
      harithmetic hexternalArithmetic).candidates h)
    (hsNear : s ∈ (transportedAmbientFamily t o cls m k a low hm hk hwindow
      harithmetic hexternalArithmetic).near h x) :
    s ∈ (candidateFamily t o cls m k a low previous hprevious hm hk hwindow
      harithmetic hexternalArithmetic).someCandidate :=
  StoppedHistoryCandidateFamily.mem_someCandidate_restrictToPrevious
    (transportedAmbientFamily t o cls m k a low hm hk hwindow harithmetic
      hexternalArithmetic) previous hprevious h x hpiece hsPiece hx hsNear

/-- Intersect any raw fixed-clock mesh decomposition with this transported
row and obtain the exact first-strip low datum. -/
noncomputable def meshLowCoordinateDataOfRawCreation
    {Index : Type} [Countable Index]
    {rawPast rawNext : Set WalkPath}
    (t : DominoTiling) (o : Orientation) (cls : DominantEndpointClass)
    (m k : ℕ) (a : GapScale) (low : ℕ)
    (previous : Set WalkPath) (hprevious : MeasurableSet previous)
    (hm : 1 < m) (hk : 0 < k)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    (raw : CountableMeshCreationData Index rawPast rawNext m k a)
    (hpast : ∀ i, IsMeasurableAtStopping
      (fun _ : StepPath ↦ raw.oldCreation i)
      (trajectory ⁻¹' (raw.pastPiece i ∩
        (candidateFamily t o cls m k a low previous hprevious hm hk hwindow
          harithmetic hexternalArithmetic).someCandidate))) :
    FirstStripMeshLowCoordinateData prop49WindowRatioConstant m k a previous
      (rawNext ∩ (candidateFamily t o cls m k a low previous hprevious hm hk
        hwindow harithmetic hexternalArithmetic).someCandidate) where
  History := TransportedHistory t o cls m k
  Candidate := Point
  Index := Index
  candidateRatio := prop49CandidateRatioEnvelope
    prop49WindowRatioConstant m a
  candidate := candidateFamily t o cls m k a low previous hprevious hm hk
    hwindow harithmetic hexternalArithmetic
  creation := HLOZCountableMeshCreationRestriction.CountableMeshCreationData.inter
    raw (measurableSet_candidateFamily t o cls m k a low previous hprevious
      hm hk hwindow harithmetic hexternalArithmetic) hpast
  ratio_le := le_rfl

end

end Erdos1165.HLOZTransportedCanonicalProp49Row
