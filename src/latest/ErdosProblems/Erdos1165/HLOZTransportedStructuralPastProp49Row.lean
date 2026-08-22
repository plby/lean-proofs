/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZSourceStructuralPastProp49Family
import ErdosProblems.Erdos1165.HLOZStructuralPastTransport
import ErdosProblems.Erdos1165.HLOZTransportedCanonicalProp49Row

/-!
# Transported Proposition 4.9 rows on structural pasts

Canonical rows and opposite column rows transport the already-conditioned
source family.  Their previous event is exactly the original structural
past, rather than a post-hoc whole-atom restriction.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.HLOZTransportedStructuralPastProp49Row

open HLOZMeshCandidatePolynomialNumerics
open HLOZPathEvents
open HLOZGapRandomClockScreen
open HLOZPrefixedCanonicalSourceLowRecovery
open HLOZPrefixedProp49CandidateWindowRatio
open HLOZProposition48Candidates
open HLOZShellZeroExternalWindow HLOZShellZeroReplacementWindows
open HLOZSourceDistinguishedEventProp49Family
open HLOZSourceEndpointTransportTable
open HLOZSourceStructuralPastInvariant
open HLOZSourceStructuralPastProp49Family
open HLOZSourceTransportCoordinateMass
open HLOZSourceTransportStoppedCandidateFamily
open HLOZStoppedHistoryCandidateFuture
open HLOZStructuralPastTransport
open HLOZThetaOneSourceShift
open HLOZTransportedCanonicalProp49Row
open LazyDecomposition

noncomputable section

abbrev DominoTiling := Tilings.Tiling
abbrev GapTriple := HLOZFilteredTransitionAssembly.GapTriple

theorem firstStructuralPastTargetFamily_near_measurable
    (t : DominoTiling) (o : Orientation) (m : ℕ)
    (gaps : GapTriple) (a : GapScale) (low : ℕ)
    (hm : 1 < m)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)) :
    ∀ h candidate, MeasurableSet
      ((firstStructuralPastTargetFamily t o m gaps a low hm hwindow harithmetic
        hexternalArithmetic).near h candidate) :=
  sourceEventTargetFamily_near_measurable a low
    (firstStructuralPast t m gaps) (measurableSet_firstStructuralPast t m gaps)
    (fun eta ↦ firstStructuralPast_distinguishedInvariant eta hm gaps)
    (firstStructuralPast_prefixInvariant t m gaps) hm (by omega) hwindow
      harithmetic hexternalArithmetic

theorem secondStructuralPastTargetFamily_near_measurable
    (t : DominoTiling) (o : Orientation) (m : ℕ)
    (gaps : GapTriple) (a : GapScale) (low : ℕ)
    (hm : 1 < m)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)) :
    ∀ h candidate, MeasurableSet
      ((secondStructuralPastTargetFamily t o m gaps a low hm hwindow harithmetic
        hexternalArithmetic).near h candidate) :=
  sourceEventTargetFamily_near_measurable a low
    (secondStructuralPast t m gaps)
    (measurableSet_secondStructuralPast t m gaps)
    (fun eta ↦ secondStructuralPast_distinguishedInvariant eta hm gaps)
    (secondStructuralPast_prefixInvariant t m gaps) hm (by omega) hwindow
      harithmetic hexternalArithmetic

noncomputable def firstStructuralTransportedFamily
    (t : DominoTiling) (o : Orientation) (cls : DominantEndpointClass)
    (m : ℕ) (gaps : GapTriple) (a : GapScale) (low : ℕ)
    (hm : 1 < m)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)) :
    StoppedHistoryCandidateFamily (TargetHistory t o cls m 2) Point
      (sourceTransportPreimage t cls
        (firstStructuralPast (TargetTiling t cls) m gaps))
      (initialBudget48 m)
      (prop49CandidateRatioEnvelope prop49WindowRatioConstant m a) :=
  stoppedHistoryCandidateFamilySourceTransport t cls
    (firstStructuralPastTargetFamily (TargetTiling t cls)
      (TargetOrientation t o cls) m gaps a low hm hwindow harithmetic
        hexternalArithmetic)
    (firstStructuralPastTargetFamily_near_measurable (TargetTiling t cls)
      (TargetOrientation t o cls) m gaps a low hm hwindow harithmetic
        hexternalArithmetic)

noncomputable def secondStructuralTransportedFamily
    (t : DominoTiling) (o : Orientation) (cls : DominantEndpointClass)
    (m : ℕ) (gaps : GapTriple) (a : GapScale) (low : ℕ)
    (hm : 1 < m)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)) :
    StoppedHistoryCandidateFamily (TargetHistory t o cls m 3) Point
      (sourceTransportPreimage t cls
        (secondStructuralPast (TargetTiling t cls) m gaps))
      (initialBudget48 m)
      (prop49CandidateRatioEnvelope prop49WindowRatioConstant m a) :=
  stoppedHistoryCandidateFamilySourceTransport t cls
    (secondStructuralPastTargetFamily (TargetTiling t cls)
      (TargetOrientation t o cls) m gaps a low hm hwindow harithmetic
        hexternalArithmetic)
    (secondStructuralPastTargetFamily_near_measurable (TargetTiling t cls)
      (TargetOrientation t o cls) m gaps a low hm hwindow harithmetic
        hexternalArithmetic)

theorem firstStructuralTransportedFamily_near_measurable
    (t : DominoTiling) (o : Orientation) (cls : DominantEndpointClass)
    (m : ℕ) (gaps : GapTriple) (a : GapScale) (low : ℕ) (hm : 1 < m)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)) :
    ∀ h candidate, MeasurableSet
      ((firstStructuralTransportedFamily t o cls m gaps a low hm hwindow
        harithmetic hexternalArithmetic).near h candidate) := by
  intro h candidate
  change MeasurableSet (sourceTransportPreimage t cls
    ((firstStructuralPastTargetFamily (TargetTiling t cls)
      (TargetOrientation t o cls) m gaps a low hm hwindow harithmetic
        hexternalArithmetic).near h candidate))
  exact (firstStructuralPastTargetFamily_near_measurable (TargetTiling t cls)
    (TargetOrientation t o cls) m gaps a low hm hwindow harithmetic
      hexternalArithmetic h candidate).preimage
        (measurable_sourceTransportPath t cls)

theorem secondStructuralTransportedFamily_near_measurable
    (t : DominoTiling) (o : Orientation) (cls : DominantEndpointClass)
    (m : ℕ) (gaps : GapTriple) (a : GapScale) (low : ℕ) (hm : 1 < m)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)) :
    ∀ h candidate, MeasurableSet
      ((secondStructuralTransportedFamily t o cls m gaps a low hm hwindow
        harithmetic hexternalArithmetic).near h candidate) := by
  intro h candidate
  change MeasurableSet (sourceTransportPreimage t cls
    ((secondStructuralPastTargetFamily (TargetTiling t cls)
      (TargetOrientation t o cls) m gaps a low hm hwindow harithmetic
        hexternalArithmetic).near h candidate))
  exact (secondStructuralPastTargetFamily_near_measurable (TargetTiling t cls)
    (TargetOrientation t o cls) m gaps a low hm hwindow harithmetic
      hexternalArithmetic h candidate).preimage
        (measurable_sourceTransportPath t cls)

theorem firstStructuralPreimage_canonical
    (t : DominoTiling) (m : ℕ) (gaps : GapTriple) :
    sourceTransportPreimage t .canonical
        (firstStructuralPast (TargetTiling t .canonical) m gaps) =
      firstStructuralPast t m gaps := by
  rfl

theorem secondStructuralPreimage_canonical
    (t : DominoTiling) (m : ℕ) (gaps : GapTriple) :
    sourceTransportPreimage t .canonical
        (secondStructuralPast (TargetTiling t .canonical) m gaps) =
      secondStructuralPast t m gaps := by
  rfl

theorem firstStructuralPreimage_opposite_column
    (t : DominoTiling) (ht : IsColumnTiling t)
    (m : ℕ) (hm : 0 < m) (gaps : GapTriple) :
    sourceTransportPreimage t .opposite
        (firstStructuralPast (TargetTiling t .opposite) m gaps) =
      firstStructuralPast t m gaps := by
  ext s
  cases t with
  | checker d => simp [IsColumnTiling] at ht
  | evenColumns =>
      change horizontalReflectPath s ∈
          firstStructuralPast .oddColumns m gaps ↔
        s ∈ firstStructuralPast .evenColumns m gaps
      exact firstStructuralPast_horizontalReflectPath (t := .evenColumns)
        (by simp [IsColumnTiling]) s m hm gaps
  | oddColumns =>
      change horizontalReflectPath s ∈
          firstStructuralPast .evenColumns m gaps ↔
        s ∈ firstStructuralPast .oddColumns m gaps
      exact firstStructuralPast_horizontalReflectPath (t := .oddColumns)
        (by simp [IsColumnTiling]) s m hm gaps

theorem secondStructuralPreimage_opposite_column
    (t : DominoTiling) (ht : IsColumnTiling t)
    (m : ℕ) (hm : 0 < m) (gaps : GapTriple) :
    sourceTransportPreimage t .opposite
        (secondStructuralPast (TargetTiling t .opposite) m gaps) =
      secondStructuralPast t m gaps := by
  ext s
  cases t with
  | checker d => simp [IsColumnTiling] at ht
  | evenColumns =>
      change horizontalReflectPath s ∈
          secondStructuralPast .oddColumns m gaps ↔
        s ∈ secondStructuralPast .evenColumns m gaps
      exact secondStructuralPast_horizontalReflectPath (t := .evenColumns)
        (by simp [IsColumnTiling]) s m hm gaps
  | oddColumns =>
      change horizontalReflectPath s ∈
          secondStructuralPast .evenColumns m gaps ↔
        s ∈ secondStructuralPast .oddColumns m gaps
      exact secondStructuralPast_horizontalReflectPath (t := .oddColumns)
        (by simp [IsColumnTiling]) s m hm gaps

/-- A canonical structural family, now typed over the original rank-two
past. -/
noncomputable def firstCanonicalStructuralFamily
    (t : DominoTiling) (o : Orientation) (m : ℕ)
    (gaps : GapTriple) (a : GapScale) (low : ℕ) (hm : 1 < m)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)) :
    StoppedHistoryCandidateFamily (TargetHistory t o .canonical m 2) Point
      (firstStructuralPast t m gaps) (initialBudget48 m)
      (prop49CandidateRatioEnvelope prop49WindowRatioConstant m a) := by
  simpa only [firstStructuralPreimage_canonical] using
    firstStructuralTransportedFamily t o .canonical m gaps a low hm hwindow
      harithmetic hexternalArithmetic

/-- An opposite-column structural family, typed over the original rank-two
past. -/
noncomputable def firstOppositeColumnStructuralFamily
    (t : DominoTiling) (ht : IsColumnTiling t) (o : Orientation) (m : ℕ)
    (gaps : GapTriple) (a : GapScale) (low : ℕ) (hm : 1 < m)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)) :
    StoppedHistoryCandidateFamily (TargetHistory t o .opposite m 2) Point
      (firstStructuralPast t m gaps) (initialBudget48 m)
      (prop49CandidateRatioEnvelope prop49WindowRatioConstant m a) := by
  simpa only [firstStructuralPreimage_opposite_column t ht m (by omega) gaps]
    using firstStructuralTransportedFamily t o .opposite m gaps a low hm hwindow
      harithmetic hexternalArithmetic

noncomputable def secondCanonicalStructuralFamily
    (t : DominoTiling) (o : Orientation) (m : ℕ)
    (gaps : GapTriple) (a : GapScale) (low : ℕ) (hm : 1 < m)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)) :
    StoppedHistoryCandidateFamily (TargetHistory t o .canonical m 3) Point
      (secondStructuralPast t m gaps) (initialBudget48 m)
      (prop49CandidateRatioEnvelope prop49WindowRatioConstant m a) := by
  simpa only [secondStructuralPreimage_canonical] using
    secondStructuralTransportedFamily t o .canonical m gaps a low hm hwindow
      harithmetic hexternalArithmetic

noncomputable def secondOppositeColumnStructuralFamily
    (t : DominoTiling) (ht : IsColumnTiling t) (o : Orientation) (m : ℕ)
    (gaps : GapTriple) (a : GapScale) (low : ℕ) (hm : 1 < m)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)) :
    StoppedHistoryCandidateFamily (TargetHistory t o .opposite m 3) Point
      (secondStructuralPast t m gaps) (initialBudget48 m)
      (prop49CandidateRatioEnvelope prop49WindowRatioConstant m a) := by
  simpa only [secondStructuralPreimage_opposite_column t ht m (by omega) gaps]
    using secondStructuralTransportedFamily t o .opposite m gaps a low hm hwindow
      harithmetic hexternalArithmetic

theorem firstStructuralTransportedFamily_someCandidate_subset_ambient
    (t : DominoTiling) (o : Orientation) (cls : DominantEndpointClass)
    (m : ℕ) (gaps : GapTriple) (a : GapScale) (low : ℕ) (hm : 1 < m)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)) :
    (firstStructuralTransportedFamily t o cls m gaps a low hm hwindow
        harithmetic hexternalArithmetic).someCandidate ⊆
      (stoppedHistoryCandidateFamilySourceTransport t cls
        (targetAmbientFamily t o cls m 2 a low hm (by omega) hwindow
          harithmetic hexternalArithmetic)
        (targetAmbientNear_measurable t o cls m 2 a low hm (by omega)
          hwindow harithmetic hexternalArithmetic)).someCandidate := by
  intro s hs
  unfold firstStructuralTransportedFamily at hs
  rw [StoppedHistoryCandidateFamily.someCandidate_sourceTransport] at hs ⊢
  exact (sourceEventTargetFamily_someCandidate_subset_unrestricted_inter_event
    a low (firstStructuralPast (TargetTiling t cls) m gaps)
    (measurableSet_firstStructuralPast (TargetTiling t cls) m gaps)
    (fun eta ↦ firstStructuralPast_distinguishedInvariant eta hm gaps)
    (firstStructuralPast_prefixInvariant (TargetTiling t cls) m gaps)
    hm (by omega) hwindow harithmetic hexternalArithmetic hs).1

theorem secondStructuralTransportedFamily_someCandidate_subset_ambient
    (t : DominoTiling) (o : Orientation) (cls : DominantEndpointClass)
    (m : ℕ) (gaps : GapTriple) (a : GapScale) (low : ℕ) (hm : 1 < m)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)) :
    (secondStructuralTransportedFamily t o cls m gaps a low hm hwindow
        harithmetic hexternalArithmetic).someCandidate ⊆
      (stoppedHistoryCandidateFamilySourceTransport t cls
        (targetAmbientFamily t o cls m 3 a low hm (by omega) hwindow
          harithmetic hexternalArithmetic)
        (targetAmbientNear_measurable t o cls m 3 a low hm (by omega)
          hwindow harithmetic hexternalArithmetic)).someCandidate := by
  intro s hs
  unfold secondStructuralTransportedFamily at hs
  rw [StoppedHistoryCandidateFamily.someCandidate_sourceTransport] at hs ⊢
  exact (sourceEventTargetFamily_someCandidate_subset_unrestricted_inter_event
    a low (secondStructuralPast (TargetTiling t cls) m gaps)
    (measurableSet_secondStructuralPast (TargetTiling t cls) m gaps)
    (fun eta ↦ secondStructuralPast_distinguishedInvariant eta hm gaps)
    (secondStructuralPast_prefixInvariant (TargetTiling t cls) m gaps)
    hm (by omega) hwindow harithmetic hexternalArithmetic hs).1

theorem targetAmbient_inter_firstStructural_subset
    (t : DominoTiling) (o : Orientation) (cls : DominantEndpointClass)
    (m : ℕ) (gaps : GapTriple) (a : GapScale) (low : ℕ) (hm : 1 < m)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)) :
    (targetAmbientFamily t o cls m 2 a low hm (by omega) hwindow
        harithmetic hexternalArithmetic).someCandidate ∩
        firstStructuralPast (TargetTiling t cls) m gaps ⊆
      (firstStructuralPastTargetFamily (TargetTiling t cls)
        (TargetOrientation t o cls) m gaps a low hm hwindow harithmetic
          hexternalArithmetic).someCandidate := by
  simpa only [targetAmbientFamily, sourceUnrestrictedTargetFamily,
    firstStructuralPastTargetFamily] using
    (sourceProp49StoppedHistoryCandidateFamily_univ_inter_event_subset
      (t := TargetTiling t cls) (o := TargetOrientation t o cls)
      a low (firstStructuralPast (TargetTiling t cls) m gaps)
      (measurableSet_firstStructuralPast (TargetTiling t cls) m gaps)
      (fun eta ↦ firstStructuralPast_distinguishedInvariant eta hm gaps)
      (firstStructuralPast_prefixInvariant (TargetTiling t cls) m gaps)
      hm (by omega) hwindow harithmetic hexternalArithmetic)

theorem targetAmbient_inter_secondStructural_subset
    (t : DominoTiling) (o : Orientation) (cls : DominantEndpointClass)
    (m : ℕ) (gaps : GapTriple) (a : GapScale) (low : ℕ) (hm : 1 < m)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)) :
    (targetAmbientFamily t o cls m 3 a low hm (by omega) hwindow
        harithmetic hexternalArithmetic).someCandidate ∩
        secondStructuralPast (TargetTiling t cls) m gaps ⊆
      (secondStructuralPastTargetFamily (TargetTiling t cls)
        (TargetOrientation t o cls) m gaps a low hm hwindow harithmetic
          hexternalArithmetic).someCandidate := by
  simpa only [targetAmbientFamily, sourceUnrestrictedTargetFamily,
    secondStructuralPastTargetFamily] using
    (sourceProp49StoppedHistoryCandidateFamily_univ_inter_event_subset
      (t := TargetTiling t cls) (o := TargetOrientation t o cls)
      a low (secondStructuralPast (TargetTiling t cls) m gaps)
      (measurableSet_secondStructuralPast (TargetTiling t cls) m gaps)
      (fun eta ↦ secondStructuralPast_distinguishedInvariant eta hm gaps)
      (secondStructuralPast_prefixInvariant (TargetTiling t cls) m gaps)
      hm (by omega) hwindow harithmetic hexternalArithmetic)

theorem transportedSourceFamily_inter_firstStructuralPreimage_subset
    (t : DominoTiling) (o : Orientation) (cls : DominantEndpointClass)
    (m : ℕ) (gaps : GapTriple) (a : GapScale) (low : ℕ) (hm : 1 < m)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)) :
    (stoppedHistoryCandidateFamilySourceTransport t cls
      (targetAmbientFamily t o cls m 2 a low hm (by omega) hwindow
        harithmetic hexternalArithmetic)
      (targetAmbientNear_measurable t o cls m 2 a low hm (by omega)
        hwindow harithmetic hexternalArithmetic)).someCandidate ∩
      sourceTransportPreimage t cls
        (firstStructuralPast (TargetTiling t cls) m gaps) ⊆
      (firstStructuralTransportedFamily t o cls m gaps a low hm hwindow
        harithmetic hexternalArithmetic).someCandidate := by
  intro s hs
  rw [StoppedHistoryCandidateFamily.someCandidate_sourceTransport] at hs
  unfold firstStructuralTransportedFamily
  rw [StoppedHistoryCandidateFamily.someCandidate_sourceTransport]
  change sourceTransportPath t cls s ∈
      (firstStructuralPastTargetFamily (TargetTiling t cls)
        (TargetOrientation t o cls) m gaps a low hm hwindow harithmetic
          hexternalArithmetic).someCandidate
  exact targetAmbient_inter_firstStructural_subset t o cls m gaps a low hm
    hwindow harithmetic hexternalArithmetic ⟨hs.1, hs.2⟩

theorem transportedSourceFamily_inter_secondStructuralPreimage_subset
    (t : DominoTiling) (o : Orientation) (cls : DominantEndpointClass)
    (m : ℕ) (gaps : GapTriple) (a : GapScale) (low : ℕ) (hm : 1 < m)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)) :
    (stoppedHistoryCandidateFamilySourceTransport t cls
      (targetAmbientFamily t o cls m 3 a low hm (by omega) hwindow
        harithmetic hexternalArithmetic)
      (targetAmbientNear_measurable t o cls m 3 a low hm (by omega)
        hwindow harithmetic hexternalArithmetic)).someCandidate ∩
      sourceTransportPreimage t cls
        (secondStructuralPast (TargetTiling t cls) m gaps) ⊆
      (secondStructuralTransportedFamily t o cls m gaps a low hm hwindow
        harithmetic hexternalArithmetic).someCandidate := by
  intro s hs
  rw [StoppedHistoryCandidateFamily.someCandidate_sourceTransport] at hs
  unfold secondStructuralTransportedFamily
  rw [StoppedHistoryCandidateFamily.someCandidate_sourceTransport]
  change sourceTransportPath t cls s ∈
      (secondStructuralPastTargetFamily (TargetTiling t cls)
        (TargetOrientation t o cls) m gaps a low hm hwindow harithmetic
          hexternalArithmetic).someCandidate
  exact targetAmbient_inter_secondStructural_subset t o cls m gaps a low hm
    hwindow harithmetic hexternalArithmetic ⟨hs.1, hs.2⟩

end

end Erdos1165.HLOZTransportedStructuralPastProp49Row
