/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.DeferredGroundingSelectedNonstationarity
import ErdosProblems.Erdos599.SplitGroundingSwitchEndpoint

/-!
# The ray-compatible endpoint of deferred grounding

The output used by the deferred bookkeeping cannot be a finite `X`--`S`
warp.  A deferred grounded record may be a ray, and an unused such record
must remain an inessential member of the final wave.  This file records the
correct, representation-independent endpoint: an arbitrary warp (rays are
allowed) with a separating finite terminal frontier.

The legacy finite endpoint remains available in
`SplitGroundingSwitchEndpoint`; `ofFinite` is the compatibility map from it.
The canonical `BB` constructor below also keeps Assertion 8.18 honest: the
separator field is proved from the auxiliary separator and the finite
descent decoder rather than included as an unexplained premise.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace DWeb
namespace KappaLadder
namespace Deferred

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

/-- Ray-compatible output of the last deferred grounding switch. -/
structure StationarySwitchOutput
    (Gamma : DWeb V) (kappa : Cardinal.{u})
    (records : Set (Stationary.Below kappa)) where
  frontier : Set V
  paths : Set Gamma.DPath
  isWarp : Gamma.IsWarp paths
  initialSet_subset : Gamma.initialSet paths ⊆ Gamma.source
  terminalFrontier_eq : Gamma.terminalFrontier paths = frontier
  separates : Popular.IsSeparator Gamma frontier
  usedStages : Set (Stationary.Below kappa)
  used_nonstationary :
    ¬ Stationary.IsStationaryBelow kappa usedStages
  unused_record_inessential : ∀ a,
    a ∈ records \ usedStages →
      ∃ p : Gamma.DPath, p ∈ Gamma.inessentialPaths paths

theorem StationarySwitchOutput.isWave
    {records : Set (Stationary.Below kappa)}
    (O : StationarySwitchOutput Gamma kappa records) :
    Gamma.IsWave O.paths := by
  apply isWave_of_terminalFrontier_isSeparator O.isWarp O.initialSet_subset
  rw [O.terminalFrontier_eq]
  exact O.separates

/-- The finite legacy endpoint is a special case of the ray-compatible
endpoint. -/
def StationarySwitchOutput.ofFinite
    {records : Set (Stationary.Below kappa)}
    (O : StationaryGroundingSwitchOutput Gamma kappa records) :
    StationarySwitchOutput Gamma kappa records where
  frontier := O.frontier
  paths := PopularSwitching.pathFamily O.warp
  isWarp := PopularSwitching.pathFamily_isWarp O.warp
  initialSet_subset := PopularSwitching.pathFamily_initialSet_subset O.warp
  terminalFrontier_eq :=
    PopularSwitching.pathFamily_terminalFrontier_eq O.warp O.covers
  separates := O.separates
  usedStages := O.usedStages
  used_nonstationary := O.used_nonstationary
  unused_record_inessential := O.unused_record_inessential

/-- A stationary family cannot be consumed by a nonstationary switch.  An
unused inessential member then makes the essential part a hindrance. -/
theorem exists_hindrance_of_stationarySwitchOutput
    {records : Set (Stationary.Below kappa)}
    (hregular : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hstationary : Stationary.IsStationaryBelow kappa records)
    (O : StationarySwitchOutput Gamma kappa records) :
    ∃ W : Set Gamma.DPath, Gamma.IsHindrance W := by
  have hleft : Stationary.IsStationaryBelow kappa
      (records \ O.usedStages) :=
    PopularSwitching.stationary_diff_of_stationary_of_nonstationary
      hregular huncountable hstationary O.used_nonstationary
  obtain ⟨a, ha⟩ := hleft.nonempty
  obtain ⟨p, hp⟩ := O.unused_record_inessential a ha
  exact ⟨Gamma.essentialWarpPart O.paths,
    essentialWarpPart_isHindrance_of_inessentialPath O.isWave hp⟩

/-- Specialized output of the separator arm.  The used stages are fixed to
the initial indices of the control-aware selected auxiliary warp. -/
structure SeparatorSwitchPruneOutput
    (L : Gamma.KappaLadder kappa) (hL : IsKappaHindrance L)
    (S : Popular.PopularSeparator (popularAuxiliaryIndexed L hL))
    (K : GroundingSelection.Controls S) where
  frontier : Set V
  paths : Set Gamma.DPath
  isWarp : Gamma.IsWarp paths
  initialSet_subset : Gamma.initialSet paths ⊆ Gamma.source
  terminalFrontier_eq : Gamma.terminalFrontier paths = frontier
  separates : Popular.IsSeparator Gamma frontier
  unused_record_inessential : ∀ a,
    a ∈ phiGround L \
      Popular.initialIndicesOf (popularAuxiliaryIndexed L hL)
        (GroundingAssembly.selectedWarp
          (popularAuxiliaryIndexed L hL) S K).paths
        (GroundingAssembly.selectedWarp
          (popularAuxiliaryIndexed L hL) S K).starts_in_source →
      ∃ p : Gamma.DPath,
        L.chosen a = some p ∧ p ∈ Gamma.inessentialPaths paths

/-- Forget the bookkeeping-specific chosen-path witness. -/
def SeparatorSwitchPruneOutput.toStationaryOutput
    {L : Gamma.KappaLadder kappa} {hL : IsKappaHindrance L}
    {S : Popular.PopularSeparator (popularAuxiliaryIndexed L hL)}
    {K : GroundingSelection.Controls S}
    (O : SeparatorSwitchPruneOutput L hL S K) :
    StationarySwitchOutput Gamma kappa (phiGround L) where
  frontier := O.frontier
  paths := O.paths
  isWarp := O.isWarp
  initialSet_subset := O.initialSet_subset
  terminalFrontier_eq := O.terminalFrontier_eq
  separates := O.separates
  usedStages :=
    Popular.initialIndicesOf (popularAuxiliaryIndexed L hL)
      (GroundingAssembly.selectedWarp
        (popularAuxiliaryIndexed L hL) S K).paths
      (GroundingAssembly.selectedWarp
        (popularAuxiliaryIndexed L hL) S K).starts_in_source
  used_nonstationary :=
    GroundingAssembly.selectedWarp_initialIndices_nonstationary
      (popularAuxiliaryIndexed L hL) S K
  unused_record_inessential := by
    intro a ha
    obtain ⟨p, _hchosen, hp⟩ := O.unused_record_inessential a ha
    exact ⟨p, hp⟩

/-- The ray-compatible canonical-`BB` switch/prune certificate. -/
structure GroundingCutSwitchPruneOutput
    (L : Gamma.KappaLadder kappa) (hL : IsKappaHindrance L)
    (S : Popular.PopularSeparator (popularAuxiliaryIndexed L hL))
    (K : GroundingSelection.Controls S) where
  descent : GroundingCut.FiniteDescentDecoder
    (popularAuxiliaryInput L hL.legal) S.cut
  paths : Set Gamma.DPath
  isWarp : Gamma.IsWarp paths
  initialSet_subset : Gamma.initialSet paths ⊆ Gamma.source
  terminalFrontier_eq : Gamma.terminalFrontier paths =
    GroundingCut.BB (popularAuxiliaryInput L hL.legal) S.cut
  unused_record_inessential : ∀ a,
    a ∈ phiGround L \
      Popular.initialIndicesOf (popularAuxiliaryIndexed L hL)
        (GroundingAssembly.selectedWarp
          (popularAuxiliaryIndexed L hL) S K).paths
        (GroundingAssembly.selectedWarp
          (popularAuxiliaryIndexed L hL) S K).starts_in_source →
      ∃ p : Gamma.DPath,
        L.chosen a = some p ∧ p ∈ Gamma.inessentialPaths paths

/-- The terminal frontier used by the auxiliary automatically roofs the
source at the final ladder stage. -/
theorem popularAuxiliary_ladder_terminal_roofs_source
    (L : Gamma.KappaLadder kappa) (hL : IsKappaHindrance L) :
    Gamma.source ⊆ Gamma.roof (Gamma.terminalFrontier
      (popularAuxiliaryInput L hL.legal).ladder.paths) := by
  simpa only [popularAuxiliaryInput, KappaLadder.limitWarp] using
    hL.legal.roofsSourceAtStages (Ladder.finalStage kappa)

/-- Assertions 8.18 and 8.22 turn the canonical-`BB` certificate into the
specialized separator-arm output. -/
def GroundingCutSwitchPruneOutput.toSeparatorSwitchPruneOutput
    {L : Gamma.KappaLadder kappa} {hL : IsKappaHindrance L}
    {S : Popular.PopularSeparator (popularAuxiliaryIndexed L hL)}
    {K : GroundingSelection.Controls S}
    (O : GroundingCutSwitchPruneOutput L hL S K) :
    SeparatorSwitchPruneOutput L hL S K where
  frontier := GroundingCut.BB (popularAuxiliaryInput L hL.legal) S.cut
  paths := O.paths
  isWarp := O.isWarp
  initialSet_subset := O.initialSet_subset
  terminalFrontier_eq := O.terminalFrontier_eq
  separates := GroundingCut.assertion8_18
    (popularAuxiliaryInput L hL.legal) S.cut S.separates
    (terminalCut_isSeparator_of_roofsSource
      (popularAuxiliaryInput L hL.legal)
      (popularAuxiliary_ladder_terminal_roofs_source L hL))
    O.descent
  unused_record_inessential := O.unused_record_inessential

end Deferred
end KappaLadder
end DWeb
end Erdos599
