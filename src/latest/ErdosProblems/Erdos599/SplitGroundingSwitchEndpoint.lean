/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingAuxiliary
import ErdosProblems.Erdos599.PopularSwitching
import ErdosProblems.Erdos599.GroundingCut

/-!
# The final endpoint of the split grounding switch

This file isolates the exact output which the geometric Lambda-to-Gamma
switch has to produce in the stationary equal-index branch.  The output is
not merely a collection of decoded routes: it is a finite source--separator
warp in the original web, together with the assertion that every grounded
record whose index was not used by the switch remains inessential in that
warp.

The theorem below proves the last stationary-ideal and essential-trimming
step of Section 8.  In particular, it returns an actual ordinary hindrance,
not an abstract obstruction or another branch handler.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace DWeb
namespace KappaLadder

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

/-- Representation-independent output of the last grounding switch.  The
index set `records` can be the grounded stages of the legacy, split, or
deferred bookkeeping. -/
structure StationaryGroundingSwitchOutput
    (Gamma : DWeb V) (kappa : Cardinal.{u})
    (records : Set (Stationary.Below kappa)) where
  frontier : Set V
  warp : Popular.XSWarp Gamma frontier
  covers : ∀ x, x ∈ frontier →
    ∃ p ∈ warp.paths, p.finish = x
  separates : Popular.IsSeparator Gamma frontier
  usedStages : Set (Stationary.Below kappa)
  used_nonstationary :
    ¬ Stationary.IsStationaryBelow kappa usedStages
  unused_record_inessential : ∀ a,
    a ∈ records \ usedStages →
      ∃ p : Gamma.DPath,
        p ∈ Gamma.inessentialPaths (PopularSwitching.pathFamily warp)

theorem StationaryGroundingSwitchOutput.isWave
    {records : Set (Stationary.Below kappa)}
    (O : StationaryGroundingSwitchOutput Gamma kappa records) :
    Gamma.IsWave (PopularSwitching.pathFamily O.warp) :=
  PopularSwitching.pathFamily_isWave O.warp O.covers O.separates

/-- The common final step for every bookkeeping variant: a nonstationary
switch cannot consume a stationary family of inessential records. -/
theorem exists_hindrance_of_stationaryGroundingSwitchOutput
    {records : Set (Stationary.Below kappa)}
    (hregular : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hstationary : Stationary.IsStationaryBelow kappa records)
    (O : StationaryGroundingSwitchOutput Gamma kappa records) :
    ∃ W : Set Gamma.DPath, Gamma.IsHindrance W := by
  have hleft : Stationary.IsStationaryBelow kappa
      (records \ O.usedStages) :=
    PopularSwitching.stationary_diff_of_stationary_of_nonstationary
      hregular huncountable hstationary O.used_nonstationary
  obtain ⟨a, ha⟩ := hleft.nonempty
  obtain ⟨p, hp⟩ := O.unused_record_inessential a ha
  exact
    ⟨Gamma.essentialWarpPart (PopularSwitching.pathFamily O.warp),
      essentialWarpPart_isHindrance_of_inessentialPath O.isWave hp⟩

/-! ## The canonical `BB` frontier -/

/-- The path-meeting and roof formulations of source--target separation
agree in the direction needed by the grounding construction. -/
theorem isSeparator_of_source_subset_roof
    {S : Set V} (hS : Gamma.source ⊆ Gamma.roof S) :
    Popular.IsSeparator Gamma S := by
  intro p hpSource hpTarget
  exact hS hpSource p ⟨rfl, hpTarget⟩

/-- The terminal frontier of the essential ladder is separating as soon as
the terminal frontier of the full ladder roofs the source.  Essential
trimming does not change a roof. -/
theorem terminalCut_isSeparator_of_roofsSource
    {I : Type u} (I' : PopularAuxiliary.Input Gamma I)
    (hroof : Gamma.source ⊆
      Gamma.roof (Gamma.terminalFrontier I'.ladder.paths)) :
    Popular.IsSeparator Gamma I'.terminalCut := by
  apply isSeparator_of_source_subset_roof
  intro x hx
  rw [PopularAuxiliary.Input.terminalCut,
    PopularAuxiliary.Input.essentialLadder,
    Gamma.terminalFrontier_essentialWarpPart, Gamma.roof_essential]
  exact hroof hx

/-- Concrete output of the last grounding switch when its frontier is the
canonical set `BB` from Assertion 8.18.  Unlike
`StationaryGroundingSwitchOutput`, this structure does not assume that the
frontier separates: the auxiliary separator, the ladder roof invariant, and
the literal finite-descent decoder prove that fact. -/
structure GroundingCutSwitchOutput
    {I : Type u} (I' : PopularAuxiliary.Input Gamma I)
    (C : Set (PopularAuxiliary.Input.LambdaVertex V I))
    (kappa : Cardinal.{u}) (records : Set (Stationary.Below kappa)) where
  auxiliary_separates : Popular.IsSeparator I'.lambda C
  terminal_roofs_source : Gamma.source ⊆
    Gamma.roof (Gamma.terminalFrontier I'.ladder.paths)
  descent : GroundingCut.FiniteDescentDecoder I' C
  warp : Popular.XSWarp Gamma (GroundingCut.BB I' C)
  covers : ∀ x, x ∈ GroundingCut.BB I' C →
    ∃ p ∈ warp.paths, p.finish = x
  usedStages : Set (Stationary.Below kappa)
  used_nonstationary :
    ¬ Stationary.IsStationaryBelow kappa usedStages
  unused_record_inessential : ∀ a,
    a ∈ records \ usedStages →
      ∃ p : Gamma.DPath,
        p ∈ Gamma.inessentialPaths (PopularSwitching.pathFamily warp)

/-- Assertion 8.18 supplies the separator field of the representation-
independent final switch output. -/
def GroundingCutSwitchOutput.toStationaryGroundingSwitchOutput
    {I : Type u} {I' : PopularAuxiliary.Input Gamma I}
    {C : Set (PopularAuxiliary.Input.LambdaVertex V I)}
    {records : Set (Stationary.Below kappa)}
    (O : GroundingCutSwitchOutput I' C kappa records) :
    StationaryGroundingSwitchOutput Gamma kappa records where
  frontier := GroundingCut.BB I' C
  warp := O.warp
  covers := O.covers
  separates := GroundingCut.assertion8_18 I' C O.auxiliary_separates
    (terminalCut_isSeparator_of_roofsSource I' O.terminal_roofs_source)
    O.descent
  usedStages := O.usedStages
  used_nonstationary := O.used_nonstationary
  unused_record_inessential := O.unused_record_inessential

/-- A completed canonical-cut switch produces an ordinary hindrance. -/
theorem exists_hindrance_of_groundingCutSwitchOutput
    {I : Type u} {I' : PopularAuxiliary.Input Gamma I}
    {C : Set (PopularAuxiliary.Input.LambdaVertex V I)}
    {records : Set (Stationary.Below kappa)}
    (hregular : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hstationary : Stationary.IsStationaryBelow kappa records)
    (O : GroundingCutSwitchOutput I' C kappa records) :
    ∃ W : Set Gamma.DPath, Gamma.IsHindrance W :=
  exists_hindrance_of_stationaryGroundingSwitchOutput
    hregular huncountable hstationary
      O.toStationaryGroundingSwitchOutput

/-- The initial-index set of the grounded part of an equal subwarp. -/
def splitEqualGroundIndices
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (P : Popular.XSWarp
      (L.splitPopularAuxiliaryInput hL.legal).lambda
      (L.splitPopularAuxiliaryInput hL.legal).lambda.target) :
    Set (Ladder.Stage kappa) :=
  Popular.initialIndicesOf (L.splitPopularAuxiliaryIndexed hL)
      ((L.splitPopularAuxiliaryIndexed hL).equalSubwarp P).paths
      ((L.splitPopularAuxiliaryIndexed hL).equalSubwarp P).starts_in_source ∩
    L.phiGround

/-- The precise global output needed from the equal-branch grounding
switch.

`usedStages` records the grounded indices whose Lambda routes participate in
the switch.  It must be nonstationary.  The pruned Gamma warp covers a
separating frontier, hence is a wave.  Finally, every unused grounded record
is still an inessential member of that wave.  These are exactly the three
facts used in the final paragraph of Assertion 8.22. -/
structure EqualGroundingSwitchOutput
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (P : Popular.XSWarp
      (L.splitPopularAuxiliaryInput hL.legal).lambda
      (L.splitPopularAuxiliaryInput hL.legal).lambda.target) where
  frontier : Set V
  warp : Popular.XSWarp Gamma frontier
  covers : ∀ x, x ∈ frontier →
    ∃ p ∈ warp.paths, p.finish = x
  separates : Popular.IsSeparator Gamma frontier
  usedStages : Set (Ladder.Stage kappa)
  used_nonstationary :
    ¬ Stationary.IsStationaryBelow kappa usedStages
  unused_record_inessential : ∀ a,
    a ∈ splitEqualGroundIndices L hL P \ usedStages →
      ∃ p : Gamma.DPath,
        L.chosen a = some p ∧
          p ∈ Gamma.inessentialPaths (PopularSwitching.pathFamily warp)

/-- A genuine wave carried by every completed equal-branch switch output. -/
theorem EqualGroundingSwitchOutput.isWave
    {L : Gamma.KappaLadder kappa} {hL : L.IsSplitKappaHindrance}
    {P : Popular.XSWarp
      (L.splitPopularAuxiliaryInput hL.legal).lambda
      (L.splitPopularAuxiliaryInput hL.legal).lambda.target}
    (O : EqualGroundingSwitchOutput L hL P) :
    Gamma.IsWave (PopularSwitching.pathFamily O.warp) :=
  PopularSwitching.pathFamily_isWave O.warp O.covers O.separates

/-- The final Section 8 implication for the stationary grounded equal
branch.  Stationarity leaves an unused record, the switch output makes that
record inessential in its pruned wave, and essential trimming therefore
produces an ordinary hindrance. -/
theorem exists_hindrance_of_splitEqualGroundingSwitchOutput
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (P : Popular.XSWarp
      (L.splitPopularAuxiliaryInput hL.legal).lambda
      (L.splitPopularAuxiliaryInput hL.legal).lambda.target)
    (hstationary : Stationary.IsStationaryBelow kappa
      (splitEqualGroundIndices L hL P))
    (O : EqualGroundingSwitchOutput L hL P) :
    ∃ W : Set Gamma.DPath, Gamma.IsHindrance W := by
  let O' : StationaryGroundingSwitchOutput Gamma kappa
      (splitEqualGroundIndices L hL P) :=
    { frontier := O.frontier
      warp := O.warp
      covers := O.covers
      separates := O.separates
      usedStages := O.usedStages
      used_nonstationary := O.used_nonstationary
      unused_record_inessential := by
        intro a ha
        obtain ⟨p, _hchosen, hp⟩ := O.unused_record_inessential a ha
        exact ⟨p, hp⟩ }
  exact exists_hindrance_of_stationaryGroundingSwitchOutput
    hL.legal.regular hL.legal.uncountable hstationary O'

end KappaLadder
end DWeb
end Erdos599
