/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingSimultaneousDecode

/-!
# Adding a fixed countable avoidance carrier to the grounding controls

The local request fan is joined at its request vertex.  Consequently, if a
fixed countable set `Z` is disjoint from the popular cut, the members of any
request fan which meet `Z` have nonstationary initial-index set.  They may be
added to the fragment-exceptional family without destroying the stationary
choice used by the simultaneous decoder.

This is useful when a grounded limiting-ladder record is chosen before the
simultaneous selector: after encoding its carrier in the auxiliary web, the
selector can be required to avoid that carrier literally.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace GroundingAvoidingControls

open DirectedPath Stationary
open PopularGroundingBridge

universe u

variable {V I : Type u} {Gamma : DWeb V}

abbrev Path (L : PopularAuxiliary.Input Gamma I) :=
  FinitePath L.lambda.graph

/-- The finite auxiliary paths which meet the fixed carrier `Z`. -/
def meetsCarrier
    {L : PopularAuxiliary.Input Gamma I}
    (Z : Set L.LV) : Set (Path L) :=
  {p | (p.support ∩ Z).Nonempty}

/-- In a local request fan, meeting a fixed countable carrier disjoint from
the popular cut is a nonstationary condition. -/
theorem meetsCarrier_indices_nonstationary
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    {U : Popular.KappaIndexed L.lambda kappa}
    (S : Popular.PopularSeparator U)
    (Z : Set L.LV) (hZcountable : Z.Countable)
    (hZcut : Disjoint Z S.cut)
    (r : Request L S.cut) :
    ¬ IsStationaryBelow kappa
      (GroundingSelection.restrictedIndices U (requestFan S r)
        (meetsCarrier Z)) := by
  apply
    PopularAuxiliary.Input.joinedFamily_initialIndices_nonstationary_of_meets_countable
      U (PopularSwitching.restrictPaths (requestFan S r) (meetsCarrier Z))
      hZcountable
  · apply Set.disjoint_singleton_right.2
    intro hx
    exact Set.disjoint_left.1 hZcut hx (requestAuxVertex_mem_cut r)
  · intro p hp
    obtain ⟨x, hxp, hxZ⟩ := hp.2
    exact ⟨x, hxZ, hxp⟩

/-- Extend an existing control package by forbidding every local-fan member
which meets `Z`.  The original ladder control is unchanged, so all of its
regressive trace data remains definitionally available. -/
noncomputable def addCountableAvoidance
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    {U : Popular.KappaIndexed L.lambda kappa}
    {S : Popular.PopularSeparator U}
    (K : GroundingSelection.Controls S)
    (Z : Set L.LV) (hZcountable : Z.Countable)
    (hZcut : Disjoint Z S.cut) :
    GroundingSelection.Controls S where
  hangingLadder := K.hangingLadder
  hangingFragment r := K.hangingFragment r ∪ meetsCarrier Z
  ladderRank := K.ladderRank
  ladderTrace := K.ladderTrace
  ladderRank_regressive := K.ladderRank_regressive
  ladderTrace_countable := K.ladderTrace_countable
  ladderTrace_disjoint_apex := K.ladderTrace_disjoint_apex
  hangingLadder_meets := K.hangingLadder_meets
  fragmentIndices_nonstationary := by
    intro r
    have hK := K.fragmentIndices_nonstationary r
    have hZ := meetsCarrier_indices_nonstationary S Z hZcountable hZcut r
    have hUnion := GroundingSelection.not_isStationaryBelow_union
      U.regular U.uncountable hK hZ
    intro hstationary
    apply hUnion
    exact hstationary.mono
      (GroundingControlledAssembly.restrictedIndices_union_subset U
        (requestFan S r) (K.hangingFragment r) (meetsCarrier Z))

@[simp]
theorem addCountableAvoidance_hangingLadder
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    {U : Popular.KappaIndexed L.lambda kappa}
    {S : Popular.PopularSeparator U}
    (K : GroundingSelection.Controls S)
    (Z : Set L.LV) (hZcountable : Z.Countable)
    (hZcut : Disjoint Z S.cut)
    (r : Request L S.cut) :
    (addCountableAvoidance K Z hZcountable hZcut).hangingLadder r =
      K.hangingLadder r :=
  rfl

@[simp]
theorem addCountableAvoidance_hangingFragment
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    {U : Popular.KappaIndexed L.lambda kappa}
    {S : Popular.PopularSeparator U}
    (K : GroundingSelection.Controls S)
    (Z : Set L.LV) (hZcountable : Z.Countable)
    (hZcut : Disjoint Z S.cut)
    (r : Request L S.cut) :
    (addCountableAvoidance K Z hZcountable hZcut).hangingFragment r =
      K.hangingFragment r ∪ meetsCarrier Z :=
  rfl

/-- Every member of a controlled local fan for the enlarged controls is
literally disjoint from the added carrier. -/
theorem controlledRequestFan_support_disjoint
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    {U : Popular.KappaIndexed L.lambda kappa}
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (Z : Set L.LV) (hZcountable : Z.Countable)
    (hZcut : Disjoint Z S.cut)
    (r : Request L S.cut) {p : Path L}
    (hp : p ∈ (GroundingControlledAssembly.controlledRequestFan S
      (addCountableAvoidance K Z hZcountable hZcut) r).paths) :
    Disjoint p.support Z := by
  rw [Set.disjoint_left]
  intro x hxp hxZ
  apply hp.2
  exact Or.inr (Or.inr ⟨x, hxp, hxZ⟩)

/-- In particular, the strong simultaneous selector built from the enlarged
controls avoids `Z` on every selected auxiliary path. -/
theorem strongSelectedPath_support_disjoint
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (Z : Set L.LV) (hZcountable : Z.Countable)
    (hZcut : Disjoint Z S.cut)
    (r : Request L S.cut) :
    Disjoint
      (GroundingSimultaneousDecode.strongSelectedPath U S
        (addCountableAvoidance K Z hZcountable hZcut) r).support Z := by
  apply controlledRequestFan_support_disjoint S K Z hZcountable hZcut r
  exact GroundingSimultaneousDecode.strongSelectedPath_mem_controlledRequestFan
    U S (addCountableAvoidance K Z hZcountable hZcut) r

end GroundingAvoidingControls
end Erdos599

#print axioms Erdos599.GroundingAvoidingControls.addCountableAvoidance
#print axioms Erdos599.GroundingAvoidingControls.strongSelectedPath_support_disjoint
