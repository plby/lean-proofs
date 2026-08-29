/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingAvoidingControls

/-!
# Request-wise countable avoidance controls

The countable-carrier argument for a joined request fan only needs the
request apex to miss the carrier.  It does not need the carrier to be
disjoint from the whole popular cut.  This request-wise form is what is
needed when a private finite exchange starts at one cut vertex: every
genuine request apex still misses its collision carrier, even though that
carrier contains the private starting cut vertex.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace GroundingRequestAvoidingControls

open DirectedPath Stationary
open PopularGroundingBridge

universe u

variable {V I : Type u} {Gamma : DWeb V}

abbrev Path (L : PopularAuxiliary.Input Gamma I) :=
  FinitePath L.lambda.graph

/-- Meeting a countable carrier which misses the request apex is
nonstationary inside that request's joined local fan. -/
theorem meetsCarrier_indices_nonstationary_of_apex_not_mem
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    {U : Popular.KappaIndexed L.lambda kappa}
    (S : Popular.PopularSeparator U)
    (Z : Set L.LV) (hZcountable : Z.Countable)
    (r : Request L S.cut) (hApex : requestAuxVertex r ∉ Z) :
    ¬ IsStationaryBelow kappa
      (GroundingSelection.restrictedIndices U (requestFan S r)
        (GroundingAvoidingControls.meetsCarrier Z)) := by
  apply
    PopularAuxiliary.Input.joinedFamily_initialIndices_nonstationary_of_meets_countable
      U (PopularSwitching.restrictPaths (requestFan S r)
        (GroundingAvoidingControls.meetsCarrier Z)) hZcountable
  · exact Set.disjoint_singleton_right.2 hApex
  · intro p hp
    obtain ⟨x, hxp, hxZ⟩ := hp.2
    exact ⟨x, hxZ, hxp⟩

/-- Add a countable forbidden carrier when each request apex individually
misses it. -/
noncomputable def addCountableRequestAvoidance
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    {U : Popular.KappaIndexed L.lambda kappa}
    {S : Popular.PopularSeparator U}
    (K : GroundingSelection.Controls S)
    (Z : Set L.LV) (hZcountable : Z.Countable)
    (hApex : ∀ r : Request L S.cut, requestAuxVertex r ∉ Z) :
    GroundingSelection.Controls S where
  hangingLadder := K.hangingLadder
  hangingFragment r := K.hangingFragment r ∪
    GroundingAvoidingControls.meetsCarrier Z
  ladderRank := K.ladderRank
  ladderTrace := K.ladderTrace
  ladderRank_regressive := K.ladderRank_regressive
  ladderTrace_countable := K.ladderTrace_countable
  ladderTrace_disjoint_apex := K.ladderTrace_disjoint_apex
  hangingLadder_meets := K.hangingLadder_meets
  fragmentIndices_nonstationary := by
    intro r
    have hK := K.fragmentIndices_nonstationary r
    have hZ := meetsCarrier_indices_nonstationary_of_apex_not_mem
      S Z hZcountable r (hApex r)
    have hUnion := GroundingSelection.not_isStationaryBelow_union
      U.regular U.uncountable hK hZ
    intro hstationary
    apply hUnion
    exact hstationary.mono
      (GroundingControlledAssembly.restrictedIndices_union_subset U
        (requestFan S r) (K.hangingFragment r)
        (GroundingAvoidingControls.meetsCarrier Z))

@[simp]
theorem addCountableRequestAvoidance_hangingLadder
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    {U : Popular.KappaIndexed L.lambda kappa}
    {S : Popular.PopularSeparator U}
    (K : GroundingSelection.Controls S)
    (Z : Set L.LV) (hZcountable : Z.Countable)
    (hApex : ∀ r : Request L S.cut, requestAuxVertex r ∉ Z)
    (r : Request L S.cut) :
    (addCountableRequestAvoidance K Z hZcountable hApex).hangingLadder r =
      K.hangingLadder r :=
  rfl

@[simp]
theorem addCountableRequestAvoidance_hangingFragment
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    {U : Popular.KappaIndexed L.lambda kappa}
    {S : Popular.PopularSeparator U}
    (K : GroundingSelection.Controls S)
    (Z : Set L.LV) (hZcountable : Z.Countable)
    (hApex : ∀ r : Request L S.cut, requestAuxVertex r ∉ Z)
    (r : Request L S.cut) :
    (addCountableRequestAvoidance K Z hZcountable hApex).hangingFragment r =
      K.hangingFragment r ∪ GroundingAvoidingControls.meetsCarrier Z :=
  rfl

/-- Every controlled request path for the enlarged controls avoids the
request-wise forbidden carrier. -/
theorem controlledRequestFan_support_disjoint
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    {U : Popular.KappaIndexed L.lambda kappa}
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (Z : Set L.LV) (hZcountable : Z.Countable)
    (hApex : ∀ r : Request L S.cut, requestAuxVertex r ∉ Z)
    (r : Request L S.cut) {p : Path L}
    (hp : p ∈ (GroundingControlledAssembly.controlledRequestFan S
      (addCountableRequestAvoidance K Z hZcountable hApex) r).paths) :
    Disjoint p.support Z := by
  rw [Set.disjoint_left]
  intro x hxp hxZ
  apply hp.2
  exact Or.inr (Or.inr ⟨x, hxp, hxZ⟩)

/-- The strong simultaneous selector for request-wise enlarged controls
avoids the carrier on every selected path. -/
theorem strongSelectedPath_support_disjoint
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (Z : Set L.LV) (hZcountable : Z.Countable)
    (hApex : ∀ r : Request L S.cut, requestAuxVertex r ∉ Z)
    (r : Request L S.cut) :
    Disjoint
      (GroundingSimultaneousDecode.strongSelectedPath U S
        (addCountableRequestAvoidance K Z hZcountable hApex) r).support Z := by
  apply controlledRequestFan_support_disjoint S K Z hZcountable hApex r
  exact GroundingSimultaneousDecode.strongSelectedPath_mem_controlledRequestFan
    U S (addCountableRequestAvoidance K Z hZcountable hApex) r

end GroundingRequestAvoidingControls
end Erdos599

#print axioms
  Erdos599.GroundingRequestAvoidingControls.addCountableRequestAvoidance
#print axioms
  Erdos599.GroundingRequestAvoidingControls.strongSelectedPath_support_disjoint
