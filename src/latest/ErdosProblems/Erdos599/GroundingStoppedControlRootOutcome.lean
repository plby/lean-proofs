/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingStoppedControlRootClassification
import ErdosProblems.Erdos599.GroundingStoppedActiveControlPrefix
import ErdosProblems.Erdos599.GroundingStoppedActiveForwardRootClassification

/-!
# Total native classification of an unrooted stopped control

This composes the three boundary-parametric pieces without transporting any
pre-stopped root.  An unrooted control is active, is absorbed through an
unrooted retained point of an active request, or has a finite classified
absorber segment.  Active controls additionally retain the honest
prefix-until-frontier alternative.
-/

noncomputable section

open Set

namespace Erdos599
namespace GroundingErasedDecode

open _root_.Erdos599.DirectedPath

universe u

variable {V I : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

/-- Complete positive data behind failure to root one control in the switch
constructed and stopped at the same frontier `T`. -/
inductive StoppedControlUnrootedOutcome
    {J : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed J.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (T A : Set V)
    (c : ControlRequest J S.cut) : Prop
  | active
      (isActive : IsActiveControlAt U S K T c)
      (outcome : ActiveControlAtUnrootedPrefixOutcome
        U S K T A ⟨c, isActive⟩)
  | absorbed
      (absorber : ActiveControlRequestAt U S K T)
      (contact : V)
      (contact_retained : contact ∈ retainedForwardVerticesAt T
        (selectedErasedCompression U S K
          (chosenRequest absorber.1)).path)
      (contact_not_rooted : ¬ ∃ a ∈ A, Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdgesAt U S K T)
        a contact)
      (outcome : ActiveRetainedForwardVertexUnrootedOutcome
        U S K T A absorber)
  | inactiveSegment
      (data : DWeb.KappaLadder.InactiveStoppedRootObstructionDataAt
        S K T A c)

/-- No-premise native-`T` expansion of an exact unrooted-control residual. -/
theorem stoppedControl_unrooted_outcome
    {J : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed J.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (hfaith : GroundingSimultaneousDecode.ProxyPathsFaithful J)
    (T A : Set V)
    (c : ControlRequest J S.cut)
    (hnotRooted : ¬ ∃ a ∈ A, Relation.ReflTransGen
      (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdgesAt U S K T)
      a c.1) :
    StoppedControlUnrootedOutcome U S K T A c := by
  rcases DWeb.KappaLadder.controlAt_unrooted_cases
      K hfaith T A c hnotRooted with hactive |
      ⟨d, x, hx, hnot⟩ | hsegment
  · exact .active hactive
      (activeControlAt_unrooted_prefix_outcome
        U S K T A ⟨c, hactive⟩ hnotRooted)
  · exact .absorbed d x hx hnot
      (activeRequestAt_retainedForwardVertex_unrooted_outcome
        U S K T A d hx hnot)
  · obtain ⟨D⟩ := hsegment
    exact .inactiveSegment D

end GroundingErasedDecode
end Erdos599

#print axioms Erdos599.GroundingErasedDecode.stoppedControl_unrooted_outcome
