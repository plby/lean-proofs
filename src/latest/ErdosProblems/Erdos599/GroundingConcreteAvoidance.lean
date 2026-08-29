/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingConcreteControls
import ErdosProblems.Erdos599.GroundingControlledAssembly

/-!
# Concrete avoidance supplied by the controlled request warp

The recursive selector is formulated using the two abstract bad families in
`GroundingSelection.Controls`.  A `ConcreteControls` package identifies those
families with the actual collisions of Assertions 8.19--8.20.  This file
records the geometric consequences in a form usable by the simultaneous
grounding decoder.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace GroundingConcreteAvoidance

open DirectedPath
open PopularGroundingBridge

universe u

variable {V I : Type u} {Gamma : DWeb V}

abbrev LV (L : PopularAuxiliary.Input Gamma I) :=
  PopularAuxiliary.Input.LambdaVertex V I

abbrev Path (L : PopularAuxiliary.Input Gamma I) :=
  FinitePath L.lambda.graph

/-- The selected member at a request has no qualifying hanging-ladder
collision. -/
theorem selectedPath_not_hangingLadderCollision
    {L : PopularAuxiliary.Input Gamma I} {kappa : Cardinal.{u}}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingConcreteControls.ConcreteControls S)
    (r : Request L S.cut) :
    ¬ GroundingConcreteControls.hangingLadderCollision L S.cut r
      (GroundingControlledAssembly.selectedPath U S K.toControls r) := by
  intro h
  apply GroundingControlledAssembly.selectedPath_not_mem_hangingLadder
    U S K.toControls r
  rw [K.hangingLadder_exact r]
  exact h

/-- The selected member at a request has no qualifying cut-preceded
hanging-fragment collision. -/
theorem selectedPath_not_hangingFragmentCollision
    {L : PopularAuxiliary.Input Gamma I} {kappa : Cardinal.{u}}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingConcreteControls.ConcreteControls S)
    (r : Request L S.cut) :
    ¬ GroundingConcreteControls.hangingFragmentCollision L S.cut r
      (GroundingControlledAssembly.selectedPath U S K.toControls r) := by
  intro h
  apply GroundingControlledAssembly.selectedPath_not_mem_hangingFragment
    U S K.toControls r
  rw [K.hangingFragment_exact r]
  exact h

/-- Expanded Assertion 8.19 avoidance: a selected member cannot meet the
trace of a hanging ladder path whose complete trace omits its request apex. -/
theorem selectedPath_no_hangingLadder_contact
    {L : PopularAuxiliary.Input Gamma I} {kappa : Cardinal.{u}}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingConcreteControls.ConcreteControls S)
    (r : Request L S.cut) {Y : Gamma.DPath}
    (hY : Y ∈ PopularAuxiliary.hangingPaths Gamma L.ladder.paths)
    (hapex : requestAuxVertex r ∉ PopularSwitching.ladderTrace L Y) :
    ¬ ∃ v ∈ Y.support,
      (PopularAuxiliary.Input.LambdaVertex.old v : LV L) ∈
        (GroundingControlledAssembly.selectedPath U S K.toControls r).support := by
  rintro ⟨v, hvY, hvp⟩
  apply selectedPath_not_hangingLadderCollision U S K r
  have htrace :
      (PopularAuxiliary.Input.LambdaVertex.old v : LV L) ∈
        PopularSwitching.ladderTrace L Y :=
    Or.inl ⟨v, hvY, rfl⟩
  refine ⟨Y, hY,
    (PopularAuxiliary.Input.LambdaVertex.old v : LV L),
    ⟨htrace, ?_⟩, hvp⟩
  intro hv
  exact hapex (Set.mem_singleton_iff.1 hv ▸ htrace)

/-- Expanded Assertion 8.20 avoidance: a selected member cannot meet a
cut-preceded hanging fragment which omits its request apex. -/
theorem selectedPath_no_hangingFragment_contact
    {L : PopularAuxiliary.Input Gamma I} {kappa : Cardinal.{u}}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingConcreteControls.ConcreteControls S)
    (r : Request L S.cut) {P : L.Fragment}
    (hP : P ∈ GroundingCut.fragments L S.cut) (hhang : P.IsHanging)
    (hpred : GroundingConcreteControls.hasCutPredecessor L S.cut P)
    (hapex : requestVertex r ∉ P.path.support) :
    ¬ ∃ v ∈ P.path.support,
      (PopularAuxiliary.Input.LambdaVertex.old v : LV L) ∈
        (GroundingControlledAssembly.selectedPath U S K.toControls r).support := by
  rintro ⟨v, hvP, hvp⟩
  exact selectedPath_not_hangingFragmentCollision U S K r
    ⟨P, hP, hhang, hpred, hapex, v, hvP, hvp⟩

/-- Every member of the concrete selected warp comes with the request whose
two exact collision predicates it avoids. -/
theorem selectedWarp_member_avoids_concrete_collisions
    {L : PopularAuxiliary.Input Gamma I} {kappa : Cardinal.{u}}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingConcreteControls.ConcreteControls S)
    {p : Path L}
    (hp : p ∈ (GroundingControlledAssembly.selectedWarp
      U S K.toControls).paths) :
    ∃ r : Request L S.cut,
      p = GroundingControlledAssembly.selectedPath U S K.toControls r ∧
      ¬ GroundingConcreteControls.hangingLadderCollision L S.cut r p ∧
      ¬ GroundingConcreteControls.hangingFragmentCollision L S.cut r p := by
  obtain ⟨r, rfl⟩ := hp
  exact ⟨r, rfl, selectedPath_not_hangingLadderCollision U S K r,
    selectedPath_not_hangingFragmentCollision U S K r⟩

end GroundingConcreteAvoidance
end Erdos599
