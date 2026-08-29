/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.Blueprint
import ErdosProblems.Erdos599.DeferredHalfwayGeometry

/-!
# Global limiting-reference closure from causal stage closures

The closing set used in the half-way construction is assembled stage by
stage.  It must be closed under the final ladder warp, but assuming this
global closure as an input would hide the essential limit argument.

At the final limit, every member of the limiting warp is the direct limit of
one extension thread.  If it meets the union of the stage closures, choose a
stage containing the contact.  Any other vertex of the limiting path also
occurs at some stage of the same thread.  At a common later stage, the two
stage paths have the same initial vertex and hence, by warp uniqueness, are
the same path.  The causal closure step absorbs that stage path into a later
stage closure, and therefore into the global union.

No finite-character hypothesis and no prior global-reference closure are
used.  In particular the theorem does not close a stage set under any future
interval row.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Blueprint.LinkageBlueprint

open DirectedPath Ladder

universe u

variable {V : Type u} {Gamma : DWeb V}
variable {kappa : Cardinal.{u}}

/-- A monotone family is causally path-closed along a ladder if every stage
path which already contacts the current closed set is absorbed by some
later stage.  The later stage may equal the current one. -/
def CausalStagePathClosure
    (L : Gamma.KappaLadder kappa)
    (closedStage : Ladder.Stage kappa → Set V) : Prop :=
  ∀ (a : Ladder.Stage kappa) (p : Gamma.DPath),
    p ∈ L.warpAt a →
    (p.support ∩ closedStage a).Nonempty →
    ∃ b : Ladder.Stage kappa, a ≤ b ∧ p.support ⊆ closedStage b

namespace CausalStagePathClosure

/-- The same-stage form of path closure is a special case of causal
later-stage closure. -/
theorem of_sameStage
    {L : Gamma.KappaLadder kappa}
    {closedStage : Ladder.Stage kappa → Set V}
    (h : ∀ (a : Ladder.Stage kappa) (p : Gamma.DPath),
      p ∈ L.warpAt a →
      (p.support ∩ closedStage a).Nonempty →
      p.support ⊆ closedStage a) :
    CausalStagePathClosure L closedStage := by
  intro a p hp hmeet
  exact ⟨a, le_rfl, h a p hp hmeet⟩

/-- A one-step closure rule supplies the causal certificate once its chosen
next stage is known to be later. -/
theorem of_nextStage
    {L : Gamma.KappaLadder kappa}
    {closedStage : Ladder.Stage kappa → Set V}
    (next : Ladder.Stage kappa → Ladder.Stage kappa)
    (hnext : ∀ a, a ≤ next a)
    (h : ∀ (a : Ladder.Stage kappa) (p : Gamma.DPath),
      p ∈ L.warpAt a →
      (p.support ∩ closedStage a).Nonempty →
      p.support ⊆ closedStage (next a)) :
    CausalStagePathClosure L closedStage := by
  intro a p hp hmeet
  exact ⟨next a, hnext a, h a p hp hmeet⟩

end CausalStagePathClosure

/-- Causal path closure at all ordinary stages closes their union under the
genuine final direct-limit warp of a ladder with the half-way geometry. -/
theorem closedUnderPaths_limitWarp_iUnion_of_causalStages
    (L : Gamma.KappaLadder kappa)
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    (closedStage : Ladder.Stage kappa → Set V)
    (hmono : Monotone closedStage)
    (hcausal : CausalStagePathClosure L closedStage) :
    ClosedUnderPaths Gamma L.limitWarp (⋃ a, closedStage a) := by
  have hkappaLimit : Order.IsSuccLimit kappa.ord :=
    Cardinal.isSuccLimit_ord hL.regular.aleph0_le
  obtain ⟨C, hstage, hlimit⟩ :=
    hL.limitStages (Ladder.finalStage kappa) hkappaLimit
  intro p hp hmeet
  have hpC : p ∈ C.limitPaths Gamma := by
    rw [← hlimit]
    exact hp
  obtain ⟨thread, hthread⟩ := (C.mem_limitPaths_iff Gamma p).1 hpC
  subst p
  obtain ⟨x, hxPath, hxUnion⟩ := hmeet
  obtain ⟨closedIndex, hxClosed⟩ := Set.mem_iUnion.1 hxUnion
  intro y hyPath
  obtain ⟨ix, qx, hqx, hqxInitial, hxqx⟩ :=
    (C.mem_support_threadLimit_iff Gamma thread x).1 hxPath
  obtain ⟨iy, qy, hqy, hqyInitial, hyqy⟩ :=
    (C.mem_support_threadLimit_iff Gamma thread y).1 hyPath
  let common : Ladder.Stage kappa := max (max ix iy) closedIndex
  have hixCommon : ix ≤ common :=
    le_trans (le_max_left ix iy) (le_max_left (max ix iy) closedIndex)
  have hiyCommon : iy ≤ common :=
    le_trans (le_max_right ix iy) (le_max_left (max ix iy) closedIndex)
  have hclosedCommon : closedIndex ≤ common :=
    le_max_right (max ix iy) closedIndex
  obtain ⟨rx, hrx, hqxrx⟩ := C.grows hixCommon qx hqx
  obtain ⟨ry, hry, hqyry⟩ := C.grows hiyCommon qy hqy
  have hxrx : x ∈ rx.support :=
    Gamma.support_mono_of_extends hqxrx hxqx
  have hyry : y ∈ ry.support :=
    Gamma.support_mono_of_extends hqyry hyqy
  have hrxInitial : rx.initial = thread.1 :=
    (Gamma.extends_initial hqxrx).symm.trans hqxInitial
  have hryInitial : ry.initial = thread.1 :=
    (Gamma.extends_initial hqyry).symm.trans hqyInitial
  have hrxry : rx = ry :=
    DWeb.IsWarp.eq_of_initial_eq Gamma (C.isWarp common) hrx hry
      (hrxInitial.trans hryInitial.symm)
  have hstageCommon : C.stage common = L.warpAt common := by
    rw [hstage common]
    rfl
  have hrxWarp : rx ∈ L.warpAt common := by
    rw [← hstageCommon]
    exact hrx
  have hxClosedCommon : x ∈ closedStage common :=
    hmono hclosedCommon hxClosed
  obtain ⟨later, _hcommonLater, hrxClosed⟩ :=
    hcausal common rx hrxWarp ⟨x, hxrx, hxClosedCommon⟩
  exact Set.mem_iUnion.2 ⟨later, hrxClosed (hrxry ▸ hyry)⟩

#print axioms CausalStagePathClosure.of_sameStage
#print axioms CausalStagePathClosure.of_nextStage
#print axioms closedUnderPaths_limitWarp_iUnion_of_causalStages

end Erdos599.Blueprint.LinkageBlueprint
