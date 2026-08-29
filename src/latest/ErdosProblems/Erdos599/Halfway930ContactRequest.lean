/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.Halfway930ContactClosureSeed

/-!
# The unconditional public request of Assertion 9.30

For a scheduled terminal of the real part there are exactly the three cases
used in Assertion 9.30.  The identity case is already resolved at the current
slice.  In either nontrivial case this file makes the large-hammock choice and
stores the selected safe member together with simultaneous avoidance of the
entire contact-reserved carrier.

The output is deliberately a request for the coupled global transaction,
not a one-path switch.  Its associated seed contains the complete selected
alternating carrier and has cardinal at most `kappa`; the downstream closure,
assignment, and orientation can therefore process all contacts at once.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint

open DirectedPath Alternating Ladder

universe u

variable {V : Type u}
variable {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

/-- The genuine branch output of the public 9.30 hammock selection. -/
inductive Contact930Request
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (W : LinkageBlueprint Gamma C.selectedReference kappa)
    (u : V) : Type u
  | identity
      (whole_terminal : u ∈ W.terminalSet)
      (at_slice : u ∈ C.newSlice)
  | terminalOutside
      (whole_terminal : u ∈ W.terminalSet)
      (outside_slice : u ∉ C.newSlice)
      (path : AltPath Gamma.graph)
      (safe : IsSafe C.selectedReference path)
      (starts : path.initial = u)
      (infinite : path.IsInfinite)
      (avoids : Disjoint (path.vertexSet \ {u})
        (continuation930ContactReserved C W))
  | imaginarySuccessor
      (v : V)
      (edge_mem : (u, v) ∈ W.edgeSet)
      (imaginary : IsImaginaryEdge Gamma C.selectedReference kappa u v)
      (path : AltPath Gamma.graph)
      (safe : IsSafe C.selectedReference path)
      (starts : path.initial = u)
      (ends : HasEnd path (.vertex v))
      (avoids : Disjoint (hammockInterior u (.vertex v) path)
        (continuation930ContactReserved C W))

namespace Contact930Request

variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {W : LinkageBlueprint Gamma C.selectedReference kappa}
variable {u : V}

/-- The exact closure seed attached to a selected 9.30 branch. -/
def seed (R : Contact930Request C W u) : Set V :=
  match R with
  | .identity .. => continuation930ContactSeed C W
  | .terminalOutside _ _ Q .. => continuation930SelectedSeed C W Q
  | .imaginarySuccessor _ _ _ Q .. => continuation930SelectedSeed C W Q

/-- Every branch retains all public contact bookkeeping. -/
theorem contactSeed_subset (R : Contact930Request C W u) :
    continuation930ContactSeed C W ⊆ R.seed := by
  cases R with
  | identity => exact Set.Subset.rfl
  | terminalOutside => exact continuation930ContactSeed.contactSeed_subset_selected C W _
  | imaginarySuccessor => exact continuation930ContactSeed.contactSeed_subset_selected C W _

/-- The branch-specific seed is uniformly `kappa`-small. -/
theorem seed_mk_le (R : Contact930Request C W u)
    (hW : W.IsLinkageBlueprint C.newSlice C.closedSet C.persistent) :
    #R.seed ≤ kappa := by
  cases R with
  | identity => exact continuation930ContactSeed.mk_le C W hW
  | terminalOutside => exact continuation930ContactSeed.selected_mk_le C W _ hW
  | imaginarySuccessor => exact continuation930ContactSeed.selected_mk_le C W _ hW

/-- Marker-starting initials are swallowed in every branch seed. -/
theorem markerInitials_subset (R : Contact930Request C W u) :
    Gamma.initialSet
        (ladderReference.markerStarting
          (Gamma := Gamma) (L := C.ladder) (a := C.newStage)) ⊆
      R.seed :=
  (continuation930ContactSeed.markerInitials_subset C W).trans
    R.contactSeed_subset

/-- Complete reference components which meet the current blueprint are
swallowed in every branch seed. -/
theorem meetingReference_subset (R : Contact930Request C W u) :
    meetingVertices Gamma C.selectedReference W.vertexSet ⊆ R.seed :=
  (continuation930ContactSeed.meetingReference_subset C W).trans
    R.contactSeed_subset

end Contact930Request

/-- Assertion 9.30's branch selection is unconditional in the public club
stage context.  There is no ambient-source cardinal bound and no replacement
compiler hypothesis in this theorem. -/
theorem exists_contact930Request
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (W : LinkageBlueprint Gamma C.selectedReference kappa)
    {u : V}
    (hW : W.IsLinkageBlueprint C.newSlice C.closedSet C.persistent)
    (hpersistent : C.persistent ⊆ C.newSlice)
    (hu : u ∈ W.realPart.terminals) :
    Nonempty (Contact930Request C W u) := by
  rcases real_terminal_is_terminal_or_has_imaginary_edge_mem hu with
      huterminal | ⟨v, huv, himaginary⟩
  · by_cases huSlice : u ∈ C.newSlice
    · exact ⟨Contact930Request.identity huterminal huSlice⟩
    · obtain ⟨Q, hsafe, hstart, hinfinite, havoid⟩ :=
        continuation930ContactSeed.exists_terminalOutside_member_avoiding_reserved
          C W hW hpersistent huterminal huSlice
      exact ⟨Contact930Request.terminalOutside huterminal huSlice Q
        hsafe hstart hinfinite havoid⟩
  · obtain ⟨Q, hsafe, hstart, hend, havoid⟩ :=
      continuation930ContactSeed.exists_imaginarySuccessor_member_avoiding_reserved
        C W hW himaginary
    exact ⟨Contact930Request.imaginarySuccessor v huv himaginary Q
      hsafe hstart hend havoid⟩

end LinkageBlueprint
end Blueprint
end Erdos599
