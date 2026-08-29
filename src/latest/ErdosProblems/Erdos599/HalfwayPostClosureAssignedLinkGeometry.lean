/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayPostClosureProducedAssignment

/-!
# Literal link geometry of the post-closure assignment

Backward links lie on the pruned interval reference and hence avoid the
closing set.  Forward links lie on the fractured outside edge warp and
hence retain literal edges of the uncut ambient interval family.  These are
the two concrete inputs used by contact segmentation and endpoint
eligibility.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Blueprint.LinkageBlueprint

open _root_.Erdos599.DirectedPath _root_.Erdos599.Alternating

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}
variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {globalZ X0 : Set V} {z : V}
variable {R : DynamicMoving931GlobalClosure C globalZ X0}
variable {T : PostClosureIntervalTransaction C globalZ X0 z R}

namespace PostClosureProducedAssignment

theorem assigned_backwardLink_disjoint_closedSet
    (A : PostClosureProducedAssignment T)
    (s : {x // x ∈ Gamma.initialSet A.fractured.outside.holes.paths \
      Gamma.initialSet (outsideReference T.intervalReference R.closedSet)})
    (l : Link Gamma.graph)
    (hl : l ∈ (A.assignment.produced.bracket.assignment.assigned s).links)
    (hdir : l.direction = .backward) :
    Disjoint l.path.support R.closedSet := by
  have hback :=
    (A.assignment.produced.bracket.bracket_safe s).isAlternating.2.1
      l hl hdir
  rcases hback with ⟨p, hp, hsub⟩
  exact hp.2.mono_left hsub.1

theorem assigned_forwardLink_edges_subset_intervalFamily
    (A : PostClosureProducedAssignment T)
    (s : {x // x ∈ Gamma.initialSet A.fractured.outside.holes.paths \
      Gamma.initialSet (outsideReference T.intervalReference R.closedSet)})
    (l : Link Gamma.graph)
    (hl : l ∈ (A.assignment.produced.bracket.assignment.assigned s).links)
    (hdir : l.direction = .forward) :
    l.path.edgeSet ⊆ familyEdges T.interval.ambientInterval := by
  have hfragment :=
    (A.assignment.produced.bracket.bracket_safe s).isBracketAlternating.2
      l hl hdir
  have hfamily : l.path.edgeSet ⊆
      familyEdges A.fractured.outside.holes.edgeWarp :=
    edgeSet_subset_familyEdges_of_isFragmentOf hfragment
  rw [A.fractured.outside.edgeWarp_familyEdges] at hfamily
  exact hfamily.trans
    (outsideFamilyEdges_subset T.interval.ambientInterval R.closedSet)

end PostClosureProducedAssignment
end Erdos599.Blueprint.LinkageBlueprint

#print axioms Erdos599.Blueprint.LinkageBlueprint.PostClosureProducedAssignment.assigned_backwardLink_disjoint_closedSet
#print axioms Erdos599.Blueprint.LinkageBlueprint.PostClosureProducedAssignment.assigned_forwardLink_edges_subset_intervalFamily
