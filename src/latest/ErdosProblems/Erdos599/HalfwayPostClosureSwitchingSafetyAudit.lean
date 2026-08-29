/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayPostClosureCompressorAssignment

/-!
# Exact switching-safety obligations for the post-closure assignment

The produced post-closure route is safe for the finite outside reference and
internally safe for the global limiting reference.  Neither certificate is
the stronger switching-ready predicate: that predicate additionally requires
literal forward/reference edge disjointness and coverage of every forward
vertex contact by a backward link.

The equivalences below isolate those two obligations exactly.  They are
useful both positively (a construction supplying the occurrence-level marks
can close them) and negatively (endpoint or closing-set purity alone does not
silently manufacture them).
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Blueprint.LinkageBlueprint.PostClosureProducedAssignment

open _root_.Erdos599.DirectedPath _root_.Erdos599.Alternating

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}
variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {globalZ X0 : Set V} {z : V}
variable {R : DynamicMoving931GlobalClosure C globalZ X0}
variable {T : PostClosureIntervalTransaction C globalZ X0 z R}

variable (A : PostClosureProducedAssignment T)
variable (s : {x // x ∈ Gamma.initialSet A.fractured.outside.holes.paths \
  Gamma.initialSet (outsideReference T.intervalReference R.closedSet)})

/-- The actual assigned route is switching-safe for its finite local
outside reference exactly when the two switching-ready incidence conditions
hold.  Ordinary safeness is already supplied by the actual producer. -/
theorem assigned_isSwitchingSafe_local_iff :
    IsSwitchingSafe (outsideReference T.intervalReference R.closedSet)
        (A.assignment.produced.bracket.assignment.assigned s) ↔
      ForwardLinksOff (outsideReference T.intervalReference R.closedSet)
          (A.assignment.produced.bracket.assignment.assigned s) ∧
        ForwardVertexContactsCovered
          (outsideReference T.intervalReference R.closedSet)
          (A.assignment.produced.bracket.assignment.assigned s) := by
  constructor
  · intro h
    exact ⟨h.forwardLinksOff, h.contactsCovered⟩
  · rintro ⟨hoff, hcontacts⟩
    exact ⟨A.assignment.produced.bracket.assignment.safe s, hoff, hcontacts⟩

/-- Once the exposed endpoints avoid the limiting reference, the internally
safe actual route is genuinely safe for that full reference. -/
theorem assigned_isSafe_global_of_exposedEndpoints
    (hinitial :
      (A.assignment.produced.bracket.assignment.assigned s).initial ∉
        Gamma.vertexSet C.ladder.limitWarp)
    (hterminal : ∀ v,
      (A.assignment.produced.bracket.assignment.assigned s).terminal? = some v →
        v ∉ Gamma.vertexSet C.ladder.limitWarp) :
    IsSafe C.ladder.limitWarp
      (A.assignment.produced.bracket.assignment.assigned s) := by
  exact (A.assigned_internallySafe_global s).isSafe_of_exposedEndpoints
    hinitial hterminal

/-- Under the same endpoint condition, the only remaining global
switching-safety obligations are, again, forward-edge disjointness and
forward-contact coverage.  These concern the limiting reference itself and
do not follow from contact purity with the closing set. -/
theorem assigned_isSwitchingSafe_global_iff_of_exposedEndpoints
    (hinitial :
      (A.assignment.produced.bracket.assignment.assigned s).initial ∉
        Gamma.vertexSet C.ladder.limitWarp)
    (hterminal : ∀ v,
      (A.assignment.produced.bracket.assignment.assigned s).terminal? = some v →
        v ∉ Gamma.vertexSet C.ladder.limitWarp) :
    IsSwitchingSafe C.ladder.limitWarp
        (A.assignment.produced.bracket.assignment.assigned s) ↔
      ForwardLinksOff C.ladder.limitWarp
          (A.assignment.produced.bracket.assignment.assigned s) ∧
        ForwardVertexContactsCovered C.ladder.limitWarp
          (A.assignment.produced.bracket.assignment.assigned s) := by
  constructor
  · intro h
    exact ⟨h.forwardLinksOff, h.contactsCovered⟩
  · rintro ⟨hoff, hcontacts⟩
    exact ⟨A.assigned_isSafe_global_of_exposedEndpoints s hinitial hterminal,
      hoff, hcontacts⟩

end Erdos599.Blueprint.LinkageBlueprint.PostClosureProducedAssignment
