/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayPostClosureProducedAssignment
import ErdosProblems.Erdos599.FiniteTraceOwnerUniqueness

/-!
# Endpoint directions of actual post-closure assigned traces

No extra direction certificate needs to be assumed of an abstract run walk.
The actual assignment starts outside the local reference by boundary
alignment, and its finite terminal is outside that reference by leaving.
A backward end link would put that endpoint on the reference, so both
exposed finite end links, and the first infinite link, are forward.
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

theorem assigned_initial_not_mem_localReference :
    (A.assignment.produced.bracket.assignment.assigned s).initial ∉
      Gamma.vertexSet (outsideReference T.intervalReference R.closedSet) := by
  rw [A.assignment.produced.bracket.assignment.starts_at s]
  intro hsY
  exact s.2.2 ((T.boundaryData_of_interval_purity A.fractured).1.1
    ⟨s.2.1, hsY⟩)

/-- Finite actual traces start and finish with forward links. -/
theorem finite_endpoint_directions
    (Q : FiniteTrace Gamma.graph)
    (hQ : A.assignment.produced.bracket.assignment.assigned s = .finite Q) :
    Q.firstLink.direction = .forward ∧ Q.lastLink.direction = .forward := by
  have hsafe : IsSafe (outsideReference T.intervalReference R.closedSet)
      (.finite Q) := by
    rw [← hQ]
    exact A.assignment.produced.bracket.assignment.safe s
  have hinitial : Q.initial ∉
      Gamma.vertexSet (outsideReference T.intervalReference R.closedSet) := by
    simpa only [hQ, AltPath.initial] using A.assigned_initial_not_mem_localReference s
  have hterminal : Q.terminal ∉
      Gamma.vertexSet (outsideReference T.intervalReference R.closedSet) := by
    exact (A.assignment.produced.bracket.assignment.finite_terminal_mem s
      (by rw [hQ]; rfl)).2
  refine ⟨?_, Q.last_direction_eq_forward_of_terminal_not_mem hsafe hterminal⟩
  cases hdir : Q.firstLink.direction with
  | forward => rfl
  | backward =>
      obtain ⟨p, hp, hsub⟩ := hsafe.1.2.1 Q.firstLink
        Q.firstLink_mem_links hdir
      exact False.elim (hinitial ⟨p, hp, hsub.1 Q.firstLink.entry_mem_support⟩)

/-- Infinite actual traces likewise start with a forward link. -/
theorem infinite_first_direction
    (Q : InfiniteTrace Gamma.graph)
    (hQ : A.assignment.produced.bracket.assignment.assigned s = .infinite Q) :
    (Q.link 0).direction = .forward := by
  have hsafe : IsSafe (outsideReference T.intervalReference R.closedSet)
      (.infinite Q) := by
    rw [← hQ]
    exact A.assignment.produced.bracket.assignment.safe s
  have hinitial : Q.initial ∉
      Gamma.vertexSet (outsideReference T.intervalReference R.closedSet) := by
    simpa only [hQ, AltPath.initial] using A.assigned_initial_not_mem_localReference s
  cases hdir : (Q.link 0).direction with
  | forward => rfl
  | backward =>
      obtain ⟨p, hp, hsub⟩ := hsafe.1.2.1 (Q.link 0)
        Q.firstLink_mem_links hdir
      exact False.elim (hinitial ⟨p, hp, hsub.1 (Q.link 0).entry_mem_support⟩)

#print axioms assigned_initial_not_mem_localReference
#print axioms finite_endpoint_directions
#print axioms infinite_first_direction

end Erdos599.Blueprint.LinkageBlueprint.PostClosureProducedAssignment
