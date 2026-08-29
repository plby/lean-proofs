/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayPostClosureAssignedDirections

/-!
# Why the local post-closure assignment cannot simply be globalized

The assignment used by the current post-closure compressor is safe for the
finite interval reference outside the closing set.  Its nontrivial paths
therefore start forwards, and finite paths also finish forwards.  Source
Definition 4.2 then shows that a limiting-reference owner at either exposed
endpoint is a genuine obstruction to safeness for the limiting reference.

These lemmas rule out the tempting but false repair of treating the existing
endpoint-covered classification as a globally safe whole-route assignment.
They also isolate the precise missing source input: the assignment must be
chosen against the limiting reference itself (and may then start or finish
backwards when an exposed endpoint is covered), rather than obtained by a
proof-only cast of the local assignment.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Blueprint.LinkageBlueprint.PostClosureProducedAssignment

open _root_.Erdos599.DirectedPath _root_.Erdos599.Alternating

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}
variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {globalZ seed : Set V} {z : V}
variable {R : DynamicMoving931GlobalClosure C globalZ seed}
variable {T : PostClosureIntervalTransaction C globalZ seed z R}

variable (A : PostClosureProducedAssignment T)
variable (s : {x // x ∈ Gamma.initialSet A.fractured.outside.holes.paths \
  Gamma.initialSet (outsideReference T.intervalReference R.closedSet)})

/-- A finite locally assigned path whose initial vertex is covered by the
limiting reference is not safe for that reference. -/
theorem finite_not_isSafe_limitWarp_of_initial_covered
    (Q : FiniteTrace Gamma.graph)
    (hQ : A.assignment.produced.bracket.assignment.assigned s = .finite Q)
    (hcovered : Q.initial ∈ Gamma.vertexSet C.ladder.limitWarp) :
    ¬ IsSafe C.ladder.limitWarp (.finite Q) := by
  intro hsafe
  have hforward :
      (AltPath.finite Q).firstDirection? = some .forward := by
    change some Q.firstLink.direction = some .forward
    rw [(A.finite_endpoint_directions s Q hQ).1]
  exact (hsafe.isAlternating.2.2.1 hforward) hcovered

/-- A finite locally assigned path whose terminal vertex is covered by the
limiting reference is not safe for that reference. -/
theorem finite_not_isSafe_limitWarp_of_terminal_covered
    (Q : FiniteTrace Gamma.graph)
    (hQ : A.assignment.produced.bracket.assignment.assigned s = .finite Q)
    (hcovered : Q.terminal ∈ Gamma.vertexSet C.ladder.limitWarp) :
    ¬ IsSafe C.ladder.limitWarp (.finite Q) := by
  intro hsafe
  have hforward :
      (AltPath.finite Q).lastDirection? = some .forward := by
    change some Q.lastLink.direction = some .forward
    rw [(A.finite_endpoint_directions s Q hQ).2]
  exact (hsafe.isAlternating.2.2.2 Q.terminal rfl hforward) hcovered

/-- The same initial-endpoint obstruction applies to an infinite locally
assigned path. -/
theorem infinite_not_isSafe_limitWarp_of_initial_covered
    (Q : InfiniteTrace Gamma.graph)
    (hQ : A.assignment.produced.bracket.assignment.assigned s = .infinite Q)
    (hcovered : Q.initial ∈ Gamma.vertexSet C.ladder.limitWarp) :
    ¬ IsSafe C.ladder.limitWarp (.infinite Q) := by
  intro hsafe
  have hforward :
      (AltPath.infinite Q).firstDirection? = some .forward := by
    change some (Q.link 0).direction = some .forward
    rw [A.infinite_first_direction s Q hQ]
  exact (hsafe.isAlternating.2.2.1 hforward) hcovered

/-- For an actual finite local assignment, the two exposed endpoint
conditions are not merely necessary: they are exactly what remains to
upgrade the already proved global internal safeness to global safeness. -/
theorem finite_isSafe_limitWarp_iff_endpoints_uncovered
    (Q : FiniteTrace Gamma.graph)
    (hQ : A.assignment.produced.bracket.assignment.assigned s = .finite Q) :
    IsSafe C.ladder.limitWarp (.finite Q) ↔
      Q.initial ∉ Gamma.vertexSet C.ladder.limitWarp ∧
        Q.terminal ∉ Gamma.vertexSet C.ladder.limitWarp := by
  constructor
  · intro hsafe
    have hdirections := A.finite_endpoint_directions s Q hQ
    constructor
    · apply hsafe.isAlternating.2.2.1
      change some Q.firstLink.direction = some .forward
      rw [hdirections.1]
    · apply hsafe.isAlternating.2.2.2 Q.terminal rfl
      change some Q.lastLink.direction = some .forward
      rw [hdirections.2]
  · rintro ⟨hinitial, hterminal⟩
    have hinternal := A.assigned_internallySafe_global s
    rw [hQ] at hinternal
    apply hinternal.isSafe_of_exposedEndpoints hinitial
    intro v hv
    have hvq : v = Q.terminal := Option.some.inj hv.symm
    simpa only [hvq] using hterminal

/-- The infinite case has only the initial exposed-endpoint condition. -/
theorem infinite_isSafe_limitWarp_iff_initial_uncovered
    (Q : InfiniteTrace Gamma.graph)
    (hQ : A.assignment.produced.bracket.assignment.assigned s = .infinite Q) :
    IsSafe C.ladder.limitWarp (.infinite Q) ↔
      Q.initial ∉ Gamma.vertexSet C.ladder.limitWarp := by
  constructor
  · intro hsafe
    apply hsafe.isAlternating.2.2.1
    change some (Q.link 0).direction = some .forward
    rw [A.infinite_first_direction s Q hQ]
  · intro hinitial
    have hinternal := A.assigned_internallySafe_global s
    rw [hQ] at hinternal
    apply hinternal.isSafe_of_exposedEndpoints hinitial
    intro v hv
    simp at hv

#print axioms finite_not_isSafe_limitWarp_of_initial_covered
#print axioms finite_not_isSafe_limitWarp_of_terminal_covered
#print axioms infinite_not_isSafe_limitWarp_of_initial_covered
#print axioms finite_isSafe_limitWarp_iff_endpoints_uncovered
#print axioms infinite_isSafe_limitWarp_iff_initial_uncovered

end Erdos599.Blueprint.LinkageBlueprint.PostClosureProducedAssignment
