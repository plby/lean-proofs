/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingAssertion818Decoder
import ErdosProblems.Erdos599.GroundingEqualMaximalActiveSupply
import ErdosProblems.Erdos599.GroundingEqualCollisionOwners

/-!
# The collision cut of a maximal equal-branch route supply

The maximal decoded-compatible family omits one reserved auxiliary source
and avoids its complete collision carrier.  Its literal vertex carrier need
not be a separator: a new auxiliary path can avoid the selected supports but
decode into an already selected original-vertex carrier.  The correct cut is
therefore the union of the complete collision carriers of the selected
routes, together with the reserved collision carrier.

Maximality says that every source--target path either meets a selected route
or has decoded contact with one.  In both cases the collision-carrier lemma
makes the contact visible in this cut.  Assertion 8.18 then turns the cut
into a genuine separator of the original web.  No active-rooting assertion
is used in this file.
-/

noncomputable section

open Set

namespace Erdos599
namespace DWeb
namespace KappaLadder

open _root_.Erdos599.DirectedPath
open GroundingEqualActiveSelection

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

/-- The separator associated to a maximal decoded-compatible supply and one
reserved path. -/
def reservedMaximalCollisionCut
    {I : Type u} (J : PopularAuxiliary.Input Gamma I)
    (q : FinitePath J.lambda.graph)
    (P : Set (FinitePath J.lambda.graph)) : Set J.LV :=
  collisionCarrier J q ∪ collisionHull J P

/-- The maximal collision cut meets every auxiliary source--target path.

The only source excluded from the maximal family is `q.start`; it already
lies in the reserved collision carrier, so a path avoiding the cut starts
in the allowed source set.  The decoded-contact half of maximality is made
literal by `support_meets_collisionCarrier_of_decodedCarrier_overlap`. -/
theorem reservedMaximalCollisionCut_isSeparator
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (q : FinitePath (EqualInput L hL).lambda.graph)
    (M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
      (EqualInput L hL)
      ((EqualInput L hL).lambda.source \ {q.start})
      (collisionCarrier (EqualInput L hL) q)) :
    Popular.IsSeparator (EqualInput L hL).lambda
      (reservedMaximalCollisionCut (EqualInput L hL) q M.paths) := by
  intro p hpSource hpTarget
  by_cases hpReserved :
      (p.support ∩ collisionCarrier (EqualInput L hL) q).Nonempty
  · exact hpReserved.mono (Set.inter_subset_inter_right _ Set.subset_union_left)
  have hpAvoid :
      Disjoint p.support (collisionCarrier (EqualInput L hL) q) := by
    rw [Set.disjoint_iff_inter_eq_empty]
    exact Set.not_nonempty_iff_eq_empty.mp hpReserved
  have hpNe : p.start ≠ q.start := by
    intro hpq
    apply hpReserved
    refine ⟨p.start, p.start_mem_support, ?_⟩
    rw [hpq]
    exact Or.inl (Or.inl q.start_mem_support)
  have hpAllowed : p.start ∈
      (EqualInput L hL).lambda.source \ {q.start} := by
    exact ⟨hpSource, by simpa only [Set.mem_singleton_iff] using hpNe⟩
  rcases M.support_meets_or_decodedCarrier_meets
      p hpAllowed hpTarget hpAvoid with hpMeet | hpDecoded
  · obtain ⟨x, hxp, r, hrM, hxr⟩ := hpMeet
    refine ⟨x, hxp, Or.inr ?_⟩
    exact mem_collisionHull.2 ⟨r, hrM, Or.inl (Or.inl hxr)⟩
  · obtain ⟨r, hrM, hoverlap⟩ := hpDecoded
    have hrSource : r.start ∈ (EqualInput L hL).lambda.source :=
      (M.starts_in_allowed hrM).1
    obtain ⟨x, hxp, hxcollision⟩ :=
      support_meets_collisionCarrier_of_decodedCarrier_overlap
        (EqualInput L hL) (L.popularAuxiliary_proxyPathsFaithful hL)
        p r hpSource hrSource hoverlap
    refine ⟨x, hxp, Or.inr ?_⟩
    exact mem_collisionHull.2 ⟨r, hrM, hxcollision⟩

/-- Assertion 8.18 turns the maximal collision cut into a separator of the
original source from the original target. -/
theorem reservedMaximalCollisionCut_BB_isSeparator
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (q : FinitePath (EqualInput L hL).lambda.graph)
    (M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
      (EqualInput L hL)
      ((EqualInput L hL).lambda.source \ {q.start})
      (collisionCarrier (EqualInput L hL) q)) :
    Popular.IsSeparator Gamma
      (GroundingCut.BB (EqualInput L hL)
        (reservedMaximalCollisionCut (EqualInput L hL) q M.paths)) := by
  exact GroundingAssertion818Decoder.assertion8_18 L hL.legal _
    (reservedMaximalCollisionCut_isSeparator L hL q M)

/-- In the finite reserved-source case, the reserved old vertex itself is a
literal member of the decoded boundary.  Consequently omission of the
reserved original root is not a formal consequence of maximal avoidance:
the active absorption argument must provide a different root for this point
or use an inessential-component conclusion instead. -/
theorem old_reserved_start_mem_maximalCollisionCut_BB
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (q : FinitePath (EqualInput L hL).lambda.graph)
    (M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
      (EqualInput L hL)
      ((EqualInput L hL).lambda.source \ {q.start})
      (collisionCarrier (EqualInput L hL) q))
    {b : V} (hstart : q.start = .old b) :
    b ∈ GroundingCut.BB (EqualInput L hL)
      (reservedMaximalCollisionCut (EqualInput L hL) q M.paths) := by
  apply GroundingCut.CV_subset_BB
  change PopularAuxiliary.Input.LambdaVertex.old b ∈
    reservedMaximalCollisionCut (EqualInput L hL) q M.paths
  apply Or.inl
  apply Or.inl
  apply Or.inl
  simpa only [hstart] using q.start_mem_support

/-- Final compiler for the corrected equal-branch boundary.

The boundary is the `BB` set decoded from the maximal collision cut, rather
than the whole limiting terminal cut.  The latter may contain a hanging
component with no original-source root.  Assertion 8.18 supplies separation
of this `BB`; the active construction only has to stop an adjacent bi-unique
relation there and root every boundary point without the reserved source. -/
theorem ReservedGroundedParent.exists_hindrance_of_maximalCollisionCut
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {q : FinitePath (EqualInput L hL).lambda.graph}
    {hqsource : q.start ∈ (EqualInput L hL).lambda.source}
    (R : L.ReservedGroundedParent hL q hqsource)
    (M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
      (EqualInput L hL)
      ((EqualInput L hL).lambda.source \ {q.start})
      (collisionCarrier (EqualInput L hL) q))
    (E : Set (V × V))
    (hEadj : E ⊆ {e | Gamma.graph.Adj e.1 e.2})
    (hbi : Relator.BiUnique fun x y ↦ (x, y) ∈ E)
    (hnoOutgoing : ∀ b ∈
      GroundingCut.BB (EqualInput L hL)
        (reservedMaximalCollisionCut (EqualInput L hL) q M.paths),
      ¬ Alternating.HasOutgoing E b)
    (hroot : ∀ b ∈
      GroundingCut.BB (EqualInput L hL)
        (reservedMaximalCollisionCut (EqualInput L hL) q M.paths),
      ∃ a ∈ Gamma.source \ {R.parent.initial},
        Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E) a b) :
    ∃ H : Set Gamma.DPath, Gamma.IsHindrance H := by
  apply
    GroundingRootedReachabilityHindrance.exists_hindrance_of_rootedSeparatingAntichain
      E (Gamma.source \ {R.parent.initial})
      (GroundingCut.BB (EqualInput L hL)
        (reservedMaximalCollisionCut (EqualInput L hL) q M.paths))
      (unused := R.parent.initial)
  · exact hEadj
  · exact hbi
  · exact Set.sdiff_subset
  · exact isReachabilityAntichain_of_noOutgoing hnoOutgoing
  · exact hroot
  · exact reservedMaximalCollisionCut_BB_isSeparator L hL q M
  · exact R.parent_initial_source
  · simp

end KappaLadder
end DWeb
end Erdos599

#print axioms Erdos599.DWeb.KappaLadder.reservedMaximalCollisionCut_isSeparator
#print axioms Erdos599.DWeb.KappaLadder.reservedMaximalCollisionCut_BB_isSeparator
#print axioms Erdos599.DWeb.KappaLadder.old_reserved_start_mem_maximalCollisionCut_BB
#print axioms Erdos599.DWeb.KappaLadder.ReservedGroundedParent.exists_hindrance_of_maximalCollisionCut
