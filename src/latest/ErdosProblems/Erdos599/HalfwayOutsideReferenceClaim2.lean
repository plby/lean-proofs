/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayOutsideReference

/-!
# The Claim 2 handoff for the pruned outside reference

Closing under the later row makes its literal outside fragments disjoint
from the closed set.  `HalfwayOutsideReference` applies Theorem 4.12 against
the subwarp of reference paths which are also disjoint from the closed set,
then lifts the resulting assignment to the full reference warp.

This file records the exact downstream handoff.  Although the cut boundary
is stated for the pruned reference, every source in the full-reference
assignment domain is still an uncovered pruned-reference source, and every
finite target is still an uncovered pruned-reference terminal.  Thus the
ordinary source/terminal hammock eligibility statements hold.  Together
with whole-trace avoidance, they give the literal `AssignmentClosureContext`
required by Claim 2, and hence the finite imaginary-edge and infinite
popularity conclusions.

No full-reference `OutsideCutBoundary` is asserted: its `reference_initials`
field is false when a reference component has been swallowed by the closed
set.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint

open DirectedPath _root_.Erdos599.Alternating

universe u

variable {V : Type u}
variable {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}
variable {W : Set Gamma.DPath} {X before innerRoof outerRoof : Set V}

namespace OutsideCutBoundary

/-- A full-reference assignment source is also an uncovered source for the
pruned outside reference, so it inherits the source-side hammock location. -/
theorem fullReference_uncoveredInitial_location
    (B : OutsideCutBoundary (Y := outsideReference Y X)
      W X before innerRoof outerRoof)
    (F : OutsideFracturedWarp W X) :
    Gamma.initialSet F.holes.paths \ Gamma.initialSet Y ⊆
      before ∩ innerRoof := by
  intro x hx
  apply B.fractured_uncoveredInitial_location F
  refine ⟨hx.1, ?_⟩
  intro hxout
  exact hx.2 (initialSet_outsideReference_subset hxout)

/-- A finite target uncovered by the full reference is also uncovered by
the pruned outside reference, so it inherits the target-side location. -/
theorem fullReference_uncoveredTerminal_location
    (B : OutsideCutBoundary (Y := outsideReference Y X)
      W X before innerRoof outerRoof)
    (F : OutsideFracturedWarp W X) :
    Gamma.terminalFrontier F.holes.paths \ Gamma.vertexSet Y ⊆
      before ∩ outerRoof := by
  intro x hx
  apply B.fractured_uncoveredTerminal_location F
  refine ⟨hx.1, ?_⟩
  intro hxout
  exact hx.2 (vertexSet_outsideReference_subset hxout)

end OutsideCutBoundary

/-- The actual output of the pruned-reference Theorem 4.12 application,
retaining both its bracket provenance and the full-reference Claim 2
context.  Every field below is constructed; there is no endpoint-clean or
global-switching hypothesis hidden in this package. -/
structure OutsideReferenceClaim2Assignment
    (F : OutsideFracturedWarp W X) where
  bracket : FracturedAssignmentPeel.BracketFracturedAssignment F.holes Y
  avoids : ∀ s, Disjoint (bracket.assignment.assigned s).vertexSet X
  closure : AssignmentClosureContext bracket.assignment X
    before innerRoof outerRoof

namespace OutsideReferenceClaim2Assignment

variable {F : OutsideFracturedWarp W X}

/-- Forget the bracket provenance after Claim 2 has been prepared.  The
returned object is the old literal endpoint-clean assignment, but it is not
paired with the impossible full-reference cut boundary. -/
def outsideAssignment
    (A : OutsideReferenceClaim2Assignment
      (Y := Y) (before := before) (innerRoof := innerRoof)
      (outerRoof := outerRoof) F) :
    OutsideAssignment (Y := Y) F :=
  OutsideAssignment.ofAssignmentClosureContext A.bracket.assignment A.closure

@[simp] theorem outsideAssignment_assignment
    (A : OutsideReferenceClaim2Assignment
      (Y := Y) (before := before) (innerRoof := innerRoof)
      (outerRoof := outerRoof) F) :
    A.outsideAssignment.assignment = A.bracket.assignment := rfl

/-- Claim 2 classifies every finite assigned endpoint as an imaginary edge
and every infinite assigned source as popular. -/
theorem classified
    {persistent : Set V}
    (A : OutsideReferenceClaim2Assignment
      (Y := Y) (before := before) (innerRoof := innerRoof)
      (outerRoof := outerRoof) F)
    (hclosed : HammockClosedUpTo Gamma Y X
      before innerRoof outerRoof kappa) :
    (∀ s v, (A.bracket.assignment.assigned s).terminal? = some v →
        IsImaginaryEdge Gamma Y kappa s.1 v) ∧
      (∀ s, (A.bracket.assignment.assigned s).IsInfinite →
        IsPopular Gamma Y persistent kappa s.1) :=
  classify_simultaneousAssignment_of_closed hclosed
    A.bracket.assignment A.closure

end OutsideReferenceClaim2Assignment

namespace OutsideSplitWarp.SplitProjectedOutsideFracturedWarp

/-- End-to-end handoff from the pruned-reference boundary to the exact
full-reference Claim 2 context. -/
theorem exists_outsideReferenceClaim2Assignment
    (F : OutsideSplitWarp.SplitProjectedOutsideFracturedWarp W X)
    (hWclosed : ClosedUnderPaths Gamma W X)
    (hYclosed : ClosedUnderPaths Gamma Y X)
    (hY : Gamma.IsWarp Y)
    (hYfinite : Gamma.HasFiniteCharacter Y)
    (hboundary : OutsideCutBoundary
      (Y := outsideReference Y X) W X before innerRoof outerRoof) :
    Nonempty (OutsideReferenceClaim2Assignment
      (Y := Y) (before := before) (innerRoof := innerRoof)
      (outerRoof := outerRoof) F.outside) := by
  obtain ⟨B, havoid⟩ := F.exists_fullReferenceBracketAssignment
    hWclosed hYclosed hY hYfinite hboundary
  have heligibleFinite : ∀ s v,
      (B.assignment.assigned s).terminal? = some v →
        HammockEligible before innerRoof outerRoof s.1 (.vertex v) := by
    intro s v hterminal
    refine ⟨hboundary.fullReference_uncoveredInitial_location
      F.outside s.property, ?_⟩
    exact hboundary.fullReference_uncoveredTerminal_location F.outside
      (B.assignment.finite_terminal_mem s hterminal)
  have heligibleInfinite : ∀ s, (B.assignment.assigned s).IsInfinite →
      HammockEligible before innerRoof outerRoof s.1 .infinity := by
    intro s _hinfinite
    exact ⟨hboundary.fullReference_uncoveredInitial_location
      F.outside s.property, trivial⟩
  exact ⟨{
    bracket := B
    avoids := havoid
    closure := AssignmentClosureContext.of_disjoint B.assignment havoid
      heligibleFinite heligibleInfinite }⟩

/-- The direct Claim 2 conclusion, retaining the assignment which realizes
the classified endpoint map. -/
theorem exists_classifiedFullReferenceAssignment
    {persistent : Set V}
    (F : OutsideSplitWarp.SplitProjectedOutsideFracturedWarp W X)
    (hWclosed : ClosedUnderPaths Gamma W X)
    (hYclosed : ClosedUnderPaths Gamma Y X)
    (hY : Gamma.IsWarp Y)
    (hYfinite : Gamma.HasFiniteCharacter Y)
    (hboundary : OutsideCutBoundary
      (Y := outsideReference Y X) W X before innerRoof outerRoof)
    (hclosed : HammockClosedUpTo Gamma Y X
      before innerRoof outerRoof kappa) :
    ∃ A : OutsideReferenceClaim2Assignment
        (Y := Y) (before := before) (innerRoof := innerRoof)
        (outerRoof := outerRoof) F.outside,
      (∀ s v, (A.bracket.assignment.assigned s).terminal? = some v →
          IsImaginaryEdge Gamma Y kappa s.1 v) ∧
        (∀ s, (A.bracket.assignment.assigned s).IsInfinite →
          IsPopular Gamma Y persistent kappa s.1) := by
  let A := (F.exists_outsideReferenceClaim2Assignment hWclosed hYclosed
    hY hYfinite hboundary).some
  exact ⟨A, A.classified hclosed⟩

end OutsideSplitWarp.SplitProjectedOutsideFracturedWarp

end LinkageBlueprint
end Blueprint
end Erdos599
