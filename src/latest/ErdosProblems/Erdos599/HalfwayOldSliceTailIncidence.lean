/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayOldSliceMacroTransaction

/-!
# Exact incidence of the local macro carrier and the external target suffix

The closed set used by the old-stage transaction also contains contact and
reference bookkeeping, so it is neither necessary nor justified to require
the whole closed set to avoid the external target suffix.  The relation
compiler only needs avoidance by the actual canonical inside carrier.

That stronger-for-the-application statement follows without a new avoidance
hypothesis.  A canonical inside carrier is a subset of the carrier of the
spliced interval row, and that row meets the suffix exactly at its splice
vertex.  Conversely the splice vertex belongs to both the internal part of
the cut carrier and the suffix.  Thus the intersection is literally the
singleton splice point.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint

open DirectedPath _root_.Erdos599.Alternating

universe u

variable {V : Type u}
variable {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

namespace OldSliceMacroTransaction

variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {W : LinkageBlueprint Gamma C.selectedReference kappa}
variable {u : V} {P : OldSlice930IntervalTransaction C W u}

/-- The actual canonical inside carrier, rather than the larger auxiliary
closed set, has exactly one contact with the external target suffix. -/
theorem inside_vertexSet_tail_inter (M : OldSliceMacroTransaction P) :
    M.inside.insideFamily.vertexSet ∩ P.interval.tail.support =
      {P.interval.tail.start} := by
  apply Set.Subset.antisymm
  · intro x hx
    have hxCarrier : x ∈ insideCutCarrier C.selectedReference
        P.interval.splicedIntervalRow P.closed.closedSet := by
      rw [← M.inside.vertexSet_eq]
      exact hx.1
    have hxRow : x ∈ Gamma.vertexSet P.interval.splicedIntervalRow :=
      insideCutCarrier_subset_vertexSet C.selectedReference
        P.interval.splicedIntervalRow P.closed.closedSet hxCarrier
    have hxContact : x ∈
        Gamma.vertexSet P.interval.splicedIntervalRow ∩
          P.interval.tail.support := ⟨hxRow, hx.2⟩
    rw [P.interval.splicedIntervalRow_tail_inter] at hxContact
    exact hxContact
  · intro x hx
    have hxeq : x = P.interval.tail.start := Set.mem_singleton_iff.1 hx
    subst x
    refine ⟨?_, P.interval.tail.start_mem_support⟩
    rw [M.inside.vertexSet_eq]
    exact Or.inl (Or.inl ⟨
      P.interval.front_support_subset_splicedIntervalRow (by
        rw [P.interval.tail_start]
        exact P.interval.front.finish_mem_support),
      P.closed.splice_mem⟩)

/-- Off the splice vertex, the canonical inside carrier and the external
suffix are disjoint.  This is the form directly used in cross-uniqueness
proofs for adjoining suffix edges. -/
theorem inside_tail_disjoint_off_start (M : OldSliceMacroTransaction P) :
    Disjoint
      (M.inside.insideFamily.vertexSet \ {P.interval.tail.start})
      (P.interval.tail.support \ {P.interval.tail.start}) := by
  apply Set.disjoint_left.2
  rintro x ⟨hxInside, hxne⟩ ⟨hxTail, _⟩
  have hx : x ∈ M.inside.insideFamily.vertexSet ∩
      P.interval.tail.support := ⟨hxInside, hxTail⟩
  rw [M.inside_vertexSet_tail_inter] at hx
  exact hxne hx

end OldSliceMacroTransaction

#print axioms OldSliceMacroTransaction.inside_vertexSet_tail_inter
#print axioms OldSliceMacroTransaction.inside_tail_disjoint_off_start

end LinkageBlueprint
end Blueprint
end Erdos599
