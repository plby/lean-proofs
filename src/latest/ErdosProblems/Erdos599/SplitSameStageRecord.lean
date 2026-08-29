/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitHindranceGrounding

/-!
# Geometry of a genuine same-stage record

For the canonical successor-normalized ladder, a selected record whose
initial vertex is the marker born at that same stage is forced to be the
inserted singleton marker component.  It cannot belong to the arrow part:
an arrow component has the same initial vertex as an old accumulated path,
whereas the canonical marker lies outside the old accumulated vertex set.

This does not make the same-stage branch empty: the singleton marker itself
may be inessential.  The lemma identifies precisely the component which the
global Section 8 switch must handle.
-/

noncomputable section

open Set

namespace Erdos599
namespace DWeb
namespace KappaLadder

universe u

variable {V : Type u} {G : DWeb V} {kappa : Cardinal.{u}}

/-- Split legality has the same exhaustive successor-component geometry as
legacy legality; hanging provenance is irrelevant to this projection. -/
theorem IsSplitLegal.successorComponentProvenance
    {L : G.KappaLadder kappa} (hL : L.IsSplitLegal)
    (a : Ladder.Stage kappa) (q : G.DPath)
    (hq : q ∈ L.successorWarp a) :
    (∃ p ∈ L.warpAt a, L.IsRungArrowPair a p q) ∨
      ∃ y : V, L.marker a = some y ∧ q = G.trivialPath y := by
  rw [(hL.exactSuccessorArrows a).2] at hq
  rcases hq with hq | hq
  · exact Or.inl ((hL.exactSuccessorArrows a).1.2 q hq)
  · cases hmarker : L.marker a with
    | none => simp [markerPathSet, hmarker] at hq
    | some y =>
        refine Or.inr ⟨y, rfl, ?_⟩
        simpa [markerPathSet, hmarker] using hq

/-- In the actual canonical ladder, a successor member beginning at the
current marker is exactly the singleton marker component. -/
theorem canonicalLadder_successorMember_eq_trivialPath_of_initial_eq_marker
    (preferred : Ladder.Stage kappa → Option V)
    (hkappa : kappa.IsRegular) (huncountable : Cardinal.aleph0 < kappa)
    (hNoEnter : G.NoEdgeEnters G.source)
    {a : Ladder.Stage kappa} {p : G.DPath} {y : V}
    (hp : p ∈ (canonicalLadder G kappa preferred).successorWarp a)
    (hy : (canonicalLadder G kappa preferred).marker a = some y)
    (hpInitial : p.initial = y) :
    p = G.trivialPath y := by
  let L := canonicalLadder G kappa preferred
  have hlegal : L.IsSplitLegal :=
    canonicalLadder_isSplitLegal preferred hkappa huncountable hNoEnter
  rcases hlegal.successorComponentProvenance a p hp with
      ⟨q, hq, hqp⟩ | ⟨z, hz, hpz⟩
  · have hqInitial : q.initial = p.initial :=
      G.extends_initial hqp.extends
    have hyOutside : y ∉ G.vertexSet (L.warpAt a) :=
      canonicalLadder_marker_not_mem_currentVertexSet
        preferred hNoEnter a y hy
    exact False.elim <| hyOutside ⟨q, hq, by
      rw [← hpInitial, ← hqInitial]
      exact q.initial_mem_support⟩
  · have hzy : z = y := Option.some.inj (hz.symm.trans hy)
    simpa [hzy] using hpz

/-- Every genuine same-stage hanging record of the canonical ladder is the
singleton path at its current marker. -/
theorem canonicalLadder_freshSameStage_record_eq_trivialPath
    (preferred : Ladder.Stage kappa → Option V)
    (hkappa : kappa.IsRegular) (huncountable : Cardinal.aleph0 < kappa)
    (hNoEnter : G.NoEdgeEnters G.source)
    {a : Ladder.Stage kappa}
    (ha : a ∈
      (canonicalLadder G kappa preferred).freshSameStageHangingStages) :
    ∃ y : V,
      (canonicalLadder G kappa preferred).marker a = some y ∧
      (canonicalLadder G kappa preferred).chosen a =
        some (G.trivialPath y) := by
  let L := canonicalLadder G kappa preferred
  obtain ⟨p, _haHanging, hpChosen, _hpFresh, hmarker⟩ := ha
  have hlegal : L.IsSplitLegal :=
    canonicalLadder_isSplitLegal preferred hkappa huncountable hNoEnter
  have hpSuccessor : p ∈ L.successorWarp a :=
    (L.bookkeeping.chosen_mem_available hlegal.validBookkeeping hpChosen).1.1
  have hpEq : p = G.trivialPath p.initial :=
    canonicalLadder_successorMember_eq_trivialPath_of_initial_eq_marker
      preferred hkappa huncountable hNoEnter hpSuccessor hmarker rfl
  exact ⟨p.initial, hmarker, hpChosen.trans (congrArg Option.some hpEq)⟩

end KappaLadder
end DWeb
end Erdos599
