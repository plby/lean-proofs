/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingFreshFiniteAvoidance
import ErdosProblems.Erdos599.LadderLimitHitClosure

/-!
# The successor-emergence gap in the fresh grounding branch

The Section 7 bookkeeping chooses the record at `a` from the inessential
part of the *successor* warp.  In the genuinely fresh branch this record is
not inessential in the current warp at `a`.  Monotonicity of inessential
components shows more: it could not have been inessential at any earlier
ordinary stage either.

Thus the statement that this record has emerged by stage `a`, with
``emerged'' interpreted as membership in `inessentialPaths (warpAt b)`, is
false on the fresh branch.  The only unconditional bound is the successor
one.  This is the precise index gap that prevents the strict Section 8
chronology from disposing of `freshInessentialGroundStages`; a simultaneous
grounding argument must handle that branch rather than silently shifting the
record back one stage.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace DWeb
namespace KappaLadder

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

/-- A genuinely successor-new record was not inessential at any ordinary
stage at or before the stage at which it was selected. -/
theorem freshInessentialRecord_not_mem_inessential_warpAt_of_le
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsSplitLegal)
    {a : Ladder.Stage kappa} (ha : a ∈ L.freshInessentialRecordStages)
    {p : Gamma.DPath} (hchosen : L.chosen a = some p)
    {b : Ladder.Stage kappa} (hba : b ≤ a) :
    p ∉ Gamma.inessentialPaths (L.warpAt b) := by
  obtain ⟨q, hqChosen, _hqSuccessor, hqNotCurrent, _hqNotRecorded⟩ :=
    L.freshInessentialRecordStages_spec hlegal.validBookkeeping ha
  have hqp : q = p := Option.some.inj (hqChosen.symm.trans hchosen)
  subst q
  intro hpEarlier
  exact hqNotCurrent (hlegal.inessentialPaths_mono_stage hba hpEarlier)

/-- Groundedness does not repair the index shift: the canonical selected
fresh grounded record likewise has no current-stage emergence at or below
its source index. -/
theorem freshGroundRecordPath_not_mem_inessential_warpAt_of_le
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsSplitLegal)
    (a : L.freshInessentialGroundStages)
    {b : Ladder.Stage kappa} (hba : b ≤ a.1) :
    L.freshGroundRecordPath hlegal a ∉
      Gamma.inessentialPaths (L.warpAt b) := by
  exact L.freshInessentialRecord_not_mem_inessential_warpAt_of_le
    hlegal a.2.2 (L.chosen_freshGroundRecordPath hlegal a) hba

/-- Exact endpoint form of the gap at the named stage.  This is the formal
negation of replacing successor-inessentiality by current-inessentiality in
the fresh branch. -/
theorem freshGroundRecordPath_not_mem_currentInessential
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsSplitLegal)
    (a : L.freshInessentialGroundStages) :
    L.freshGroundRecordPath hlegal a ∉
      Gamma.inessentialPaths (L.warpAt a.1) :=
  L.freshGroundRecordPath_not_mem_inessential_warpAt_of_le
    hlegal a le_rfl

/-- Finite avoidance cannot supply the missing connector.  If a selected
fresh record is chosen disjoint from an ambient finite path, its initial
vertex is necessarily different from that path's start, so the reverse
record cannot be concatenated directly with the ambient path. -/
theorem freshGroundRecordPath_initial_ne_start_of_disjoint_path
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsSplitLegal)
    (a : L.freshInessentialGroundStages)
    (R : DirectedPath.FinitePath Gamma.graph)
    (hdisjoint : Disjoint
      (L.freshGroundRecordPath hlegal a).support R.support) :
    (L.freshGroundRecordPath hlegal a).initial ≠ R.start := by
  intro hjoin
  exact Set.disjoint_left.1 hdisjoint
    (L.freshGroundRecordPath hlegal a).initial_mem_support
    (hjoin ▸ R.start_mem_support)

end KappaLadder
end DWeb
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.freshInessentialRecord_not_mem_inessential_warpAt_of_le
#print axioms
  Erdos599.DWeb.KappaLadder.freshGroundRecordPath_not_mem_inessential_warpAt_of_le
#print axioms
  Erdos599.DWeb.KappaLadder.freshGroundRecordPath_initial_ne_start_of_disjoint_path
