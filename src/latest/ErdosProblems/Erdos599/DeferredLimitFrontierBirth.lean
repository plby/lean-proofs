/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.FiniteWarpLimitAttainment
import ErdosProblems.Erdos599.DeferredLimitHitClosure

/-!
# No new frontier vertex at a genuine deferred-ladder limit

A limit-frontier vertex is the terminal of a finite essential component.
Finite attainment places that component at an earlier stage. If it were
inessential there, persistence would contradict its essentiality at the
limit. Frontier chronology then puts the vertex on a cofinal earlier family.
-/

noncomputable section

open Set Cardinal Order

namespace Erdos599.DWeb.KappaLadder.Deferred

open _root_.Erdos599.DirectedPath Ladder

universe u v

variable {V : Type u} {G : DWeb V} {kappa : Cardinal.{u}}
variable {L : G.KappaLadder kappa}

/-- A vertex of a genuine limit frontier occurs on some strictly earlier
frontier. The terminal component is finite even when the full warp is not. -/
theorem exists_earlier_frontier_of_mem_limit_frontier
    (hL : HalfwayGeometry L) {a : Ladder.Stage kappa}
    (haLimit : Order.IsSuccLimit a.1) {x : V} (hx : x ∈ L.frontier a) :
    ∃ b : Ladder.Stage kappa, b < a ∧ x ∈ L.frontier b := by
  have hxEssential : x ∈ G.essential (G.terminalFrontier (L.warpAt a)) := by
    rwa [L.frontier_eq_essential_terminalFrontier hL.roofsSourceAtStages a] at hx
  obtain ⟨p, hp, hpTerminal⟩ := G.essential_subset _ hxEssential
  have hpEssential : p ∈ G.essentialWarpPart (L.warpAt a) :=
    ⟨hp, x, hpTerminal, hxEssential⟩
  have hpFinite : p.support.Finite := by
    cases p with
    | inl q => exact q.support_finite
    | inr r => simp [DWeb.terminal?, Path.terminal?] at hpTerminal
  let ae : Ladder.ExtendedStage kappa := Ladder.Stage.toExtended a
  obtain ⟨D, hstage, hpaths⟩ := hL.limitStages ae haLimit
  have hpD : p ∈ D.limitPaths G := by
    change p ∈ L.accumulated ae at hp
    rwa [hpaths] at hp
  obtain ⟨b, hpb⟩ :=
    D.exists_stage_of_mem_limitPaths_of_finite_support hpD hpFinite
  let bs : Ladder.Stage kappa :=
    ⟨b.1, show b.1 < kappa.ord from (show b.1 < a.1 from b.2).trans a.2⟩
  have hba : bs < a := b.2
  have hpBs : p ∈ L.warpAt bs := by
    rw [hstage b] at hpb
    exact hpb
  have hpBsEssential : p ∈ G.essentialWarpPart (L.warpAt bs) := by
    by_contra hpNotEssential
    have hpInessential := hL.inessentialPaths_mono_stage hba.le
      (show p ∈ G.inessentialPaths (L.warpAt bs) from ⟨hpBs, hpNotEssential⟩)
    exact hpInessential.2 hpEssential
  obtain ⟨_, y, hpy, hyEssential⟩ := hpBsEssential
  have hyx : y = x := Option.some.inj (hpy.symm.trans hpTerminal)
  refine ⟨bs, hba, ?_⟩
  rw [L.frontier_eq_essential_terminalFrontier hL.roofsSourceAtStages bs]
  exact hyx ▸ hyEssential

/-- A limit-frontier vertex lies on one member of any cofinal earlier
stage family. No monotonicity of the indexing function is needed. -/
theorem frontier_subset_iUnion_of_lub
    (hL : HalfwayGeometry L) {I : Type v}
    (stageIndex : I → Ladder.Stage kappa)
    {a : Ladder.Stage kappa} (haLimit : Order.IsSuccLimit a.1)
    (hindex : ∀ i, stageIndex i < a)
    (hLUB : IsLUB (Set.range stageIndex) a) :
    L.frontier a ⊆ ⋃ i, L.frontier (stageIndex i) := by
  intro x hx
  obtain ⟨b, hba, hxb⟩ := exists_earlier_frontier_of_mem_limit_frontier hL haLimit hx
  obtain ⟨_, ⟨i, rfl⟩, hbi⟩ := (lt_isLUB_iff hLUB).mp hba
  have hxRoof : x ∈ G.roof (L.frontier (stageIndex i)) :=
    G.roof_cut (hL.frontierChronology hbi) (G.subset_roof _ hxb)
  have hxNotStrict : x ∉ G.strictRoof (L.frontier (stageIndex i)) := by
    intro hxs
    exact Set.disjoint_left.1 (hL.strictFrontierChronology (hindex i)) hxs hx
  have hxEssential : x ∈ G.essential (L.frontier (stageIndex i)) := by
    by_contra hxNotEssential
    exact hxNotStrict ⟨hxRoof, hxNotEssential⟩
  rw [hL.frontiersEssential (stageIndex i)] at hxEssential
  exact Set.mem_iUnion.2 ⟨i, hxEssential⟩

/-- A path which hits the limit frontier already hits a frontier in any
cofinal earlier family. This applies to arbitrary ambient paths, not just
members of the limiting reference. -/
theorem path_hit_earlier_of_hit_limit
    (hL : HalfwayGeometry L) {I : Type v}
    (stageIndex : I → Ladder.Stage kappa)
    {a : Ladder.Stage kappa} (haLimit : Order.IsSuccLimit a.1)
    (hindex : ∀ i, stageIndex i < a)
    (hLUB : IsLUB (Set.range stageIndex) a)
    {p : G.DPath} (hhit : (p.support ∩ L.frontier a).Nonempty) :
    ∃ i, (p.support ∩ L.frontier (stageIndex i)).Nonempty := by
  obtain ⟨x, hxp, hxa⟩ := hhit
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.1
    (frontier_subset_iUnion_of_lub hL stageIndex haLimit hindex hLUB hxa)
  exact ⟨i, x, hxp, hxi⟩

#print axioms exists_earlier_frontier_of_mem_limit_frontier
#print axioms frontier_subset_iUnion_of_lub
#print axioms path_hit_earlier_of_hit_limit

end Erdos599.DWeb.KappaLadder.Deferred
