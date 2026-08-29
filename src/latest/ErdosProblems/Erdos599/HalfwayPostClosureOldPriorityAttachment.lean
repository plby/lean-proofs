/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayPostClosureClosedEdgeBiunique
import ErdosProblems.Erdos599.RootReachableBlueprint

/-!
# Old-priority attachment for the actual post-closure relation

The source diamond never replaces an outgoing edge of the old warp.  Before
the later family has been packaged as a star-compatible warp, the same rule
can be imposed directly on its edge relation: discard a fresh edge whenever
its tail already has an old outgoing edge.

The actual closed post-closure edges never enter the old carrier.  Hence this
one-sided filtering is enough to make their union with the old edge relation
biunique.  This file proves only that exact relation geometry; source and sink
accounting for the newly rooted components remains separate.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Blueprint.LinkageBlueprint.PostClosureMacroCompressorAssignment

open DirectedPath _root_.Erdos599.Alternating

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}
variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {globalZ seed : Set V} {z : V}
variable {Rlimit : LimitMoving931GlobalClosure C globalZ seed}
variable {T : PostClosureIntervalTransaction C globalZ seed z
  Rlimit.toDynamicMoving931GlobalClosure}

/-- The fresh closed edges whose tail has no outgoing edge in the current
blueprint.  This is the edge-level old-priority rule of the source diamond. -/
def oldPriorityFreshEdges
    (A : PostClosureMacroCompressorAssignment T)
    (current : LinkageBlueprint Gamma C.ladder.limitWarp kappa) :
    Set (V × V) :=
  {e | e ∈ A.toPostClosureCompressorAssignment.actualPostClosureClosedEdges ∧
    ¬ ∃ v, (e.1, v) ∈ current.edgeSet}

/-- The current edge relation with the old-priority fresh attachment. -/
def oldPriorityAttachedEdges
    (A : PostClosureMacroCompressorAssignment T)
    (current : LinkageBlueprint Gamma C.ladder.limitWarp kappa) :
    Set (V × V) :=
  current.edgeSet ∪ A.oldPriorityFreshEdges current

theorem oldPriorityFreshEdges_subset_closedEdges
    (A : PostClosureMacroCompressorAssignment T)
    (current : LinkageBlueprint Gamma C.ladder.limitWarp kappa) :
    A.oldPriorityFreshEdges current ⊆
      A.toPostClosureCompressorAssignment.actualPostClosureClosedEdges := by
  intro e he
  exact he.1

theorem oldPriorityFreshEdges_noOldOutgoing
    (A : PostClosureMacroCompressorAssignment T)
    (current : LinkageBlueprint Gamma C.ladder.limitWarp kappa)
    {x y : V} (hxy : (x, y) ∈ A.oldPriorityFreshEdges current) :
    ¬ ∃ v, (x, v) ∈ current.edgeSet :=
  hxy.2

theorem oldPriorityFreshEdge_head_not_mem_of_vertices_roofed
    (A : PostClosureMacroCompressorAssignment T)
    (current : LinkageBlueprint Gamma C.ladder.limitWarp kappa)
    (hroof : current.vertexSet ⊆ Gamma.roof C.newSlice)
    {x y : V} (hxy : (x, y) ∈ A.oldPriorityFreshEdges current) :
    y ∉ current.vertexSet := by
  intro hy
  exact A.toPostClosureCompressorAssignment
    |>.actualPostClosureClosedEdge_head_not_mem_currentRoof hxy.1 (hroof hy)

theorem oldPriorityFreshEdge_head_not_mem_current
    (A : PostClosureMacroCompressorAssignment T)
    {currentClosed : Set V}
    (current : LinkageBlueprint Gamma C.ladder.limitWarp kappa)
    (hcurrent : current.IsLinkageBlueprint
      C.newSlice currentClosed C.persistent)
    {x y : V} (hxy : (x, y) ∈ A.oldPriorityFreshEdges current) :
    y ∉ current.vertexSet := by
  exact A.oldPriorityFreshEdge_head_not_mem_of_vertices_roofed
    current hcurrent.vertices_roofed hxy

theorem oldPriorityAttachedEdges_subset_imaginaryGraph
    (A : PostClosureMacroCompressorAssignment T)
    (current : LinkageBlueprint Gamma C.ladder.limitWarp kappa) :
    A.oldPriorityAttachedEdges current ⊆
      {e | (imaginaryGraph Gamma C.ladder.limitWarp kappa).Adj e.1 e.2} := by
  intro e he
  rcases he with hold | hfresh
  · change e ∈ familyEdges
      (Γ := imaginaryWeb Gamma C.ladder.limitWarp kappa) current.paths at hold
    exact familyEdges_subset_adj
      (Γ := imaginaryWeb Gamma C.ladder.limitWarp kappa) current.paths hold
  · exact A.toPostClosureCompressorAssignment
      |>.actualPostClosureClosedEdges_subset_imaginaryGraph hfresh.1

theorem current_edgeSet_subset_oldPriorityAttachedEdges
    (A : PostClosureMacroCompressorAssignment T)
    (current : LinkageBlueprint Gamma C.ladder.limitWarp kappa) :
    current.edgeSet ⊆ A.oldPriorityAttachedEdges current :=
  Set.subset_union_left

/-- No fresh edge shares a head with a current edge: a current edge head is
an old-carrier vertex, while every actual fresh edge enters outside that
carrier. -/
theorem current_oldPriorityFresh_no_common_head
    (A : PostClosureMacroCompressorAssignment T)
    {currentClosed : Set V}
    (current : LinkageBlueprint Gamma C.ladder.limitWarp kappa)
    (hcurrent : current.IsLinkageBlueprint
      C.newSlice currentClosed C.persistent)
    {a b y : V}
    (hay : (a, y) ∈ current.edgeSet)
    (hby : (b, y) ∈ A.oldPriorityFreshEdges current) : False := by
  apply A.oldPriorityFreshEdge_head_not_mem_current current hcurrent hby
  change (a, y) ∈ familyEdges
    (Γ := imaginaryWeb Gamma C.ladder.limitWarp kappa) current.paths at hay
  exact (familyEdges_subset_vertexSet_prod
    (Γ := imaginaryWeb Gamma C.ladder.limitWarp kappa) current.paths hay).2

theorem current_oldPriorityFresh_no_common_head_of_vertices_roofed
    (A : PostClosureMacroCompressorAssignment T)
    (current : LinkageBlueprint Gamma C.ladder.limitWarp kappa)
    (hroof : current.vertexSet ⊆ Gamma.roof C.newSlice)
    {a b y : V}
    (hay : (a, y) ∈ current.edgeSet)
    (hby : (b, y) ∈ A.oldPriorityFreshEdges current) : False := by
  apply A.oldPriorityFreshEdge_head_not_mem_of_vertices_roofed current hroof hby
  change (a, y) ∈ familyEdges
    (Γ := imaginaryWeb Gamma C.ladder.limitWarp kappa) current.paths at hay
  exact (familyEdges_subset_vertexSet_prod
    (Γ := imaginaryWeb Gamma C.ladder.limitWarp kappa) current.paths hay).2

/-- No fresh edge shares a tail with a current edge, by definition of the
old-priority filter. -/
theorem current_oldPriorityFresh_no_common_tail
    (A : PostClosureMacroCompressorAssignment T)
    (current : LinkageBlueprint Gamma C.ladder.limitWarp kappa)
    {x b c : V}
    (hxb : (x, b) ∈ current.edgeSet)
    (hxc : (x, c) ∈ A.oldPriorityFreshEdges current) : False :=
  hxc.2 ⟨b, hxb⟩

/-- The old-priority union has indegree and outdegree at most one.  This is
the relation-level counterpart of the source diamond's compatibility rule. -/
theorem oldPriorityAttachedEdges_biUnique
    (A : PostClosureMacroCompressorAssignment T)
    {currentClosed : Set V}
    (current : LinkageBlueprint Gamma C.ladder.limitWarp kappa)
    (hcurrent : current.IsLinkageBlueprint
      C.newSlice currentClosed C.persistent) :
    Relator.BiUnique (fun x y ↦
      (x, y) ∈ A.oldPriorityAttachedEdges current) := by
  have hold : Relator.BiUnique (fun x y ↦ (x, y) ∈ current.edgeSet) :=
    _root_.Erdos599.Alternating.IsWarp.familyEdges_biUnique current.isWarp
  have hfresh := A.actualPostClosureClosedEdges_biUnique
  constructor
  · intro x w y hxy hwy
    rcases hxy with hxy | hxy <;> rcases hwy with hwy | hwy
    · exact hold.1 hxy hwy
    · exact False.elim
        (A.current_oldPriorityFresh_no_common_head current hcurrent hxy hwy)
    · exact False.elim
        (A.current_oldPriorityFresh_no_common_head current hcurrent hwy hxy)
    · exact hfresh.1 hxy.1 hwy.1
  · intro x y w hxy hxw
    rcases hxy with hxy | hxy <;> rcases hxw with hxw | hxw
    · exact hold.2 hxy hxw
    · exact False.elim
        (A.current_oldPriorityFresh_no_common_tail current hxy hxw)
    · exact False.elim
        (A.current_oldPriorityFresh_no_common_tail current hxw hxy)
    · exact hfresh.2 hxy.1 hxw.1

theorem oldPriorityAttachedEdges_biUnique_of_vertices_roofed
    (A : PostClosureMacroCompressorAssignment T)
    (current : LinkageBlueprint Gamma C.ladder.limitWarp kappa)
    (hroof : current.vertexSet ⊆ Gamma.roof C.newSlice) :
    Relator.BiUnique (fun x y ↦
      (x, y) ∈ A.oldPriorityAttachedEdges current) := by
  have hold : Relator.BiUnique (fun x y ↦ (x, y) ∈ current.edgeSet) :=
    _root_.Erdos599.Alternating.IsWarp.familyEdges_biUnique current.isWarp
  have hfresh := A.actualPostClosureClosedEdges_biUnique
  constructor
  · intro x w y hxy hwy
    rcases hxy with hxy | hxy <;> rcases hwy with hwy | hwy
    · exact hold.1 hxy hwy
    · exact False.elim
        (A.current_oldPriorityFresh_no_common_head_of_vertices_roofed
          current hroof hxy hwy)
    · exact False.elim
        (A.current_oldPriorityFresh_no_common_head_of_vertices_roofed
          current hroof hwy hxy)
    · exact hfresh.1 hxy.1 hwy.1
  · intro x y w hxy hxw
    rcases hxy with hxy | hxy <;> rcases hxw with hxw | hxw
    · exact hold.2 hxy hxw
    · exact False.elim
        (A.current_oldPriorityFresh_no_common_tail current hxy hxw)
    · exact False.elim
        (A.current_oldPriorityFresh_no_common_tail current hxw hxy)
    · exact hfresh.2 hxy.1 hxw.1

/-- Every current initial remains a root of the old-priority union. -/
theorem currentInitial_noIncoming_oldPriorityAttachedEdges
    (A : PostClosureMacroCompressorAssignment T)
    {currentClosed : Set V}
    (current : LinkageBlueprint Gamma C.ladder.limitWarp kappa)
    (hcurrent : current.IsLinkageBlueprint
      C.newSlice currentClosed C.persistent)
    {x : V} (hx : x ∈ current.initialSet) :
    ¬ ∃ y, (y, x) ∈ A.oldPriorityAttachedEdges current := by
  have hxVertex : x ∈ current.vertexSet := by
    obtain ⟨p, hp, hpInitial⟩ := hx
    exact ⟨p, hp, hpInitial.symm ▸ p.initial_mem_support⟩
  have hnoOld : ¬ ∃ y, (y, x) ∈ current.edgeSet :=
    isWarp_noIncoming_familyEdges_of_mem_initialSet current.isWarp hx
  rintro ⟨y, hyx⟩
  rcases hyx with hyx | hyx
  · exact hnoOld ⟨y, hyx⟩
  · exact A.oldPriorityFreshEdge_head_not_mem_current
      current hcurrent hyx hxVertex

theorem currentInitial_noIncoming_oldPriorityAttachedEdges_of_vertices_roofed
    (A : PostClosureMacroCompressorAssignment T)
    (current : LinkageBlueprint Gamma C.ladder.limitWarp kappa)
    (hroof : current.vertexSet ⊆ Gamma.roof C.newSlice)
    {x : V} (hx : x ∈ current.initialSet) :
    ¬ ∃ y, (y, x) ∈ A.oldPriorityAttachedEdges current := by
  have hxVertex : x ∈ current.vertexSet := by
    obtain ⟨p, hp, hpInitial⟩ := hx
    exact ⟨p, hp, hpInitial.symm ▸ p.initial_mem_support⟩
  have hnoOld : ¬ ∃ y, (y, x) ∈ current.edgeSet :=
    isWarp_noIncoming_familyEdges_of_mem_initialSet current.isWarp hx
  rintro ⟨y, hyx⟩
  rcases hyx with hyx | hyx
  · exact hnoOld ⟨y, hyx⟩
  · exact A.oldPriorityFreshEdge_head_not_mem_of_vertices_roofed
      current hroof hyx hxVertex

/-- The degree-safe candidate therefore has a root-reachable realization
which retains the entire current blueprint.  This intentionally roots only
at the current initials; accounting for any additional source components is
the independent source-cover obligation of Assertion 9.31. -/
theorem exists_rootReachableOldPriorityBlueprint
    (A : PostClosureMacroCompressorAssignment T)
    {currentClosed : Set V}
    (current : LinkageBlueprint Gamma C.ladder.limitWarp kappa)
    (hcurrent : current.IsLinkageBlueprint
      C.newSlice currentClosed C.persistent) :
    ∃ U : LinkageBlueprint Gamma C.ladder.limitWarp kappa,
      current.OrdinaryExtends U ∧
      U.edgeSet = RootReachableRelation.edges
        (A.oldPriorityAttachedEdges current) current.initialSet ∧
      U.vertexSet = RootReachableRelation.carrier
        (A.oldPriorityAttachedEdges current) current.initialSet ∧
      U.initialSet = current.initialSet ∧
      U.terminalSet = {x | x ∈ RootReachableRelation.carrier
        (A.oldPriorityAttachedEdges current) current.initialSet ∧
        ¬ ∃ y, (x, y) ∈ A.oldPriorityAttachedEdges current} := by
  exact exists_rootReachableBlueprint_extending current
    (A.oldPriorityAttachedEdges current) current.initialSet
    (A.oldPriorityAttachedEdges_subset_imaginaryGraph current)
    (A.oldPriorityAttachedEdges_biUnique current hcurrent)
    (fun x hx ↦ A.currentInitial_noIncoming_oldPriorityAttachedEdges
      current hcurrent hx)
    (A.current_edgeSet_subset_oldPriorityAttachedEdges current)
    Set.Subset.rfl

#print axioms oldPriorityAttachedEdges_biUnique
#print axioms currentInitial_noIncoming_oldPriorityAttachedEdges
#print axioms exists_rootReachableOldPriorityBlueprint

end Erdos599.Blueprint.LinkageBlueprint.PostClosureMacroCompressorAssignment
