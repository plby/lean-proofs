/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayMovingBetaLimit
import ErdosProblems.Erdos599.HalfwayPostClosureProducedAssignment

/-!
# Eligibility at contacts of the actual post-closure interval

The closing set has an exact persistent-frontier intersection at the genuine
moving-stage limit.  Consequently a closing-set vertex from which an edge of
the later interval row leaves cannot be persistent: persistence would put it
on the later frontier, while the interval row meets that frontier only at its
finite terminals.  The nonpersistent part of the closing set lies in the
limiting strict roof, which is exactly the initial-endpoint condition needed
for the hammocks used in Claim 9.31.

This argument uses the literal interval edge and does not assume eligibility
for arbitrary endpoints.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Blueprint.LinkageBlueprint

open _root_.Erdos599.DirectedPath _root_.Erdos599.Alternating

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

namespace PostClosureIntervalTransaction

variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {globalZ seed : Set V} {z : V}

/-- A forward edge of the actual later interval cannot leave a persistent
vertex of the genuine moving-limit closing set. -/
theorem not_mem_persistent_of_mem_closedSet_of_mem_intervalEdge
    (Rlimit : LimitMoving931GlobalClosure C globalZ seed)
    (T : PostClosureIntervalTransaction C globalZ seed z
      Rlimit.toDynamicMoving931GlobalClosure)
    {u v : V} (huX : u ∈ Rlimit.closedSet)
    (huv : (u, v) ∈ familyEdges T.interval.ambientInterval) :
    u ∉ C.persistent := by
  intro huPersistent
  have huFrontier : u ∈ C.ladder.frontier Rlimit.later.stage := by
    have huInter : u ∈ Rlimit.closedSet ∩ C.persistent :=
      ⟨huX, huPersistent⟩
    rw [← Rlimit.frontier_inter] at huInter
    exact huInter.2
  have huvFamily := huv
  simp only [familyEdges, Set.mem_iUnion] at huv
  obtain ⟨p, hp, huvPath⟩ := huv
  have huSupport : u ∈ p.support :=
    (p.edgeSet_subset_support_prod huvPath).1
  have hpTerminal : Gamma.terminal? p = some u := by
    apply T.interval.ambientInterval_meetsOnlyAtTerminal p hp u huSupport
    simpa only [DynamicMoving931GlobalClosure.capturedGeometry_newSlice]
      using huFrontier
  exact (isWarp_noOutgoing_familyEdges_of_mem_terminalFrontier
    T.interval.ambientInterval_linkage.isWarp
      ⟨p, hp, hpTerminal⟩) ⟨v, huvFamily⟩

/-- The same literal-edge hypothesis places its tail in the limiting strict
roof. -/
theorem mem_limitStrictRoof_of_mem_closedSet_of_mem_intervalEdge
    (Rlimit : LimitMoving931GlobalClosure C globalZ seed)
    (T : PostClosureIntervalTransaction C globalZ seed z
      Rlimit.toDynamicMoving931GlobalClosure)
    {u v : V} (huX : u ∈ Rlimit.closedSet)
    (huv : (u, v) ∈ familyEdges T.interval.ambientInterval) :
    u ∈ C.ladder.limitStrictRoof := by
  have huRoof : u ∈ C.ladder.limitRoof := Rlimit.subset_limitRoof huX
  have huNotPersistent : u ∉ C.persistent :=
    T.not_mem_persistent_of_mem_closedSet_of_mem_intervalEdge
      Rlimit huX huv
  by_contra huNotStrict
  exact huNotPersistent ⟨huRoof, huNotStrict⟩

/-- A forward interval edge at a closed contact supplies the finite hammock
eligibility condition for every other closed contact. -/
theorem hammockEligible_vertex_of_mem_intervalEdge
    (Rlimit : LimitMoving931GlobalClosure C globalZ seed)
    (T : PostClosureIntervalTransaction C globalZ seed z
      Rlimit.toDynamicMoving931GlobalClosure)
    {u w v : V} (huX : u ∈ Rlimit.closedSet)
    (huv : (u, w) ∈ familyEdges T.interval.ambientInterval)
    (hvX : v ∈ Rlimit.closedSet) :
    HammockEligible Rlimit.closedSet C.ladder.limitStrictRoof
      C.ladder.limitRoof u (.vertex v) := by
  exact ⟨⟨huX,
    T.mem_limitStrictRoof_of_mem_closedSet_of_mem_intervalEdge
      Rlimit huX huv⟩,
    ⟨hvX, Rlimit.subset_limitRoof hvX⟩⟩

/-- The forward-edge tail is likewise eligible for an infinite hammock. -/
theorem hammockEligible_infinity_of_mem_intervalEdge
    (Rlimit : LimitMoving931GlobalClosure C globalZ seed)
    (T : PostClosureIntervalTransaction C globalZ seed z
      Rlimit.toDynamicMoving931GlobalClosure)
    {u v : V} (huX : u ∈ Rlimit.closedSet)
    (huv : (u, v) ∈ familyEdges T.interval.ambientInterval) :
    HammockEligible Rlimit.closedSet C.ladder.limitStrictRoof
      C.ladder.limitRoof u .infinity := by
  exact ⟨⟨huX,
    T.mem_limitStrictRoof_of_mem_closedSet_of_mem_intervalEdge
      Rlimit huX huv⟩, trivial⟩

/-- A literal initial created at the cutting set is the tail of a genuine
edge of the uncut interval family. -/
theorem exists_intervalEdge_of_mem_cutInitial_inter_closedSet
    (Rlimit : LimitMoving931GlobalClosure C globalZ seed)
    (T : PostClosureIntervalTransaction C globalZ seed z
      Rlimit.toDynamicMoving931GlobalClosure)
    {u : V}
    (hu : u ∈ CutSplit.initialVertices
        (outsideCarrier T.interval.ambientInterval Rlimit.closedSet)
        (outsideFamilyEdges T.interval.ambientInterval Rlimit.closedSet)
        Rlimit.closedSet ∩ Rlimit.closedSet) :
    ∃ v, (u, v) ∈ familyEdges T.interval.ambientInterval := by
  rcases hu.1 with hexit | houtside
  · obtain ⟨v, huv⟩ := hexit.2
    exact ⟨v, outsideFamilyEdges_subset
      T.interval.ambientInterval Rlimit.closedSet huv⟩
  · exact False.elim (houtside.2.1 hu.2)

/-- In particular, every literal cut initial belonging to the closing set
is nonpersistent. -/
theorem not_mem_persistent_of_mem_cutInitial_inter_closedSet
    (Rlimit : LimitMoving931GlobalClosure C globalZ seed)
    (T : PostClosureIntervalTransaction C globalZ seed z
      Rlimit.toDynamicMoving931GlobalClosure)
    {u : V}
    (hu : u ∈ CutSplit.initialVertices
        (outsideCarrier T.interval.ambientInterval Rlimit.closedSet)
        (outsideFamilyEdges T.interval.ambientInterval Rlimit.closedSet)
        Rlimit.closedSet ∩ Rlimit.closedSet) :
    u ∉ C.persistent := by
  obtain ⟨v, huv⟩ := T.exists_intervalEdge_of_mem_cutInitial_inter_closedSet
    Rlimit hu
  exact T.not_mem_persistent_of_mem_closedSet_of_mem_intervalEdge
    Rlimit hu.2 huv

/-- Hence every such literal cut initial lies in the limiting strict roof. -/
theorem mem_limitStrictRoof_of_mem_cutInitial_inter_closedSet
    (Rlimit : LimitMoving931GlobalClosure C globalZ seed)
    (T : PostClosureIntervalTransaction C globalZ seed z
      Rlimit.toDynamicMoving931GlobalClosure)
    {u : V}
    (hu : u ∈ CutSplit.initialVertices
        (outsideCarrier T.interval.ambientInterval Rlimit.closedSet)
        (outsideFamilyEdges T.interval.ambientInterval Rlimit.closedSet)
        Rlimit.closedSet ∩ Rlimit.closedSet) :
    u ∈ C.ladder.limitStrictRoof := by
  obtain ⟨v, huv⟩ := T.exists_intervalEdge_of_mem_cutInitial_inter_closedSet
    Rlimit hu
  exact T.mem_limitStrictRoof_of_mem_closedSet_of_mem_intervalEdge
    Rlimit hu.2 huv

/-- Every literal cut initial which lies in the closing set is eligible with
every closing-set vertex as finite endpoint. -/
theorem hammockEligible_vertex_of_mem_cutInitial_inter_closedSet
    (Rlimit : LimitMoving931GlobalClosure C globalZ seed)
    (T : PostClosureIntervalTransaction C globalZ seed z
      Rlimit.toDynamicMoving931GlobalClosure)
    {u v : V}
    (hu : u ∈ CutSplit.initialVertices
        (outsideCarrier T.interval.ambientInterval Rlimit.closedSet)
        (outsideFamilyEdges T.interval.ambientInterval Rlimit.closedSet)
        Rlimit.closedSet ∩ Rlimit.closedSet)
    (hvX : v ∈ Rlimit.closedSet) :
    HammockEligible Rlimit.closedSet C.ladder.limitStrictRoof
      C.ladder.limitRoof u (.vertex v) := by
  obtain ⟨w, huw⟩ := T.exists_intervalEdge_of_mem_cutInitial_inter_closedSet
    Rlimit hu
  exact T.hammockEligible_vertex_of_mem_intervalEdge
    Rlimit hu.2 huw hvX

/-- Infinite-end eligibility for every literal cut initial in the closing
set. -/
theorem hammockEligible_infinity_of_mem_cutInitial_inter_closedSet
    (Rlimit : LimitMoving931GlobalClosure C globalZ seed)
    (T : PostClosureIntervalTransaction C globalZ seed z
      Rlimit.toDynamicMoving931GlobalClosure)
    {u : V}
    (hu : u ∈ CutSplit.initialVertices
        (outsideCarrier T.interval.ambientInterval Rlimit.closedSet)
        (outsideFamilyEdges T.interval.ambientInterval Rlimit.closedSet)
        Rlimit.closedSet ∩ Rlimit.closedSet) :
    HammockEligible Rlimit.closedSet C.ladder.limitStrictRoof
      C.ladder.limitRoof u .infinity := by
  obtain ⟨v, huv⟩ := T.exists_intervalEdge_of_mem_cutInitial_inter_closedSet
    Rlimit hu
  exact T.hammockEligible_infinity_of_mem_intervalEdge Rlimit hu.2 huv

end PostClosureIntervalTransaction

#print axioms
  PostClosureIntervalTransaction.not_mem_persistent_of_mem_closedSet_of_mem_intervalEdge
#print axioms
  PostClosureIntervalTransaction.hammockEligible_vertex_of_mem_cutInitial_inter_closedSet
#print axioms
  PostClosureIntervalTransaction.hammockEligible_infinity_of_mem_cutInitial_inter_closedSet

end Erdos599.Blueprint.LinkageBlueprint
