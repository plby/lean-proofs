/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.FracturedAssignmentPeel
import ErdosProblems.Erdos599.ColouredSafeComponentPromotion

/-!
# Restoring common singleton reference members after occurrence projection

Peeling common singleton members changes no reference edges. Fractured
intersection geometry makes every original forward edge avoid those
singletons, so retyping the unchanged finite or infinite occurrence word
preserves all four interval-safeness clauses.
-/

namespace Erdos599.Blueprint.LinkageBlueprint.FracturedAssignmentPeel

open Set DirectedPath Alternating ColouredSafeReverseReachability

universe u

variable {V : Type u} {Gamma : DWeb V} (Z : FracturedWarp Gamma)
variable {Y : Set Gamma.DPath}

theorem exists_singleton_of_mem_coveredSingletonReference
    {p : Gamma.DPath} (hp : p ∈ coveredSingletonReference Z Y) :
    ∃ x ∈ singletonVertices Z, p = Gamma.trivialPath x := by
  obtain ⟨x, hx, hxp⟩ := hp.1
  exact ⟨x, hx, hxp.symm⟩

theorem familyEdges_activeReference :
    familyEdges (activeReference Z Y) = familyEdges Y := by
  ext e
  simp only [familyEdges, Set.mem_iUnion]
  constructor
  · rintro ⟨p, hp, he⟩
    exact ⟨p, hp.1, he⟩
  · rintro ⟨p, hp, he⟩
    refine ⟨p, ⟨hp, ?_⟩, he⟩
    intro hcovered
    obtain ⟨x, _, rfl⟩ := exists_singleton_of_mem_coveredSingletonReference Z hcovered
    simpa [DWeb.trivialPath, Path.trivial, FinitePath.edgeSet,
      FinitePath.trivial, Walk.edgeSet] using he

theorem edge_not_incident_singletonVertex
    {x : V} (hx : x ∈ singletonVertices Z) {e : V × V}
    (he : e ∈ familyEdges Z.edgeWarp) : e.1 ≠ x ∧ e.2 ≠ x := by
  rw [← Z.same_edges] at he
  simp only [familyEdges, Set.mem_iUnion] at he
  obtain ⟨p, hp, he⟩ := he
  have hnot : x ∉ p.support := by
    intro hxp
    have hpTriv := eq_trivialPath_of_mem_support_singletonHole Z hx hp hxp
    rw [hpTriv] at he
    simpa [DWeb.trivialPath, Path.trivial, FinitePath.edgeSet,
      FinitePath.trivial, Walk.edgeSet] using he
  have heV := p.edgeSet_subset_support_prod he
  exact ⟨fun h ↦ hnot (h ▸ heV.1), fun h ↦ hnot (h ▸ heV.2)⟩

theorem initial_mem_activeReference_of_forward_target
    {x y : V} (hxy : (x, y) ∈ familyEdges Z.edgeWarp)
    (hy : y ∈ Gamma.initialSet Y) : y ∈ Gamma.initialSet (activeReference Z Y) := by
  obtain ⟨p, hp, hpy⟩ := hy
  refine ⟨p, ⟨hp, ?_⟩, hpy⟩
  intro hcovered
  obtain ⟨z, hz, rfl⟩ := exists_singleton_of_mem_coveredSingletonReference Z hcovered
  have hzy : z = y := hpy
  exact (edge_not_incident_singletonVertex Z hz hxy).2 hzy.symm

theorem terminal_mem_activeReference_of_forward_source
    {x y : V} (hxy : (x, y) ∈ familyEdges Z.edgeWarp)
    (hx : x ∈ Gamma.terminalFrontier Y) :
    x ∈ Gamma.terminalFrontier (activeReference Z Y) := by
  obtain ⟨p, hp, hpx⟩ := hx
  refine ⟨p, ⟨hp, ?_⟩, hpx⟩
  intro hcovered
  obtain ⟨z, hz, rfl⟩ := exists_singleton_of_mem_coveredSingletonReference Z hcovered
  have hzx : z = x := by
    simpa only [Gamma.terminal?_trivialPath, Option.some.injEq] using hpx
  exact (edge_not_incident_singletonVertex Z hz hxy).1 hzx.symm

theorem intervals_fullReference_of_active
    {R : Set (V × V)}
    (hR : ∀ p ∈ activeReference Z Y, IsEdgeInterval (R ∩ p.edgeSet) p) :
    ∀ p ∈ Y, IsEdgeInterval (R ∩ p.edgeSet) p := by
  intro p hp
  by_cases hcovered : p ∈ coveredSingletonReference Z Y
  · obtain ⟨x, _, rfl⟩ := exists_singleton_of_mem_coveredSingletonReference Z hcovered
    left
    simp [DWeb.trivialPath, Path.trivial, FinitePath.edgeSet,
      FinitePath.trivial, Walk.edgeSet]
  · exact hR p ⟨hp, hcovered⟩

/-- Literal finite-word promotion; no occurrences are modified. -/
theorem finite_promotePeeledReference_isIntervalSafe
    (Q : FiniteColouredOccurrenceWord Z.edgeWarp (activeReference Z Y))
    (hQ : Q.IsIntervalSafe) :
    (promoteFiniteReference Q (familyEdges_activeReference Z).subset).IsIntervalSafe := by
  refine ⟨?_, ?_, intervals_fullReference_of_active Z hQ.intervals, ?_⟩
  · intro a b x hax hbx
    apply hQ.incoming_removed hax
    rw [familyEdges_activeReference]
    exact hbx
  · intro x a b hxa hxb
    apply hQ.outgoing_removed hxa
    rw [familyEdges_activeReference]
    exact hxb
  · intro x y hxy
    have hpure := hQ.endpoint_pure hxy
    have he := Q.forwardEdges_subset_familyEdges hxy
    exact ⟨fun hy ↦ hpure.1 (initial_mem_activeReference_of_forward_target Z he hy),
      fun hx ↦ hpure.2 (terminal_mem_activeReference_of_forward_source Z he hx)⟩

/-- Literal infinite-word promotion, with the same unchanged coloured
relations and singleton avoidance argument. -/
theorem infinite_promotePeeledReference_isIntervalSafe
    (Q : InfiniteColouredOccurrenceWord Z.edgeWarp (activeReference Z Y))
    (hQ : Q.IsIntervalSafe) :
    (promoteInfiniteReference Q (familyEdges_activeReference Z).subset).IsIntervalSafe := by
  refine ⟨?_, ?_, intervals_fullReference_of_active Z hQ.intervals, ?_⟩
  · intro a b x hax hbx
    apply hQ.incoming_removed hax
    rw [familyEdges_activeReference]
    exact hbx
  · intro x a b hxa hxb
    apply hQ.outgoing_removed hxa
    rw [familyEdges_activeReference]
    exact hxb
  · intro x y hxy
    have hpure := hQ.endpoint_pure hxy
    have he := Q.forwardEdges_subset_familyEdges hxy
    exact ⟨fun hy ↦ hpure.1 (initial_mem_activeReference_of_forward_target Z he hy),
      fun hx ↦ hpure.2 (terminal_mem_activeReference_of_forward_source Z he hx)⟩

#print axioms familyEdges_activeReference
#print axioms edge_not_incident_singletonVertex
#print axioms finite_promotePeeledReference_isIntervalSafe
#print axioms infinite_promotePeeledReference_isIntervalSafe

end Erdos599.Blueprint.LinkageBlueprint.FracturedAssignmentPeel
