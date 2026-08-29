/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayCompleteInsideFamily

/-!
# Exact old-head cross incidence for the complete inside union

The row can legitimately leave a joint terminal by a new edge, so it is
false that every row edge incident with the joint carrier is already a
joint edge.  The source construction supplies the following asymmetric
facts instead:

* every joint edge is either an old edge or a row edge;
* a row edge entering the head of an old edge has the same predecessor;
* a row edge leaving the tail of an old edge has the same successor.

The last clause is used only when the old successor actually exists; old
terminals are therefore not constrained.  These are exactly the cross
conditions needed for the joint/row union to be bi-unique.
-/

noncomputable section

open Cardinal Set

namespace Erdos599.Blueprint.LinkageBlueprint

open DirectedPath Alternating

universe u

variable {V : Type u}
variable {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

namespace CompleteJointRowInsideFamily

variable {current joint row : LinkageBlueprint Gamma Y kappa}

/-- Exact cross-biuniqueness from old-edge/row-edge provenance.  Notice that
the outgoing compatibility hypothesis is only invoked with an actual old
outgoing edge. -/
theorem union_biUnique_of_old_cross
    (hprovenance : joint.edgeSet ⊆ current.edgeSet ∪ row.edgeSet)
    (hincoming : ∀ {x y z : V}, (x, z) ∈ current.edgeSet →
      (y, z) ∈ row.edgeSet → x = y)
    (houtgoing : ∀ {x y z : V}, (x, y) ∈ current.edgeSet →
      (x, z) ∈ row.edgeSet → y = z) :
    Relator.BiUnique
      (fun x y ↦ (x, y) ∈ joint.edgeSet ∪ row.edgeSet) := by
  have hjoint := Alternating.IsWarp.familyEdges_biUnique joint.isWarp
  have hrow := Alternating.IsWarp.familyEdges_biUnique row.isWarp
  constructor
  · intro x y z hxz hyz
    rcases hxz with hxz | hxz <;> rcases hyz with hyz | hyz
    · exact hjoint.1 hxz hyz
    · rcases hprovenance hxz with hxzOld | hxzRow
      · exact hincoming hxzOld hyz
      · exact hrow.1 hxzRow hyz
    · rcases hprovenance hyz with hyzOld | hyzRow
      · exact (hincoming hyzOld hxz).symm
      · exact hrow.1 hxz hyzRow
    · exact hrow.1 hxz hyz
  · intro x y z hxy hxz
    rcases hxy with hxy | hxy <;> rcases hxz with hxz | hxz
    · exact hjoint.2 hxy hxz
    · rcases hprovenance hxy with hxyOld | hxyRow
      · exact houtgoing hxyOld hxz
      · exact hrow.2 hxyRow hxz
    · rcases hprovenance hxz with hxzOld | hxzRow
      · exact (houtgoing hxzOld hxy).symm
      · exact hrow.2 hxy hxzRow
    · exact hrow.2 hxy hxz

/-- Compile the complete inside family from the source-faithful asymmetric
cross conditions and the common chronology. -/
theorem exists_completeJointRowInsideFamily_of_old_cross
    (current joint row : LinkageBlueprint Gamma Y kappa)
    (rank : V → Nat)
    (hprovenance : joint.edgeSet ⊆ current.edgeSet ∪ row.edgeSet)
    (hincoming : ∀ {x y z : V}, (x, z) ∈ current.edgeSet →
      (y, z) ∈ row.edgeSet → x = y)
    (houtgoing : ∀ {x y z : V}, (x, y) ∈ current.edgeSet →
      (x, z) ∈ row.edgeSet → y = z)
    (hjoint : ∀ {x y}, (x, y) ∈ joint.edgeSet → rank x < rank y)
    (hrow : ∀ {x y}, (x, y) ∈ row.edgeSet → rank x < rank y) :
    Nonempty (CompleteJointRowInsideFamily joint row) :=
  exists_completeJointRowInsideFamily joint row rank
    (union_biUnique_of_old_cross hprovenance hincoming houtgoing)
      hjoint hrow

/-- Every noninitial vertex of an actual blueprint has an incoming edge.
This is the initial-end dual of the public nonterminal/outgoing lemma. -/
theorem exists_incoming_of_mem_vertexSet_of_not_mem_initialSet
    (F : LinkageBlueprint Gamma Y kappa) {x : V}
    (hx : x ∈ F.vertexSet) (hinitial : x ∉ F.initialSet) :
    ∃ y, (y, x) ∈ F.edgeSet := by
  obtain ⟨p, hpF, hxp⟩ := hx
  have hne : x ≠ p.initial := by
    intro h
    exact hinitial ⟨p, hpF, h.symm⟩
  rcases p with p | r
  · obtain ⟨y, hy⟩ :=
      FinitePath.exists_incoming_edge_of_mem_support_of_ne_start p hxp hne
    exact ⟨y, Set.mem_iUnion.2 ⟨Sum.inl p,
      Set.mem_iUnion.2 ⟨hpF, hy⟩⟩⟩
  · obtain ⟨n, hn⟩ := hxp
    have hnpos : 0 < n := by
      by_contra hnzero
      have hn0 : n = 0 := Nat.eq_zero_of_not_pos hnzero
      apply hne
      simpa only [DirectedPath.Path.initial, Ray.initial, hn0] using hn.symm
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hnpos)
    refine ⟨r m, Set.mem_iUnion.2 ⟨Sum.inr r,
      Set.mem_iUnion.2 ⟨hpF, ?_⟩⟩⟩
    exact ⟨m, Prod.ext rfl hn.symm⟩

/-- Incoming compatibility at old heads, together with purity at old roots,
says that every row edge entering the old carrier is already an old edge. -/
theorem row_edge_mem_current_of_incoming_old
    (hroot : ∀ {x y : V}, x ∈ current.initialSet →
      (y, x) ∈ row.edgeSet → False)
    (hincoming : ∀ {x y z : V}, (x, z) ∈ current.edgeSet →
      (y, z) ∈ row.edgeSet → x = y) :
    ∀ {x y : V}, x ∈ current.vertexSet →
      (y, x) ∈ row.edgeSet → (y, x) ∈ current.edgeSet := by
  intro x y hx hyx
  by_cases hxinitial : x ∈ current.initialSet
  · exact False.elim (hroot hxinitial hyx)
  · obtain ⟨z, hzx⟩ :=
      exists_incoming_of_mem_vertexSet_of_not_mem_initialSet
        current hx hxinitial
    have hzy : z = y := hincoming hzx hyx
    simpa only [hzy] using hzx

/-- The exact fresh incidence for the compiled joint/row family.  New row
edges may leave old terminals; only edges entering the old carrier are
restricted. -/
theorem fresh_no_incoming_old_of_old_cross
    (U : CompleteJointRowInsideFamily joint row)
    (hjoint : ∀ {x y : V}, x ∈ current.vertexSet →
      (y, x) ∈ joint.edgeSet → (y, x) ∉ current.edgeSet → False)
    (hroot : ∀ {x y : V}, x ∈ current.initialSet →
      (y, x) ∈ row.edgeSet → False)
    (hincoming : ∀ {x y z : V}, (x, z) ∈ current.edgeSet →
      (y, z) ∈ row.edgeSet → x = y) :
    ∀ {x y : V}, x ∈ current.vertexSet →
      (y, x) ∈ U.insideFamily.edgeSet \ current.edgeSet → False := by
  apply U.fresh_no_incoming_old hjoint
  intro x y hx hrow hnot
  exact hnot (row_edge_mem_current_of_incoming_old hroot hincoming hx hrow)

/-- Add the finite occurrence edges to the exact old-head incidence proof. -/
theorem fresh_no_incoming_old_with_assignment_of_old_cross
    {Zf : FracturedWarp Gamma} {A : CompressedFracturedAssignment Zf Y}
    (U : CompleteJointRowInsideFamily joint row)
    (hjoint : ∀ {x y : V}, x ∈ current.vertexSet →
      (y, x) ∈ joint.edgeSet → (y, x) ∉ current.edgeSet → False)
    (hroot : ∀ {x y : V}, x ∈ current.initialSet →
      (y, x) ∈ row.edgeSet → False)
    (hincoming : ∀ {x y z : V}, (x, z) ∈ current.edgeSet →
      (y, z) ∈ row.edgeSet → x = y)
    (hassigned : ∀ {x y : V}, x ∈ current.vertexSet →
      (y, x) ∈ A.finiteEdges → (y, x) ∉ current.edgeSet → False) :
    ∀ {x y : V}, x ∈ current.vertexSet →
      (y, x) ∈
          (U.insideFamily.edgeSet ∪ A.finiteEdges) \ current.edgeSet →
        False := by
  intro x y hx hfresh
  exact U.fresh_no_incoming_old_with_assignment hjoint
    (fun hx hrow hnot ↦ hnot
      (row_edge_mem_current_of_incoming_old hroot hincoming hx hrow))
    hassigned hx hfresh

#print axioms union_biUnique_of_old_cross
#print axioms exists_completeJointRowInsideFamily_of_old_cross
#print axioms fresh_no_incoming_old_with_assignment_of_old_cross

end CompleteJointRowInsideFamily
end Erdos599.Blueprint.LinkageBlueprint
