/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayCompressedInsideUnion

/-!
# The exact joint-survivor/row-inside union

The complete inside family in moving Assertion 9.31 is not just the
canonical row-inside family: it must also retain the joint survivor produced
by the preceding Assertion 9.30 transaction.  This file constructs the
honest path family of their literal edge union.  The carrier is kept exact,
so isolated roots of either input are not lost by the orientation step.

The hypotheses are the genuinely local union geometry: cross-biuniqueness
and a common strict rank.  The latter rules out both directed cycles and
reverse rays.  No whole-family replacement or scheduler premise is used.
-/

noncomputable section

open Cardinal Set

namespace Erdos599.Blueprint.LinkageBlueprint

open DirectedPath Alternating
open Alternating.RelationDecomposition

universe u

variable {V : Type u}
variable {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

/-- The exact orientation of the joint-survivor/row-inside union. -/
structure CompleteJointRowInsideFamily
    (joint row : LinkageBlueprint Gamma Y kappa) where
  orientation : ForwardOrientation (imaginaryGraph Gamma Y kappa)
  edge_eq : orientation.edge = joint.edgeSet ∪ row.edgeSet
  carrier_eq : orientation.carrier = joint.vertexSet ∪ row.vertexSet

namespace CompleteJointRowInsideFamily

variable {joint row current : LinkageBlueprint Gamma Y kappa}

/-- The actual inside linkage family selected by the exact orientation. -/
def insideFamily (U : CompleteJointRowInsideFamily joint row) :
    LinkageBlueprint Gamma Y kappa :=
  orientationBlueprint U.orientation

@[simp] theorem insideFamily_edgeSet
    (U : CompleteJointRowInsideFamily joint row) :
    U.insideFamily.edgeSet = joint.edgeSet ∪ row.edgeSet := by
  rw [insideFamily, orientationBlueprint_edgeSet, U.edge_eq]

@[simp] theorem insideFamily_vertexSet
    (U : CompleteJointRowInsideFamily joint row) :
    U.insideFamily.vertexSet = joint.vertexSet ∪ row.vertexSet := by
  rw [insideFamily, orientationBlueprint_vertexSet, U.carrier_eq]

theorem joint_vertices
    (U : CompleteJointRowInsideFamily joint row) :
    joint.vertexSet ⊆ U.insideFamily.vertexSet := by
  rw [U.insideFamily_vertexSet]
  exact Set.subset_union_left

theorem row_vertices
    (U : CompleteJointRowInsideFamily joint row) :
    row.vertexSet ⊆ U.insideFamily.vertexSet := by
  rw [U.insideFamily_vertexSet]
  exact Set.subset_union_right

theorem joint_edges
    (U : CompleteJointRowInsideFamily joint row) :
    joint.edgeSet ⊆ U.insideFamily.edgeSet := by
  rw [U.insideFamily_edgeSet]
  exact Set.subset_union_left

theorem row_edges
    (U : CompleteJointRowInsideFamily joint row) :
    row.edgeSet ⊆ U.insideFamily.edgeSet := by
  rw [U.insideFamily_edgeSet]
  exact Set.subset_union_right

/-- Membership in the exact carrier together with the literal absence of an
outgoing union edge gives a terminal of the complete inside family. -/
theorem mem_terminalSet
    (U : CompleteJointRowInsideFamily joint row) {x : V}
    (hx : x ∈ joint.vertexSet ∪ row.vertexSet)
    (hno : ¬ ∃ y, (x, y) ∈ joint.edgeSet ∪ row.edgeSet) :
    x ∈ U.insideFamily.terminalSet := by
  rw [insideFamily, orientationBlueprint_terminalSet_eq_no_outgoing,
    U.carrier_eq, U.edge_eq]
  exact ⟨hx, hno⟩

/-- Membership in the exact carrier together with the literal absence of an
incoming union edge gives an initial of the complete inside family. -/
theorem mem_initialSet
    (U : CompleteJointRowInsideFamily joint row) {x : V}
    (hx : x ∈ joint.vertexSet ∪ row.vertexSet)
    (hno : ¬ ∃ y, (y, x) ∈ joint.edgeSet ∪ row.edgeSet) :
    x ∈ U.insideFamily.initialSet := by
  rw [insideFamily, orientationBlueprint_initialSet_eq_no_incoming,
    U.carrier_eq, U.edge_eq]
  exact ⟨hx, hno⟩

/-- A common rank on the two literal pieces is also a rank on the compiled
inside family. -/
theorem inside_rank
    (U : CompleteJointRowInsideFamily joint row) (rank : V → Nat)
    (hjoint : ∀ {x y}, (x, y) ∈ joint.edgeSet → rank x < rank y)
    (hrow : ∀ {x y}, (x, y) ∈ row.edgeSet → rank x < rank y)
    {x y : V} (hxy : (x, y) ∈ U.insideFamily.edgeSet) :
    rank x < rank y := by
  rw [U.insideFamily_edgeSet] at hxy
  exact hxy.elim hjoint hrow

/-- Any incoming current carrier contained in the literal union is retained
by the compiled inside family. -/
theorem current_vertices
    (U : CompleteJointRowInsideFamily joint row)
    (hcurrent : current.vertexSet ⊆ joint.vertexSet ∪ row.vertexSet) :
    current.vertexSet ⊆ U.insideFamily.vertexSet := by
  simpa only [U.insideFamily_vertexSet] using hcurrent

/-- Current edges accounted for either by the joint/row union or by a
compressed finite edge remain accounted for after compilation. -/
theorem current_edges_with_assignment
    {Zf : FracturedWarp Gamma} {A : CompressedFracturedAssignment Zf Y}
    (U : CompleteJointRowInsideFamily joint row)
    (hcurrent : current.edgeSet ⊆
      (joint.edgeSet ∪ row.edgeSet) ∪ A.finiteEdges) :
    current.edgeSet ⊆ U.insideFamily.edgeSet ∪ A.finiteEdges := by
  simpa only [U.insideFamily_edgeSet] using hcurrent

/-- Componentwise no-new-incoming incidence gives the exact fresh incidence
for the compiled inside family. -/
theorem fresh_no_incoming_old
    (U : CompleteJointRowInsideFamily joint row)
    (hjoint : ∀ {x y : V}, x ∈ current.vertexSet →
      (y, x) ∈ joint.edgeSet → (y, x) ∉ current.edgeSet → False)
    (hrow : ∀ {x y : V}, x ∈ current.vertexSet →
      (y, x) ∈ row.edgeSet → (y, x) ∉ current.edgeSet → False) :
    ∀ {x y : V}, x ∈ current.vertexSet →
      (y, x) ∈ U.insideFamily.edgeSet \ current.edgeSet → False := by
  intro x y hx hfresh
  rw [U.insideFamily_edgeSet] at hfresh
  rcases hfresh.1 with hxy | hxy
  · exact hjoint hx hxy hfresh.2
  · exact hrow hx hxy hfresh.2

/-- The form consumed by `CompressedCompleteInsideFragmentSplice`: the
finite occurrence edges are handled as a third literal component. -/
theorem fresh_no_incoming_old_with_assignment
    {Zf : FracturedWarp Gamma} {A : CompressedFracturedAssignment Zf Y}
    (U : CompleteJointRowInsideFamily joint row)
    (hjoint : ∀ {x y : V}, x ∈ current.vertexSet →
      (y, x) ∈ joint.edgeSet → (y, x) ∉ current.edgeSet → False)
    (hrow : ∀ {x y : V}, x ∈ current.vertexSet →
      (y, x) ∈ row.edgeSet → (y, x) ∉ current.edgeSet → False)
    (hassigned : ∀ {x y : V}, x ∈ current.vertexSet →
      (y, x) ∈ A.finiteEdges → (y, x) ∉ current.edgeSet → False) :
    ∀ {x y : V}, x ∈ current.vertexSet →
      (y, x) ∈
          (U.insideFamily.edgeSet ∪ A.finiteEdges) \ current.edgeSet →
        False := by
  intro x y hx hfresh
  rcases hfresh.1 with hinside | hassignedEdge
  · exact U.fresh_no_incoming_old hjoint hrow hx
      ⟨hinside, hfresh.2⟩
  · exact hassigned hx hassignedEdge hfresh.2

private theorem no_directed_cycle_of_rank
    (E : Set (V × V)) (rank : V → Nat)
    (hrank : ∀ {x y}, (x, y) ∈ E → rank x < rank y) :
    ¬ ContainsDirectedCycle E := by
  rintro ⟨C, hC⟩
  let last : Nat := C.length - 1
  have hlast : last < C.length := Nat.sub_lt C.positive (by omega)
  have hnextLast : C.next ⟨last, hlast⟩ =
      (⟨0, C.positive⟩ : Fin C.length) := by
    apply Fin.ext
    have hs : last + 1 = C.length := Nat.sub_add_cancel C.positive
    simp [DirectedCycle.next, hs]
  have hmono : ∀ n, (hn : n < C.length) →
      rank (C.vertex ⟨0, C.positive⟩) ≤ rank (C.vertex ⟨n, hn⟩) := by
    intro n
    induction n with
    | zero => intro _; exact Nat.le_refl _
    | succ n ih =>
        intro hn
        have hn' : n < C.length := Nat.lt_trans (Nat.lt_succ_self n) hn
        have hnext : C.next (⟨n, hn'⟩ : Fin C.length) = ⟨n + 1, hn⟩ := by
          apply Fin.ext
          exact Nat.mod_eq_of_lt hn
        exact (ih hn').trans (Nat.le_of_lt (by
          rw [← hnext]
          exact hrank (hC ⟨⟨n, hn'⟩, rfl⟩)))
  have hback : rank (C.vertex ⟨last, hlast⟩) <
      rank (C.vertex ⟨0, C.positive⟩) := by
    rw [← hnextLast]
    exact hrank (hC ⟨⟨last, hlast⟩, rfl⟩)
  exact (Nat.not_lt_of_ge (hmono last hlast)) hback

private theorem no_reverse_ray_of_rank
    (E : Set (V × V)) (rank : V → Nat)
    (hrank : ∀ {x y}, (x, y) ∈ E → rank x < rank y) :
    ¬ ContainsReverseDirectedRay E := by
  rintro ⟨R, hR⟩
  have hdesc (n : Nat) : rank (R.vertex (n + 1)) < rank (R.vertex n) :=
    hrank (hR n)
  have hbound : ∀ n, rank (R.vertex n) + n ≤ rank (R.vertex 0) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        have hs := hdesc n
        omega
  have h := hbound (rank (R.vertex 0) + 1)
  omega

private theorem edgeSet_in_imaginaryGraph
    (F : LinkageBlueprint Gamma Y kappa) :
    F.edgeSet ⊆
      {e | (imaginaryGraph Gamma Y kappa).Adj e.1 e.2} := by
  intro e he
  simp only [edgeSet, Set.mem_iUnion] at he
  obtain ⟨p, _hp, hep⟩ := he
  exact p.edgeSet_subset_adj hep

private theorem edgeSet_endpoints
    (F : LinkageBlueprint Gamma Y kappa) {e : V × V}
    (he : e ∈ F.edgeSet) :
    e.1 ∈ F.vertexSet ∧ e.2 ∈ F.vertexSet := by
  simp only [edgeSet, Set.mem_iUnion] at he
  obtain ⟨p, hp, hep⟩ := he
  have hend := p.edgeSet_subset_support_prod hep
  exact ⟨⟨p, hp, hend.1⟩, ⟨p, hp, hend.2⟩⟩

/-- Construct the complete inside family from the literal union geometry.
The strict common rank supplies both well-foundedness obstructions, while
the explicit carrier preserves every isolated vertex of either piece. -/
theorem exists_completeJointRowInsideFamily
    (joint row : LinkageBlueprint Gamma Y kappa)
    (rank : V → Nat)
    (hunique : Relator.BiUnique
      (fun x y ↦ (x, y) ∈ joint.edgeSet ∪ row.edgeSet))
    (hjoint : ∀ {x y}, (x, y) ∈ joint.edgeSet → rank x < rank y)
    (hrow : ∀ {x y}, (x, y) ∈ row.edgeSet → rank x < rank y) :
    Nonempty (CompleteJointRowInsideFamily joint row) := by
  let E : Set (V × V) := joint.edgeSet ∪ row.edgeSet
  let carrier : Set V := joint.vertexSet ∪ row.vertexSet
  have hgraph : E ⊆
      {e | (imaginaryGraph Gamma Y kappa).Adj e.1 e.2} := by
    intro e he
    exact he.elim (fun h ↦ edgeSet_in_imaginaryGraph joint h)
      (fun h ↦ edgeSet_in_imaginaryGraph row h)
  have hendpoints : ∀ e ∈ E, e.1 ∈ carrier ∧ e.2 ∈ carrier := by
    intro e he
    rcases he with he | he
    · have h := edgeSet_endpoints joint he
      exact ⟨Or.inl h.1, Or.inl h.2⟩
    · have h := edgeSet_endpoints row he
      exact ⟨Or.inr h.1, Or.inr h.2⟩
  have hrank : ∀ {x y}, (x, y) ∈ E → rank x < rank y := by
    intro x y hxy
    exact hxy.elim hjoint hrow
  obtain ⟨O, hOE, hOC⟩ := exists_forwardOrientation_exact
    E carrier hgraph hendpoints hunique
      (no_directed_cycle_of_rank E rank hrank)
      (no_reverse_ray_of_rank E rank hrank)
  exact ⟨⟨O, hOE, hOC⟩⟩

#print axioms exists_completeJointRowInsideFamily
#print axioms CompleteJointRowInsideFamily.fresh_no_incoming_old_with_assignment

end CompleteJointRowInsideFamily
end Erdos599.Blueprint.LinkageBlueprint
