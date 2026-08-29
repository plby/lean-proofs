/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularSafeDesignatedLinkage
import ErdosProblems.Erdos599.HalfwayFrontierHeight

/-!
# Cardinality of the carrier of a designated linkage

A linkage has at most one component for each of its initial vertices, and
every directed path has countable support.  Consequently a linkage on `A`
uses at most `max #A aleph0` vertices.  In particular, below an uncountable
cardinal `kappa`, the whole carrier of a linkage on a set of cardinality
strictly below `kappa` is again strictly below `kappa`.

This bookkeeping is important at a singular safe-selection limit.  The
lower-cardinal induction hypothesis may therefore be applied to an
auxiliary construction containing the *whole* limiting carrier; it is not
restricted merely to the set of its initial vertices.  No regularity of
`kappa` is used.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace SingularSafeCarrierCardinal

universe u

variable {V : Type u}

/-- A linkage has no more paths than initial vertices. -/
theorem mk_paths_le_mk_initial
    {G : DWeb V} {A B : Set V} {P : Set G.DPath}
    (hP : IsLinkageBetween G A B P) :
    #P ≤ #A := by
  apply FamilyTools.mk_le_of_pairwiseDisjoint_of_meets
      (F := fun p : G.DPath ↦ p.support)
  · exact hP.isWarp
  · intro p hp
    refine ⟨p.initial, ?_, p.initial_mem_support⟩
    rw [← hP.initialSet_eq]
    exact ⟨p, hp, rfl⟩

/-- The carrier of a linkage on `A` has cardinality at most
`max #A aleph0`. -/
theorem mk_vertexSet_le_max_initial_aleph0
    {G : DWeb V} {A B : Set V} {P : Set G.DPath}
    (hP : IsLinkageBetween G A B P) :
    #(G.vertexSet P) ≤ max (#A) aleph0 := by
  apply HalfwayFrontierHeight.mk_vertexSet_le_of_mk_family_le
      (kappa := max (#A) aleph0)
  · exact le_max_right _ _
  · exact (mk_paths_le_mk_initial hP).trans (le_max_left _ _)

/-- At an uncountable cardinal, a linkage whose initial set is strictly
smaller than the cardinal has a strictly smaller whole carrier. -/
theorem mk_vertexSet_lt_of_mk_initial_lt
    {G : DWeb V} {A B : Set V} {P : Set G.DPath}
    {kappa : Cardinal.{u}}
    (hkappa : aleph0 < kappa)
    (hP : IsLinkageBetween G A B P)
    (hA : #A < kappa) :
    #(G.vertexSet P) < kappa := by
  exact (mk_vertexSet_le_max_initial_aleph0 hP).trans_lt
    (max_lt hA hkappa)

/-- In particular, the non-source part of the carrier which is passed to
the source-disjoint deletion--quotient arrow is still strictly below
`kappa`. -/
theorem mk_nonSourceCarrier_lt_of_mk_initial_lt
    {G : DWeb V} {A B : Set V} {P : Set G.DPath}
    {kappa : Cardinal.{u}}
    (hkappa : aleph0 < kappa)
    (hP : IsLinkageBetween G A B P)
    (hA : #A < kappa) :
    #((G.vertexSet P \ G.source : Set V)) < kappa :=
  (Cardinal.mk_le_mk_of_subset Set.sdiff_subset).trans_lt
    (mk_vertexSet_lt_of_mk_initial_lt hkappa hP hA)

/-- Specialization to the ambiently safe designated-linkage interface. -/
theorem SafeDesignatedLinkage.mk_vertexSet_lt
    {G : DWeb V} {A : Set V} {kappa : Cardinal.{u}}
    (hkappa : aleph0 < kappa)
    (S : SingularSafeDesignatedLinkage.SafeDesignatedLinkage G A)
    (hA : #A < kappa) :
    #(G.vertexSet S.paths) < kappa :=
  mk_vertexSet_lt_of_mk_initial_lt hkappa S.linkage hA

#print axioms mk_paths_le_mk_initial
#print axioms mk_vertexSet_le_max_initial_aleph0
#print axioms mk_vertexSet_lt_of_mk_initial_lt
#print axioms mk_nonSourceCarrier_lt_of_mk_initial_lt

end SingularSafeCarrierCardinal
end CardinalInduction
end Erdos599
