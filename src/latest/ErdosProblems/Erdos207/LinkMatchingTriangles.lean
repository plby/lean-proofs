/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.GreedyLegality
import ErdosProblems.Erdos207.RandomRobustMatching

/-!
# Turning a robust link matching into covering triangles

The final part of one KSSS cover-down step takes place in the link graph of
an outer vertex.  This file supplies the deterministic bridge which was
missing from the abstract robust Hall development: a bijection between two
disjoint classes of inner vertices gives edge-disjoint triples through the
outer vertex and covers every corresponding crossing edge.

The last lemmas also isolate the exact safety certificate used after random
sparsification.  It is enough that each retained matching triple does not
participate in a forbidden configuration contained in the old family plus
the complete sparsified reservoir.
-/

namespace Erdos207

open Finset

noncomputable section

/-- The triple through the link center and one vertex in each side of a
bipartition.  The embeddings and separation assumptions carry all three
distinctness proofs. -/
def linkMatchingTriple
    {A B V : Type*} [DecidableEq V]
    (center : V) (left : A ↪ V) (right : B ↪ V)
    (hcenterLeft : ∀ a, center ≠ left a)
    (hcenterRight : ∀ b, center ≠ right b)
    (hleftRight : ∀ a b, left a ≠ right b)
    (a : A) (b : B) : TripleOn V :=
  ⟨{center, left a, right b}, by
    simp [hcenterLeft a, hcenterRight b, hleftRight a b]⟩

@[simp]
lemma mem_linkMatchingTriple_iff
    {A B V : Type*} [DecidableEq V]
    {center : V} {left : A ↪ V} {right : B ↪ V}
    {hcenterLeft : ∀ a, center ≠ left a}
    {hcenterRight : ∀ b, center ≠ right b}
    {hleftRight : ∀ a b, left a ≠ right b}
    {a : A} {b : B} {x : V} :
    x ∈ (linkMatchingTriple center left right hcenterLeft hcenterRight
      hleftRight a b).1 ↔ x = center ∨ x = left a ∨ x = right b := by
  simp [linkMatchingTriple]

/-- The family of link triples associated with a map from the left class to
the right class. -/
def linkMatchingTriangles
    {A B V : Type*} [Fintype A] [DecidableEq V]
    (center : V) (left : A ↪ V) (right : B ↪ V)
    (hcenterLeft : ∀ a, center ≠ left a)
    (hcenterRight : ∀ b, center ≠ right b)
    (hleftRight : ∀ a b, left a ≠ right b)
    (f : A → B) : TripleSystemOn V := by
  classical
  exact Finset.univ.image fun a ↦
    linkMatchingTriple center left right hcenterLeft hcenterRight
      hleftRight a (f a)

@[simp]
lemma mem_linkMatchingTriangles_iff
    {A B V : Type*} [Fintype A] [DecidableEq V]
    {center : V} {left : A ↪ V} {right : B ↪ V}
    {hcenterLeft : ∀ a, center ≠ left a}
    {hcenterRight : ∀ b, center ≠ right b}
    {hleftRight : ∀ a b, left a ≠ right b}
    {f : A → B} {T : TripleOn V} :
    T ∈ linkMatchingTriangles center left right hcenterLeft hcenterRight
      hleftRight f ↔
      ∃ a : A, T = linkMatchingTriple center left right hcenterLeft
        hcenterRight hleftRight a (f a) := by
  classical
  rw [linkMatchingTriangles, mem_image]
  constructor
  · rintro ⟨a, _ha, rfl⟩
    exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨a, mem_univ a, rfl⟩

private lemma common_vertex_eq_center
    {A B V : Type*} [DecidableEq V]
    {center : V} {left : A ↪ V} {right : B ↪ V}
    {hcenterLeft : ∀ a, center ≠ left a}
    {hcenterRight : ∀ b, center ≠ right b}
    {hleftRight : ∀ a b, left a ≠ right b}
    {f : A → B} (hf : Function.Injective f)
    {a c : A} (hac : a ≠ c) {x : V}
    (hxa : x ∈ (linkMatchingTriple center left right hcenterLeft
      hcenterRight hleftRight a (f a)).1)
    (hxc : x ∈ (linkMatchingTriple center left right hcenterLeft
      hcenterRight hleftRight c (f c)).1) :
    x = center := by
  rw [mem_linkMatchingTriple_iff] at hxa hxc
  rcases hxa with rfl | hxa | hxa
  · rfl
  · rcases hxc with hxc | hxc | hxc
    · exact hxc
    · exact (hac (left.injective (hxa.symm.trans hxc))).elim
    · exact (hleftRight a (f c) (hxa.symm.trans hxc)).elim
  · rcases hxc with hxc | hxc | hxc
    · exact hxc
    · exact (hleftRight c (f a) (hxc.symm.trans hxa)).elim
    · have hfac : f a = f c := right.injective (hxa.symm.trans hxc)
      exact (hac (hf hfac)).elim

/-- An injective link matching produces a partial Steiner triple system. -/
theorem linkMatchingTriangles_isPacking
    {A B V : Type*} [Fintype A] [DecidableEq V]
    (center : V) (left : A ↪ V) (right : B ↪ V)
    (hcenterLeft : ∀ a, center ≠ left a)
    (hcenterRight : ∀ b, center ≠ right b)
    (hleftRight : ∀ a b, left a ≠ right b)
    (f : A → B) (hf : Function.Injective f) :
    IsPackingOn (linkMatchingTriangles center left right hcenterLeft
      hcenterRight hleftRight f) := by
  classical
  intro u v huv T hT huT hvT U hU huU hvU
  obtain ⟨a, rfl⟩ := mem_linkMatchingTriangles_iff.mp hT
  obtain ⟨c, rfl⟩ := mem_linkMatchingTriangles_iff.mp hU
  by_cases hac : a = c
  · subst c
    rfl
  · have hu := common_vertex_eq_center hf hac huT huU
    have hv := common_vertex_eq_center hf hac hvT hvU
    exact (huv (hu.trans hv.symm)).elim

/-- Every left spoke at the center is covered by its matching triple. -/
theorem linkMatchingTriangles_covers_left
    {A B V : Type*} [Fintype A] [DecidableEq V]
    (center : V) (left : A ↪ V) (right : B ↪ V)
    (hcenterLeft : ∀ a, center ≠ left a)
    (hcenterRight : ∀ b, center ≠ right b)
    (hleftRight : ∀ a b, left a ≠ right b)
    (f : A → B) (a : A) :
    (coveredGraph (linkMatchingTriangles center left right hcenterLeft
      hcenterRight hleftRight f)).Adj center (left a) := by
  classical
  refine coveredGraph_adj.mpr ⟨linkMatchingTriple center left right
    hcenterLeft hcenterRight hleftRight a (f a), ?_, ?_, ?_, ?_⟩
  · exact mem_linkMatchingTriangles_iff.mpr ⟨a, rfl⟩
  · simp
  · simp
  · exact hcenterLeft a

/-- Surjectivity of the matching covers every right spoke as well. -/
theorem linkMatchingTriangles_covers_right
    {A B V : Type*} [Fintype A] [DecidableEq V]
    (center : V) (left : A ↪ V) (right : B ↪ V)
    (hcenterLeft : ∀ a, center ≠ left a)
    (hcenterRight : ∀ b, center ≠ right b)
    (hleftRight : ∀ a b, left a ≠ right b)
    (f : A → B) (hf : Function.Surjective f) (b : B) :
    (coveredGraph (linkMatchingTriangles center left right hcenterLeft
      hcenterRight hleftRight f)).Adj center (right b) := by
  classical
  obtain ⟨a, rfl⟩ := hf b
  refine coveredGraph_adj.mpr ⟨linkMatchingTriple center left right
    hcenterLeft hcenterRight hleftRight a (f a), ?_, ?_, ?_, ?_⟩
  · exact mem_linkMatchingTriangles_iff.mpr ⟨a, rfl⟩
  · simp
  · simp
  · exact hcenterRight (f a)

/-- If a relation certifies available link triples, the whole matching
family lies in the available family. -/
theorem linkMatchingTriangles_subset_of_relation
    {A B V : Type*} [Fintype A] [DecidableEq V]
    (center : V) (left : A ↪ V) (right : B ↪ V)
    (hcenterLeft : ∀ a, center ≠ left a)
    (hcenterRight : ∀ b, center ≠ right b)
    (hleftRight : ∀ a b, left a ≠ right b)
    (r : A → B → Prop) (available : TripleSystemOn V)
    (havailable : ∀ a b, r a b →
      linkMatchingTriple center left right hcenterLeft hcenterRight
        hleftRight a b ∈ available)
    (f : A → B) (hf : ∀ a, r a (f a)) :
    linkMatchingTriangles center left right hcenterLeft hcenterRight
      hleftRight f ⊆ available := by
  classical
  intro T hT
  obtain ⟨a, rfl⟩ := mem_linkMatchingTriangles_iff.mp hT
  exact havailable a (f a) (hf a)

/-- A family of new packing triangles, each avoiding every old covered pair,
can be adjoined to the old packing. -/
theorem IsPackingOn.union_of_triangleAvoidsCovered
    {V : Type*} [DecidableEq V]
    {P M : TripleSystemOn V}
    (hP : IsPackingOn P) (hM : IsPackingOn M)
    (havoid : ∀ T ∈ M, TriangleAvoidsGraph (coveredGraph P) T) :
    IsPackingOn (P ∪ M) := by
  apply hP.union_of_cross hM
  intro u v huv T hTP huT hvT U hUM huU hvU
  exact havoid U hUM u huU v hvU huv
    (coveredGraph_adj.mpr ⟨T, hTP, huT, hvT, huv⟩)

/-- A triangle which avoids every pair covered by `P` cannot itself already
belong to `P`.  Consequently a whole avoiding family is disjoint from `P`. -/
theorem disjoint_of_triangleAvoidsCovered
    {V : Type*} [DecidableEq V]
    {P M : TripleSystemOn V}
    (havoid : ∀ T ∈ M, TriangleAvoidsGraph (coveredGraph P) T) :
    Disjoint P M := by
  rw [Finset.disjoint_left]
  intro T hTP hTM
  have htwo : 1 < T.1.card := by rw [T.2]; omega
  obtain ⟨u, huT, v, hvT, huv⟩ := Finset.one_lt_card.mp htwo
  exact havoid T hTM u huT v hvT huv
    (coveredGraph_adj.mpr ⟨T, hTP, huT, hvT, huv⟩)

/-- A triple participates in a forbidden configuration already contained in
the old family together with a specified reservoir. -/
def ParticipatesForbidden
    {V : Type*} [DecidableEq V]
    (F : ForbiddenFamilyOn V) (P R : TripleSystemOn V)
    (T : TripleOn V) : Prop :=
  ∃ C ∈ F, T ∈ C ∧ C ⊆ P ∪ R

/-- If the old family is forbidden-free and every selected new triple is
safe even relative to a larger reservoir, then every subfamily selected from
that reservoir remains forbidden-free. -/
theorem avoidsForbidden_union_of_nonparticipating
    {V : Type*} [DecidableEq V]
    {F : ForbiddenFamilyOn V} {P R M : TripleSystemOn V}
    (hP : AvoidsForbidden P F) (hMR : M ⊆ R)
    (hsafe : ∀ T ∈ M, ¬ ParticipatesForbidden F P R T) :
    AvoidsForbidden (P ∪ M) F := by
  intro C hCF hCsub
  by_cases hCP : C ⊆ P
  · exact hP C hCF hCP
  · obtain ⟨T, hTC, hTP⟩ := not_subset.mp hCP
    have hTPM := hCsub hTC
    rw [mem_union] at hTPM
    rcases hTPM with hTP' | hTM
    · exact (hTP hTP').elim
    · apply hsafe T hTM
      refine ⟨C, hCF, hTC, ?_⟩
      intro U hUC
      rcases mem_union.mp (hCsub hUC) with hUP | hUM
      · exact mem_union_left R hUP
      · exact mem_union_right P (hMR hUM)

/-- A robust Hall relation on the two link classes gives a concrete family
of covering triples.  The result records precisely the surviving relation
certificate needed by later packing and forbidden-safety lemmas. -/
theorem exists_linkMatchingTriangles_after_deletion
    {A B V : Type*} [Fintype A] [Fintype B] [DecidableEq B]
    [DecidableEq V]
    (center : V) (left : A ↪ V) (right : B ↪ V)
    (hcenterLeft : ∀ a, center ≠ left a)
    (hcenterRight : ∀ b, center ≠ right b)
    (hleftRight : ∀ a b, left a ≠ right b)
    (r deleted : A → B → Prop) [DecidableRel r] [DecidableRel deleted]
    (hcard : Fintype.card A = Fintype.card B)
    (hrobust : SurvivesEveryHallObstruction r deleted) :
    ∃ f : A → B, ∃ M : TripleSystemOn V,
      Function.Bijective f ∧
      M = linkMatchingTriangles center left right hcenterLeft
        hcenterRight hleftRight f ∧
      IsPackingOn M ∧
      (∀ a, r a (f a) ∧ ¬ deleted a (f a)) ∧
      (∀ a, (coveredGraph M).Adj center (left a)) ∧
      (∀ b, (coveredGraph M).Adj center (right b)) := by
  classical
  obtain ⟨f, hf, hrel⟩ :=
    exists_bijective_matching_after_deletion r deleted hcard hrobust
  let M := linkMatchingTriangles center left right hcenterLeft
    hcenterRight hleftRight f
  refine ⟨f, M, hf, rfl, ?_, hrel, ?_, ?_⟩
  · exact linkMatchingTriangles_isPacking center left right hcenterLeft
      hcenterRight hleftRight f hf.1
  · intro a
    exact linkMatchingTriangles_covers_left center left right hcenterLeft
      hcenterRight hleftRight f a
  · intro b
    exact linkMatchingTriangles_covers_right center left right hcenterLeft
      hcenterRight hleftRight f hf.2 b

end

end Erdos207
