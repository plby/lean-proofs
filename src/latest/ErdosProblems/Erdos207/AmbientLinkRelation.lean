/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.PairedBisectionSampling
import ErdosProblems.Erdos207.LinkDeletion
import ErdosProblems.Erdos207.BipartiteCodegreeMoment

/-!
# The available link relation before choosing a bisection

The random bisection acts on one ambient link graph.  This file defines that
graph without choosing sides, proves that its restriction across a
`BipartiteLink` is exactly `linkAvailableRelation`, and identifies the
corresponding degree and codegree cardinalities.
-/

namespace Erdos207

open Finset

noncomputable section

/-- Two ambient vertices form an available link pair at `center` when their
three-element set is a member of `available`.  Writing this with an
existential triple makes distinctness automatic and keeps the definition
symmetric in the two endpoints. -/
def ambientLinkRelation
    {V : Type*} [DecidableEq V]
    (center : V) (available : TripleSystemOn V) (u v : V) : Prop :=
  ∃ T ∈ available, T.1 = {center, u, v}

instance ambientLinkRelation.instDecidableRel
    {V : Type*} [DecidableEq V]
    (center : V) (available : TripleSystemOn V) :
    DecidableRel (ambientLinkRelation center available) := by
  intro u v
  unfold ambientLinkRelation
  infer_instance

lemma ambientLinkRelation_symm
    {V : Type*} [DecidableEq V]
    {center : V} {available : TripleSystemOn V} {u v : V} :
    ambientLinkRelation center available u v ↔
      ambientLinkRelation center available v u := by
  constructor <;> rintro ⟨T, hT, hval⟩
  · refine ⟨T, hT, ?_⟩
    rw [hval]
    ext x
    simp only [mem_insert, mem_singleton]
    tauto
  · refine ⟨T, hT, ?_⟩
    rw [hval]
    ext x
    simp only [mem_insert, mem_singleton]
    tauto

/-- The concrete bipartite link relation is the restriction of the ambient
link relation to its two endpoint subtypes. -/
lemma linkAvailableRelation_iff_ambient
    {V : Type*} [DecidableEq V]
    {K : BipartiteLink V} {available : TripleSystemOn V}
    {a : ↥K.left} {b : ↥K.right} :
    linkAvailableRelation K available a b ↔
      ambientLinkRelation K.center available a.1 b.1 := by
  constructor
  · intro h
    exact ⟨linkMatchingTriple K.center K.leftEmbedding K.rightEmbedding
      K.center_ne_left K.center_ne_right K.left_ne_right a b,
      h, rfl⟩
  · rintro ⟨T, hT, hval⟩
    let S := linkMatchingTriple K.center K.leftEmbedding K.rightEmbedding
      K.center_ne_left K.center_ne_right K.left_ne_right a b
    have hTS : T = S := by
      apply Subtype.ext
      exact hval
    change S ∈ available
    exact hTS ▸ hT

/-- Ambient link neighbors restricted to a finite side. -/
def ambientLinkNeighborsIn
    {V : Type*} [Fintype V] [DecidableEq V]
    (center : V) (available : TripleSystemOn V)
    (U : Finset V) (u : V) : Finset V :=
  U.filter (ambientLinkRelation center available u)

@[simp]
lemma mem_ambientLinkNeighborsIn_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    {center : V} {available : TripleSystemOn V}
    {U : Finset V} {u v : V} :
    v ∈ ambientLinkNeighborsIn center available U u ↔
      v ∈ U ∧ ambientLinkRelation center available u v := by
  simp [ambientLinkNeighborsIn]

/-- Ambient common link neighbors restricted to a finite side. -/
def ambientLinkCommonNeighborsIn
    {V : Type*} [Fintype V] [DecidableEq V]
    (center : V) (available : TripleSystemOn V)
    (U : Finset V) (u v : V) : Finset V :=
  U.filter fun w ↦ ambientLinkRelation center available u w ∧
    ambientLinkRelation center available v w

@[simp]
lemma mem_ambientLinkCommonNeighborsIn_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    {center : V} {available : TripleSystemOn V}
    {U : Finset V} {u v w : V} :
    w ∈ ambientLinkCommonNeighborsIn center available U u v ↔
      w ∈ U ∧ ambientLinkRelation center available u w ∧
        ambientLinkRelation center available v w := by
  simp [ambientLinkCommonNeighborsIn, and_assoc]

lemma card_relationNeighborsIn_linkAvailable_eq_ambient
    {V : Type*} [Fintype V] [DecidableEq V]
    (K : BipartiteLink V) (available : TripleSystemOn V)
    (a : ↥K.left) :
    (relationNeighborsIn (linkAvailableRelation K available) univ a).card =
      (ambientLinkNeighborsIn K.center available K.right a.1).card := by
  classical
  let S := relationNeighborsIn (linkAvailableRelation K available) univ a
  have himage : S.image Subtype.val =
      ambientLinkNeighborsIn K.center available K.right a.1 := by
    ext x
    simp only [mem_image, mem_ambientLinkNeighborsIn_iff]
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact ⟨b.2, linkAvailableRelation_iff_ambient.mp
        (mem_relationNeighborsIn_iff _ |>.mp hb).2⟩
    · rintro ⟨hxR, hxrel⟩
      let b : ↥K.right := ⟨x, hxR⟩
      refine ⟨b, ?_, rfl⟩
      exact mem_relationNeighborsIn_iff _ |>.mpr
        ⟨mem_univ b, linkAvailableRelation_iff_ambient.mpr hxrel⟩
  calc
    S.card = (S.image Subtype.val).card := by
      rw [card_image_of_injective _ Subtype.val_injective]
    _ = (ambientLinkNeighborsIn K.center available K.right a.1).card :=
      congrArg card himage

lemma card_relationNeighborsIn_transpose_linkAvailable_eq_ambient
    {V : Type*} [Fintype V] [DecidableEq V]
    (K : BipartiteLink V) (available : TripleSystemOn V)
    (b : ↥K.right) :
    (relationNeighborsIn (transposeRelation (linkAvailableRelation K available))
      univ b).card =
      (ambientLinkNeighborsIn K.center available K.left b.1).card := by
  classical
  let S := relationNeighborsIn
    (transposeRelation (linkAvailableRelation K available)) univ b
  have himage : S.image Subtype.val =
      ambientLinkNeighborsIn K.center available K.left b.1 := by
    ext x
    simp only [mem_image, mem_ambientLinkNeighborsIn_iff]
    constructor
    · rintro ⟨a, ha, rfl⟩
      have hrel := (mem_relationNeighborsIn_iff _ |>.mp ha).2
      exact ⟨a.2, ambientLinkRelation_symm.mpr
        (linkAvailableRelation_iff_ambient.mp hrel)⟩
    · rintro ⟨hxL, hxrel⟩
      let a : ↥K.left := ⟨x, hxL⟩
      refine ⟨a, ?_, rfl⟩
      exact mem_relationNeighborsIn_iff _ |>.mpr
        ⟨mem_univ a, linkAvailableRelation_iff_ambient.mpr
          (ambientLinkRelation_symm.mp hxrel)⟩
  calc
    S.card = (S.image Subtype.val).card := by
      rw [card_image_of_injective _ Subtype.val_injective]
    _ = (ambientLinkNeighborsIn K.center available K.left b.1).card :=
      congrArg card himage

lemma card_relationCommonNeighbors_linkAvailable_eq_ambient
    {V : Type*} [Fintype V] [DecidableEq V]
    (K : BipartiteLink V) (available : TripleSystemOn V)
    (a a' : ↥K.left) :
    (relationCommonNeighbors (linkAvailableRelation K available) a a').card =
      (ambientLinkCommonNeighborsIn K.center available K.right a.1 a'.1).card := by
  classical
  let S := relationCommonNeighbors (linkAvailableRelation K available) a a'
  have himage : S.image Subtype.val =
      ambientLinkCommonNeighborsIn K.center available K.right a.1 a'.1 := by
    ext x
    simp only [mem_image, mem_ambientLinkCommonNeighborsIn_iff]
    constructor
    · rintro ⟨b, hb, rfl⟩
      have hb' := (mem_relationCommonNeighbors_iff _).mp hb
      exact ⟨b.2, linkAvailableRelation_iff_ambient.mp hb'.1,
        linkAvailableRelation_iff_ambient.mp hb'.2⟩
    · rintro ⟨hxR, hax, ha'x⟩
      let b : ↥K.right := ⟨x, hxR⟩
      exact ⟨b, (mem_relationCommonNeighbors_iff _).mpr
        ⟨linkAvailableRelation_iff_ambient.mpr hax,
          linkAvailableRelation_iff_ambient.mpr ha'x⟩, rfl⟩
  calc
    S.card = (S.image Subtype.val).card := by
      rw [card_image_of_injective _ Subtype.val_injective]
    _ = (ambientLinkCommonNeighborsIn K.center available K.right a.1 a'.1).card :=
      congrArg card himage

lemma card_relationCommonNeighbors_transpose_linkAvailable_eq_ambient
    {V : Type*} [Fintype V] [DecidableEq V]
    (K : BipartiteLink V) (available : TripleSystemOn V)
    (b b' : ↥K.right) :
    (relationCommonNeighbors
      (transposeRelation (linkAvailableRelation K available)) b b').card =
      (ambientLinkCommonNeighborsIn K.center available K.left b.1 b'.1).card := by
  classical
  let S := relationCommonNeighbors
    (transposeRelation (linkAvailableRelation K available)) b b'
  have himage : S.image Subtype.val =
      ambientLinkCommonNeighborsIn K.center available K.left b.1 b'.1 := by
    ext x
    simp only [mem_image, mem_ambientLinkCommonNeighborsIn_iff]
    constructor
    · rintro ⟨a, ha, rfl⟩
      have ha' := (mem_relationCommonNeighbors_iff _).mp ha
      exact ⟨a.2,
        ambientLinkRelation_symm.mpr
          (linkAvailableRelation_iff_ambient.mp ha'.1),
        ambientLinkRelation_symm.mpr
          (linkAvailableRelation_iff_ambient.mp ha'.2)⟩
    · rintro ⟨hxL, hbx, hb'x⟩
      let a : ↥K.left := ⟨x, hxL⟩
      exact ⟨a, (mem_relationCommonNeighbors_iff _).mpr
        ⟨linkAvailableRelation_iff_ambient.mpr
            (ambientLinkRelation_symm.mp hbx),
          linkAvailableRelation_iff_ambient.mpr
            (ambientLinkRelation_symm.mp hb'x)⟩, rfl⟩
  calc
    S.card = (S.image Subtype.val).card := by
      rw [card_image_of_injective _ Subtype.val_injective]
    _ = (ambientLinkCommonNeighborsIn K.center available K.left b.1 b'.1).card :=
      congrArg card himage

end

end Erdos207
