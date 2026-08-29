/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingAllMarkerMatchingDecode

/-!
# Finite augmenting port paths give genuine matching toggles

The old matching may be infinite. Simplicity is required only of the
finite path in the two-copy port graph, not of its original-vertex
projection. Every old incidence conflicting with a new forward pair is
traversed backwards and hence removed. No companion component is discarded.
-/

namespace Erdos599.GroundingPortToggle

open Set DirectedPath Alternating GroundingAllMarkerPorts

universe u

variable {V : Type u} {G : DWeb V} {M : V → V → Prop}

structure AugmentingPath (G : DWeb V) (M : V → V → Prop) where
  portGraph : Digraph (Port V)
  path : FinitePath portGraph
  first : V
  last : V
  path_start : path.start = .inl first
  path_finish : path.finish = .inr last
  step : ∀ {a b}, (a, b) ∈ path.edgeSet →
    GroundingAllMarkerAuxiliary.Input.matchingStep (G := G) M a b
  first_free : ∀ y, ¬ M first y
  last_free : ∀ x, ¬ M x last

namespace AugmentingPath

variable (D : AugmentingPath G M)

def forward (x y : V) : Prop := (.inl x, .inr y) ∈ D.path.edgeSet

def backward (x y : V) : Prop := (.inr y, .inl x) ∈ D.path.edgeSet

def toggled (x y : V) : Prop := (M x y ∧ ¬ D.backward x y) ∨ D.forward x y

theorem backward_mem {x y : V} (h : D.backward x y) : M x y := D.step h

theorem forward_not_mem {x y : V} (h : D.forward x y) : ¬ M x y := (D.step h).2

theorem forward_adj_or_eq {x y : V} (h : D.forward x y) : G.graph.Adj x y ∨ x = y :=
  (D.step h).1

theorem forward_biUnique : Relator.BiUnique D.forward := by
  constructor
  · intro x y z hx hy
    exact Sum.inl.inj (Walk.edgeSet_leftUnique D.path.walk D.path.isPath hx hy)
  · intro x y z hy hz
    exact Sum.inr.inj (Walk.edgeSet_rightUnique D.path.walk D.path.isPath hy hz)

theorem forward_finite : {e : V × V | D.forward e.1 e.2}.Finite := by
  let f : V × V → Port V × Port V := fun e ↦ (.inl e.1, .inr e.2)
  have hinj : Function.Injective f := by
    intro a b h
    exact Prod.ext (Sum.inl.inj (congrArg Prod.fst h))
      (Sum.inr.inj (congrArg Prod.snd h))
  exact Set.Finite.preimage hinj.injOn (FinitePath.edgeSet_finite D.path)

theorem backward_finite : {e : V × V | D.backward e.1 e.2}.Finite := by
  let f : V × V → Port V × Port V := fun e ↦ (.inr e.2, .inl e.1)
  have hinj : Function.Injective f := by
    intro a b h
    exact Prod.ext (Sum.inl.inj (congrArg Prod.snd h))
      (Sum.inr.inj (congrArg Prod.fst h))
  exact Set.Finite.preimage hinj.injOn (FinitePath.edgeSet_finite D.path)

theorem forward_outgoing_of_mem {x : V} (hx : Sum.inl x ∈ D.path.support) :
    ∃ y, D.forward x y := by
  have hne : Sum.inl x ≠ D.path.finish := by
    rw [D.path_finish]
    intro h
    cases h
  obtain ⟨y, hy⟩ := FinitePath.exists_outgoing_edge_of_mem_support_of_ne_finish D.path hx hne
  cases y with
  | inl y => exact (D.step hy).elim
  | inr y => exact ⟨y, hy⟩

theorem forward_incoming_of_mem {y : V} (hy : Sum.inr y ∈ D.path.support) :
    ∃ x, D.forward x y := by
  have hne : Sum.inr y ≠ D.path.start := by
    rw [D.path_start]
    intro h
    cases h
  obtain ⟨x, hx⟩ := FinitePath.exists_incoming_edge_of_mem_support_of_ne_start D.path hy hne
  cases x with
  | inl x => exact ⟨x, hx⟩
  | inr x => exact (D.step hx).elim

theorem backward_outgoing_of_mem_ne_first {x : V}
    (hx : Sum.inl x ∈ D.path.support) (hne : x ≠ D.first) : ∃ y, D.backward x y := by
  have hstart : Sum.inl x ≠ D.path.start := by
    rw [D.path_start]
    exact fun h ↦ hne (Sum.inl.inj h)
  obtain ⟨y, hy⟩ := FinitePath.exists_incoming_edge_of_mem_support_of_ne_start D.path hx hstart
  cases y with
  | inl y => exact (D.step hy).elim
  | inr y => exact ⟨y, hy⟩

theorem backward_incoming_of_mem_ne_last {y : V}
    (hy : Sum.inr y ∈ D.path.support) (hne : y ≠ D.last) : ∃ x, D.backward x y := by
  have hfinish : Sum.inr y ≠ D.path.finish := by
    rw [D.path_finish]
    exact fun h ↦ hne (Sum.inr.inj h)
  obtain ⟨x, hx⟩ := FinitePath.exists_outgoing_edge_of_mem_support_of_ne_finish D.path hy hfinish
  cases x with
  | inl x => exact ⟨x, hx⟩
  | inr x => exact (D.step hx).elim

theorem conflicting_outgoing_removed (hM : Relator.BiUnique M) {x y z : V}
    (hF : D.forward x y) (hOld : M x z) : D.backward x z := by
  have hne : x ≠ D.first := fun h ↦ D.first_free z (h ▸ hOld)
  obtain ⟨t, ht⟩ := D.backward_outgoing_of_mem_ne_first
    (D.path.edgeSet_subset_support_prod hF).1 hne
  have htz : t = z := hM.2 (D.backward_mem ht) hOld
  exact htz ▸ ht

theorem conflicting_incoming_removed (hM : Relator.BiUnique M) {x y z : V}
    (hF : D.forward x y) (hOld : M z y) : D.backward z y := by
  have hne : y ≠ D.last := fun h ↦ D.last_free z (h ▸ hOld)
  obtain ⟨t, ht⟩ := D.backward_incoming_of_mem_ne_last
    (D.path.edgeSet_subset_support_prod hF).2 hne
  have htz : t = z := hM.1 (D.backward_mem ht) hOld
  exact htz ▸ ht

/-- The actual toggle, including all of its components, is biunique. -/
theorem toggled_biUnique (hM : Relator.BiUnique M) : Relator.BiUnique D.toggled := by
  constructor
  · intro x y z hx hy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact hM.1 hx.1 hy.1
    · exact (hx.2 (D.conflicting_incoming_removed hM hy hx.1)).elim
    · exact (hy.2 (D.conflicting_incoming_removed hM hx hy.1)).elim
    · exact D.forward_biUnique.1 hx hy
  · intro x y z hy hz
    rcases hy with hy | hy <;> rcases hz with hz | hz
    · exact hM.2 hy.1 hz.1
    · exact (hy.2 (D.conflicting_outgoing_removed hM hz hy.1)).elim
    · exact (hz.2 (D.conflicting_outgoing_removed hM hy hz.1)).elim
    · exact D.forward_biUnique.2 hy hz

#print axioms forward_finite
#print axioms backward_finite
#print axioms toggled_biUnique

end AugmentingPath
end Erdos599.GroundingPortToggle
