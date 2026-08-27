/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.FiniteSpanCounting

/-! # The off-diagonal equal-remainder family in source condition W2 -/

namespace Erdos207

open Finset

noncomputable section

def distinctEqualRemainderPairs
    {W : Type*} [DecidableEq W] (F : Finset (Finset W)) (T T' : W) :
    Finset (Finset W × Finset W) :=
  (F ×ˢ F).filter fun p ↦ p.1 ≠ p.2 ∧ T ∈ p.1 ∧ T' ∈ p.2 ∧
    p.1.erase T = p.2.erase T'

@[simp] theorem mem_distinctEqualRemainderPairs_iff
    {W : Type*} [DecidableEq W] {F : Finset (Finset W)} {T T' : W}
    {p : Finset W × Finset W} :
    p ∈ distinctEqualRemainderPairs F T T' ↔
      p.1 ∈ F ∧ p.2 ∈ F ∧ p.1 ≠ p.2 ∧ T ∈ p.1 ∧ T' ∈ p.2 ∧
        p.1.erase T = p.2.erase T' := by
  simp [distinctEqualRemainderPairs, and_assoc]

theorem distinctEqualRemainderPairs_second_eq
    {W : Type*} [DecidableEq W] {F : Finset (Finset W)} {T T' : W}
    {p : Finset W × Finset W} (hp : p ∈ distinctEqualRemainderPairs F T T') :
    p.2 = insert T' (p.1.erase T) := by
  have h := mem_distinctEqualRemainderPairs_iff.mp hp
  rw [h.2.2.2.2.2, insert_erase h.2.2.2.2.1]

theorem distinctEqualRemainderPairs_roots_ne
    {W : Type*} [DecidableEq W] {F : Finset (Finset W)} {T T' : W}
    {p : Finset W × Finset W} (hp : p ∈ distinctEqualRemainderPairs F T T') : T ≠ T' := by
  intro hTT'
  subst T'
  have h := mem_distinctEqualRemainderPairs_iff.mp hp
  have hsecond := distinctEqualRemainderPairs_second_eq hp
  rw [insert_erase h.2.2.2.1] at hsecond
  exact h.2.2.1 hsecond.symm

theorem distinctEqualRemainderPairs_cross_not_mem
    {W : Type*} [DecidableEq W] {F : Finset (Finset W)} {T T' : W}
    {p : Finset W × Finset W} (hp : p ∈ distinctEqualRemainderPairs F T T') :
    T' ∉ p.1 ∧ T ∉ p.2 := by
  have h := mem_distinctEqualRemainderPairs_iff.mp hp
  have hne := distinctEqualRemainderPairs_roots_ne hp
  constructor
  · intro hm
    have herase : T' ∈ p.1.erase T := mem_erase.mpr ⟨hne.symm, hm⟩
    rw [h.2.2.2.2.2] at herase
    exact (mem_erase.mp herase).1 rfl
  · intro hm
    have herase : T ∈ p.2.erase T' := mem_erase.mpr ⟨hne, hm⟩
    rw [← h.2.2.2.2.2] at herase
    exact (mem_erase.mp herase).1 rfl

theorem distinctEqualRemainderPairs_fst_injOn
    {W : Type*} [DecidableEq W] (F : Finset (Finset W)) (T T' : W) :
    Set.InjOn (fun p : Finset W × Finset W ↦ p.1)
      (distinctEqualRemainderPairs F T T' : Set (Finset W × Finset W)) := by
  intro p hp q hq hfirst
  change p.1 = q.1 at hfirst
  apply Prod.ext hfirst
  rw [distinctEqualRemainderPairs_second_eq hp, distinctEqualRemainderPairs_second_eq hq, hfirst]

@[simp] theorem distinctEqualRemainderPairs_self
    {W : Type*} [DecidableEq W] (F : Finset (Finset W)) (T : W) :
    distinctEqualRemainderPairs F T T = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro p hp
  exact distinctEqualRemainderPairs_roots_ne hp rfl

theorem IsErdosConfig.vertices_erase_eq
    {V : Type*} [DecidableEq V] {j : ℕ} {E : TripleSystemOn V} {T : TripleOn V}
    (hE : IsErdosConfigOn j E) (hj : 5 ≤ j) (hT : T ∈ E) :
    verticesOn (E.erase T) = verticesOn E := by
  apply IsErdosConfig.vertices_eq_of_card_sub_three hE hj (erase_subset _ _)
  rw [card_erase_of_mem hT, hE.1.1]
  omega

theorem genuine_distinctEqualRemainderPairs_span_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {j : ℕ} {T T' : TripleOn V}
    {p : TripleSystemOn V × TripleSystemOn V}
    (hconfig : ∀ E ∈ F, IsErdosConfigOn j E) (hj : 5 ≤ j)
    (hp : p ∈ distinctEqualRemainderPairs F T T') :
    verticesOn p.1 = verticesOn p.2 := by
  have h := mem_distinctEqualRemainderPairs_iff.mp hp
  rw [← IsErdosConfig.vertices_erase_eq (hconfig p.1 h.1) hj h.2.2.2.1,
    h.2.2.2.2.2, IsErdosConfig.vertices_erase_eq (hconfig p.2 h.2.1) hj h.2.2.2.2.1]

theorem four_le_vertices_pair_of_ne
    {V : Type*} [DecidableEq V] {T T' : TripleOn V} (hne : T ≠ T') :
    4 ≤ (verticesOn ({T, T'} : TripleSystemOn V)).card := by
  have hspan : verticesOn ({T, T'} : TripleSystemOn V) = T.1 ∪ T'.1 := by
    simp [verticesOn]
  rw [hspan]
  by_contra hsmall
  have heq : T.1 = T.1 ∪ T'.1 := eq_of_subset_of_card_le subset_union_left (by
    have := T.2
    omega)
  have hsub : T'.1 ⊆ T.1 := by rw [heq]; exact subset_union_right
  have heq' : T'.1 = T.1 := eq_of_subset_of_card_le hsub (by rw [T.2, T'.2])
  exact hne (Subtype.ext heq'.symm)

end

end Erdos207
