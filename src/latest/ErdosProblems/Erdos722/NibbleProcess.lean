/-
Copyright 2026 The Lean-Proofs Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import ErdosProblems.Erdos722.NibbleBasics
import ErdosProblems.Erdos722.RandomGreedy
import ErdosProblems.Erdos722.Boost
import ErdosProblems.Erdos722.FiniteFreedman
import Mathlib

/-!
# Finite clique-removal process

This file defines the state of the random-greedy matching used in the
nibble.  It is independent of the concentration estimates: a legal history
is proved to be a genuine matching, and its residual vertex set is exactly
the leave of that matching.
-/

namespace Erdos722.NibbleProcess

open Finset
open Erdos722.NibbleBasics
open Erdos722.RandomGreedy

noncomputable section

variable {n q r : ℕ}

/-- Host edges already covered by a history of selected blocks. -/
def usedEdges (r : ℕ) (history : List (Finset (Fin n))) :
    Finset (Finset (Fin n)) :=
  history.toFinset.biUnion (blockEdges r)

@[simp] lemma usedEdges_nil :
    usedEdges r ([] : List (Finset (Fin n))) = ∅ := by
  simp [usedEdges]

lemma usedEdges_append_single (history : List (Finset (Fin n)))
    (Q : Finset (Fin n)) :
    usedEdges r (history ++ [Q]) = usedEdges r history ∪ blockEdges r Q := by
  classical
  simp [usedEdges, Finset.biUnion_insert, Finset.union_comm]

/-- Cliques which do not meet any edge covered earlier in the process. -/
def availableCliques (H : Finset (Finset (Fin n))) (r : ℕ)
    (history : List (Finset (Fin n))) : Finset (Finset (Fin n)) :=
  H.filter fun Q ↦ Disjoint (blockEdges r Q) (usedEdges r history)

@[simp] lemma mem_availableCliques {H : Finset (Finset (Fin n))}
    {history : List (Finset (Fin n))} {Q : Finset (Fin n)} :
    Q ∈ availableCliques H r history ↔
      Q ∈ H ∧ Disjoint (blockEdges r Q) (usedEdges r history) := by
  simp [availableCliques]

lemma availableCliques_subset (H : Finset (Finset (Fin n)))
    (r : ℕ) (history : List (Finset (Fin n))) :
    availableCliques H r history ⊆ H :=
  Finset.filter_subset _ _

lemma usedEdges_mono_of_prefix {xs ys : List (Finset (Fin n))}
    (hprefix : xs <+: ys) : usedEdges r xs ⊆ usedEdges r ys := by
  classical
  obtain ⟨tail, rfl⟩ := hprefix
  intro e he
  simp only [usedEdges, Finset.mem_biUnion] at he ⊢
  obtain ⟨Q, hQ, heQ⟩ := he
  exact ⟨Q, by simp only [List.toFinset_append, Finset.mem_union]; exact Or.inl hQ,
    heQ⟩

/-- A concrete legal clique-removal history. -/
abbrev FollowsAvailable (H : Finset (Finset (Fin n))) (r : ℕ)
    (history path : List (Finset (Fin n))) : Prop :=
  FollowsLegal (availableCliques H r) history path

lemma FollowsAvailable.head_mem {H : Finset (Finset (Fin n))}
    {history : List (Finset (Fin n))} {Q : Finset (Fin n)}
    {rest : List (Finset (Fin n))}
    (h : FollowsAvailable H r history (Q :: rest)) :
    Q ∈ H ∧ Disjoint (blockEdges r Q) (usedEdges r history) := by
  exact mem_availableCliques.mp h.1

lemma FollowsAvailable.mem_H {H : Finset (Finset (Fin n))}
    {history path : List (Finset (Fin n))}
    (h : FollowsAvailable H r history path) :
    ∀ Q ∈ path.toFinset, Q ∈ H := by
  intro Q hQ
  induction path generalizing history with
  | nil => simp at hQ
  | cons a rest ih =>
      simp only [List.toFinset_cons, Finset.mem_insert] at hQ
      rcases hQ with rfl | hQ
      · exact (h.head_mem).1
      · exact ih h.2 hQ

lemma FollowsAvailable.blocks_disjoint_initial
    {H : Finset (Finset (Fin n))}
    {history path : List (Finset (Fin n))}
    (h : FollowsAvailable H r history path) :
    ∀ Q ∈ path.toFinset,
      Disjoint (blockEdges r Q) (usedEdges r history) := by
  intro Q hQ
  induction path generalizing history with
  | nil => simp at hQ
  | cons a rest ih =>
      simp only [List.toFinset_cons, Finset.mem_insert] at hQ
      rcases hQ with rfl | hQ
      · exact h.head_mem.2
      · have hrest := ih h.2 hQ
        exact hrest.mono_right (by
          intro e he
          rw [usedEdges_append_single]
          exact Finset.mem_union_left _ he)

lemma FollowsAvailable.pairwise_disjoint_edges
    {H : Finset (Finset (Fin n))}
    {history path : List (Finset (Fin n))}
    (h : FollowsAvailable H r history path) :
    ∀ Q ∈ path.toFinset, ∀ R ∈ path.toFinset, Q ≠ R →
      Disjoint (blockEdges r Q) (blockEdges r R) := by
  intro Q hQ R hR hne
  induction path generalizing history Q R with
  | nil => simp at hQ
  | cons a rest ih =>
      simp only [List.toFinset_cons, Finset.mem_insert] at hQ hR
      rcases hQ with hQa | hQrest
      · subst Q
        rcases hR with hRa | hRrest
        · exact (hne hRa.symm).elim
        · have hrest := FollowsAvailable.blocks_disjoint_initial h.2 R hRrest
          exact (hrest.mono_right (by
            intro e he
            rw [usedEdges_append_single]
            exact Finset.mem_union_right _ he)).symm
      · rcases hR with hRa | hRrest
        · subst R
          have hrest := FollowsAvailable.blocks_disjoint_initial h.2 Q hQrest
          exact hrest.mono_right (by
            intro e he
            rw [usedEdges_append_single]
            exact Finset.mem_union_right _ he)
        · exact ih h.2 Q hQrest R hRrest hne

/- The preceding direct induction is easier to consume through the union
state invariant below; this exact invariant is what later proofs use. -/

lemma FollowsAvailable.disjoint_new_used
    {H : Finset (Finset (Fin n))}
    {history : List (Finset (Fin n))} {Q : Finset (Fin n)}
    {rest : List (Finset (Fin n))}
    (h : FollowsAvailable H r history (Q :: rest)) :
    Disjoint (blockEdges r Q) (usedEdges r history) :=
  h.head_mem.2

/-- A legal history, started from the empty state, is a clique packing in
the ambient host containing `H`. -/
theorem followsAvailable_isCliquePacking
    {host H : Finset (Finset (Fin n))}
    (hH : ∀ Q ∈ H, Q.card = q ∧ blockEdges r Q ⊆ host)
    {path : List (Finset (Fin n))}
    (hpath : FollowsAvailable H r [] path) :
    IsCliquePacking host path.toFinset q r := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro Q hQ
    exact (hH Q (hpath.mem_H Q hQ)).1
  · intro Q hQ
    exact (hH Q (hpath.mem_H Q hQ)).2
  · intro Q hQ R hR hne
    exact hpath.pairwise_disjoint_edges Q hQ R hR hne

/-- The union state is exactly the edge union of the selected block
family. -/
theorem usedEdges_eq_coveredEdges (history : List (Finset (Fin n))) :
    usedEdges r history = coveredEdges r history.toFinset := by
  rfl

/-- The remaining process vertices are exactly the matching leave. -/
theorem host_sdiff_usedEdges_eq_leave
    (host : Finset (Finset (Fin n)))
    (history : List (Finset (Fin n))) :
    host \ usedEdges r history = leave host history.toFinset r := by
  rfl

end

end Erdos722.NibbleProcess
