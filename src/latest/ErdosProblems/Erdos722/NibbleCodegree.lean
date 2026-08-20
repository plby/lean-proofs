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
import ErdosProblems.Erdos722.NibbleCounters
import Mathlib

/-!
# Codegree bounds for the design hypergraph

Two distinct `r`-edges have a union of size at least `r+1`; consequently
the number of `q`-sets containing both is at most `n^(q-r-1)`.  This is the
bounded-jump input for every edge-degree counter in the clique-removal
process.
-/

namespace Erdos722.NibbleCodegree

open Finset
open Erdos722.NibbleBasics
open Erdos722.NibbleProcess
open Erdos722.NibbleCounters
open Erdos722.Typicality

noncomputable section

variable {n q r : ℕ}

/-- Available cliques containing both designated host edges. -/
def availableCodegree (H : Finset (Finset (Fin n))) (r : ℕ)
    (history : List (Finset (Fin n)))
    (e f : Finset (Fin n)) : ℕ :=
  ((availableCliques H r history).filter fun Q ↦
    e ∈ blockEdges r Q ∧ f ∈ blockEdges r Q).card

lemma card_union_ge_succ
    {e f : Finset (Fin n)} (hecard : e.card = r)
    (hfcard : f.card = r) (hne : e ≠ f) :
    r + 1 ≤ (e ∪ f).card := by
  have hnot : ¬ f ⊆ e := by
    intro hsub
    apply hne
    exact (Finset.eq_of_subset_of_card_le hsub (by omega)).symm
  obtain ⟨x, hxf, hxe⟩ := Set.not_subset.mp hnot
  have hproper : e ⊂ e ∪ f := by
    refine ⟨Finset.subset_union_left, ?_⟩
    intro hback
    exact hxe (hback (Finset.mem_union_right e hxf))
  have hcardlt := Finset.card_lt_card hproper
  omega

/-- Complete-host bound for `q`-sets containing two distinct `r`-sets. -/
lemma card_uniform_containing_pair_le
    (hr : 0 < r) (hrq : r < q)
    {e f : Finset (Fin n)} (hecard : e.card = r)
    (hfcard : f.card = r) (hne : e ≠ f) :
    ((uniformEdges n q).filter fun Q ↦ e ⊆ Q ∧ f ⊆ Q).card ≤
      n ^ (q - r - 1) := by
  classical
  let U := e ∪ f
  have hUcard : r + 1 ≤ U.card := card_union_ge_succ hecard hfcard hne
  have hn : 0 < n := by
    have hern : r ≤ n := by
      simpa [← hecard] using Finset.card_le_univ e
    omega
  by_cases hUq : U.card ≤ q
  · have heq :
        (uniformEdges n q).filter (fun Q ↦ e ⊆ Q ∧ f ⊆ Q) =
          ((Finset.univ : Finset (Fin n)).powersetCard q).filter
            (fun Q ↦ U ⊆ Q) := by
      ext Q
      simp only [uniformEdges, Finset.mem_filter, Finset.mem_powersetCard,
        U, Finset.union_subset_iff]
    rw [heq, Finset.card_filter_powersetCard_subset U Finset.univ q
      (Finset.subset_univ U) hUq]
    simp only [Finset.card_univ, Fintype.card_fin]
    calc
      Nat.choose (n - U.card) (q - U.card) ≤
          (n - U.card) ^ (q - U.card) := Nat.choose_le_pow _ _
      _ ≤ n ^ (q - U.card) := Nat.pow_le_pow_left (Nat.sub_le n U.card) _
      _ ≤ n ^ (q - r - 1) := Nat.pow_le_pow_right hn (by omega)
  · have hempty :
        (uniformEdges n q).filter (fun Q ↦ e ⊆ Q ∧ f ⊆ Q) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro Q hQ
      have hm := Finset.mem_filter.mp hQ
      have hUQ : U ⊆ Q := Finset.union_subset hm.2.1 hm.2.2
      have hcard := Finset.card_le_card hUQ
      have hQcard := mem_uniformEdges.mp hm.1
      omega
    simp [hempty]

/-- The same bound for any available subfamily of uniform `q`-sets. -/
theorem availableCodegree_le
    (hr : 0 < r) (hrq : r < q)
    {H : Finset (Finset (Fin n))}
    (hH : ∀ Q ∈ H, Q.card = q)
    (history : List (Finset (Fin n)))
    {e f : Finset (Fin n)} (hecard : e.card = r)
    (hfcard : f.card = r) (hne : e ≠ f) :
    availableCodegree H r history e f ≤ n ^ (q - r - 1) := by
  apply (Finset.card_le_card (fun Q hQ ↦ ?_)).trans
    (card_uniform_containing_pair_le hr hrq hecard hfcard hne)
  have hm := Finset.mem_filter.mp hQ
  have hQH := availableCliques_subset H r history hm.1
  have hQcard := hH Q hQH
  exact Finset.mem_filter.mpr
    ⟨mem_uniformEdges.mpr hQcard,
      (Finset.mem_powersetCard.mp hm.2.1).1,
      (Finset.mem_powersetCard.mp hm.2.2).1⟩

lemma deletedAtEdge_subset_biUnion
    {H : Finset (Finset (Fin n))}
    {history : List (Finset (Fin n))} {e Q : Finset (Fin n)} :
    deletedAtEdge H r history e Q ⊆
      (blockEdges r Q).biUnion (fun f ↦
        (availableCliques H r history).filter fun P ↦
          e ∈ blockEdges r P ∧ f ∈ blockEdges r P) := by
  intro P hP
  have hm := Finset.mem_filter.mp hP
  have hdel := Finset.mem_sdiff.mp hm.1
  have hPold := mem_availableCliques.mp hdel.1
  have hnotNew := hdel.2
  have hmeet : ¬ Disjoint (blockEdges r P) (blockEdges r Q) := by
    intro hdisj
    apply hnotNew
    apply mem_availableCliques.mpr
    refine ⟨hPold.1, ?_⟩
    rw [usedEdges_append_single]
    apply Finset.disjoint_left.mpr
    intro x hxP hxUnion
    rcases Finset.mem_union.mp hxUnion with hxUsed | hxQ
    · exact Finset.disjoint_left.mp hPold.2 hxP hxUsed
    · exact Finset.disjoint_left.mp hdisj hxP hxQ
  rw [Finset.not_disjoint_iff] at hmeet
  obtain ⟨f, hfP, hfQ⟩ := hmeet
  exact Finset.mem_biUnion.mpr
    ⟨f, hfQ, Finset.mem_filter.mpr ⟨hdel.1, hm.2, hfP⟩⟩

/-- If `e` survives the selected block, its available-degree jump is at
most clique size times the complete design-hypergraph codegree. -/
theorem card_deletedAtEdge_le
    (hr : 0 < r) (hrq : r < q)
    {H : Finset (Finset (Fin n))}
    (hH : ∀ Q ∈ H, Q.card = q)
    {history : List (Finset (Fin n))} {e Q : Finset (Fin n)}
    (hecard : e.card = r) (hQcard : Q.card = q)
    (heQ : e ∉ blockEdges r Q) :
    (deletedAtEdge H r history e Q).card ≤
      Nat.choose q r * n ^ (q - r - 1) := by
  have hsub := deletedAtEdge_subset_biUnion (r := r)
    (H := H) (history := history) (e := e) (Q := Q)
  calc
    (deletedAtEdge H r history e Q).card ≤
        ((blockEdges r Q).biUnion (fun f ↦
          (availableCliques H r history).filter fun P ↦
            e ∈ blockEdges r P ∧ f ∈ blockEdges r P)).card :=
      Finset.card_le_card hsub
    _ ≤ ∑ f ∈ blockEdges r Q,
        ((availableCliques H r history).filter fun P ↦
          e ∈ blockEdges r P ∧ f ∈ blockEdges r P).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _f ∈ blockEdges r Q, n ^ (q - r - 1) := by
      apply Finset.sum_le_sum
      intro f hf
      have hfcard : f.card = r := (Finset.mem_powersetCard.mp hf).2
      have hne : e ≠ f := by
        intro hef
        exact heQ (hef ▸ hf)
      exact availableCodegree_le hr hrq hH history hecard hfcard hne
    _ = _ := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      rw [card_blockEdges, hQcard]
      norm_num

lemma deletedCliques_subset_biUnion
    {H : Finset (Finset (Fin n))}
    {history : List (Finset (Fin n))} {Q : Finset (Fin n)} :
    deletedCliques H r history Q ⊆
      (blockEdges r Q).biUnion (fun e ↦
        (availableCliques H r history).filter fun P ↦
          e ∈ blockEdges r P) := by
  intro P hP
  have hdel := Finset.mem_sdiff.mp hP
  have hPold := mem_availableCliques.mp hdel.1
  have hmeet : ¬ Disjoint (blockEdges r P) (blockEdges r Q) := by
    intro hdisj
    apply hdel.2
    apply mem_availableCliques.mpr
    refine ⟨hPold.1, ?_⟩
    rw [usedEdges_append_single]
    apply Finset.disjoint_left.mpr
    intro x hxP hxUnion
    rcases Finset.mem_union.mp hxUnion with hxUsed | hxQ
    · exact Finset.disjoint_left.mp hPold.2 hxP hxUsed
    · exact Finset.disjoint_left.mp hdisj hxP hxQ
  rw [Finset.not_disjoint_iff] at hmeet
  obtain ⟨e, heP, heQ⟩ := hmeet
  exact Finset.mem_biUnion.mpr
    ⟨e, heQ, Finset.mem_filter.mpr ⟨hdel.1, heP⟩⟩

/-- Deleting one selected clique removes at most clique size times the
current maximum available edge-degree. -/
theorem card_deletedCliques_le
    {H : Finset (Finset (Fin n))}
    {history : List (Finset (Fin n))} {Q : Finset (Fin n)}
    (D : ℕ) (hdegree : ∀ e ∈ blockEdges r Q,
      availableDegree H r history e ≤ D) :
    (deletedCliques H r history Q).card ≤
      (blockEdges r Q).card * D := by
  have hsub := deletedCliques_subset_biUnion
    (r := r) (H := H) (history := history) (Q := Q)
  calc
    (deletedCliques H r history Q).card ≤
        ((blockEdges r Q).biUnion (fun e ↦
          (availableCliques H r history).filter fun P ↦
            e ∈ blockEdges r P)).card := Finset.card_le_card hsub
    _ ≤ ∑ e ∈ blockEdges r Q,
        ((availableCliques H r history).filter fun P ↦
          e ∈ blockEdges r P).card := Finset.card_biUnion_le
    _ ≤ ∑ _e ∈ blockEdges r Q, D := by
      apply Finset.sum_le_sum
      intro e he
      exact hdegree e he
    _ = _ := by simp

end

end Erdos722.NibbleCodegree
