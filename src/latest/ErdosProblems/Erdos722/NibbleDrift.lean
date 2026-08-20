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
import ErdosProblems.Erdos722.NibbleCodegree
import ErdosProblems.Erdos722.FiniteUnionBounds
import Mathlib

/-!
# Exact drift counts for clique removal

For an available clique `P` through a surviving edge `e`, its destroyers
are the available choices meeting one of the other edges of `P`.  The first
Bonferroni inequality and the design-hypergraph codegree bound show that
there are almost `(choose q r - 1)` times the typical degree many such
choices.  This is the finite combinatorial heart of the random-greedy drift
estimate.
-/

namespace Erdos722.NibbleDrift

open Finset
open Erdos722.NibbleBasics
open Erdos722.NibbleProcess
open Erdos722.NibbleCounters
open Erdos722.NibbleCodegree
open Erdos722.FiniteUnionBounds

noncomputable section

variable {n q r : ℕ}

/-- Available choices through a design-hypergraph vertex. -/
def edgeNeighborhood (H : Finset (Finset (Fin n))) (r : ℕ)
    (history : List (Finset (Fin n))) (e : Finset (Fin n)) :
    Finset (Finset (Fin n)) :=
  (availableCliques H r history).filter fun Q ↦ e ∈ blockEdges r Q

/-- All choices which delete an available clique `P`. -/
def cliqueDestroyers (H : Finset (Finset (Fin n))) (r : ℕ)
    (history : List (Finset (Fin n))) (P : Finset (Fin n)) :
    Finset (Finset (Fin n)) :=
  (availableCliques H r history).filter fun Q ↦
    ¬ Disjoint (blockEdges r P) (blockEdges r Q)

lemma cliqueDestroyers_eq_biUnion
    (H : Finset (Finset (Fin n))) (r : ℕ)
    (history : List (Finset (Fin n))) (P : Finset (Fin n)) :
    cliqueDestroyers H r history P =
      (blockEdges r P).biUnion (edgeNeighborhood H r history) := by
  ext Q
  constructor
  · intro hQ
    have hm := Finset.mem_filter.mp hQ
    rw [Finset.not_disjoint_iff] at hm
    obtain ⟨f, hfP, hfQ⟩ := hm.2
    exact Finset.mem_biUnion.mpr
      ⟨f, hfP, Finset.mem_filter.mpr ⟨hm.1, hfQ⟩⟩
  · intro hQ
    obtain ⟨f, hfP, hfQ⟩ := Finset.mem_biUnion.mp hQ
    have hm := Finset.mem_filter.mp hfQ
    apply Finset.mem_filter.mpr
    refine ⟨hm.1, ?_⟩
    rw [Finset.not_disjoint_iff]
    exact ⟨f, hfP, hm.2⟩

lemma card_edgeNeighborhood
    (H : Finset (Finset (Fin n))) (r : ℕ)
    (history : List (Finset (Fin n))) (e : Finset (Fin n)) :
    (edgeNeighborhood H r history e).card =
      availableDegree H r history e := by rfl

/-- Upper count for all choices deleting one available clique. -/
theorem card_cliqueDestroyers_le
    {H : Finset (Finset (Fin n))}
    {history : List (Finset (Fin n))} {P : Finset (Fin n)}
    (U : ℕ)
    (hupper : ∀ f ∈ blockEdges r P,
      availableDegree H r history f ≤ U) :
    (cliqueDestroyers H r history P).card ≤
      (blockEdges r P).card * U := by
  rw [cliqueDestroyers_eq_biUnion]
  calc
    ((blockEdges r P).biUnion (edgeNeighborhood H r history)).card ≤
        ∑ f ∈ blockEdges r P, (edgeNeighborhood H r history f).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _f ∈ blockEdges r P, U := by
      apply Finset.sum_le_sum
      intro f hf
      simpa [card_edgeNeighborhood] using hupper f hf
    _ = (blockEdges r P).card * U := by simp

/-- Bonferroni lower count for all choices deleting one available clique. -/
theorem card_blockEdges_mul_lower_le_cliqueDestroyers_add_error
    (hr : 0 < r) (hrq : r < q)
    {H : Finset (Finset (Fin n))}
    (hH : ∀ Q ∈ H, Q.card = q)
    {history : List (Finset (Fin n))} {P : Finset (Fin n)}
    (hPcard : P.card = q) (L : ℕ)
    (hlower : ∀ f ∈ blockEdges r P,
      L ≤ availableDegree H r history f) :
    (blockEdges r P).card * L ≤
      (cliqueDestroyers H r history P).card +
        (blockEdges r P).card ^ 2 * n ^ (q - r - 1) := by
  let S := blockEdges r P
  let F := edgeNeighborhood H r history
  have hfuniform : ∀ f ∈ S, f.card = r := by
    intro f hf
    exact (Finset.mem_powersetCard.mp hf).2
  have hpair : ∀ f ∈ S, ∀ g ∈ S.erase f,
      (F f ∩ F g).card ≤ n ^ (q - r - 1) := by
    intro f hf g hg
    have hgS := Finset.mem_of_mem_erase hg
    have hfg : f ≠ g := fun h ↦ (Finset.mem_erase.mp hg).1 (h ▸ rfl)
    have hsub : F f ∩ F g ⊆
        (availableCliques H r history).filter fun Q ↦
          f ∈ blockEdges r Q ∧ g ∈ blockEdges r Q := by
      intro Q hQ
      have hm := Finset.mem_inter.mp hQ
      have hfQ := Finset.mem_filter.mp hm.1
      have hgQ := Finset.mem_filter.mp hm.2
      exact Finset.mem_filter.mpr ⟨hfQ.1, hfQ.2, hgQ.2⟩
    apply (Finset.card_le_card hsub).trans
    exact availableCodegree_le hr hrq hH history
      (hfuniform f hf) (hfuniform g hgS) hfg
  have hbon := sum_card_le_card_biUnion_add_sq_mul S F
    (n ^ (q - r - 1)) hpair
  calc
    S.card * L = ∑ _f ∈ S, L := by simp
    _ ≤ ∑ f ∈ S, (F f).card := by
      apply Finset.sum_le_sum
      intro f hf
      simpa [F, card_edgeNeighborhood] using hlower f hf
    _ ≤ (S.biUnion F).card + S.card ^ 2 * n ^ (q - r - 1) := hbon
    _ = (cliqueDestroyers H r history P).card +
        S.card ^ 2 * n ^ (q - r - 1) := by
          rw [← cliqueDestroyers_eq_biUnion]

/-- Other design-hypergraph vertices in a clique through `e`. -/
def otherEdges (r : ℕ) (P e : Finset (Fin n)) :
    Finset (Finset (Fin n)) :=
  (blockEdges r P).erase e

/-- Available choices through `f` which do not cover `e`. -/
def survivingNeighborhood (H : Finset (Finset (Fin n))) (r : ℕ)
    (history : List (Finset (Fin n))) (e f : Finset (Fin n)) :
    Finset (Finset (Fin n)) :=
  (availableCliques H r history).filter fun Q ↦
    f ∈ blockEdges r Q ∧ e ∉ blockEdges r Q

/-- Choices which destroy `P` while leaving `e` uncovered. -/
def survivingDestroyers (H : Finset (Finset (Fin n))) (r : ℕ)
    (history : List (Finset (Fin n))) (e P : Finset (Fin n)) :
    Finset (Finset (Fin n)) :=
  (availableCliques H r history).filter fun Q ↦
    e ∉ blockEdges r Q ∧ ¬ Disjoint (blockEdges r P) (blockEdges r Q)

lemma survivingDestroyers_eq_biUnion
    (H : Finset (Finset (Fin n))) (r : ℕ)
    (history : List (Finset (Fin n))) (e P : Finset (Fin n)) :
    survivingDestroyers H r history e P =
      (otherEdges r P e).biUnion
        (survivingNeighborhood H r history e) := by
  ext Q
  constructor
  · intro hQ
    have hm := Finset.mem_filter.mp hQ
    have hQA := hm.1
    have heQ := hm.2.1
    have hmeet := hm.2.2
    rw [Finset.not_disjoint_iff] at hmeet
    obtain ⟨f, hfP, hfQ⟩ := hmeet
    have hfe : f ≠ e := by
      intro h
      exact heQ (h ▸ hfQ)
    exact Finset.mem_biUnion.mpr ⟨f,
      Finset.mem_erase.mpr ⟨hfe, hfP⟩,
      Finset.mem_filter.mpr ⟨hQA, hfQ, heQ⟩⟩
  · intro hQ
    obtain ⟨f, hfOther, hfN⟩ := Finset.mem_biUnion.mp hQ
    have hfOther' := Finset.mem_erase.mp hfOther
    have hfN' := Finset.mem_filter.mp hfN
    apply Finset.mem_filter.mpr
    refine ⟨hfN'.1, hfN'.2.2, ?_⟩
    rw [Finset.not_disjoint_iff]
    exact ⟨f, hfOther'.2, hfN'.2.1⟩

lemma card_otherEdges
    {P e : Finset (Fin n)} (hPcard : P.card = q)
    (heP : e ∈ blockEdges r P) :
    (otherEdges r P e).card = Nat.choose q r - 1 := by
  rw [otherEdges, Finset.card_erase_of_mem heP, card_blockEdges, hPcard]

lemma survivingNeighborhood_subset_through
    (H : Finset (Finset (Fin n))) (r : ℕ)
    (history : List (Finset (Fin n))) (e f : Finset (Fin n)) :
    survivingNeighborhood H r history e f ⊆
      (availableCliques H r history).filter fun Q ↦
        f ∈ blockEdges r Q := by
  intro Q hQ
  have hm := Finset.mem_filter.mp hQ
  exact Finset.mem_filter.mpr ⟨hm.1, hm.2.1⟩

lemma card_survivingNeighborhood_le_degree
    (H : Finset (Finset (Fin n))) (r : ℕ)
    (history : List (Finset (Fin n))) (e f : Finset (Fin n)) :
    (survivingNeighborhood H r history e f).card ≤
      availableDegree H r history f := by
  exact Finset.card_le_card
    (survivingNeighborhood_subset_through H r history e f)

lemma degree_le_survivingNeighborhood_add_codegree
    (H : Finset (Finset (Fin n))) (r : ℕ)
    (history : List (Finset (Fin n))) (e f : Finset (Fin n)) :
    availableDegree H r history f ≤
      (survivingNeighborhood H r history e f).card +
        availableCodegree H r history e f := by
  let through := (availableCliques H r history).filter fun Q ↦
    f ∈ blockEdges r Q
  let survive := survivingNeighborhood H r history e f
  let both := (availableCliques H r history).filter fun Q ↦
    e ∈ blockEdges r Q ∧ f ∈ blockEdges r Q
  have hsub : through ⊆ survive ∪ both := by
    intro Q hQ
    have hm := Finset.mem_filter.mp hQ
    by_cases heQ : e ∈ blockEdges r Q
    · exact Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨hm.1, heQ, hm.2⟩)
    · exact Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨hm.1, hm.2, heQ⟩)
  calc
    availableDegree H r history f = through.card := rfl
    _ ≤ (survive ∪ both).card := Finset.card_le_card hsub
    _ ≤ survive.card + both.card := Finset.card_union_le _ _
    _ = (survivingNeighborhood H r history e f).card +
        availableCodegree H r history e f := by rfl

lemma survivingNeighborhood_inter_subset_codegree
    (H : Finset (Finset (Fin n))) (r : ℕ)
    (history : List (Finset (Fin n))) (e f g : Finset (Fin n)) :
    survivingNeighborhood H r history e f ∩
        survivingNeighborhood H r history e g ⊆
      (availableCliques H r history).filter fun Q ↦
        f ∈ blockEdges r Q ∧ g ∈ blockEdges r Q := by
  intro Q hQ
  have hm := Finset.mem_inter.mp hQ
  have hf := Finset.mem_filter.mp hm.1
  have hg := Finset.mem_filter.mp hm.2
  exact Finset.mem_filter.mpr ⟨hf.1, hf.2.1, hg.2.1⟩

/-- Upper destroyer count from a uniform upper degree bound. -/
theorem card_survivingDestroyers_le
    {H : Finset (Finset (Fin n))}
    {history : List (Finset (Fin n))} {e P : Finset (Fin n)}
    (U : ℕ)
    (hupper : ∀ f ∈ otherEdges r P e,
      availableDegree H r history f ≤ U) :
    (survivingDestroyers H r history e P).card ≤
      (otherEdges r P e).card * U := by
  rw [survivingDestroyers_eq_biUnion]
  calc
    ((otherEdges r P e).biUnion
        (survivingNeighborhood H r history e)).card ≤
        ∑ f ∈ otherEdges r P e,
          (survivingNeighborhood H r history e f).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _f ∈ otherEdges r P e, U := by
      apply Finset.sum_le_sum
      intro f hf
      exact (card_survivingNeighborhood_le_degree H r history e f).trans
        (hupper f hf)
    _ = (otherEdges r P e).card * U := by simp

/-- Lower destroyer count from lower edge degrees and pairwise codegrees. -/
theorem card_otherEdges_mul_lower_le_destroyers_add_error
    (hr : 0 < r) (hrq : r < q)
    {H : Finset (Finset (Fin n))}
    (hH : ∀ Q ∈ H, Q.card = q)
    {history : List (Finset (Fin n))} {e P : Finset (Fin n)}
    (hecard : e.card = r) (hPcard : P.card = q)
    (heP : e ∈ blockEdges r P) (L : ℕ)
    (hlower : ∀ f ∈ otherEdges r P e,
      L ≤ availableDegree H r history f) :
    (otherEdges r P e).card * (L - n ^ (q - r - 1)) ≤
      (survivingDestroyers H r history e P).card +
        (otherEdges r P e).card ^ 2 * n ^ (q - r - 1) := by
  let S := otherEdges r P e
  let F := survivingNeighborhood H r history e
  have hfuniform : ∀ f ∈ S, f.card = r := by
    intro f hf
    exact (Finset.mem_powersetCard.mp
      (Finset.mem_erase.mp hf).2).2
  have hsingle : ∀ f ∈ S,
      L - n ^ (q - r - 1) ≤ (F f).card := by
    intro f hf
    have hcodeg := availableCodegree_le hr hrq hH history
      hecard (hfuniform f hf) (Finset.mem_erase.mp hf).1.symm
    have hdegree := degree_le_survivingNeighborhood_add_codegree
      H r history e f
    have hlo := hlower f hf
    dsimp [F]
    omega
  have hpair : ∀ f ∈ S, ∀ g ∈ S.erase f,
      (F f ∩ F g).card ≤ n ^ (q - r - 1) := by
    intro f hf g hg
    have hgS := Finset.mem_of_mem_erase hg
    have hfg : f ≠ g := by
      exact fun h ↦ (Finset.mem_erase.mp hg).1 (h ▸ rfl)
    apply (Finset.card_le_card
      (survivingNeighborhood_inter_subset_codegree H r history e f g)).trans
    exact availableCodegree_le hr hrq hH history
      (hfuniform f hf) (hfuniform g hgS) hfg
  have hbon := sum_card_le_card_biUnion_add_sq_mul S F
    (n ^ (q - r - 1)) hpair
  have hsumLower : S.card * (L - n ^ (q - r - 1)) ≤
      ∑ f ∈ S, (F f).card := by
    calc
      S.card * (L - n ^ (q - r - 1)) =
          ∑ _f ∈ S, (L - n ^ (q - r - 1)) := by simp
      _ ≤ ∑ f ∈ S, (F f).card := by
        exact Finset.sum_le_sum fun f hf ↦ hsingle f hf
  calc
    S.card * (L - n ^ (q - r - 1)) ≤
        ∑ f ∈ S, (F f).card := hsumLower
    _ ≤ (S.biUnion F).card + S.card ^ 2 * n ^ (q - r - 1) := hbon
    _ = (survivingDestroyers H r history e P).card +
        S.card ^ 2 * n ^ (q - r - 1) := by
          rw [← survivingDestroyers_eq_biUnion]

lemma mem_deletedAtEdge_iff_of_available_surviving
    {H : Finset (Finset (Fin n))}
    {history : List (Finset (Fin n))} {e Q P : Finset (Fin n)}
    (hQ : Q ∈ availableCliques H r history)
    (heQ : e ∉ blockEdges r Q) :
    P ∈ deletedAtEdge H r history e Q ↔
      P ∈ availableCliques H r history ∧
        e ∈ blockEdges r P ∧
        ¬ Disjoint (blockEdges r P) (blockEdges r Q) := by
  constructor
  · intro hP
    have hm := Finset.mem_filter.mp hP
    have hdel := Finset.mem_sdiff.mp hm.1
    refine ⟨hdel.1, hm.2, ?_⟩
    intro hdisj
    apply hdel.2
    have hPold := mem_availableCliques.mp hdel.1
    apply mem_availableCliques.mpr
    refine ⟨hPold.1, ?_⟩
    rw [usedEdges_append_single]
    apply Finset.disjoint_left.mpr
    intro f hfP hfUnion
    rcases Finset.mem_union.mp hfUnion with hfUsed | hfQ
    · exact Finset.disjoint_left.mp hPold.2 hfP hfUsed
    · exact Finset.disjoint_left.mp hdisj hfP hfQ
  · rintro ⟨hPold, heP, hmeet⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_sdiff.mpr ⟨hPold, ?_⟩, heP⟩
    intro hPnew
    have hm := mem_availableCliques.mp hPnew
    apply hmeet
    apply Finset.disjoint_left.mpr
    intro f hfP hfQ
    exact Finset.disjoint_left.mp hm.2 hfP
      (by rw [usedEdges_append_single]; exact Finset.mem_union_right _ hfQ)

/-- Exact double count of the degree loss of a surviving edge. -/
theorem sum_surviving_deletedAtEdge_eq_sum_destroyers
    (H : Finset (Finset (Fin n))) (r : ℕ)
    (history : List (Finset (Fin n))) (e : Finset (Fin n)) :
    (∑ Q ∈ availableCliques H r history,
        if e ∈ blockEdges r Q then 0
        else (deletedAtEdge H r history e Q).card) =
      ∑ P ∈ (availableCliques H r history).filter
          (fun P ↦ e ∈ blockEdges r P),
        (survivingDestroyers H r history e P).card := by
  let A := availableCliques H r history
  let T := A.filter fun P ↦ e ∈ blockEdges r P
  let rel : Finset (Fin n) → Finset (Fin n) → Prop := fun Q P ↦
    e ∉ blockEdges r Q ∧
      ¬ Disjoint (blockEdges r P) (blockEdges r Q)
  have hdouble := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (r := rel) (s := A) (t := T)
  calc
    (∑ Q ∈ availableCliques H r history,
        if e ∈ blockEdges r Q then 0
        else (deletedAtEdge H r history e Q).card) =
        ∑ Q ∈ A, (T.bipartiteAbove rel Q).card := by
          apply Finset.sum_congr rfl
          intro Q hQA
          by_cases heQ : e ∈ blockEdges r Q
          · have hempty : T.bipartiteAbove rel Q = ∅ := by
              apply Finset.eq_empty_iff_forall_notMem.mpr
              intro P hP
              exact (Finset.mem_filter.mp hP).2.1 heQ
            simp [heQ, hempty]
          · have heq : T.bipartiteAbove rel Q =
                deletedAtEdge H r history e Q := by
              ext P
              rw [Finset.mem_bipartiteAbove,
                mem_deletedAtEdge_iff_of_available_surviving hQA heQ]
              simp [T, rel, A, heQ, and_left_comm, and_assoc]
            simp [heQ, heq]
    _ = ∑ P ∈ T, (A.bipartiteBelow rel P).card := hdouble
    _ = ∑ P ∈ (availableCliques H r history).filter
          (fun P ↦ e ∈ blockEdges r P),
        (survivingDestroyers H r history e P).card := by
          apply Finset.sum_congr rfl
          intro P hPT
          rfl

/-- Uniform upper degree bounds give the exact upper drift estimate for a
surviving edge. -/
theorem sum_surviving_deletedAtEdge_le
    {host H : Finset (Finset (Fin n))}
    (hH : ∀ Q ∈ H, Q.card = q ∧ blockEdges r Q ⊆ host)
    (history : List (Finset (Fin n))) (e : Finset (Fin n)) (U : ℕ)
    (hupper : ∀ f ∈ residualHost host r history,
      availableDegree H r history f ≤ U) :
    (∑ Q ∈ availableCliques H r history,
        if e ∈ blockEdges r Q then 0
        else (deletedAtEdge H r history e Q).card) ≤
      availableDegree H r history e * (Nat.choose q r - 1) * U := by
  rw [sum_surviving_deletedAtEdge_eq_sum_destroyers]
  calc
    (∑ P ∈ (availableCliques H r history).filter
          (fun P ↦ e ∈ blockEdges r P),
        (survivingDestroyers H r history e P).card) ≤
        ∑ _P ∈ (availableCliques H r history).filter
          (fun P ↦ e ∈ blockEdges r P),
            (Nat.choose q r - 1) * U := by
      apply Finset.sum_le_sum
      intro P hP
      have hPA := Finset.mem_filter.mp hP
      have hPH := availableCliques_subset H r history hPA.1
      have hsub := blockEdges_subset_residual_of_available
        (fun Q hQ ↦ (hH Q hQ).2) hPA.1
      have hother : ∀ f ∈ otherEdges r P e,
          availableDegree H r history f ≤ U := by
        intro f hf
        exact hupper f (hsub (Finset.mem_of_mem_erase hf))
      simpa [card_otherEdges (hH P hPH).1 hPA.2] using
        card_survivingDestroyers_le (H := H) (history := history)
          (e := e) (P := P) U hother
    _ = availableDegree H r history e * (Nat.choose q r - 1) * U := by
      simp [availableDegree]
      ring

/-- Additive-error lower drift estimate.  This form avoids division and is
the one consumed by the real-valued barrier calculation. -/
theorem degree_mul_other_mul_lower_le_sum_deleted_add_error
    (hr : 0 < r) (hrq : r < q)
    {host H : Finset (Finset (Fin n))}
    (hH : ∀ Q ∈ H, Q.card = q ∧ blockEdges r Q ⊆ host)
    (history : List (Finset (Fin n)))
    {e : Finset (Fin n)} (hecard : e.card = r) (L : ℕ)
    (hlower : ∀ f ∈ residualHost host r history,
      L ≤ availableDegree H r history f) :
    availableDegree H r history e * (Nat.choose q r - 1) *
        (L - n ^ (q - r - 1)) ≤
      (∑ Q ∈ availableCliques H r history,
        if e ∈ blockEdges r Q then 0
        else (deletedAtEdge H r history e Q).card) +
      availableDegree H r history e *
        (Nat.choose q r - 1) ^ 2 * n ^ (q - r - 1) := by
  rw [sum_surviving_deletedAtEdge_eq_sum_destroyers]
  let T := (availableCliques H r history).filter
    (fun P ↦ e ∈ blockEdges r P)
  have hpoint : ∀ P ∈ T,
      (Nat.choose q r - 1) * (L - n ^ (q - r - 1)) ≤
        (survivingDestroyers H r history e P).card +
          (Nat.choose q r - 1) ^ 2 * n ^ (q - r - 1) := by
    intro P hP
    have hPA := Finset.mem_filter.mp hP
    have hPH := availableCliques_subset H r history hPA.1
    have hsub := blockEdges_subset_residual_of_available
      (fun Q hQ ↦ (hH Q hQ).2) hPA.1
    have hlowerOther : ∀ f ∈ otherEdges r P e,
        L ≤ availableDegree H r history f := by
      intro f hf
      exact hlower f (hsub (Finset.mem_of_mem_erase hf))
    simpa [card_otherEdges (hH P hPH).1 hPA.2] using
      card_otherEdges_mul_lower_le_destroyers_add_error
        hr hrq (fun Q hQ ↦ (hH Q hQ).1) hecard
        (hH P hPH).1 hPA.2 L hlowerOther
  have hsum := Finset.sum_le_sum hpoint
  have hTcard : T.card = availableDegree H r history e := rfl
  simpa [T, hTcard, Finset.sum_add_distrib, Nat.mul_add,
    Nat.add_mul, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hsum

lemma mem_deletedCliques_iff_of_available
    {H : Finset (Finset (Fin n))}
    {history : List (Finset (Fin n))} {Q P : Finset (Fin n)}
    (hQ : Q ∈ availableCliques H r history) :
    P ∈ deletedCliques H r history Q ↔
      P ∈ availableCliques H r history ∧
        ¬ Disjoint (blockEdges r P) (blockEdges r Q) := by
  constructor
  · intro hP
    have hm := Finset.mem_sdiff.mp hP
    refine ⟨hm.1, ?_⟩
    intro hdisj
    apply hm.2
    have hPold := mem_availableCliques.mp hm.1
    apply mem_availableCliques.mpr
    refine ⟨hPold.1, ?_⟩
    rw [usedEdges_append_single]
    apply Finset.disjoint_left.mpr
    intro f hfP hfUnion
    rcases Finset.mem_union.mp hfUnion with hfUsed | hfQ
    · exact Finset.disjoint_left.mp hPold.2 hfP hfUsed
    · exact Finset.disjoint_left.mp hdisj hfP hfQ
  · rintro ⟨hPold, hmeet⟩
    apply Finset.mem_sdiff.mpr
    refine ⟨hPold, ?_⟩
    intro hPnew
    have hm := mem_availableCliques.mp hPnew
    apply hmeet
    apply Finset.disjoint_left.mpr
    intro f hfP hfQ
    exact Finset.disjoint_left.mp hm.2 hfP
      (by rw [usedEdges_append_single]; exact Finset.mem_union_right _ hfQ)

/-- Exact double count of total available-clique deletion. -/
theorem sum_card_deletedCliques_eq_sum_cliqueDestroyers
    (H : Finset (Finset (Fin n))) (r : ℕ)
    (history : List (Finset (Fin n))) :
    (∑ Q ∈ availableCliques H r history,
        (deletedCliques H r history Q).card) =
      ∑ P ∈ availableCliques H r history,
        (cliqueDestroyers H r history P).card := by
  let A := availableCliques H r history
  let rel : Finset (Fin n) → Finset (Fin n) → Prop := fun Q P ↦
    ¬ Disjoint (blockEdges r P) (blockEdges r Q)
  have hdouble := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (r := rel) (s := A) (t := A)
  calc
    (∑ Q ∈ availableCliques H r history,
        (deletedCliques H r history Q).card) =
        ∑ Q ∈ A, (A.bipartiteAbove rel Q).card := by
          apply Finset.sum_congr rfl
          intro Q hQA
          congr 1
          ext P
          rw [Finset.mem_bipartiteAbove,
            mem_deletedCliques_iff_of_available hQA]
    _ = ∑ P ∈ A, (A.bipartiteBelow rel P).card := hdouble
    _ = ∑ P ∈ availableCliques H r history,
        (cliqueDestroyers H r history P).card := by rfl

/-- Uniform upper edge-degree bound gives total-deletion upper drift. -/
theorem sum_card_deletedCliques_le
    {host H : Finset (Finset (Fin n))}
    (hH : ∀ Q ∈ H, Q.card = q ∧ blockEdges r Q ⊆ host)
    (history : List (Finset (Fin n))) (U : ℕ)
    (hupper : ∀ e ∈ residualHost host r history,
      availableDegree H r history e ≤ U) :
    (∑ Q ∈ availableCliques H r history,
        (deletedCliques H r history Q).card) ≤
      (availableCliques H r history).card * Nat.choose q r * U := by
  rw [sum_card_deletedCliques_eq_sum_cliqueDestroyers]
  calc
    (∑ P ∈ availableCliques H r history,
        (cliqueDestroyers H r history P).card) ≤
        ∑ _P ∈ availableCliques H r history, Nat.choose q r * U := by
      apply Finset.sum_le_sum
      intro P hPA
      have hPH := availableCliques_subset H r history hPA
      have hsub := blockEdges_subset_residual_of_available
        (fun Q hQ ↦ (hH Q hQ).2) hPA
      have hp := card_cliqueDestroyers_le (H := H) (history := history)
        U (fun e he ↦ hupper e (hsub he))
      simpa [card_blockEdges, (hH P hPH).1] using hp
    _ = (availableCliques H r history).card * Nat.choose q r * U := by
      simp
      ring

/-- Additive-error total-deletion lower drift. -/
theorem card_available_mul_choose_mul_lower_le_sum_deleted_add_error
    (hr : 0 < r) (hrq : r < q)
    {host H : Finset (Finset (Fin n))}
    (hH : ∀ Q ∈ H, Q.card = q ∧ blockEdges r Q ⊆ host)
    (history : List (Finset (Fin n))) (L : ℕ)
    (hlower : ∀ e ∈ residualHost host r history,
      L ≤ availableDegree H r history e) :
    (availableCliques H r history).card * Nat.choose q r * L ≤
      (∑ Q ∈ availableCliques H r history,
        (deletedCliques H r history Q).card) +
      (availableCliques H r history).card *
        (Nat.choose q r) ^ 2 * n ^ (q - r - 1) := by
  rw [sum_card_deletedCliques_eq_sum_cliqueDestroyers]
  have hpoint : ∀ P ∈ availableCliques H r history,
      Nat.choose q r * L ≤
        (cliqueDestroyers H r history P).card +
          (Nat.choose q r) ^ 2 * n ^ (q - r - 1) := by
    intro P hPA
    have hPH := availableCliques_subset H r history hPA
    have hsub := blockEdges_subset_residual_of_available
      (fun Q hQ ↦ (hH Q hQ).2) hPA
    simpa [card_blockEdges, (hH P hPH).1] using
      card_blockEdges_mul_lower_le_cliqueDestroyers_add_error
        hr hrq (fun Q hQ ↦ (hH Q hQ).1) (hH P hPH).1 L
          (fun e he ↦ hlower e (hsub he))
  have hsum := Finset.sum_le_sum hpoint
  simpa [Finset.sum_add_distrib, Nat.mul_add, Nat.add_mul,
    Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hsum

end

end Erdos722.NibbleDrift
