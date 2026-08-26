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
import ErdosProblems.Erdos76.PentagonTwoBlob

/-!
# Saturated cross matchings for Proposition 7.2(b)

A cross matching can be enlarged until it saturates the smaller blob.  The
Appendix A weight is easiest to state after choosing the corresponding
embedding of the smaller blob into the larger one.  This module records the
finite matching represented by such an embedding and its exact endpoint
counts; the weight construction is built on these lemmas.
-/

open Finset
open scoped BigOperators

namespace Erdos76

noncomputable section

attribute [local instance] Classical.propDecidable

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The forbidden cross pairs specified by an embedding of `A` into `B`. -/
def embeddingCrossMatching (A B : Finset α) (f : A ↪ B) : Finset (Sym2 α) :=
  Finset.univ.image fun a : A ↦ s(a.1, (f a).1)

/-- Vertices of `B` hit by the matching embedding. -/
def embeddingRangeFinset (A B : Finset α) (f : A ↪ B) : Finset α :=
  Finset.univ.image fun a : A ↦ (f a).1

lemma embeddingRangeFinset_subset (A B : Finset α) (f : A ↪ B) :
    embeddingRangeFinset A B f ⊆ B := by
  classical
  intro b hb
  obtain ⟨a, _ha, rfl⟩ := mem_image.mp hb
  exact (f a).2

lemma mem_embeddingRangeFinset (A B : Finset α) (f : A ↪ B) (a : A) :
    (f a).1 ∈ embeddingRangeFinset A B f := by
  classical
  exact mem_image.mpr ⟨a, mem_univ _, rfl⟩

lemma card_embeddingRangeFinset (A B : Finset α) (f : A ↪ B) :
    (embeddingRangeFinset A B f).card = A.card := by
  classical
  rw [embeddingRangeFinset]
  calc
    (Finset.univ.image fun a : A ↦ (f a).1).card =
        (Finset.univ : Finset A).card := by
      apply card_image_of_injOn
      intro a _ b _ hab
      exact f.injective (Subtype.ext hab)
    _ = A.card := by simp

private lemma left_endpoint_ne_right_endpoint
    {A B : Finset α} (hAB : Disjoint A B) (a : A) (b : B) :
    a.1 ≠ b.1 := by
  intro h
  exact Finset.disjoint_left.mp hAB a.2 (h ▸ b.2)

lemma card_embeddingCrossMatching
    {A B : Finset α} (hAB : Disjoint A B) (f : A ↪ B) :
    (embeddingCrossMatching A B f).card = A.card := by
  classical
  rw [embeddingCrossMatching]
  calc
    (Finset.univ.image fun a : A ↦ s(a.1, (f a).1)).card =
        (Finset.univ : Finset A).card := by
      apply card_image_of_injOn
      intro a _ b _ hab
      have haMem : a.1 ∈ s(b.1, (f b).1).toFinset := by
        have haSelf : a.1 ∈ s(a.1, (f a).1).toFinset := by simp
        exact (congrArg (fun e : Sym2 α ↦ a.1 ∈ e.toFinset) hab).mp haSelf
      have haCases : a.1 = b.1 ∨ a.1 = (f b).1 := by
        simpa [Sym2.toFinset_mk_eq] using haMem
      rcases haCases with ha | ha
      · exact Subtype.ext ha
      · exact (left_endpoint_ne_right_endpoint hAB a (f b) ha).elim
    _ = A.card := by simp

lemma matching_pair_mem
    (A B : Finset α) (f : A ↪ B) (a : A) :
    s(a.1, (f a).1) ∈ embeddingCrossMatching A B f := by
  classical
  exact mem_image.mpr ⟨a, mem_univ _, rfl⟩

/-- Distinct embedding pairs have disjoint endpoint sets. -/
lemma embeddingCrossMatching_pairwiseDisjoint
    {A B : Finset α} (hAB : Disjoint A B) (f : A ↪ B) :
    (embeddingCrossMatching A B f : Set (Sym2 α)).PairwiseDisjoint
      fun e ↦ e.toFinset := by
  classical
  intro e he q hq heq
  obtain ⟨a, _ha, rfl⟩ := mem_image.mp he
  obtain ⟨b, _hb, rfl⟩ := mem_image.mp hq
  apply Finset.disjoint_left.mpr
  intro x hxa hxb
  have hxa' : x = a.1 ∨ x = (f a).1 := by
    simpa [Sym2.toFinset_mk_eq] using hxa
  have hxb' : x = b.1 ∨ x = (f b).1 := by
    simpa [Sym2.toFinset_mk_eq] using hxb
  rcases hxa' with hxa' | hxa' <;> rcases hxb' with hxb' | hxb'
  · apply heq
    have hab : a = b := Subtype.ext (hxa'.symm.trans hxb')
    subst b
    rfl
  · exact (left_endpoint_ne_right_endpoint hAB a (f b)
      (hxa'.symm.trans hxb')).elim
  · exact (left_endpoint_ne_right_endpoint hAB b (f a)
      (hxb'.symm.trans hxa')).elim
  · apply heq
    have hab : a = b := f.injective (Subtype.ext (hxa'.symm.trans hxb'))
    subst b
    rfl

/-- The embedding pairs form a cross matching for the bipartition with
first side `A`. -/
lemma isCrossMatching_embeddingCrossMatching
    {A B : Finset α} (hAB : Disjoint A B) (f : A ↪ B) :
    IsCrossMatching (A : Set α) (embeddingCrossMatching A B f) := by
  classical
  constructor
  · intro e he
    obtain ⟨a, _ha, rfl⟩ := mem_image.mp he
    rw [sameSide_mk]
    have hfA : (f a).1 ∉ A := fun hfA ↦
      Finset.disjoint_left.mp hAB hfA (f a).2
    simp [a.2, hfA]
  · exact embeddingCrossMatching_pairwiseDisjoint hAB f

lemma card_unmatched_embeddingRange_le_one
    {A B : Finset α} (hABcard : B.card ≤ A.card + 1) (f : A ↪ B) :
    (B \ embeddingRangeFinset A B f).card ≤ 1 := by
  classical
  rw [card_sdiff_of_subset (embeddingRangeFinset_subset A B f),
    card_embeddingRangeFinset]
  omega

/-- The complete graph with precisely the embedding pairs deleted. -/
def completeExceptEmbeddingMatching
    (A B : Finset α) (f : A ↪ B) : SimpleGraph α :=
  (⊤ : SimpleGraph α).deleteEdges
    (embeddingCrossMatching A B f : Set (Sym2 α))

lemma completeExceptEmbeddingMatching_cross_adj
    {A B : Finset α} (hAB : Disjoint A B) (f : A ↪ B)
    (a : A) (b : B) :
    (completeExceptEmbeddingMatching A B f).Adj a.1 b.1 ↔ b ≠ f a := by
  classical
  have hab : a.1 ≠ b.1 := left_endpoint_ne_right_endpoint hAB a b
  rw [completeExceptEmbeddingMatching, SimpleGraph.deleteEdges_adj]
  simp only [SimpleGraph.top_adj, hab, true_and]
  constructor
  · intro hnot hbf
    subst b
    exact hnot.2 (matching_pair_mem A B f a)
  · intro hbf
    refine ⟨hab, ?_⟩
    intro hmem
    obtain ⟨c, _hc, hcEq⟩ := mem_image.mp hmem
    have haMem : a.1 ∈ s(c.1, (f c).1).toFinset := by
      have haSelf : a.1 ∈ s(a.1, b.1).toFinset := by simp
      exact (congrArg (fun e : Sym2 α ↦ a.1 ∈ e.toFinset) hcEq).mpr haSelf
    have haCases : a.1 = c.1 ∨ a.1 = (f c).1 := by
      simpa [Sym2.toFinset_mk_eq] using haMem
    rcases haCases with hac | hac
    · have hca : c = a := Subtype.ext hac.symm
      subst c
      have hbMem : b.1 ∈ s(a.1, (f a).1).toFinset := by
        have hbSelf : b.1 ∈ s(a.1, b.1).toFinset := by simp
        exact (congrArg (fun e : Sym2 α ↦ b.1 ∈ e.toFinset) hcEq).mpr hbSelf
      have hbCases : b.1 = a.1 ∨ b.1 = (f a).1 := by
        simpa [Sym2.toFinset_mk_eq] using hbMem
      rcases hbCases with hba | hba
      · exact (hab hba.symm).elim
      · exact hbf (Subtype.ext hba)
    · exact (left_endpoint_ne_right_endpoint hAB a (f c) hac).elim

end

end Erdos76
