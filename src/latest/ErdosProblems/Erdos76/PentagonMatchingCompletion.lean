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
import ErdosProblems.Erdos76.PentagonMatchingWeights

/-!
# Completing a cross matching

A matching between disjoint finite sets `A` and `B`, with `|A| ≤ |B|`,
extends to the matching represented by an embedding `A ↪ B`.  This is the
finite completion step used to pass from the saturated form of Proposition
7.2(b) to the paper's arbitrary-matching statement.
-/

open Finset

namespace Erdos76

noncomputable section

attribute [local instance] Classical.propDecidable

variable {α : Type*} [DecidableEq α]

/-- A cross matching is supported on the displayed pair of finite sides. -/
def IsABCrossMatching (A B : Finset α) (M : Finset (Sym2 α)) : Prop :=
  IsCrossMatching (A : Set α) M ∧
    ∀ e ∈ M, e.toFinset ⊆ A ∪ B

/-- Every pair in a supported cross matching has a unique orientation from
`A` to `B`.  Only existence is recorded here; uniqueness follows from the
matching property and is used below. -/
lemma IsABCrossMatching.exists_orientation
    {A B : Finset α} {M : Finset (Sym2 α)}
    (hM : IsABCrossMatching A B M) {e : Sym2 α} (he : e ∈ M) :
    ∃ p : A × B, e = s(p.1.1, p.2.1) := by
  classical
  induction e using Sym2.inductionOn with
  | hf x y =>
      have hnotSame : ¬SameSide (A : Set α) s(x, y) := hM.1.1 _ he
      have hsupport : s(x, y).toFinset ⊆ A ∪ B := hM.2 _ he
      have hxUnion : x ∈ A ∪ B := hsupport (by simp)
      have hyUnion : y ∈ A ∪ B := hsupport (by simp)
      by_cases hxA : x ∈ A
      · have hyA : y ∉ A := by
          intro hyA
          apply hnotSame
          simp [sameSide_mk, hxA, hyA]
        have hyB : y ∈ B := (mem_union.mp hyUnion).resolve_left hyA
        exact ⟨(⟨x, hxA⟩, ⟨y, hyB⟩), rfl⟩
      · have hyA : y ∈ A := by
          by_contra hyA
          apply hnotSame
          simp [sameSide_mk, hxA, hyA]
        have hxB : x ∈ B := (mem_union.mp hxUnion).resolve_left hxA
        refine ⟨(⟨y, hyA⟩, ⟨x, hxB⟩), ?_⟩
        exact Sym2.eq_swap

/-- A chosen orientation of every edge of a supported cross matching. -/
noncomputable def crossMatchingOrientation
    {A B : Finset α} {M : Finset (Sym2 α)}
    (hM : IsABCrossMatching A B M) (e : M) : A × B :=
  Classical.choose (hM.exists_orientation e.2)

lemma crossMatchingOrientation_spec
    {A B : Finset α} {M : Finset (Sym2 α)}
    (hM : IsABCrossMatching A B M) (e : M) :
    e.1 = s((crossMatchingOrientation hM e).1.1,
      (crossMatchingOrientation hM e).2.1) :=
  Classical.choose_spec (hM.exists_orientation e.2)

/-- The left endpoints of distinct pairs of a matching are distinct. -/
lemma crossMatchingOrientation_left_injective
    {A B : Finset α} {M : Finset (Sym2 α)}
    (hM : IsABCrossMatching A B M) :
    Function.Injective (fun e : M ↦ (crossMatchingOrientation hM e).1) := by
  classical
  intro e q heq
  apply Subtype.ext
  by_contra hne
  have hdis := hM.1.2 e.2 q.2 hne
  have heMem : (crossMatchingOrientation hM e).1.1 ∈ e.1.toFinset := by
    rw [crossMatchingOrientation_spec hM e]
    simp
  have hqMem : (crossMatchingOrientation hM q).1.1 ∈ q.1.toFinset := by
    rw [crossMatchingOrientation_spec hM q]
    simp
  have hval : (crossMatchingOrientation hM e).1.1 =
      (crossMatchingOrientation hM q).1.1 := congrArg Subtype.val heq
  exact (Finset.disjoint_left.mp hdis heMem (hval ▸ hqMem)).elim

/-- The right endpoints of distinct pairs of a matching are distinct. -/
lemma crossMatchingOrientation_right_injective
    {A B : Finset α} {M : Finset (Sym2 α)}
    (hM : IsABCrossMatching A B M) :
    Function.Injective (fun e : M ↦ (crossMatchingOrientation hM e).2) := by
  classical
  intro e q heq
  apply Subtype.ext
  by_contra hne
  have hdis := hM.1.2 e.2 q.2 hne
  have heMem : (crossMatchingOrientation hM e).2.1 ∈ e.1.toFinset := by
    rw [crossMatchingOrientation_spec hM e]
    simp
  have hqMem : (crossMatchingOrientation hM q).2.1 ∈ q.1.toFinset := by
    rw [crossMatchingOrientation_spec hM q]
    simp
  have hval : (crossMatchingOrientation hM e).2.1 =
      (crossMatchingOrientation hM q).2.1 := congrArg Subtype.val heq
  exact (Finset.disjoint_left.mp hdis heMem (hval ▸ hqMem)).elim

/-- Complete a supported cross matching to one saturating the smaller side.
The proof first chooses any embedding `A ↪ B`, then permutes `B` so that it
agrees with all already prescribed matching pairs. -/
theorem exists_embeddingCrossMatching_superset
    {A B : Finset α} {M : Finset (Sym2 α)}
    (hcard : A.card ≤ B.card) (hM : IsABCrossMatching A B M) :
    ∃ f : A ↪ B, M ⊆ embeddingCrossMatching A B f := by
  classical
  have hcard' : Fintype.card A ≤ Fintype.card B := by simpa using hcard
  obtain ⟨f₀ : A ↪ B⟩ := Function.Embedding.nonempty_of_card_le hcard'
  let left : M ↪ A :=
    ⟨fun e ↦ (crossMatchingOrientation hM e).1,
      crossMatchingOrientation_left_injective hM⟩
  let right : M ↪ B :=
    ⟨fun e ↦ (crossMatchingOrientation hM e).2,
      crossMatchingOrientation_right_injective hM⟩
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair
    (fun e : M ↦ f₀ (left e)) (fun e : M ↦ right e)
    (f₀.injective.comp left.injective) right.injective
  let f : A ↪ B := f₀.trans σ.toEmbedding
  refine ⟨f, ?_⟩
  intro e he
  let em : M := ⟨e, he⟩
  have horient := crossMatchingOrientation_spec hM em
  have hf : f (left em) = right em := by
    exact hσ em
  apply mem_image.mpr
  refine ⟨left em, mem_univ _, ?_⟩
  calc
    s((left em).1, (f (left em)).1) =
        s((left em).1, (right em).1) :=
      congrArg (fun b : B ↦ s((left em).1, b.1)) hf
    _ = e := by simpa [left, right, em] using horient.symm

end

end Erdos76
