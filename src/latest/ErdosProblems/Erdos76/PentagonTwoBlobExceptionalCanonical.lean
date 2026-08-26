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
import ErdosProblems.Erdos76.PentagonTwoBlobExceptional

/-!
# The canonical eight-vertex certificate for Proposition 7.2(d)

We label the blobs by `A = {0,1,2}` and `B = {3,4,5,6,7}`, and delete the
cross pairs `03` and `14`.  The three finite families below are exactly the
Appendix A cases of weight `1/2`, `1/3`, and `1/6`.
-/

open Finset

namespace Erdos76

noncomputable section

abbrev Proposition72dVertex := Fin 8

def proposition72dCanonicalA : Finset Proposition72dVertex := {0, 1, 2}

def proposition72dCanonicalB : Finset Proposition72dVertex := {3, 4, 5, 6, 7}

def proposition72dCanonicalMissing : Finset (Sym2 Proposition72dVertex) :=
  {s(0, 3), s(1, 4)}

def proposition72dCanonicalGraph : SimpleGraph Proposition72dVertex :=
  (⊤ : SimpleGraph Proposition72dVertex).deleteEdges
    (proposition72dCanonicalMissing : Set (Sym2 Proposition72dVertex))

def proposition72dCanonicalHalfFamily :
    Finset (Finset Proposition72dVertex) :=
  {{2, 3, 4}}

def proposition72dCanonicalThirdFamily :
    Finset (Finset Proposition72dVertex) :=
  {{0, 4, 5}, {0, 4, 6}, {0, 4, 7},
    {1, 3, 5}, {1, 3, 6}, {1, 3, 7}}

def proposition72dCanonicalSixthFamily :
    Finset (Finset Proposition72dVertex) :=
  {{0, 1, 5}, {0, 1, 6}, {0, 1, 7},
    {0, 2, 5}, {0, 2, 6}, {0, 2, 7},
    {1, 2, 5}, {1, 2, 6}, {1, 2, 7},
    {2, 3, 5}, {2, 3, 6}, {2, 3, 7},
    {2, 4, 5}, {2, 4, 6}, {2, 4, 7},
    {2, 5, 6}, {2, 5, 7}, {2, 6, 7},
    {0, 5, 6}, {0, 5, 7}, {0, 6, 7},
    {1, 5, 6}, {1, 5, 7}, {1, 6, 7}}

def proposition72dCanonicalWeight :
    Finset Proposition72dVertex → ℝ :=
  addTriangleWeight
    (constantTriangleFamilyWeight proposition72dCanonicalHalfFamily 2)
    (addTriangleWeight
      (constantTriangleFamilyWeight proposition72dCanonicalThirdFamily 3)
      (constantTriangleFamilyWeight proposition72dCanonicalSixthFamily 6))

private lemma proposition72dCanonicalGraph_isNClique_of_card_avoids
    (t : Finset Proposition72dVertex) (hcard : t.card = 3)
    (havoid : ∀ e ∈ proposition72dCanonicalMissing, ¬ e.toFinset ⊆ t) :
    proposition72dCanonicalGraph.IsNClique 3 t := by
  rw [SimpleGraph.isNClique_iff]
  refine ⟨?_, hcard⟩
  intro x hx y hy hxy
  change ((⊤ : SimpleGraph Proposition72dVertex).deleteEdges
    (proposition72dCanonicalMissing : Set (Sym2 Proposition72dVertex))).Adj x y
  rw [SimpleGraph.deleteEdges_adj]
  refine ⟨by simpa using hxy, ?_⟩
  intro hxyMissing
  exact havoid s(x, y) hxyMissing (by
    intro z hz
    simp only [Sym2.toFinset_mk_eq, mem_insert, mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact hx
    · exact hy)

private def Proposition72dCanonicalFamilyData
    (t : Finset Proposition72dVertex) : Prop :=
  t.card = 3 ∧
    (∀ e ∈ proposition72dCanonicalMissing, ¬ e.toFinset ⊆ t) ∧
      t ∈ twoOneTriangleFamily proposition72dCanonicalA proposition72dCanonicalB ∪
        twoOneTriangleFamily proposition72dCanonicalB proposition72dCanonicalA

private lemma proposition72dCanonicalHalfFamily_data :
    ∀ t ∈ proposition72dCanonicalHalfFamily,
      Proposition72dCanonicalFamilyData t := by
  intro t ht
  simp only [proposition72dCanonicalHalfFamily, mem_singleton] at ht
  subst t
  unfold Proposition72dCanonicalFamilyData
  decide

private lemma proposition72dCanonicalThirdFamily_data :
    ∀ t ∈ proposition72dCanonicalThirdFamily,
      Proposition72dCanonicalFamilyData t := by
  intro t ht
  simp only [proposition72dCanonicalThirdFamily, mem_insert, mem_singleton] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals unfold Proposition72dCanonicalFamilyData
  all_goals decide

private lemma proposition72dCanonicalSixthFamily_data :
    ∀ t ∈ proposition72dCanonicalSixthFamily,
      Proposition72dCanonicalFamilyData t := by
  intro t ht
  simp only [proposition72dCanonicalSixthFamily, mem_insert, mem_singleton] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals unfold Proposition72dCanonicalFamilyData
  all_goals decide

lemma proposition72dCanonicalHalfFamily_isNClique :
    ∀ t ∈ proposition72dCanonicalHalfFamily,
      proposition72dCanonicalGraph.IsNClique 3 t := by
  intro t ht
  exact proposition72dCanonicalGraph_isNClique_of_card_avoids t
    (proposition72dCanonicalHalfFamily_data t ht).1
    (proposition72dCanonicalHalfFamily_data t ht).2.1

lemma proposition72dCanonicalThirdFamily_isNClique :
    ∀ t ∈ proposition72dCanonicalThirdFamily,
      proposition72dCanonicalGraph.IsNClique 3 t := by
  intro t ht
  exact proposition72dCanonicalGraph_isNClique_of_card_avoids t
    (proposition72dCanonicalThirdFamily_data t ht).1
    (proposition72dCanonicalThirdFamily_data t ht).2.1

lemma proposition72dCanonicalSixthFamily_isNClique :
    ∀ t ∈ proposition72dCanonicalSixthFamily,
      proposition72dCanonicalGraph.IsNClique 3 t := by
  intro t ht
  exact proposition72dCanonicalGraph_isNClique_of_card_avoids t
    (proposition72dCanonicalSixthFamily_data t ht).1
    (proposition72dCanonicalSixthFamily_data t ht).2.1

lemma proposition72dCanonicalWeight_nonneg (t : Finset Proposition72dVertex) :
    0 ≤ proposition72dCanonicalWeight t := by
  simp only [proposition72dCanonicalWeight, addTriangleWeight,
    constantTriangleFamilyWeight]
  split_ifs <;> norm_num

def proposition72dCanonicalEdgeScore
    (e : Sym2 Proposition72dVertex) : ℕ :=
  3 * (proposition72dCanonicalHalfFamily.filter fun t ↦ e ∈ t.sym2).card +
    2 * (proposition72dCanonicalThirdFamily.filter fun t ↦ e ∈ t.sym2).card +
      (proposition72dCanonicalSixthFamily.filter fun t ↦ e ∈ t.sym2).card

private lemma proposition72dCanonicalEdgeScore_le
    (e : Sym2 Proposition72dVertex)
    (hne : ¬ e.IsDiag) :
    proposition72dCanonicalEdgeScore e ≤ 6 := by
  induction e using Sym2.inductionOn with
  | hf x y =>
      have hxy : x ≠ y := by
        simpa only [Sym2.mk_isDiag_iff] using hne
      fin_cases x <;> fin_cases y
      all_goals simp at hxy
      all_goals decide

lemma proposition72dCanonicalEdgeScore_eq_three_of_sameSide
    (e : Sym2 Proposition72dVertex) (hne : ¬ e.IsDiag)
    (hsame : SameSide (proposition72dCanonicalA : Set Proposition72dVertex) e) :
    proposition72dCanonicalEdgeScore e = 3 := by
  induction e using Sym2.inductionOn with
  | hf x y =>
      have hxy : x ≠ y := by
        simpa only [Sym2.mk_isDiag_iff] using hne
      simp only [sameSide_mk] at hsame
      fin_cases x <;> fin_cases y
      all_goals simp [proposition72dCanonicalA] at hxy hsame
      all_goals decide

lemma fractionalEdgeLoad_proposition72dCanonicalWeight
    (e : Sym2 Proposition72dVertex)
    (hne : ¬ e.IsDiag) :
    fractionalEdgeLoad proposition72dCanonicalGraph
      proposition72dCanonicalWeight e ≤ 1 := by
  rw [proposition72dCanonicalWeight,
    show addTriangleWeight _ _ = (fun t ↦ _ + _) by rfl,
    fractionalEdgeLoad_add,
    show addTriangleWeight _ _ = (fun t ↦ _ + _) by rfl,
    fractionalEdgeLoad_add,
    fractionalEdgeLoad_constantTriangleFamilyWeight
      proposition72dCanonicalHalfFamily_isNClique,
    fractionalEdgeLoad_constantTriangleFamilyWeight
      proposition72dCanonicalThirdFamily_isNClique,
      fractionalEdgeLoad_constantTriangleFamilyWeight
      proposition72dCanonicalSixthFamily_isNClique]
  have hscore := proposition72dCanonicalEdgeScore_le e hne
  unfold proposition72dCanonicalEdgeScore at hscore
  have hscoreReal :
      3 * (((proposition72dCanonicalHalfFamily.filter
          fun t ↦ e ∈ t.sym2).card : ℕ) : ℝ) +
        2 * (((proposition72dCanonicalThirdFamily.filter
          fun t ↦ e ∈ t.sym2).card : ℕ) : ℝ) +
          (((proposition72dCanonicalSixthFamily.filter
            fun t ↦ e ∈ t.sym2).card : ℕ) : ℝ) ≤ 6 := by
    exact_mod_cast hscore
  norm_num [div_eq_mul_inv] at hscoreReal ⊢
  linarith

lemma fractionalEdgeLoad_proposition72dCanonicalWeight_internal
    (e : Sym2 Proposition72dVertex)
    (he : e ∈ internalEdgeFinset proposition72dCanonicalGraph
      (proposition72dCanonicalA : Set Proposition72dVertex)) :
    fractionalEdgeLoad proposition72dCanonicalGraph
      proposition72dCanonicalWeight e = 1 / 2 := by
  classical
  rw [proposition72dCanonicalWeight,
    show addTriangleWeight _ _ = (fun t ↦ _ + _) by rfl,
    fractionalEdgeLoad_add,
    show addTriangleWeight _ _ = (fun t ↦ _ + _) by rfl,
    fractionalEdgeLoad_add,
    fractionalEdgeLoad_constantTriangleFamilyWeight
      proposition72dCanonicalHalfFamily_isNClique,
    fractionalEdgeLoad_constantTriangleFamilyWeight
      proposition72dCanonicalThirdFamily_isNClique,
    fractionalEdgeLoad_constantTriangleFamilyWeight
      proposition72dCanonicalSixthFamily_isNClique]
  have heData := mem_filter.mp he
  have hscore := proposition72dCanonicalEdgeScore_eq_three_of_sameSide e
    (proposition72dCanonicalGraph.not_isDiag_of_mem_edgeFinset heData.1)
    heData.2
  unfold proposition72dCanonicalEdgeScore at hscore
  have hscoreReal :
      3 * (((proposition72dCanonicalHalfFamily.filter
          fun t ↦ e ∈ t.sym2).card : ℕ) : ℝ) +
        2 * (((proposition72dCanonicalThirdFamily.filter
          fun t ↦ e ∈ t.sym2).card : ℕ) : ℝ) +
          (((proposition72dCanonicalSixthFamily.filter
            fun t ↦ e ∈ t.sym2).card : ℕ) : ℝ) = 3 := by
    exact_mod_cast hscore
  norm_num [div_eq_mul_inv] at hscoreReal ⊢
  linarith

lemma isFractionalPacking_proposition72dCanonicalWeight :
    IsFractionalPacking proposition72dCanonicalGraph
      proposition72dCanonicalWeight := by
  classical
  constructor
  · intro t _ht
    exact proposition72dCanonicalWeight_nonneg t
  · intro e _he
    exact fractionalEdgeLoad_proposition72dCanonicalWeight e
      (proposition72dCanonicalGraph.not_isDiag_of_mem_edgeFinset _he)

lemma proposition72dCanonicalFamilies_internalCross :
    proposition72dCanonicalHalfFamily ∪
        proposition72dCanonicalThirdFamily ∪
          proposition72dCanonicalSixthFamily ⊆
      internalCrossTriangles proposition72dCanonicalGraph
        (proposition72dCanonicalA : Set Proposition72dVertex) := by
  intro t ht
  have htri : proposition72dCanonicalGraph.IsNClique 3 t := by
    rcases mem_union.mp ht with htHalfThird | htSixth
    · rcases mem_union.mp htHalfThird with htHalf | htThird
      · exact proposition72dCanonicalHalfFamily_isNClique t htHalf
      · exact proposition72dCanonicalThirdFamily_isNClique t htThird
    · exact proposition72dCanonicalSixthFamily_isNClique t htSixth
  have htwo :
      t ∈ twoOneTriangleFamily proposition72dCanonicalA proposition72dCanonicalB ∪
        twoOneTriangleFamily proposition72dCanonicalB proposition72dCanonicalA := by
    rcases mem_union.mp ht with htHalfThird | htSixth
    · rcases mem_union.mp htHalfThird with htHalf | htThird
      · exact (proposition72dCanonicalHalfFamily_data t htHalf).2.2
      · exact (proposition72dCanonicalThirdFamily_data t htThird).2.2
    · exact (proposition72dCanonicalSixthFamily_data t htSixth).2.2
  have hAB : Disjoint proposition72dCanonicalA proposition72dCanonicalB := by
    decide
  rcases mem_union.mp htwo with htAB | htBA
  · exact twoOneTriangleFamily_mem_internalCrossTriangles_of_sides
      (s := (proposition72dCanonicalA : Set Proposition72dVertex))
      (fun _x hx ↦ hx)
      (fun _z hzB hzA ↦ Finset.disjoint_left.mp hAB hzA hzB)
      htAB htri
  · have hcomp := twoOneTriangleFamily_mem_internalCrossTriangles_of_sides
      (s := (proposition72dCanonicalA : Set Proposition72dVertex)ᶜ)
      (fun _x hxB ↦ by
        simp only [Set.mem_compl_iff, Finset.mem_coe]
        exact fun hxA ↦ Finset.disjoint_left.mp hAB hxA hxB)
      (fun _z hzA ↦ by simp [hzA]) htBA htri
    simpa only [internalCrossTriangles_set_compl] using hcomp

lemma proposition72dCanonicalWeight_support
    (t : Finset Proposition72dVertex)
    (ht : t ∉ internalCrossTriangles proposition72dCanonicalGraph
      (proposition72dCanonicalA : Set Proposition72dVertex)) :
    proposition72dCanonicalWeight t = 0 := by
  have hHalf : t ∉ proposition72dCanonicalHalfFamily := fun h ↦
    ht (proposition72dCanonicalFamilies_internalCross
      (mem_union_left _ (mem_union_left _ h)))
  have hThird : t ∉ proposition72dCanonicalThirdFamily := fun h ↦
    ht (proposition72dCanonicalFamilies_internalCross
      (mem_union_left _ (mem_union_right _ h)))
  have hSixth : t ∉ proposition72dCanonicalSixthFamily := fun h ↦
    ht (proposition72dCanonicalFamilies_internalCross
      (mem_union_right _ h))
  simp [proposition72dCanonicalWeight, addTriangleWeight,
    constantTriangleFamilyWeight, hHalf, hThird, hSixth]

theorem isFractionalInternalCrossPacking_proposition72dCanonicalWeight :
    IsFractionalInternalCrossPacking proposition72dCanonicalGraph
      (proposition72dCanonicalA : Set Proposition72dVertex)
      proposition72dCanonicalWeight :=
  ⟨isFractionalPacking_proposition72dCanonicalWeight,
    proposition72dCanonicalWeight_support⟩

private lemma proposition72dCanonicalHalfFamily_card :
    proposition72dCanonicalHalfFamily.card = 1 := by decide

private lemma proposition72dCanonicalThirdFamily_card :
    proposition72dCanonicalThirdFamily.card = 6 := by decide

private lemma proposition72dCanonicalSixthFamily_card :
    proposition72dCanonicalSixthFamily.card = 24 := by decide

theorem proposition72dCanonicalPacking :
    IsFractionalInternalCrossPacking proposition72dCanonicalGraph
        (proposition72dCanonicalA : Set Proposition72dVertex)
        proposition72dCanonicalWeight ∧
      fractionalSize proposition72dCanonicalGraph
          proposition72dCanonicalWeight = 13 / 2 := by
  refine ⟨isFractionalInternalCrossPacking_proposition72dCanonicalWeight, ?_⟩
  rw [proposition72dCanonicalWeight,
    fractionalSize_addTriangleWeight,
    fractionalSize_addTriangleWeight,
    fractionalSize_constantTriangleFamilyWeight
      proposition72dCanonicalHalfFamily_isNClique,
    fractionalSize_constantTriangleFamilyWeight
      proposition72dCanonicalThirdFamily_isNClique,
    fractionalSize_constantTriangleFamilyWeight
      proposition72dCanonicalSixthFamily_isNClique,
    proposition72dCanonicalHalfFamily_card,
    proposition72dCanonicalThirdFamily_card,
    proposition72dCanonicalSixthFamily_card]
  norm_num

end

end Erdos76
