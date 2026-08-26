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
import ErdosProblems.Erdos76.AlmostCompleteCompactness

/-!
# The downward reduction for almost-complete decompositions

This file formalizes Gruslys--Letzter Lemma 2.3: an exact-cardinality
fractional-decomposition theorem automatically holds with "at most" in place
of "exactly".  The induction deletes each of the three edges of a triangle,
averages the three decompositions, and restores the triangle with weight
`1 / 3`.
-/

open Finset
open scoped BigOperators

namespace Erdos76

noncomputable section

attribute [local instance] Classical.propDecidable

variable {A : Type*} [Fintype A] [DecidableEq A]

lemma card_edges_add_missing (G : SimpleGraph A) :
    Nat.card G.edgeSet + missingEdgeCount G =
      (Fintype.card A).choose 2 := by
  have hdisj : Disjoint G.edgeFinset Gᶜ.edgeFinset := by
    rw [Finset.disjoint_left]
    intro e heG heGc
    induction e using Sym2.inductionOn with
    | hf a b =>
        have hab : G.Adj a b := by
          simpa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using heG
        have hnab : ¬ G.Adj a b := by
          have hcomp : Gᶜ.Adj a b := by
            simpa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using heGc
          exact hcomp.2
        exact hnab hab
  have hunion : G.edgeFinset ∪ Gᶜ.edgeFinset =
      (⊤ : SimpleGraph A).edgeFinset := by
    ext e
    induction e using Sym2.inductionOn with
    | hf a b =>
        simp only [mem_union, SimpleGraph.mem_edgeFinset,
          SimpleGraph.mem_edgeSet, SimpleGraph.compl_adj,
          SimpleGraph.top_adj]
        by_cases hab : G.Adj a b
        · exact ⟨fun _ ↦ hab.ne, fun _ ↦ Or.inl hab⟩
        · constructor
          · rintro (h | ⟨hne, _⟩)
            · exact h.ne
            · exact hne
          · intro hne
            exact Or.inr ⟨hne, hab⟩
  rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card, missingEdgeCount,
    ← card_union_of_disjoint hdisj, hunion]
  exact SimpleGraph.card_edgeFinset_top_eq_card_choose_two

lemma pred_le_choose_two (n : ℕ) : n - 1 ≤ n.choose 2 := by
  cases n with
  | zero => simp
  | succ k =>
      rw [Nat.choose_succ_succ]
      simp

lemma four_le_card_edges_of_missing_lt (G : SimpleGraph A)
    (hcard : 7 ≤ Fintype.card A)
    {m : ℕ} (hm : m ≤ Fintype.card A - 4)
    (hmissing : missingEdgeCount G < m) : 4 ≤ G.edgeFinset.card := by
  rw [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card]
  have hp := pred_le_choose_two (Fintype.card A)
  have hsum := card_edges_add_missing G
  omega

lemma missingEdgeCount_delete_singleton {G : SimpleGraph A} {e : Sym2 A}
    (he : e ∈ G.edgeFinset) :
    missingEdgeCount (G.deleteEdges ({e} : Finset (Sym2 A))) =
      missingEdgeCount G + 1 := by
  have hcard : (G.deleteEdges ({e} : Finset (Sym2 A))).edgeFinset.card =
      G.edgeFinset.card - 1 := by
    rw [SimpleGraph.edgeFinset_deleteEdges]
    simpa using card_sdiff_of_subset (show ({e} : Finset (Sym2 A)) ⊆ G.edgeFinset by
      simpa using he)
  rw [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card,
    SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at hcard
  have hsumG := card_edges_add_missing G
  have hsumH := card_edges_add_missing
    (G.deleteEdges ({e} : Finset (Sym2 A)))
  have heCard : 1 ≤ Nat.card G.edgeSet := by
    have hne : Nonempty G.edgeSet :=
      ⟨⟨e, SimpleGraph.mem_edgeFinset.mp he⟩⟩
    exact Finite.card_pos_iff.mpr hne
  have hcard' : Nat.card G.edgeSet =
      Nat.card (G.deleteEdges ({e} : Finset (Sym2 A))).edgeSet + 1 := by
    omega
  have hsumEq : Nat.card G.edgeSet + missingEdgeCount G =
      Nat.card (G.deleteEdges ({e} : Finset (Sym2 A))).edgeSet +
        missingEdgeCount (G.deleteEdges ({e} : Finset (Sym2 A))) :=
    hsumG.trans hsumH.symm
  omega

lemma exists_triangle_of_fractionalDecomposition
    {G : SimpleGraph A} {w : Finset A → ℝ}
    (hw : IsFractionalDecomposition G w) (hne : G.edgeSet.Nonempty) :
    ∃ t, G.IsNClique 3 t := by
  obtain ⟨e, he⟩ := hne
  have he' : e ∈ G.edgeFinset := by
    rw [SimpleGraph.mem_edgeFinset]
    exact he
  by_contra htri
  have hempty : G.cliqueFinset 3 = ∅ := by
    apply not_nonempty_iff_eq_empty.mp
    intro hne'
    obtain ⟨t, ht⟩ := hne'
    exact htri ⟨t, SimpleGraph.mem_cliqueFinset_iff.mp ht⟩
  have hload := hw.edgeLoad_eq_one he'
  simp [fractionalEdgeLoad, hempty] at hload

lemma averageSubgraphPacking_isCapacityDecomposition_in
    {I : Type*} [Fintype I] [Nonempty I]
    (G : SimpleGraph A) (H : I → SimpleGraph A)
    (hHG : ∀ i, H i ≤ G) (w : I → Finset A → ℝ)
    (hw : ∀ i, IsFractionalDecomposition (H i) (w i)) :
    IsCapacityDecomposition G (averageGraphCapacity H)
      (averageSubgraphPacking H w) := by
  constructor
  · constructor
    · apply averageTriangleWeight_nonneg
      intro i
      exact zeroExtendTriangleWeight_nonneg (hHG i) (hw i).isPacking
    · intro e he
      rw [averageSubgraphPacking, fractionalEdgeLoad_average]
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg _))
      gcongr with i
      rw [fractionalEdgeLoad_zeroExtend (hHG i)]
      by_cases hei : e ∈ (H i).edgeFinset
      · rw [(hw i).edgeLoad_eq_one hei, if_pos hei]
      · have heND : ¬ e.IsDiag := SimpleGraph.not_isDiag_of_mem_edgeFinset he
        rw [fractionalEdgeLoad_eq_zero_of_not_edge (H i) (w i) heND hei,
          if_neg hei]
  · intro e he
    rw [averageSubgraphPacking, fractionalEdgeLoad_average, averageGraphCapacity]
    congr 1
    apply sum_congr rfl
    intro i hi
    rw [fractionalEdgeLoad_zeroExtend (hHG i)]
    by_cases hei : e ∈ (H i).edgeFinset
    · rw [(hw i).edgeLoad_eq_one hei, if_pos hei]
    · have heND : ¬ e.IsDiag := SimpleGraph.not_isDiag_of_mem_edgeFinset he
      rw [fractionalEdgeLoad_eq_zero_of_not_edge (H i) (w i) heND hei,
        if_neg hei]

/-- Proposition-level version of `averageGraphCapacity`.  Using `edgeSet`
keeps graph-family reduction independent of synthesized decidability data. -/
def averageGraphCapacitySet {I : Type*} [Fintype I]
    (H : I → SimpleGraph A) : Sym2 A → ℝ :=
  fun e ↦ (Fintype.card I : ℝ)⁻¹ * ∑ i, if e ∈ (H i).edgeSet then 1 else 0

lemma averageSubgraphPacking_isCapacityDecomposition_in_set
    {I : Type*} [Fintype I] [Nonempty I]
    (G : SimpleGraph A) (H : I → SimpleGraph A)
    (hHG : ∀ i, H i ≤ G) (w : I → Finset A → ℝ)
    (hw : ∀ i, IsFractionalDecomposition (H i) (w i)) :
    IsCapacityDecomposition G (averageGraphCapacitySet H)
      (averageSubgraphPacking H w) := by
  constructor
  · constructor
    · apply averageTriangleWeight_nonneg
      intro i
      exact zeroExtendTriangleWeight_nonneg (hHG i) (hw i).isPacking
    · intro e he
      rw [averageSubgraphPacking, fractionalEdgeLoad_average]
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg _))
      gcongr with i
      rw [fractionalEdgeLoad_zeroExtend (hHG i)]
      by_cases hei : e ∈ (H i).edgeSet
      · have hei' : e ∈ (H i).edgeFinset := by
          rw [SimpleGraph.mem_edgeFinset]
          exact hei
        rw [(hw i).edgeLoad_eq_one hei', if_pos hei]
      · have hei' : e ∉ (H i).edgeFinset := fun h ↦
          hei (SimpleGraph.mem_edgeFinset.mp h)
        have heND : ¬ e.IsDiag := SimpleGraph.not_isDiag_of_mem_edgeFinset he
        rw [fractionalEdgeLoad_eq_zero_of_not_edge (H i) (w i) heND hei',
          if_neg hei]
  · intro e he
    rw [averageSubgraphPacking, fractionalEdgeLoad_average,
      averageGraphCapacitySet]
    congr 1
    apply sum_congr rfl
    intro i hi
    rw [fractionalEdgeLoad_zeroExtend (hHG i)]
    by_cases hei : e ∈ (H i).edgeSet
    · have hei' : e ∈ (H i).edgeFinset := by
        rw [SimpleGraph.mem_edgeFinset]
        exact hei
      rw [(hw i).edgeLoad_eq_one hei', if_pos hei]
    · have hei' : e ∉ (H i).edgeFinset := fun h ↦
        hei (SimpleGraph.mem_edgeFinset.mp h)
      have heND : ¬ e.IsDiag := SimpleGraph.not_isDiag_of_mem_edgeFinset he
      rw [fractionalEdgeLoad_eq_zero_of_not_edge (H i) (w i) heND hei',
        if_neg hei]

/-- The three non-diagonal pairs of an explicitly enumerated triangle. -/
def triangleEdges (x y z : A) : Finset (Sym2 A) :=
  {s(x, y), s(x, z), s(y, z)}

lemma mem_triangleEdges_iff_mem_sym2 {x y z : A}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {e : Sym2 A} (heND : ¬ e.IsDiag) :
    e ∈ triangleEdges x y z ↔ e ∈ ({x, y, z} : Finset A).sym2 := by
  induction e using Sym2.inductionOn with
  | hf a b =>
      simp only [triangleEdges, mem_insert, mem_singleton,
        Finset.mk_mem_sym2_iff, Sym2.mk_isDiag_iff] at heND ⊢
      constructor
      · rintro (h | h | h) <;> rcases Sym2.eq_iff.mp h with h | h <;>
          simp [h.1, h.2]
      · rintro ⟨(rfl | rfl | rfl), (rfl | rfl | rfl)⟩ <;>
          simp_all [Sym2.eq_iff]

/-- Delete, in turn, the three edges of an explicitly enumerated triangle. -/
def triangleDeletionFamily (G : SimpleGraph A) (x y z : A) :
    Fin 3 → SimpleGraph A
  | ⟨0, _⟩ => G.deleteEdges ({s(x, y)} : Finset (Sym2 A))
  | ⟨1, _⟩ => G.deleteEdges ({s(x, z)} : Finset (Sym2 A))
  | ⟨2, _⟩ => G.deleteEdges ({s(y, z)} : Finset (Sym2 A))

lemma triangleDeletionFamily_le (G : SimpleGraph A) (x y z : A) (i : Fin 3) :
    triangleDeletionFamily G x y z i ≤ G := by
  fin_cases i <;> exact SimpleGraph.deleteEdges_le _

lemma averageGraphCapacity_triangleDeletionFamily
    (G : SimpleGraph A) {x y z : A}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {e : Sym2 A} (he : e ∈ G.edgeFinset) :
    averageGraphCapacitySet (triangleDeletionFamily G x y z) e +
        (if e ∈ ({x, y, z} : Finset A).sym2 then (1 / 3 : ℝ) else 0) = 1 := by
  have heND : ¬ e.IsDiag := SimpleGraph.not_isDiag_of_mem_edgeFinset he
  have hmem := mem_triangleEdges_iff_mem_sym2 hxy hxz hyz heND
  have heSet : e ∈ G.edgeSet := SimpleGraph.mem_edgeFinset.mp he
  have hindicator (i : Fin 3) (d : Sym2 A)
      (hi : triangleDeletionFamily G x y z i =
        G.deleteEdges ({d} : Finset (Sym2 A))) :
      (if e ∈ (triangleDeletionFamily G x y z i).edgeSet
        then (1 : ℝ) else 0) = if e ≠ d then 1 else 0 := by
    have hiff : e ∈ (triangleDeletionFamily G x y z i).edgeSet ↔ e ≠ d := by
      rw [hi, SimpleGraph.edgeSet_deleteEdges]
      simp [heSet]
    by_cases hd : e ∈ (triangleDeletionFamily G x y z i).edgeSet
    · have hne := hiff.mp hd
      simp [hd, hne]
    · have heq : ¬ e ≠ d := mt hiff.mpr hd
      simp [hd, heq]
  simp only [← hmem]
  unfold averageGraphCapacitySet triangleEdges
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_one]
  simp only [Fintype.card_fin, Nat.cast_ofNat]
  rw [hindicator (0 : Fin 3) s(x, y) rfl,
    hindicator (Fin.succ (0 : Fin 2)) s(x, z) rfl,
    hindicator (Fin.succ (Fin.succ (0 : Fin 1))) s(y, z) rfl]
  by_cases h₁ : e = s(x, y) <;>
    by_cases h₂ : e = s(x, z) <;>
      by_cases h₃ : e = s(y, z) <;>
        simp [h₁, h₂, h₃, Sym2.eq_iff, hxy, hxz, hyz,
          hxy.symm, hxz.symm, hyz.symm] <;> norm_num

lemma triple_not_mem_triangleDeletionFamily
    (G : SimpleGraph A) {x y z : A}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) (i : Fin 3) :
    ({x, y, z} : Finset A) ∉
      (triangleDeletionFamily G x y z i).cliqueFinset 3 := by
  fin_cases i <;>
    simp [triangleDeletionFamily, SimpleGraph.mem_cliqueFinset_iff,
      SimpleGraph.is3Clique_triple_iff, hxy, hxz, hyz,
      hxy.symm, hxz.symm, hyz.symm]

lemma averageSubgraphPacking_add_triangle_halfBounded
    (G : SimpleGraph A) {x y z : A}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (w : Fin 3 → Finset A → ℝ)
    (hw : ∀ i, IsHalfBounded (triangleDeletionFamily G x y z i) (w i)) :
    IsHalfBounded G (fun u ↦
      averageSubgraphPacking (triangleDeletionFamily G x y z) w u +
        singleTriangleWeight {x, y, z} (1 / 3) u) := by
  intro t ht
  by_cases htriple : t = {x, y, z}
  · subst t
    have havg : averageSubgraphPacking
        (triangleDeletionFamily G x y z) w {x, y, z} = 0 := by
      unfold averageSubgraphPacking averageTriangleWeight
      rw [mul_eq_zero]
      right
      apply sum_eq_zero
      intro i hi
      exact zeroExtendTriangleWeight_of_not_mem
        (triple_not_mem_triangleDeletionFamily G hxy hxz hyz i)
    change averageSubgraphPacking (triangleDeletionFamily G x y z) w
        {x, y, z} + singleTriangleWeight {x, y, z} (1 / 3) {x, y, z} ≤ 1 / 2
    rw [havg]
    norm_num [singleTriangleWeight]
  · change averageSubgraphPacking (triangleDeletionFamily G x y z) w t +
        singleTriangleWeight {x, y, z} (1 / 3) t ≤ 1 / 2
    rw [singleTriangleWeight, if_neg htriple, add_zero]
    apply averageTriangleWeight_le_half
    · intro i
      exact zeroExtendTriangleWeight_le_half
        (triangleDeletionFamily_le G x y z i) (hw i)
    · exact ht

/-- One downward step in Gruslys--Letzter Lemma 2.3. -/
theorem fractionalDecomposition_of_next_missing
    (hcard : 7 ≤ Fintype.card A) {m k : ℕ}
    (hm : m ≤ Fintype.card A - 4) (hk : k < m)
    (hnext : ∀ H : SimpleGraph A, missingEdgeCount H = k + 1 →
      ∃ w : Finset A → ℝ, IsFractionalDecomposition H w)
    (G : SimpleGraph A) (hG : missingEdgeCount G = k) :
    ∃ w : Finset A → ℝ, IsFractionalDecomposition G w := by
  have hfour : 4 ≤ G.edgeFinset.card :=
    four_le_card_edges_of_missing_lt G hcard hm (hG.symm ▸ hk)
  obtain ⟨e, he⟩ := card_pos.mp (lt_of_lt_of_le (by omega) hfour)
  obtain ⟨f, hf, hfe⟩ := exists_mem_ne (lt_of_lt_of_le (by omega) hfour) e
  let H := G.deleteEdges ({e} : Finset (Sym2 A))
  have hmissH : missingEdgeCount H = k + 1 := by
    dsimp only [H]
    rw [missingEdgeCount_delete_singleton he, hG]
  obtain ⟨wH, hwH⟩ := hnext H hmissH
  have hfSet : f ∈ G.edgeSet := SimpleGraph.mem_edgeFinset.mp hf
  have hfH : f ∈ H.edgeSet := by
    dsimp only [H]
    rw [SimpleGraph.edgeSet_deleteEdges]
    simp [hfSet, hfe]
  obtain ⟨t, htData⟩ := exists_triangle_of_fractionalDecomposition hwH ⟨f, hfH⟩
  obtain ⟨x, y, z, hxyH, hxzH, hyzH, ht⟩ :=
    SimpleGraph.is3Clique_iff.mp htData
  have hHG : H ≤ G := by
    dsimp only [H]
    exact SimpleGraph.deleteEdges_le _
  have hxy : G.Adj x y := hHG hxyH
  have hxz : G.Adj x z := hHG hxzH
  have hyz : G.Adj y z := hHG hyzH
  have htG : ({x, y, z} : Finset A) ∈ G.cliqueFinset 3 := by
    rw [SimpleGraph.mem_cliqueFinset_iff, SimpleGraph.is3Clique_triple_iff]
    exact ⟨hxy, hxz, hyz⟩
  let D : Fin 3 → SimpleGraph A := triangleDeletionFamily G x y z
  have hmissD : ∀ i, missingEdgeCount (D i) = k + 1 := by
    intro i
    fin_cases i
    · dsimp only [D, triangleDeletionFamily]
      rw [missingEdgeCount_delete_singleton (by simpa using hxy), hG]
    · dsimp only [D, triangleDeletionFamily]
      rw [missingEdgeCount_delete_singleton (by simpa using hxz), hG]
    · dsimp only [D, triangleDeletionFamily]
      rw [missingEdgeCount_delete_singleton (by simpa using hyz), hG]
  have hex : ∀ i, ∃ w : Finset A → ℝ, IsFractionalDecomposition (D i) w := by
    intro i
    exact hnext (D i) (hmissD i)
  choose w hw using hex
  have hwAvg : IsCapacityDecomposition G (averageGraphCapacitySet D)
      (averageSubgraphPacking D w) :=
    averageSubgraphPacking_isCapacityDecomposition_in_set G D
      (fun i ↦ by simpa only [D] using triangleDeletionFamily_le G x y z i) w hw
  refine ⟨fun u ↦ averageSubgraphPacking D w u +
      singleTriangleWeight {x, y, z} (1 / 3) u, ?_⟩
  apply isFractionalDecomposition_add_singleTriangle htG (by norm_num) hwAvg
  intro edge hedge
  simpa only [D] using averageGraphCapacity_triangleDeletionFamily G
    hxy.ne hxz.ne hyz.ne hedge

/-- Gruslys--Letzter Lemma 2.3: an exact-missing-edge decomposition theorem
at level `m` implies the corresponding theorem for every lower level. -/
theorem fractionalDecomposition_of_exact_missing
    (hcard : 7 ≤ Fintype.card A) {m : ℕ}
    (hm : m ≤ Fintype.card A - 4)
    (hexact : ∀ G : SimpleGraph A, missingEdgeCount G = m →
      ∃ w : Finset A → ℝ, IsFractionalDecomposition G w) :
    ∀ G : SimpleGraph A, missingEdgeCount G ≤ m →
      ∃ w : Finset A → ℝ, IsFractionalDecomposition G w := by
  let P : ℕ → Prop := fun k ↦
    ∀ G : SimpleGraph A, missingEdgeCount G = k →
      ∃ w : Finset A → ℝ, IsFractionalDecomposition G w
  have hP : ∀ k (hk : k ≤ m), P k := by
    intro k hk
    exact Nat.decreasingInduction
      (motive := fun j _ ↦ P j)
      (fun j hj ih ↦ fractionalDecomposition_of_next_missing
        hcard hm hj ih)
      hexact hk
  intro G hG
  exact hP (missingEdgeCount G) hG G rfl

/-- The bounded-weight form of one downward step.  This is the precise form
of Gruslys--Letzter Lemma 2.3 used to promote the exact strong bases. -/
theorem halfBoundedDecomposition_of_next_missing
    (hcard : 7 ≤ Fintype.card A) {m k : ℕ}
    (hm : m ≤ Fintype.card A - 4) (hk : k < m)
    (hnext : ∀ H : SimpleGraph A, missingEdgeCount H = k + 1 →
      ∃ w : Finset A → ℝ,
        IsFractionalDecomposition H w ∧ IsHalfBounded H w)
    (G : SimpleGraph A) (hG : missingEdgeCount G = k) :
    ∃ w : Finset A → ℝ,
      IsFractionalDecomposition G w ∧ IsHalfBounded G w := by
  have hfour : 4 ≤ G.edgeFinset.card :=
    four_le_card_edges_of_missing_lt G hcard hm (hG.symm ▸ hk)
  obtain ⟨e, he⟩ := card_pos.mp (lt_of_lt_of_le (by omega) hfour)
  obtain ⟨f, hf, hfe⟩ := exists_mem_ne (lt_of_lt_of_le (by omega) hfour) e
  let H := G.deleteEdges ({e} : Finset (Sym2 A))
  have hmissH : missingEdgeCount H = k + 1 := by
    dsimp only [H]
    rw [missingEdgeCount_delete_singleton he, hG]
  obtain ⟨wH, hwH, _⟩ := hnext H hmissH
  have hfSet : f ∈ G.edgeSet := SimpleGraph.mem_edgeFinset.mp hf
  have hfH : f ∈ H.edgeSet := by
    dsimp only [H]
    rw [SimpleGraph.edgeSet_deleteEdges]
    simp [hfSet, hfe]
  obtain ⟨t, htData⟩ := exists_triangle_of_fractionalDecomposition hwH ⟨f, hfH⟩
  obtain ⟨x, y, z, hxyH, hxzH, hyzH, ht⟩ :=
    SimpleGraph.is3Clique_iff.mp htData
  have hHG : H ≤ G := by
    dsimp only [H]
    exact SimpleGraph.deleteEdges_le _
  have hxy : G.Adj x y := hHG hxyH
  have hxz : G.Adj x z := hHG hxzH
  have hyz : G.Adj y z := hHG hyzH
  have htG : ({x, y, z} : Finset A) ∈ G.cliqueFinset 3 := by
    rw [SimpleGraph.mem_cliqueFinset_iff, SimpleGraph.is3Clique_triple_iff]
    exact ⟨hxy, hxz, hyz⟩
  let D : Fin 3 → SimpleGraph A := triangleDeletionFamily G x y z
  have hmissD : ∀ i, missingEdgeCount (D i) = k + 1 := by
    intro i
    fin_cases i
    · dsimp only [D, triangleDeletionFamily]
      rw [missingEdgeCount_delete_singleton (by simpa using hxy), hG]
    · dsimp only [D, triangleDeletionFamily]
      rw [missingEdgeCount_delete_singleton (by simpa using hxz), hG]
    · dsimp only [D, triangleDeletionFamily]
      rw [missingEdgeCount_delete_singleton (by simpa using hyz), hG]
  have hex : ∀ i, ∃ w : Finset A → ℝ,
      IsFractionalDecomposition (D i) w ∧ IsHalfBounded (D i) w := by
    intro i
    exact hnext (D i) (hmissD i)
  choose w hw hhalf using hex
  have hwAvg : IsCapacityDecomposition G (averageGraphCapacitySet D)
      (averageSubgraphPacking D w) :=
    averageSubgraphPacking_isCapacityDecomposition_in_set G D
      (fun i ↦ by simpa only [D] using triangleDeletionFamily_le G x y z i) w hw
  let wFinal : Finset A → ℝ := fun u ↦ averageSubgraphPacking D w u +
    singleTriangleWeight {x, y, z} (1 / 3) u
  refine ⟨wFinal, ?_, ?_⟩
  · dsimp only [wFinal]
    apply isFractionalDecomposition_add_singleTriangle htG (by norm_num) hwAvg
    intro edge hedge
    simpa only [D] using averageGraphCapacity_triangleDeletionFamily G
      hxy.ne hxz.ne hyz.ne hedge
  · dsimp only [wFinal]
    simpa only [D] using averageSubgraphPacking_add_triangle_halfBounded G
      hxy.ne hxz.ne hyz.ne w hhalf

/-- Exact-to-at-most promotion preserving the `1/2` triangle bound. -/
theorem halfBoundedDecomposition_of_exact_missing
    (hcard : 7 ≤ Fintype.card A) {m : ℕ}
    (hm : m ≤ Fintype.card A - 4)
    (hexact : ∀ G : SimpleGraph A, missingEdgeCount G = m →
      ∃ w : Finset A → ℝ,
        IsFractionalDecomposition G w ∧ IsHalfBounded G w) :
    ∀ G : SimpleGraph A, missingEdgeCount G ≤ m →
      ∃ w : Finset A → ℝ,
        IsFractionalDecomposition G w ∧ IsHalfBounded G w := by
  let P : ℕ → Prop := fun k ↦
    ∀ G : SimpleGraph A, missingEdgeCount G = k →
      ∃ w : Finset A → ℝ,
        IsFractionalDecomposition G w ∧ IsHalfBounded G w
  have hP : ∀ k (hk : k ≤ m), P k := by
    intro k hk
    exact Nat.decreasingInduction
      (motive := fun j _ ↦ P j)
      (fun j hj ih ↦ halfBoundedDecomposition_of_next_missing
        hcard hm hj ih)
      hexact hk
  intro G hG
  exact hP (missingEdgeCount G) hG G rfl

end

end Erdos76
