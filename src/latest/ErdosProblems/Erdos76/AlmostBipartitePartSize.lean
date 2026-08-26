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
import ErdosProblems.Erdos76.FractionalTransport
import ErdosProblems.Erdos76.GruslysLetzter
import Mathlib.Tactic

/-!
# Part sizes in an almost-bipartite colouring

This file formalizes Proposition 4.1 of Gruslys--Letzter.  The main auxiliary
construction starts with the uniform fractional decomposition of a complete
graph and discards every triangle containing a missing edge.  If there are
`k` missing edges, at most `k` triangle-weight, hence at most `3k`
covered-edge weight, is discarded.
-/

open Finset
open scoped BigOperators

namespace Erdos76

noncomputable section

attribute [local instance] Classical.propDecidable

variable {α β : Type*} [Fintype α] [DecidableEq α]
  [Fintype β] [DecidableEq β]

private def completeTriangleWeight (α : Type*) [Fintype α] : Finset α → ℝ :=
  fun _ ↦ (((Fintype.card α - 2 : ℕ) : ℝ))⁻¹

private lemma card_complete_triangles_through_edge
    (e : Sym2 α) (hecard : e.toFinset.card = 2) :
    (((univ : Finset α).powersetCard 3).filter fun t ↦ e ∈ t.sym2).card =
      Fintype.card α - 2 := by
  have hfilter :
      ((univ : Finset α).powersetCard 3).filter (fun t ↦ e ∈ t.sym2) =
        ((univ : Finset α).powersetCard 3).filter (e.toFinset ⊆ ·) := by
    ext t
    simp only [mem_filter]
    rw [Finset.mem_sym2_iff]
    simp [subset_iff]
  rw [hfilter, card_filter_powersetCard_subset e.toFinset univ 3
    (subset_univ _) (by omega), hecard]
  simp

private lemma isFractionalPacking_restrict_complete
    (H : SimpleGraph α) (hcard : 3 ≤ Fintype.card α) :
    IsFractionalPacking H
      (zeroExtendTriangleWeight H (completeTriangleWeight α)) := by
  constructor
  · intro t ht
    rw [zeroExtendTriangleWeight_of_mem ht]
    simp [completeTriangleWeight]
  · intro e he
    rw [fractionalEdgeLoad_zeroExtend le_rfl]
    unfold fractionalEdgeLoad completeTriangleWeight
    rw [sum_const, nsmul_eq_mul]
    have hsub :
        (H.cliqueFinset 3).filter (fun t ↦ e ∈ t.sym2) ⊆
          ((univ : Finset α).powersetCard 3).filter (fun t ↦ e ∈ t.sym2) := by
      intro t ht
      have htdata := SimpleGraph.mem_cliqueFinset_iff.mp (mem_filter.mp ht).1
      exact mem_filter.mpr ⟨mem_powersetCard.mpr ⟨subset_univ _, htdata.card_eq⟩,
        (mem_filter.mp ht).2⟩
    have hecard : e.toFinset.card = 2 :=
      SimpleGraph.card_toFinset_mem_edgeFinset ⟨e, he⟩
    have htri := card_complete_triangles_through_edge e hecard
    have hcardLe := card_le_card hsub
    rw [htri] at hcardLe
    have hpos : 0 < Fintype.card α - 2 := by omega
    calc
      (((H.cliqueFinset 3).filter (fun t ↦ e ∈ t.sym2)).card : ℝ) *
          (((Fintype.card α - 2 : ℕ) : ℝ))⁻¹ ≤
          ((Fintype.card α - 2 : ℕ) : ℝ) *
            (((Fintype.card α - 2 : ℕ) : ℝ))⁻¹ := by
        apply mul_le_mul_of_nonneg_right
        · exact_mod_cast hcardLe
        · positivity
      _ = 1 := mul_inv_cancel₀ (by exact_mod_cast hpos.ne')

private def discardedCompleteTriangles (H : SimpleGraph α) : Finset (Finset α) :=
  (univ : Finset α).powersetCard 3 \ H.cliqueFinset 3

private def completeTrianglesThrough (e : Sym2 α) : Finset (Finset α) :=
  ((univ : Finset α).powersetCard 3).filter fun t ↦ e ∈ t.sym2

private lemma discardedCompleteTriangles_subset_missing_biUnion
    (H : SimpleGraph α) :
    discardedCompleteTriangles H ⊆
      Hᶜ.edgeFinset.biUnion completeTrianglesThrough := by
  intro t ht
  rcases mem_sdiff.mp ht with ⟨htTop, htH⟩
  have htTop' := mem_powersetCard.mp htTop
  have hnotClique : ¬ H.IsClique (t : Set α) := by
    intro hclique
    exact htH (SimpleGraph.mem_cliqueFinset_iff.mpr
      ⟨hclique, htTop'.2⟩)
  obtain ⟨u, v, huv, hnadj⟩ := (SimpleGraph.not_isClique_iff _).mp hnotClique
  let e : Sym2 α := s(u.1, v.1)
  have hec : e ∈ Hᶜ.edgeFinset := by
    apply SimpleGraph.mem_edgeFinset.mpr
    simpa [e, SimpleGraph.compl_adj] using ⟨huv, hnadj⟩
  apply mem_biUnion.mpr
  refine ⟨e, hec, mem_filter.mpr ⟨htTop, ?_⟩⟩
  apply Finset.mk_mem_sym2_iff.mpr
  exact ⟨u.2, v.2⟩

private lemma card_discardedCompleteTriangles_le
    (H : SimpleGraph α) :
    (discardedCompleteTriangles H).card ≤
      missingEdgeCount H * (Fintype.card α - 2) := by
  calc
    (discardedCompleteTriangles H).card ≤
        (Hᶜ.edgeFinset.biUnion completeTrianglesThrough).card :=
      card_le_card (discardedCompleteTriangles_subset_missing_biUnion H)
    _ ≤ ∑ e ∈ Hᶜ.edgeFinset, (completeTrianglesThrough e).card :=
      card_biUnion_le
    _ = missingEdgeCount H * (Fintype.card α - 2) := by
      have hcard : ∀ e ∈ Hᶜ.edgeFinset,
          (completeTrianglesThrough e).card = Fintype.card α - 2 := by
        intro e he
        apply card_complete_triangles_through_edge
        exact SimpleGraph.card_toFinset_mem_edgeFinset ⟨e, he⟩
      calc
        (∑ e ∈ Hᶜ.edgeFinset, (completeTrianglesThrough e).card) =
            ∑ _e ∈ Hᶜ.edgeFinset, (Fintype.card α - 2) := by
          apply sum_congr rfl
          intro e he
          exact hcard e he
        _ = missingEdgeCount H * (Fintype.card α - 2) := by
          simp [missingEdgeCount]

private lemma card_complete_cliques_eq_add_discarded (H : SimpleGraph α) :
    ((univ : Finset α).powersetCard 3).card =
      (H.cliqueFinset 3).card + (discardedCompleteTriangles H).card := by
  have hsub : H.cliqueFinset 3 ⊆ (univ : Finset α).powersetCard 3 := by
    intro t ht
    have htdata := SimpleGraph.mem_cliqueFinset_iff.mp ht
    exact mem_powersetCard.mpr ⟨subset_univ _, htdata.card_eq⟩
  have hcard := card_sdiff_add_card_eq_card hsub
  dsimp only [discardedCompleteTriangles]
  omega

private lemma cast_choose_three (n : ℕ) :
    ((n.choose 3 : ℕ) : ℝ) =
      (n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2) / 6 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [Nat.choose_succ_succ]
      push_cast
      rw [Nat.cast_choose_two, ih]
      push_cast
      ring

private lemma restrictedCompleteCoveredSize_lower
    (H : SimpleGraph α) (hcard : 3 ≤ Fintype.card α) :
    (((Fintype.card α).choose 2 : ℕ) : ℝ) - 3 * missingEdgeCount H ≤
      fractionalCoveredSize H
        (zeroExtendTriangleWeight H (completeTriangleWeight α)) := by
  let w := completeTriangleWeight α
  let b := (discardedCompleteTriangles H).card
  let d := Fintype.card α - 2
  have hd : 0 < d := by dsimp only [d]; omega
  have hbad : b ≤ missingEdgeCount H * d := by
    exact card_discardedCompleteTriangles_le H
  have hcardSplit := card_complete_cliques_eq_add_discarded H
  have hcardSplitR :
      (((Fintype.card α).choose 3 : ℕ) : ℝ) =
        (H.cliqueFinset 3).card + b := by
    have hcompleteCard :
        ((univ : Finset α).powersetCard 3).card =
          (Fintype.card α).choose 3 := by simp
    rw [hcompleteCard] at hcardSplit
    exact_mod_cast hcardSplit
  have hsize :
      fractionalCoveredSize H (zeroExtendTriangleWeight H w) =
        3 * ((H.cliqueFinset 3).card : ℝ) * (d : ℝ)⁻¹ := by
    unfold fractionalCoveredSize fractionalSize
    rw [show (∑ t ∈ H.cliqueFinset 3, zeroExtendTriangleWeight H w t) =
        ∑ t ∈ H.cliqueFinset 3, w t by
      apply sum_congr rfl
      intro t ht
      simp [zeroExtendTriangleWeight, ht]]
    simp only [w, completeTriangleWeight, sum_const, nsmul_eq_mul]
    ring
  have hratio : (b : ℝ) * (d : ℝ)⁻¹ ≤ missingEdgeCount H := by
    rw [← div_eq_mul_inv]
    rw [div_le_iff₀ (by exact_mod_cast hd)]
    exact_mod_cast hbad
  have hdcast : (d : ℝ) = (Fintype.card α : ℝ) - 2 := by
    dsimp only [d]
    rw [Nat.cast_sub (by omega : 2 ≤ Fintype.card α)]
    norm_num
  have hdne : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hcomplete :
      3 * (((Fintype.card α).choose 3 : ℕ) : ℝ) * (d : ℝ)⁻¹ =
        (((Fintype.card α).choose 2 : ℕ) : ℝ) := by
    rw [cast_choose_three, Nat.cast_choose_two, hdcast]
    calc
      3 * ((Fintype.card α : ℝ) * ((Fintype.card α : ℝ) - 1) *
          ((Fintype.card α : ℝ) - 2) / 6) *
          ((Fintype.card α : ℝ) - 2)⁻¹ =
          ((Fintype.card α : ℝ) * ((Fintype.card α : ℝ) - 1) / 2) *
            (((Fintype.card α : ℝ) - 2) *
              ((Fintype.card α : ℝ) - 2)⁻¹) := by ring
      _ = (Fintype.card α : ℝ) * ((Fintype.card α : ℝ) - 1) / 2 := by
        rw [mul_inv_cancel₀]
        · ring
        · simpa only [← hdcast] using hdne
  rw [hsize]
  rw [hcardSplitR] at hcomplete
  nlinarith [hratio]

private lemma IsFractionalDecomposition.relabel_complete
    {G : SimpleGraph α} {w : Finset α → ℝ}
    (hw : IsFractionalDecomposition G w) (e : α ≃ β) :
    IsFractionalDecomposition (G.map e.toEmbedding) (relabelWeight e w) := by
  classical
  letI : DecidableRel G.Adj := Classical.decRel _
  letI : DecidableRel (G.map e.toEmbedding).Adj := Classical.decRel _
  refine ⟨hw.isPacking.relabel e, ?_⟩
  intro p hp
  have hp' := SimpleGraph.mem_edgeFinset.mp hp
  rw [SimpleGraph.edgeSet_map e.toEmbedding G] at hp'
  obtain ⟨q, hq, rfl⟩ := hp'
  rw [fractionalEdgeLoad_relabel]
  exact hw.edgeLoad_eq_one (SimpleGraph.mem_edgeFinset.mpr hq)

private lemma almostCompleteFractionalDecomposition_of_card
    (hAC : AlmostCompleteFractionalDecomposition)
    (G : SimpleGraph α) (hcard : 7 ≤ Fintype.card α)
    (hmissing : missingEdgeCount G ≤ Fintype.card α - 4) :
    ∃ w : Finset α → ℝ, IsFractionalDecomposition G w := by
  let e : α ≃ Fin (Fintype.card α) := Fintype.equivFinOfCardEq rfl
  let H : SimpleGraph (Fin (Fintype.card α)) := G.map e.toEmbedding
  letI : DecidableRel H.Adj := Classical.decRel _
  have hmissH : missingEdgeCount H ≤ Fintype.card α - 4 := by
    have hc : Hᶜ = Gᶜ.map e.toEmbedding := compl_map_equiv G e
    have hedge : Hᶜ.edgeFinset = (Gᶜ.map e.toEmbedding).edgeFinset := by
      ext p
      simp only [SimpleGraph.mem_edgeFinset]
      rw [hc]
    unfold missingEdgeCount at hmissing ⊢
    calc
      Hᶜ.edgeFinset.card = (Gᶜ.map e.toEmbedding).edgeFinset.card :=
        congrArg Finset.card hedge
      _ = Gᶜ.edgeFinset.card :=
        SimpleGraph.card_edgeFinset_map e.toEmbedding Gᶜ
      _ ≤ Fintype.card α - 4 := hmissing
  obtain ⟨w, hw⟩ := hAC (Fintype.card α) hcard H hmissH
  let u : Finset α → ℝ := relabelWeight e.symm w
  have hmap : H.map e.symm.toEmbedding = G := by
    dsimp only [H]
    rw [SimpleGraph.map_map]
    simpa using G.map_id
  refine ⟨u, ?_⟩
  simpa only [u, hmap] using hw.relabel_complete e.symm

private lemma missingEdgeCount_compl_induce (G : SimpleGraph α) (S : Finset α) :
    missingEdgeCount (Gᶜ.induce (S : Set α)) =
      (G.induce (S : Set α)).edgeFinset.card := by
  have hgraph : (Gᶜ.induce (S : Set α))ᶜ =
      G.induce (S : Set α) := by
    rw [compl_induce, compl_compl]
  unfold missingEdgeCount
  congr 1
  ext e
  simp only [SimpleGraph.mem_edgeFinset]
  rw [hgraph]

private lemma card_edges_add_missing_finset (G : SimpleGraph α) :
    G.edgeFinset.card + missingEdgeCount G = (Fintype.card α).choose 2 := by
  have hdisj : Disjoint G.edgeFinset Gᶜ.edgeFinset := by
    rw [Finset.disjoint_left]
    intro e heG heGc
    induction e using Sym2.inductionOn with
    | hf a b =>
        have hab : G.Adj a b := by
          simpa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using heG
        have hnab : ¬ G.Adj a b := by
          have := (show Gᶜ.Adj a b by
            simpa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using heGc)
          exact this.2
        exact hnab hab
  have hunion : G.edgeFinset ∪ Gᶜ.edgeFinset =
      (⊤ : SimpleGraph α).edgeFinset := by
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
  rw [missingEdgeCount, ← card_union_of_disjoint hdisj, hunion]
  exact SimpleGraph.card_edgeFinset_top_eq_card_choose_two

private lemma card_edges_add_missing (G : SimpleGraph α) :
    Nat.card G.edgeSet + missingEdgeCount G = (Fintype.card α).choose 2 := by
  have h := card_edges_add_missing_finset G
  have hcard : G.edgeFinset.card = Nat.card G.edgeSet := by
    rw [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card]
  omega

private lemma internal_missing_sum (G : SimpleGraph α) (s : Set α) :
    missingEdgeCount (Gᶜ.induce (s.toFinset : Set α)) +
        missingEdgeCount (Gᶜ.induce (sᶜ.toFinset : Set α)) =
      (internalEdgeFinset G s).card := by
  rw [missingEdgeCount_compl_induce, missingEdgeCount_compl_induce]
  have hS : (G.induce (s.toFinset : Set α)).edgeFinset.card =
      Nat.card (G.induce (s.toFinset : Set α)).edgeSet := by
    rw [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card]
  have hT : (G.induce (sᶜ.toFinset : Set α)).edgeFinset.card =
      Nat.card (G.induce (sᶜ.toFinset : Set α)).edgeSet := by
    rw [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card]
  rw [hS, hT]
  exact (card_internalEdgeFinset_eq_card_induced_sides G s).symm

private theorem exists_internal_complement_packing
    (G : SimpleGraph α) (s : Set α)
    (hs : 3 ≤ s.ncard) (ht : 3 ≤ sᶜ.ncard) :
    ∃ w : Finset α → ℝ, IsFractionalPacking Gᶜ w ∧
      (((s.ncard.choose 2 + sᶜ.ncard.choose 2 : ℕ) : ℝ) -
          3 * (internalEdgeFinset G s).card ≤
        fractionalCoveredSize Gᶜ w) := by
  let S := s.toFinset
  let T := sᶜ.toFinset
  let HS := Gᶜ.induce (S : Set α)
  let HT := Gᶜ.induce (T : Set α)
  let wS : Finset S → ℝ :=
    zeroExtendTriangleWeight HS (completeTriangleWeight S)
  let wT : Finset T → ℝ :=
    zeroExtendTriangleWeight HT (completeTriangleWeight T)
  have hScardEq : Fintype.card S = s.ncard := by
    rw [Fintype.card_coe]
    exact (Set.ncard_eq_toFinset_card' s).symm
  have hTcardEq : Fintype.card T = sᶜ.ncard := by
    rw [Fintype.card_coe]
    exact (Set.ncard_eq_toFinset_card' sᶜ).symm
  have hScard : 3 ≤ Fintype.card S := by omega
  have hTcard : 3 ≤ Fintype.card T := by omega
  have hwS : IsFractionalPacking HS wS := by
    exact isFractionalPacking_restrict_complete HS hScard
  have hwT : IsFractionalPacking HT wT := by
    exact isFractionalPacking_restrict_complete HT hTcard
  let w := addTriangleWeight (extendInducedWeight S wS)
    (extendInducedWeight T wT)
  have hST : Disjoint S T := by
    rw [Finset.disjoint_left]
    intro x hxs hxt
    have hxs' : x ∈ s := by simpa [S] using hxs
    have hxt' : x ∉ s := by simpa [T] using hxt
    exact hxt' hxs'
  have hw : IsFractionalPacking Gᶜ w :=
    isFractionalPacking_add_extendInduced_of_disjoint
      Gᶜ S T hST wS wT hwS hwT
  refine ⟨w, hw, ?_⟩
  have hlowS :
      (((Fintype.card S).choose 2 : ℕ) : ℝ) - 3 * missingEdgeCount HS ≤
        fractionalCoveredSize HS wS := by
    exact restrictedCompleteCoveredSize_lower HS hScard
  have hlowT :
      (((Fintype.card T).choose 2 : ℕ) : ℝ) - 3 * missingEdgeCount HT ≤
        fractionalCoveredSize HT wT := by
    exact restrictedCompleteCoveredSize_lower HT hTcard
  have hsize : fractionalCoveredSize Gᶜ w =
      fractionalCoveredSize HS wS + fractionalCoveredSize HT wT := by
    simp only [w, fractionalCoveredSize, fractionalSize_addTriangleWeight,
      fractionalSize_extendInducedWeight, HS, HT]
    ring
  have hmissing := internal_missing_sum G s
  rw [hsize]
  rw [hScardEq] at hlowS
  rw [hTcardEq] at hlowT
  push_cast
  have hmissingR : (missingEdgeCount HS : ℝ) + missingEdgeCount HT =
      (internalEdgeFinset G s).card := by exact_mod_cast hmissing
  nlinarith

private lemma large_side_decomposition_contradiction
    (hAC : AlmostCompleteFractionalDecomposition)
    {n k : ℕ} (hn : 19 ≤ n) (G : SimpleGraph (Fin n))
    (s : Set (Fin n))
    (hkdef : k = (internalEdgeFinset G s).card)
    (hk : k ≤ n / 8)
    (hupper : FractionalCoveredSizeAtMost G
      ((n : ℝ) * ((n : ℝ) - 1) / 4))
    (hsmall : s.ncard < 3) : False := by
  let T := sᶜ.toFinset
  let H := Gᶜ.induce (T : Set (Fin n))
  letI : DecidableRel H.Adj := Classical.decRel _
  have hsum : s.ncard + sᶜ.ncard = n := by
    rw [Set.ncard_add_ncard_compl]
    simp
  have hTcard : Fintype.card T = sᶜ.ncard := by
    rw [Fintype.card_coe]
    exact (Set.ncard_eq_toFinset_card' sᶜ).symm
  have hk8 : 8 * k ≤ n := by omega
  have hseven : 7 ≤ Fintype.card T := by
    rw [hTcard]
    omega
  have hmissing : missingEdgeCount H ≤ k := by
    dsimp only [H]
    rw [missingEdgeCount_compl_induce]
    have hle : (G.induce (T : Set (Fin n))).edgeFinset.card ≤
        (internalEdgeFinset G s).card := by
      rw [card_internalEdgeFinset_eq_card_induced_sides]
      rw [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card]
      dsimp only [T]
      omega
    simpa only [hkdef] using hle
  have hmissBound : missingEdgeCount H ≤ Fintype.card T - 4 := by
    rw [hTcard]
    omega
  obtain ⟨u, hu⟩ := almostCompleteFractionalDecomposition_of_card
    hAC H hseven hmissBound
  let wB : Finset (Fin n) → ℝ := extendInducedWeight T u
  have hwB : IsFractionalPacking Gᶜ wB := by
    exact hu.isPacking.extendInduced
  have hwR : IsFractionalPacking G (fun _ ↦ 0) := isFractionalPacking_zero G
  have hpack := hupper (fun _ ↦ 0) wB hwR hwB
  have hcovered :
      fractionalCoveredSize Gᶜ wB = (Nat.card H.edgeSet : ℝ) := by
    dsimp only [wB]
    rw [fractionalCoveredSize_extendInducedWeight]
    rw [fractionalCoveredSize_eq_card_of_decomposition hu]
    norm_cast
    rw [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card]
  have hcardH := card_edges_add_missing H
  rw [twoColorCoveredSize, fractionalCoveredSize, fractionalSize_zero,
    mul_zero, zero_add, hcovered] at hpack
  have hchoose :
      (n : ℝ) * ((n : ℝ) - 1) / 4 + (k : ℝ) <
        ((sᶜ.ncard.choose 2 : ℕ) : ℝ) := by
    rw [Nat.cast_choose_two]
    have hnR : (19 : ℝ) ≤ n := by exact_mod_cast hn
    have hkR : (8 : ℝ) * k ≤ n := by exact_mod_cast hk8
    have hn2nat : 2 ≤ n := by omega
    have hsideNat : n - 2 ≤ sᶜ.ncard := by omega
    have hsideR0 : ((n - 2 : ℕ) : ℝ) ≤ (sᶜ.ncard : ℝ) := by
      exact_mod_cast hsideNat
    have hsideR : (n : ℝ) - 2 ≤ sᶜ.ncard := by
      calc
        (n : ℝ) - 2 = ((n - 2 : ℕ) : ℝ) := by
          rw [Nat.cast_sub hn2nat]
          norm_num
        _ ≤ (sᶜ.ncard : ℝ) := hsideR0
    have hn2 : (0 : ℝ) ≤ (n : ℝ) - 2 := by linarith
    have hmono :
        ((n : ℝ) - 2) * ((n : ℝ) - 3) ≤
          (sᶜ.ncard : ℝ) * ((sᶜ.ncard : ℝ) - 1) := by
      have hfirst : 0 ≤ (sᶜ.ncard : ℝ) - ((n : ℝ) - 2) := by linarith
      have hsecond : 0 ≤ (sᶜ.ncard : ℝ) + ((n : ℝ) - 2) - 1 := by
        linarith
      nlinarith [mul_nonneg hfirst hsecond]
    have hquad : 0 ≤ (n : ℝ) * ((n : ℝ) - 19) :=
      mul_nonneg (by positivity) (by linarith)
    nlinarith
  have hmissingR : (missingEdgeCount H : ℝ) ≤ k := by exact_mod_cast hmissing
  have hcardHR :
      (Nat.card H.edgeSet : ℝ) + missingEdgeCount H =
        (sᶜ.ncard.choose 2 : ℕ) := by
    exact_mod_cast (by simpa [hTcard] using hcardH)
  nlinarith

/-- Proposition 4.1 of Gruslys--Letzter: under the sharp upper bound, both
parts of an almost-bipartite witness are large enough for the subsequent
almost-complete decompositions. -/
theorem almostBipartitePartSizeBound
    (hAC : AlmostCompleteFractionalDecomposition) :
    ∀ n, 19 ≤ n → ∀ (G : SimpleGraph (Fin n)) (s : Set (Fin n)),
      let k := (internalEdgeFinset G s).card
      k ≤ n / 8 →
      FractionalCoveredSizeAtMost G ((n : ℝ) * ((n : ℝ) - 1) / 4) →
      k + 4 ≤ s.ncard ∧ k + 4 ≤ sᶜ.ncard ∧
        7 ≤ s.ncard ∧ 7 ≤ sᶜ.ncard := by
  intro n hn G s k hk hupper
  have hsum : s.ncard + sᶜ.ncard = n := by
    rw [Set.ncard_add_ncard_compl]
    simp
  have hk8 : 8 * k ≤ n := by omega
  have hs3 : 3 ≤ s.ncard := by
    by_contra h
    exact large_side_decomposition_contradiction hAC hn G s rfl hk hupper (by omega)
  have ht3 : 3 ≤ sᶜ.ncard := by
    let t : Set (Fin n) := sᶜ
    have hkt : (internalEdgeFinset G t).card = k := by
      rw [show t = sᶜ by rfl, internalEdgeFinset_set_compl]
    by_contra h
    have htupper : FractionalCoveredSizeAtMost G
        ((n : ℝ) * ((n : ℝ) - 1) / 4) := hupper
    exact large_side_decomposition_contradiction hAC hn G t hkt.symm hk htupper (by
      simpa [t] using (show sᶜ.ncard < 3 by omega))
  obtain ⟨w, hw, hlower⟩ := exists_internal_complement_packing G s hs3 ht3
  have hzero := isFractionalPacking_zero G
  have hpack := hupper (fun _ ↦ 0) w hzero hw
  rw [twoColorCoveredSize, fractionalCoveredSize, fractionalSize_zero,
    mul_zero, zero_add] at hpack
  have hchooseR :
      ((s.ncard.choose 2 + sᶜ.ncard.choose 2 : ℕ) : ℝ) =
        (s.ncard : ℝ) * ((s.ncard : ℝ) - 1) / 2 +
          (sᶜ.ncard : ℝ) * ((sᶜ.ncard : ℝ) - 1) / 2 := by
    push_cast
    rw [Nat.cast_choose_two, Nat.cast_choose_two]
  have hbalance :
      ((s.ncard : ℝ) - (sᶜ.ncard : ℝ)) ^ 2 ≤
        (n : ℝ) + 12 * (k : ℝ) := by
    rw [hchooseR] at hlower
    have hsumR : (s.ncard : ℝ) + (sᶜ.ncard : ℝ) = n := by
      exact_mod_cast hsum
    nlinarith
  have hpart (r t : ℕ) (hrt : r + t = n)
      (hbal : ((r : ℝ) - (t : ℝ)) ^ 2 ≤ (n : ℝ) + 12 * (k : ℝ)) :
      k + 4 ≤ r := by
    by_contra hkr
    have hr : r ≤ k + 3 := by omega
    have hnR : (19 : ℝ) ≤ n := by exact_mod_cast hn
    have hkR : (8 : ℝ) * k ≤ n := by exact_mod_cast hk8
    have hrtR : (r : ℝ) + (t : ℝ) = n := by exact_mod_cast hrt
    have hrR : (r : ℝ) ≤ (k : ℝ) + 3 := by exact_mod_cast hr
    have hdiff : (0 : ℝ) ≤ (t : ℝ) - (r : ℝ) := by
      nlinarith
    have hlowerDiff : (3 * (n : ℝ)) / 4 - 6 ≤ (t : ℝ) - (r : ℝ) := by
      nlinarith
    have hfactor :
        0 ≤ ((t : ℝ) - (r : ℝ) - (3 * (n : ℝ) / 4 - 6)) *
          ((t : ℝ) - (r : ℝ) + (3 * (n : ℝ) / 4 - 6)) := by
      apply mul_nonneg
      · linarith
      · nlinarith
    have hquad : 0 ≤ (n : ℝ) * ((n : ℝ) - 19) :=
      mul_nonneg (by positivity) (by linarith)
    nlinarith
  have hsK : k + 4 ≤ s.ncard :=
    hpart s.ncard sᶜ.ncard hsum hbalance
  have htK : k + 4 ≤ sᶜ.ncard := by
    exact hpart sᶜ.ncard s.ncard (by omega) (by
      convert hbalance using 1 <;> ring)
  have hseven (r t : ℕ) (hrt : r + t = n) (hkr : k + 4 ≤ r)
      (hbal : ((r : ℝ) - (t : ℝ)) ^ 2 ≤ (n : ℝ) + 12 * (k : ℝ)) :
      7 ≤ r := by
    by_contra hr7
    have hk2 : k ≤ 2 := by omega
    have hnR : (19 : ℝ) ≤ n := by exact_mod_cast hn
    have hrtR : (r : ℝ) + (t : ℝ) = n := by exact_mod_cast hrt
    have hkR : (k : ℝ) ≤ 2 := by exact_mod_cast hk2
    have hrR : (r : ℝ) ≤ 6 := by exact_mod_cast (by omega : r ≤ 6)
    have hdiff : (0 : ℝ) ≤ (t : ℝ) - (r : ℝ) := by nlinarith
    have hlowerDiff : (n : ℝ) - 12 ≤ (t : ℝ) - (r : ℝ) := by
      nlinarith
    have hfactor :
        0 ≤ ((t : ℝ) - (r : ℝ) - ((n : ℝ) - 12)) *
          ((t : ℝ) - (r : ℝ) + ((n : ℝ) - 12)) := by
      apply mul_nonneg
      · linarith
      · nlinarith
    have hquad : 0 ≤ (n : ℝ) * ((n : ℝ) - 19) :=
      mul_nonneg (by positivity) (by linarith)
    nlinarith
  exact ⟨hsK, htK,
    hseven s.ncard sᶜ.ncard hsum hsK hbalance,
    hseven sᶜ.ncard s.ncard (by omega) htK (by
      convert hbalance using 1 <;> ring)⟩

end

end Erdos76
