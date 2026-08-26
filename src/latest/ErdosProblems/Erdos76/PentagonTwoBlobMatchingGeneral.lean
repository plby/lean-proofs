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
import ErdosProblems.Erdos76.PentagonMatchingCompletion
import ErdosProblems.Erdos76.PentagonTwoBlobMatching

/-!
# Proposition 7.2(b) for an arbitrary deleted cross matching

The explicit Appendix A construction is stated most naturally when the
deleted matching saturates the smaller blob.  We complete an arbitrary
deleted matching to such a saturated matching, restrict to the resulting
subgraph, and finally extend the packing by zero to the original graph.
-/

open Finset

namespace Erdos76

noncomputable section

attribute [local instance] Classical.propDecidable

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A supported matching between disjoint finite sides can be viewed with
the two sides interchanged. -/
lemma IsABCrossMatching.symm
    {A B : Finset α} {M : Finset (Sym2 α)}
    (hM : IsABCrossMatching A B M) (hAB : Disjoint A B) :
    IsABCrossMatching B A M := by
  classical
  refine ⟨⟨?_, hM.1.2⟩, ?_⟩
  · intro e he hsame
    obtain ⟨p, rfl⟩ := hM.exists_orientation he
    have hleftNot : p.1.1 ∉ B := fun hleftB ↦
      Finset.disjoint_left.mp hAB p.1.2 hleftB
    have hright : p.2.1 ∈ B := p.2.2
    exact (by simpa [sameSide_mk, hleftNot, hright] using hsame)
  · intro e he
    simpa [union_comm] using hM.2 e he

/-- Zero extension preserves feasibility when a packing is moved to a
supergraph. -/
lemma IsFractionalPacking.zeroExtend_to_supergraph
    {H G : SimpleGraph α} (hHG : H ≤ G) {w : Finset α → ℝ}
    (hw : IsFractionalPacking H w) :
    IsFractionalPacking G (zeroExtendTriangleWeight H w) := by
  constructor
  · exact zeroExtendTriangleWeight_nonneg hHG hw
  · intro e heG
    rw [fractionalEdgeLoad_zeroExtend hHG]
    by_cases heH : e ∈ H.edgeFinset
    · exact hw.edgeLoad_le_one heH
    · have heND : ¬e.IsDiag := G.not_isDiag_of_mem_edgeFinset heG
      rw [fractionalEdgeLoad_eq_zero_of_not_edge H w heND heH]
      norm_num

/-- Zero extension to a supergraph does not change total triangle weight. -/
lemma fractionalSize_zeroExtend_to_supergraph
    {H G : SimpleGraph α} (hHG : H ≤ G) (w : Finset α → ℝ) :
    fractionalSize G (zeroExtendTriangleWeight H w) = fractionalSize H w := by
  let sH := H.cliqueFinset 3
  let sG := G.cliqueFinset 3
  have hsub : sH ⊆ sG := by
    intro t ht
    exact SimpleGraph.cliqueFinset_mono G hHG ht
  unfold fractionalSize
  change (∑ t ∈ sG, zeroExtendTriangleWeight H w t) = ∑ t ∈ sH, w t
  calc
    (∑ t ∈ sG, zeroExtendTriangleWeight H w t) =
        ∑ t ∈ sH, zeroExtendTriangleWeight H w t := by
      symm
      apply sum_subset hsub
      intro t _htG htH
      exact zeroExtendTriangleWeight_of_not_mem htH
    _ = ∑ t ∈ sH, w t := by
      apply sum_congr rfl
      intro t ht
      exact zeroExtendTriangleWeight_of_mem ht

/-- Cross-triangle support is monotone along a graph inclusion that does not
change the internal edge set. -/
lemma internalCrossTriangles_mono_of_internalEdgeFinset_eq
    {H G : SimpleGraph α} {s : Set α} (hHG : H ≤ G)
    (hInternal : internalEdgeFinset H s = internalEdgeFinset G s) :
    internalCrossTriangles H s ⊆ internalCrossTriangles G s := by
  intro t ht
  rcases mem_internalCrossTriangles.mp ht with ⟨htClique, htOne⟩
  apply mem_internalCrossTriangles.mpr
  refine ⟨?_, ?_⟩
  · exact SimpleGraph.mem_cliqueFinset_iff.mp
      (SimpleGraph.cliqueFinset_mono G hHG
        (SimpleGraph.mem_cliqueFinset_iff.mpr htClique))
  · rw [← hInternal]
    exact htOne

/-- A supported cross packing remains supported after zero extension along
a graph inclusion, provided every old cross triangle is still a cross
triangle. -/
lemma IsFractionalInternalCrossPacking.zeroExtend_to_supergraph
    {H G : SimpleGraph α} {s : Set α} (hHG : H ≤ G)
    (hCross : internalCrossTriangles H s ⊆ internalCrossTriangles G s)
    {w : Finset α → ℝ} (hw : IsFractionalInternalCrossPacking H s w) :
    IsFractionalInternalCrossPacking G s (zeroExtendTriangleWeight H w) := by
  refine ⟨hw.1.zeroExtend_to_supergraph hHG, ?_⟩
  intro t htNot
  by_cases htH : t ∈ H.cliqueFinset 3
  · rw [zeroExtendTriangleWeight_of_mem htH]
    exact hw.2 t (fun ht ↦ htNot (hCross ht))
  · exact zeroExtendTriangleWeight_of_not_mem htH

/-- Deleting an embedding matching removes no edge internal to either side
of the bipartition. -/
lemma internalEdgeFinset_delete_embeddingCrossMatching
    {G : SimpleGraph α} {A B : Finset α} (hAB : Disjoint A B)
    (f : A ↪ B) :
    internalEdgeFinset
        (G.deleteEdges (embeddingCrossMatching A B f : Set (Sym2 α)))
        (A : Set α) =
      internalEdgeFinset G (A : Set α) := by
  have hmatching := isCrossMatching_embeddingCrossMatching hAB f
  ext e
  simp only [internalEdgeFinset, mem_filter]
  constructor
  · rintro ⟨heK, heSame⟩
    refine ⟨?_, heSame⟩
    induction e using Sym2.inductionOn with
    | hf x y =>
        have hxyK :
            (G.deleteEdges
              (embeddingCrossMatching A B f : Set (Sym2 α))).Adj x y := by
          simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using heK
        simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using hxyK.1
  · rintro ⟨heG, heSame⟩
    refine ⟨?_, heSame⟩
    induction e using Sym2.inductionOn with
    | hf x y =>
        have hxyG : G.Adj x y := by
          simpa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using heG
        have hnot : s(x, y) ∉
            (embeddingCrossMatching A B f : Set (Sym2 α)) := by
          intro hmem
          exact hmatching.1 _ hmem heSame
        have hxyK :
            (G.deleteEdges
              (embeddingCrossMatching A B f : Set (Sym2 α))).Adj x y :=
          SimpleGraph.deleteEdges_adj.mpr ⟨hxyG, hnot⟩
        simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using hxyK

/-- The cross graph obtained by completing the deleted matching has exactly
the saturated forbidden pairs. -/
lemma delete_embeddingCrossMatching_cross_adj
    {G : SimpleGraph α} {A B : Finset α} {M : Finset (Sym2 α)}
    (hAB : Disjoint A B) (f : A ↪ B)
    (hMsub : M ⊆ embeddingCrossMatching A B f)
    (hcross : ∀ a : A, ∀ b : B,
      G.Adj a.1 b.1 ↔ s(a.1, b.1) ∉ M)
    (a : A) (b : B) :
    (G.deleteEdges (embeddingCrossMatching A B f : Set (Sym2 α))).Adj
        a.1 b.1 ↔ b ≠ f a := by
  rw [SimpleGraph.deleteEdges_adj]
  constructor
  · intro h
    intro heq
    subst b
    exact h.2 (matching_pair_mem A B f a)
  · intro hne
    have hCE := (completeExceptEmbeddingMatching_cross_adj hAB f a b).2 hne
    rw [completeExceptEmbeddingMatching, SimpleGraph.deleteEdges_adj] at hCE
    refine ⟨(hcross a b).2 ?_, hCE.2⟩
    intro hmem
    exact hCE.2 (hMsub hmem)

/-- Internal cross-triangle support is preserved when a packing is extended
by zero from the graph with the completed matching deleted. -/
lemma IsFractionalInternalCrossPacking.zeroExtend_deleteEmbedding
    {G : SimpleGraph α} {A B : Finset α} (hAB : Disjoint A B)
    (f : A ↪ B)
    {w : Finset α → ℝ}
    (hw : IsFractionalInternalCrossPacking
      (G.deleteEdges (embeddingCrossMatching A B f : Set (Sym2 α)))
      (A : Set α) w) :
    IsFractionalInternalCrossPacking G (A : Set α)
      (zeroExtendTriangleWeight
        (G.deleteEdges (embeddingCrossMatching A B f : Set (Sym2 α))) w) := by
  have hKG :
      G.deleteEdges (embeddingCrossMatching A B f : Set (Sym2 α)) ≤ G :=
    SimpleGraph.deleteEdges_le _
  have hInternal := internalEdgeFinset_delete_embeddingCrossMatching
    (G := G) hAB f
  exact hw.zeroExtend_to_supergraph hKG
    (internalCrossTriangles_mono_of_internalEdgeFinset_eq hKG hInternal)

/-- Deleting any supported cross matching leaves all edges internal to the
displayed bipartition unchanged. -/
lemma internalEdgeFinset_delete_ABCrossMatching
    {G : SimpleGraph α} {A B : Finset α} {M : Finset (Sym2 α)}
    (hM : IsABCrossMatching A B M) :
    internalEdgeFinset (G.deleteEdges (M : Set (Sym2 α))) (A : Set α) =
      internalEdgeFinset G (A : Set α) := by
  ext e
  simp only [internalEdgeFinset, mem_filter]
  constructor
  · rintro ⟨heK, heSame⟩
    refine ⟨?_, heSame⟩
    induction e using Sym2.inductionOn with
    | hf x y =>
        have hxyK : (G.deleteEdges (M : Set (Sym2 α))).Adj x y := by
          simpa only [SimpleGraph.mem_edgeFinset,
            SimpleGraph.mem_edgeSet] using heK
        simpa only [SimpleGraph.mem_edgeFinset,
          SimpleGraph.mem_edgeSet] using hxyK.1
  · rintro ⟨heG, heSame⟩
    refine ⟨?_, heSame⟩
    induction e using Sym2.inductionOn with
    | hf x y =>
        have hxyG : G.Adj x y := by
          simpa only [SimpleGraph.mem_edgeFinset,
            SimpleGraph.mem_edgeSet] using heG
        have hnot : s(x, y) ∉ (M : Set (Sym2 α)) := by
          intro hmem
          exact hM.1.1 _ hmem heSame
        have hxyK : (G.deleteEdges (M : Set (Sym2 α))).Adj x y :=
          SimpleGraph.deleteEdges_adj.mpr ⟨hxyG, hnot⟩
        simpa only [SimpleGraph.mem_edgeFinset,
          SimpleGraph.mem_edgeSet] using hxyK

/-- A cross packing remains a cross packing after it is extended by zero
from the graph obtained by deleting a supported cross matching. -/
lemma IsFractionalInternalCrossPacking.zeroExtend_deleteABCrossMatching
    {G : SimpleGraph α} {A B : Finset α} {M : Finset (Sym2 α)}
    (hM : IsABCrossMatching A B M) {w : Finset α → ℝ}
    (hw : IsFractionalInternalCrossPacking
      (G.deleteEdges (M : Set (Sym2 α))) (A : Set α) w) :
    IsFractionalInternalCrossPacking G (A : Set α)
      (zeroExtendTriangleWeight (G.deleteEdges (M : Set (Sym2 α))) w) := by
  have hKG : G.deleteEdges (M : Set (Sym2 α)) ≤ G :=
    SimpleGraph.deleteEdges_le _
  exact hw.zeroExtend_to_supergraph hKG
    (internalCrossTriangles_mono_of_internalEdgeFinset_eq hKG
      (internalEdgeFinset_delete_ABCrossMatching hM))

private lemma sideEdgeFinset_delete_ABCrossMatching_left
    {G : SimpleGraph α} {A B : Finset α} {M : Finset (Sym2 α)}
    (hM : IsABCrossMatching A B M) :
    sideEdgeFinset (G.deleteEdges (M : Set (Sym2 α))) A =
      sideEdgeFinset G A := by
  have hInternal := internalEdgeFinset_delete_ABCrossMatching
    (G := G) hM
  ext e
  simp only [sideEdgeFinset, mem_filter]
  constructor
  · rintro ⟨heK, heA⟩
    have heSame : SameSide (A : Set α) e :=
      (sameSide_iff_subset_side_or_compl (A : Set α) e).mpr
        (Or.inl (by simpa using heA))
    have heI : e ∈ internalEdgeFinset
        (G.deleteEdges (M : Set (Sym2 α))) (A : Set α) :=
      mem_filter.mpr ⟨heK, heSame⟩
    rw [hInternal] at heI
    exact ⟨(mem_filter.mp heI).1, heA⟩
  · rintro ⟨heG, heA⟩
    have heSame : SameSide (A : Set α) e :=
      (sameSide_iff_subset_side_or_compl (A : Set α) e).mpr
        (Or.inl (by simpa using heA))
    have heI : e ∈ internalEdgeFinset G (A : Set α) :=
      mem_filter.mpr ⟨heG, heSame⟩
    rw [← hInternal] at heI
    exact ⟨(mem_filter.mp heI).1, heA⟩

private lemma sideEdgeFinset_delete_ABCrossMatching_right
    {G : SimpleGraph α} {A B : Finset α} {M : Finset (Sym2 α)}
    (hAB : Disjoint A B) (hM : IsABCrossMatching A B M) :
    sideEdgeFinset (G.deleteEdges (M : Set (Sym2 α))) B =
      sideEdgeFinset G B := by
  have hInternal := internalEdgeFinset_delete_ABCrossMatching
    (G := G) hM
  ext e
  simp only [sideEdgeFinset, mem_filter]
  have same_of_subset_B (heB : e.toFinset ⊆ B) :
      SameSide (A : Set α) e :=
    (sameSide_iff_subset_side_or_compl (A : Set α) e).mpr
      (Or.inr (by
        intro x hx
        simp only [Set.mem_toFinset, Set.mem_compl_iff]
        intro hxA
        exact Finset.disjoint_left.mp hAB hxA (heB hx)))
  constructor
  · rintro ⟨heK, heB⟩
    have heI : e ∈ internalEdgeFinset
        (G.deleteEdges (M : Set (Sym2 α))) (A : Set α) :=
      mem_filter.mpr ⟨heK, same_of_subset_B heB⟩
    rw [hInternal] at heI
    exact ⟨(mem_filter.mp heI).1, heB⟩
  · rintro ⟨heG, heB⟩
    have heI : e ∈ internalEdgeFinset G (A : Set α) :=
      mem_filter.mpr ⟨heG, same_of_subset_B heB⟩
    rw [← hInternal] at heI
    exact ⟨(mem_filter.mp heI).1, heB⟩

private lemma sideEdgeFinset_delete_embeddingCrossMatching_left
    {G : SimpleGraph α} {A B : Finset α} (hAB : Disjoint A B)
    (f : A ↪ B) :
    sideEdgeFinset
        (G.deleteEdges (embeddingCrossMatching A B f : Set (Sym2 α))) A =
      sideEdgeFinset G A := by
  have hInternal := internalEdgeFinset_delete_embeddingCrossMatching
    (G := G) hAB f
  ext e
  simp only [sideEdgeFinset, mem_filter]
  constructor
  · rintro ⟨heK, heA⟩
    have heSame : SameSide (A : Set α) e := by
      induction e using Sym2.inductionOn with
      | hf x y =>
          have hxA : x ∈ A := heA (by simp)
          have hyA : y ∈ A := heA (by simp)
          simp [sameSide_mk, hxA, hyA]
    have heInternalK : e ∈ internalEdgeFinset
        (G.deleteEdges (embeddingCrossMatching A B f : Set (Sym2 α)))
        (A : Set α) := mem_filter.mpr ⟨heK, heSame⟩
    have heInternalG : e ∈ internalEdgeFinset G (A : Set α) := by
      rw [← hInternal]
      exact heInternalK
    exact ⟨(mem_filter.mp heInternalG).1, heA⟩
  · rintro ⟨heG, heA⟩
    have heSame : SameSide (A : Set α) e := by
      induction e using Sym2.inductionOn with
      | hf x y =>
          have hxA : x ∈ A := heA (by simp)
          have hyA : y ∈ A := heA (by simp)
          simp [sameSide_mk, hxA, hyA]
    have heInternal : e ∈ internalEdgeFinset G (A : Set α) :=
      mem_filter.mpr ⟨heG, heSame⟩
    have heInternalK : e ∈ internalEdgeFinset
        (G.deleteEdges (embeddingCrossMatching A B f : Set (Sym2 α)))
        (A : Set α) := by
      rw [hInternal]
      exact heInternal
    exact ⟨(mem_filter.mp heInternalK).1, heA⟩

private lemma sideEdgeFinset_delete_embeddingCrossMatching_right
    {G : SimpleGraph α} {A B : Finset α} (hAB : Disjoint A B)
    (f : A ↪ B) :
    sideEdgeFinset
        (G.deleteEdges (embeddingCrossMatching A B f : Set (Sym2 α))) B =
      sideEdgeFinset G B := by
  have hInternal := internalEdgeFinset_delete_embeddingCrossMatching
    (G := G) hAB f
  ext e
  simp only [sideEdgeFinset, mem_filter]
  constructor
  · rintro ⟨heK, heB⟩
    have heSame : SameSide (A : Set α) e := by
      induction e using Sym2.inductionOn with
      | hf x y =>
          have hxB : x ∈ B := heB (by simp)
          have hyB : y ∈ B := heB (by simp)
          have hxA : x ∉ A := fun hxA ↦ Finset.disjoint_left.mp hAB hxA hxB
          have hyA : y ∉ A := fun hyA ↦ Finset.disjoint_left.mp hAB hyA hyB
          simp [sameSide_mk, hxA, hyA]
    have heInternalK : e ∈ internalEdgeFinset
        (G.deleteEdges (embeddingCrossMatching A B f : Set (Sym2 α)))
        (A : Set α) := mem_filter.mpr ⟨heK, heSame⟩
    have heInternalG : e ∈ internalEdgeFinset G (A : Set α) := by
      rw [← hInternal]
      exact heInternalK
    exact ⟨(mem_filter.mp heInternalG).1, heB⟩
  · rintro ⟨heG, heB⟩
    have heSame : SameSide (A : Set α) e := by
      induction e using Sym2.inductionOn with
      | hf x y =>
          have hxB : x ∈ B := heB (by simp)
          have hyB : y ∈ B := heB (by simp)
          have hxA : x ∉ A := fun hxA ↦ Finset.disjoint_left.mp hAB hxA hxB
          have hyA : y ∉ A := fun hyA ↦ Finset.disjoint_left.mp hAB hyA hyB
          simp [sameSide_mk, hxA, hyA]
    have heInternal : e ∈ internalEdgeFinset G (A : Set α) :=
      mem_filter.mpr ⟨heG, heSame⟩
    have heInternalK : e ∈ internalEdgeFinset
        (G.deleteEdges (embeddingCrossMatching A B f : Set (Sym2 α)))
        (A : Set α) := by
      rw [hInternal]
      exact heInternal
    exact ⟨(mem_filter.mp heInternalK).1, heB⟩

/-- Proposition 7.2(b), exactly in the paper's arbitrary deleted-matching
form and with arbitrary colours inside the blobs. -/
theorem proposition72b_arbitraryMatching
    {G : SimpleGraph α} {A B : Finset α} {M : Finset (Sym2 α)}
    (hAB : Disjoint A B) (hM : IsABCrossMatching A B M)
    (hcross : ∀ a : A, ∀ b : B,
      G.Adj a.1 b.1 ↔ s(a.1, b.1) ∉ M)
    (hAcard : 3 ≤ A.card) (hAleB : A.card ≤ B.card)
    (hBle : B.card ≤ A.card + 1) :
    ∃ w : Finset α → ℝ,
      IsFractionalInternalCrossPacking G (A : Set α) w ∧
      fractionalSize G w =
        ((sideEdgeFinset G A).card : ℝ) / 2 +
          ((sideEdgeFinset G B).card : ℝ) / 2 := by
  obtain ⟨f, hMsub⟩ := exists_embeddingCrossMatching_superset hAleB hM
  let wK := zeroExtendTriangleWeight
    (G.deleteEdges (embeddingCrossMatching A B f : Set (Sym2 α)))
    (proposition72bWeight A B f)
  let w := zeroExtendTriangleWeight
    (G.deleteEdges (embeddingCrossMatching A B f : Set (Sym2 α))) wK
  have hKcross : ∀ a : A, ∀ b : B,
      (G.deleteEdges
        (embeddingCrossMatching A B f : Set (Sym2 α))).Adj a.1 b.1 ↔
          b ≠ f a := by
    intro a b
    exact delete_embeddingCrossMatching_cross_adj
      hAB f hMsub hcross a b
  have hPK := proposition72b_twoBlobPacking_exact
    (G := G.deleteEdges
      (embeddingCrossMatching A B f : Set (Sym2 α)))
    hAB f hKcross hAcard hAleB hBle
  refine ⟨w, ?_, ?_⟩
  · exact hPK.1.zeroExtend_deleteEmbedding hAB f
  · calc
      fractionalSize G w =
          fractionalSize
            (G.deleteEdges
              (embeddingCrossMatching A B f : Set (Sym2 α))) wK := by
        exact fractionalSize_zeroExtend_to_supergraph
          (SimpleGraph.deleteEdges_le _) wK
      _ = ((sideEdgeFinset
          (G.deleteEdges
            (embeddingCrossMatching A B f : Set (Sym2 α))) A).card : ℝ) / 2 +
          ((sideEdgeFinset
            (G.deleteEdges
              (embeddingCrossMatching A B f : Set (Sym2 α))) B).card : ℝ) / 2 :=
        hPK.2
      _ = ((sideEdgeFinset G A).card : ℝ) / 2 +
          ((sideEdgeFinset G B).card : ℝ) / 2 := by
        rw [sideEdgeFinset_delete_embeddingCrossMatching_left
              (G := G) hAB f,
          sideEdgeFinset_delete_embeddingCrossMatching_right
            (G := G) hAB f]

/-- The arbitrary-matching form of Proposition 7.2(b), with the local load
information needed when several two-blob packings are added.  Every actual
edge internal to either blob has load exactly one half, and an edge outside
the union of the two blobs has load zero. -/
theorem proposition72b_arbitraryMatching_with_loads
    {G : SimpleGraph α} {A B : Finset α} {M : Finset (Sym2 α)}
    (hAB : Disjoint A B) (hM : IsABCrossMatching A B M)
    (hcross : ∀ a : A, ∀ b : B,
      G.Adj a.1 b.1 ↔ s(a.1, b.1) ∉ M)
    (hAcard : 3 ≤ A.card) (hAleB : A.card ≤ B.card)
    (hBle : B.card ≤ A.card + 1) :
    ∃ w : Finset α → ℝ,
      IsFractionalInternalCrossPacking G (A : Set α) w ∧
      fractionalSize G w =
        ((sideEdgeFinset G A).card : ℝ) / 2 +
          ((sideEdgeFinset G B).card : ℝ) / 2 ∧
      (∀ e ∈ G.edgeFinset, e.toFinset ⊆ A →
        fractionalEdgeLoad G w e = 1 / 2) ∧
      (∀ e ∈ G.edgeFinset, e.toFinset ⊆ B →
        fractionalEdgeLoad G w e = 1 / 2) ∧
      (∀ e : Sym2 α, ¬e.toFinset ⊆ A ∪ B →
        fractionalEdgeLoad G w e = 0) := by
  classical
  obtain ⟨f, hMsub⟩ := exists_embeddingCrossMatching_superset hAleB hM
  let K := G.deleteEdges (embeddingCrossMatching A B f : Set (Sym2 α))
  let wK := zeroExtendTriangleWeight K (proposition72bWeight A B f)
  let w := zeroExtendTriangleWeight K wK
  have hKG : K ≤ G := SimpleGraph.deleteEdges_le _
  have hKcross : ∀ a : A, ∀ b : B, K.Adj a.1 b.1 ↔ b ≠ f a := by
    intro a b
    exact delete_embeddingCrossMatching_cross_adj
      hAB f hMsub hcross a b
  have hPK := proposition72b_twoBlobPacking_exact
    (G := K) hAB f hKcross hAcard hAleB hBle
  have hLoads := proposition72b_twoBlobPacking
    (G := K) hAB f hKcross hAcard hAleB hBle
  refine ⟨w, ?_, ?_, ?_, ?_, ?_⟩
  · exact hPK.1.zeroExtend_deleteEmbedding hAB f
  · calc
      fractionalSize G w = fractionalSize K wK := by
        exact fractionalSize_zeroExtend_to_supergraph hKG wK
      _ = ((sideEdgeFinset K A).card : ℝ) / 2 +
          ((sideEdgeFinset K B).card : ℝ) / 2 := hPK.2
      _ = ((sideEdgeFinset G A).card : ℝ) / 2 +
          ((sideEdgeFinset G B).card : ℝ) / 2 := by
        rw [sideEdgeFinset_delete_embeddingCrossMatching_left
              (G := G) hAB f,
          sideEdgeFinset_delete_embeddingCrossMatching_right
            (G := G) hAB f]
  · intro e heG heA
    have heSideG : e ∈ sideEdgeFinset G A :=
      mem_filter.mpr ⟨heG, heA⟩
    have heSideK : e ∈ sideEdgeFinset K A := by
      rw [sideEdgeFinset_delete_embeddingCrossMatching_left
        (G := G) hAB f]
      exact heSideG
    rw [show w = zeroExtendTriangleWeight K wK by rfl,
      fractionalEdgeLoad_zeroExtend hKG]
    exact hLoads.2.1 e (mem_filter.mp heSideK).1 heA
  · intro e heG heB
    have heSideG : e ∈ sideEdgeFinset G B :=
      mem_filter.mpr ⟨heG, heB⟩
    have heSideK : e ∈ sideEdgeFinset K B := by
      rw [sideEdgeFinset_delete_embeddingCrossMatching_right
        (G := G) hAB f]
      exact heSideG
    rw [show w = zeroExtendTriangleWeight K wK by rfl,
      fractionalEdgeLoad_zeroExtend hKG]
    exact hLoads.2.2 e (mem_filter.mp heSideK).1 heB
  · intro e heOutside
    rw [show w = zeroExtendTriangleWeight K wK by rfl,
      fractionalEdgeLoad_zeroExtend hKG,
      show wK = zeroExtendTriangleWeight K
        (proposition72bWeight A B f) by rfl,
      fractionalEdgeLoad_zeroExtend (G := K) le_rfl]
    exact fractionalEdgeLoad_proposition72bWeight_eq_zero_of_not_subset_union
      hAB f heOutside

/-- Proposition 7.2(b) in the form used in the one-edge-flip construction:
the ambient cross graph is complete, but the resulting packing is required
to avoid a prescribed cross matching. -/
theorem proposition72b_avoidMatching_with_loads
    {G : SimpleGraph α} {A B : Finset α} {M : Finset (Sym2 α)}
    (hAB : Disjoint A B) (hM : IsABCrossMatching A B M)
    (hcross : ∀ a : A, ∀ b : B, G.Adj a.1 b.1)
    (hAcard : 3 ≤ A.card) (hAleB : A.card ≤ B.card)
    (hBle : B.card ≤ A.card + 1) :
    ∃ w : Finset α → ℝ,
      IsFractionalInternalCrossPacking G (A : Set α) w ∧
      fractionalSize G w =
        ((sideEdgeFinset G A).card : ℝ) / 2 +
          ((sideEdgeFinset G B).card : ℝ) / 2 ∧
      (∀ e ∈ G.edgeFinset, e.toFinset ⊆ A →
        fractionalEdgeLoad G w e = 1 / 2) ∧
      (∀ e ∈ G.edgeFinset, e.toFinset ⊆ B →
        fractionalEdgeLoad G w e = 1 / 2) ∧
      (∀ e : Sym2 α, ¬e.toFinset ⊆ A ∪ B →
        fractionalEdgeLoad G w e = 0) ∧
      (∀ e ∈ M, fractionalEdgeLoad G w e = 0) := by
  classical
  let K := G.deleteEdges (M : Set (Sym2 α))
  have hKG : K ≤ G := SimpleGraph.deleteEdges_le _
  have hKcross : ∀ a : A, ∀ b : B,
      K.Adj a.1 b.1 ↔ s(a.1, b.1) ∉ M := by
    intro a b
    rw [SimpleGraph.deleteEdges_adj]
    simp only [Set.mem_setOf_eq, Finset.mem_coe]
    exact and_iff_right (hcross a b)
  obtain ⟨wK, hwK, hsizeK, hloadA, hloadB, houtside⟩ :=
    proposition72b_arbitraryMatching_with_loads
      (G := K) hAB hM hKcross hAcard hAleB hBle
  let w := zeroExtendTriangleWeight K wK
  have hInternal := internalEdgeFinset_delete_ABCrossMatching
    (G := G) hM
  refine ⟨w, hwK.zeroExtend_deleteABCrossMatching hM, ?_, ?_, ?_, ?_, ?_⟩
  · calc
      fractionalSize G w = fractionalSize K wK :=
        fractionalSize_zeroExtend_to_supergraph hKG wK
      _ = ((sideEdgeFinset K A).card : ℝ) / 2 +
          ((sideEdgeFinset K B).card : ℝ) / 2 := hsizeK
      _ = ((sideEdgeFinset G A).card : ℝ) / 2 +
          ((sideEdgeFinset G B).card : ℝ) / 2 := by
        rw [sideEdgeFinset_delete_ABCrossMatching_left
              (G := G) hM,
          sideEdgeFinset_delete_ABCrossMatching_right
              (G := G) hAB hM]
  · intro e heG heA
    have heSame : SameSide (A : Set α) e :=
      (sameSide_iff_subset_side_or_compl (A : Set α) e).mpr
        (Or.inl (by simpa using heA))
    have heInternalG : e ∈ internalEdgeFinset G (A : Set α) :=
      mem_filter.mpr ⟨heG, heSame⟩
    have heInternalK : e ∈ internalEdgeFinset K (A : Set α) := by
      rw [hInternal]
      exact heInternalG
    rw [show w = zeroExtendTriangleWeight K wK by rfl,
      fractionalEdgeLoad_zeroExtend hKG]
    exact hloadA e (mem_filter.mp heInternalK).1 heA
  · intro e heG heB
    have heSame : SameSide (A : Set α) e :=
      (sameSide_iff_subset_side_or_compl (A : Set α) e).mpr
        (Or.inr (by
          intro x hx
          simp only [Set.mem_toFinset, Set.mem_compl_iff]
          intro hxA
          exact Finset.disjoint_left.mp hAB hxA (heB hx)))
    have heInternalG : e ∈ internalEdgeFinset G (A : Set α) :=
      mem_filter.mpr ⟨heG, heSame⟩
    have heInternalK : e ∈ internalEdgeFinset K (A : Set α) := by
      rw [hInternal]
      exact heInternalG
    rw [show w = zeroExtendTriangleWeight K wK by rfl,
      fractionalEdgeLoad_zeroExtend hKG]
    exact hloadB e (mem_filter.mp heInternalK).1 heB
  · intro e heOutside
    rw [show w = zeroExtendTriangleWeight K wK by rfl,
      fractionalEdgeLoad_zeroExtend hKG]
    exact houtside e heOutside
  · intro e heM
    rw [show w = zeroExtendTriangleWeight K wK by rfl,
      fractionalEdgeLoad_zeroExtend hKG]
    have heND : ¬e.IsDiag := by
      induction e using Sym2.inductionOn with
      | hf x y =>
          intro hdiag
          have hxy : x = y := by
            simpa [Sym2.mk_isDiag_iff] using hdiag
          subst y
          exact hM.1.1 s(x, x) heM (by simp [sameSide_mk])
    apply fractionalEdgeLoad_eq_zero_of_not_edge K wK heND
    intro he
    induction e using Sym2.inductionOn with
    | hf x y =>
        have hxy : K.Adj x y := by
          simpa [SimpleGraph.mem_edgeFinset,
            SimpleGraph.mem_edgeSet] using he
        exact hxy.2 (by
          simpa [SimpleGraph.fromEdgeSet_adj] using And.intro heM hxy.ne)

end

end Erdos76
