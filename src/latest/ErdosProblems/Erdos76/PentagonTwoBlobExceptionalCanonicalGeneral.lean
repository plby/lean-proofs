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
import ErdosProblems.Erdos76.PentagonTwoBlobExceptionalCanonical

/-!
# Proposition 7.2(d) with arbitrary internal colours on the canonical blobs

The finite certificate was checked in the graph in which both blobs are
cliques.  Here we restrict it to a graph with the same cross edges and
arbitrary internal edges.
-/

open Finset

namespace Erdos76

noncomputable section

attribute [local instance] Classical.propDecidable

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Two graphs agree on every pair crossing the displayed bipartition. -/
def SameCrossAdj (G H : SimpleGraph α) (s : Set α) : Prop :=
  ∀ x y, ¬(x ∈ s ↔ y ∈ s) → (G.Adj x y ↔ H.Adj x y)

lemma internalEdgeFinset_map_equiv
    {β : Type*} [Fintype β] [DecidableEq β]
    (G : SimpleGraph α) (s : Set α) (e : α ≃ β) :
    internalEdgeFinset (G.map e.toEmbedding) (e '' s) =
      (internalEdgeFinset G s).map e.toEmbedding.sym2Map := by
  classical
  ext p
  induction p using Sym2.inductionOn with
  | hf a b =>
      let x := e.symm a
      let y := e.symm b
      have hax : e x = a := e.apply_symm_apply a
      have hby : e y = b := e.apply_symm_apply b
      have hmapAdj :
          (G.map e.toEmbedding).Adj a b ↔ G.Adj x y := by
        rw [← hax, ← hby]
        exact SimpleGraph.map_adj_apply
      simp only [internalEdgeFinset, mem_filter, SimpleGraph.mem_edgeFinset,
        SimpleGraph.mem_edgeSet, sameSide_mk, mem_map]
      constructor
      · rintro ⟨hab, hside⟩
        refine ⟨s(x, y), ⟨hmapAdj.mp hab, ?_⟩, ?_⟩
        · simpa [x, y, hax, hby] using hside
        · simpa [x, y, hax, hby]
      · rintro ⟨q, hq, hqeq⟩
        have hq' : q = s(x, y) := by
          apply e.toEmbedding.sym2Map.injective
          simpa [x, y, hax, hby] using hqeq
        subst q
        exact ⟨hmapAdj.mpr hq.1, by
          simpa [x, y, hax, hby] using hq.2⟩

lemma sym2Map_mem_sym2_map_iff
    {β : Type*} [DecidableEq β] (e : α ≃ β)
    (p : Sym2 α) (t : Finset α) :
    e.toEmbedding.sym2Map p ∈ (t.map e.toEmbedding).sym2 ↔ p ∈ t.sym2 := by
  rw [Finset.sym2_map]
  constructor
  · intro hp
    obtain ⟨q, hq, hqp⟩ := mem_map.mp hp
    have : q = p := e.toEmbedding.sym2Map.injective hqp
    simpa only [this] using hq
  · exact fun hp ↦ mem_map.mpr ⟨p, hp, rfl⟩

lemma mem_internalCrossTriangles_map_equiv_iff
    {β : Type*} [Fintype β] [DecidableEq β]
    (G : SimpleGraph α) (s : Set α) (e : α ≃ β) (t : Finset α) :
    t.map e.toEmbedding ∈
        internalCrossTriangles (G.map e.toEmbedding) (e '' s) ↔
      t ∈ internalCrossTriangles G s := by
  classical
  rw [mem_internalCrossTriangles, mem_internalCrossTriangles]
  constructor
  · rintro ⟨htMap, htOne⟩
    have ht : G.IsNClique 3 t := by
      have hback := htMap.map (f := e.symm.toEmbedding)
      have hgraph : (G.map e.toEmbedding).map e.symm.toEmbedding = G := by
        rw [SimpleGraph.map_map]
        simpa using G.map_id
      have hfin : (t.map e.toEmbedding).map e.symm.toEmbedding = t := by
        simp [Finset.map_map]
      simpa only [hgraph, hfin] using hback
    refine ⟨ht, ?_⟩
    rw [internalEdgeFinset_map_equiv G s e, Finset.filter_map] at htOne
    rw [card_map] at htOne
    change ((internalEdgeFinset G s).filter
      (fun p ↦ e.toEmbedding.sym2Map p ∈ (t.map e.toEmbedding).sym2)).card = 1 at htOne
    have hfilter :
        (internalEdgeFinset G s).filter
            (fun p ↦ e.toEmbedding.sym2Map p ∈ (t.map e.toEmbedding).sym2) =
          (internalEdgeFinset G s).filter (fun p ↦ p ∈ t.sym2) := by
      ext p
      simp only [mem_filter, sym2Map_mem_sym2_map_iff]
    rwa [hfilter] at htOne
  · rintro ⟨ht, htOne⟩
    refine ⟨ht.map, ?_⟩
    rw [internalEdgeFinset_map_equiv G s e, Finset.filter_map]
    rw [card_map]
    change ((internalEdgeFinset G s).filter
      (fun p ↦ e.toEmbedding.sym2Map p ∈ (t.map e.toEmbedding).sym2)).card = 1
    have hfilter :
        (internalEdgeFinset G s).filter
            (fun p ↦ e.toEmbedding.sym2Map p ∈ (t.map e.toEmbedding).sym2) =
          (internalEdgeFinset G s).filter (fun p ↦ p ∈ t.sym2) := by
      ext p
      simp only [mem_filter, sym2Map_mem_sym2_map_iff]
    rw [hfilter]
    exact htOne

lemma IsFractionalInternalCrossPacking.relabel
    {β : Type*} [Fintype β] [DecidableEq β]
    {G : SimpleGraph α} {s : Set α} {w : Finset α → ℝ}
    (hw : IsFractionalInternalCrossPacking G s w) (e : α ≃ β) :
    IsFractionalInternalCrossPacking (G.map e.toEmbedding) (e '' s)
      (relabelWeight e w) := by
  classical
  refine ⟨hw.1.relabel e, ?_⟩
  intro u hu
  apply hw.2 (u.map e.symm.toEmbedding)
  intro ht
  apply hu
  have hmap := (mem_internalCrossTriangles_map_equiv_iff G s e
    (u.map e.symm.toEmbedding)).mpr ht
  simpa [Finset.map_map] using hmap

/-- Restricting a cross triangle to a subgraph preserves it whenever the
triangle itself survives in the subgraph. -/
lemma mem_internalCrossTriangles_of_le_of_isNClique
    {G H : SimpleGraph α} {s : Set α} {t : Finset α}
    (hGH : G ≤ H) (htH : t ∈ internalCrossTriangles H s)
    (htG : G.IsNClique 3 t) :
    t ∈ internalCrossTriangles G s := by
  classical
  rcases mem_internalCrossTriangles.mp htH with ⟨_htHClique, htOne⟩
  apply mem_internalCrossTriangles.mpr
  refine ⟨htG, ?_⟩
  rw [show (internalEdgeFinset G s).filter (fun e ↦ e ∈ t.sym2) =
      (internalEdgeFinset H s).filter (fun e ↦ e ∈ t.sym2) by
    ext e
    constructor
    · intro he
      rcases mem_filter.mp he with ⟨heG, het⟩
      rcases mem_filter.mp heG with ⟨heGEdge, heSame⟩
      exact mem_filter.mpr ⟨mem_filter.mpr
        ⟨SimpleGraph.edgeFinset_mono hGH heGEdge, heSame⟩, het⟩
    · intro he
      rcases mem_filter.mp he with ⟨heH, het⟩
      rcases mem_filter.mp heH with ⟨heHEdge, heSame⟩
      induction e using Sym2.inductionOn with
      | hf x y =>
          simp only [Finset.mk_mem_sym2_iff] at het
          have hxy : x ≠ y := by
            have hnd := H.not_isDiag_of_mem_edgeFinset heHEdge
            simpa only [Sym2.mk_isDiag_iff] using hnd
          have hGxy : G.Adj x y := htG.isClique het.1 het.2 hxy
          exact mem_filter.mpr ⟨mem_filter.mpr
            ⟨by simpa only [SimpleGraph.mem_edgeFinset,
                SimpleGraph.mem_edgeSet] using hGxy, heSame⟩,
              by simpa only [Finset.mk_mem_sym2_iff] using het⟩]
  exact htOne

lemma proposition72dCanonicalGraph_adj_of_sameSide
    {x y : Proposition72dVertex} (hxy : x ≠ y)
    (hsame : x ∈ (proposition72dCanonicalA : Set Proposition72dVertex) ↔
      y ∈ (proposition72dCanonicalA : Set Proposition72dVertex)) :
    proposition72dCanonicalGraph.Adj x y := by
  fin_cases x <;> fin_cases y
  all_goals simp [proposition72dCanonicalA] at hxy hsame
  all_goals
    norm_num [proposition72dCanonicalGraph, proposition72dCanonicalMissing,
      Sym2.eq_iff]
  all_goals decide

lemma le_proposition72dCanonicalGraph_of_sameCross
    {G : SimpleGraph Proposition72dVertex}
    (hcross : SameCrossAdj G proposition72dCanonicalGraph
      (proposition72dCanonicalA : Set Proposition72dVertex)) :
    G ≤ proposition72dCanonicalGraph := by
  intro x y hGxy
  by_cases hsame :
      x ∈ (proposition72dCanonicalA : Set Proposition72dVertex) ↔
        y ∈ (proposition72dCanonicalA : Set Proposition72dVertex)
  · exact proposition72dCanonicalGraph_adj_of_sameSide hGxy.ne hsame
  · exact (hcross x y hsame).mp hGxy

private lemma proposition72dCanonicalFamily_isNClique_of_internalEdge
    {G : SimpleGraph Proposition72dVertex}
    (hcross : SameCrossAdj G proposition72dCanonicalGraph
      (proposition72dCanonicalA : Set Proposition72dVertex))
    {t : Finset Proposition72dVertex} {e : Sym2 Proposition72dVertex}
    (htFamily : t ∈ proposition72dCanonicalHalfFamily ∪
      proposition72dCanonicalThirdFamily ∪ proposition72dCanonicalSixthFamily)
    (he : e ∈ internalEdgeFinset G
      (proposition72dCanonicalA : Set Proposition72dVertex))
    (het : e ∈ t.sym2) :
    G.IsNClique 3 t := by
  classical
  let H := proposition72dCanonicalGraph
  let sA : Set Proposition72dVertex := proposition72dCanonicalA
  have hGH : G ≤ H := le_proposition72dCanonicalGraph_of_sameCross hcross
  have htH : t ∈ internalCrossTriangles H sA := by
    exact proposition72dCanonicalFamilies_internalCross htFamily
  rcases mem_internalCrossTriangles.mp htH with ⟨htHClique, htOne⟩
  rw [SimpleGraph.isNClique_iff]
  refine ⟨?_, htHClique.card_eq⟩
  intro x hx y hy hxy
  by_cases hsame : x ∈ sA ↔ y ∈ sA
  · have hHxy : H.Adj x y := htHClique.isClique hx hy hxy
    have hqInternal : s(x, y) ∈ internalEdgeFinset H sA :=
      mem_filter.mpr ⟨by
        simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using hHxy,
        by simpa only [sameSide_mk] using hsame⟩
    have hq : s(x, y) ∈
        (internalEdgeFinset H sA).filter (fun q ↦ q ∈ t.sym2) :=
      mem_filter.mpr ⟨hqInternal, by
        simpa only [Finset.mk_mem_sym2_iff, Finset.mem_coe] using And.intro hx hy⟩
    rcases mem_filter.mp he with ⟨heGEdge, heSame⟩
    have heHInternal : e ∈ internalEdgeFinset H sA :=
      mem_filter.mpr ⟨SimpleGraph.edgeFinset_mono hGH heGEdge, heSame⟩
    have he' : e ∈
        (internalEdgeFinset H sA).filter (fun q ↦ q ∈ t.sym2) :=
      mem_filter.mpr ⟨heHInternal, het⟩
    have hqe : s(x, y) = e :=
      (card_le_one.mp (by omega)) s(x, y) hq e he'
    have heGSet := SimpleGraph.mem_edgeFinset.mp heGEdge
    rw [← hqe] at heGSet
    simpa only [SimpleGraph.mem_edgeSet] using heGSet
  · exact (hcross x y hsame).mpr (htHClique.isClique hx hy hxy)

lemma fractionalEdgeLoad_zeroExtend_proposition72dCanonicalWeight_internal
    {G : SimpleGraph Proposition72dVertex}
    (hcross : SameCrossAdj G proposition72dCanonicalGraph
      (proposition72dCanonicalA : Set Proposition72dVertex))
    (e : Sym2 Proposition72dVertex)
    (he : e ∈ internalEdgeFinset G
      (proposition72dCanonicalA : Set Proposition72dVertex)) :
    fractionalEdgeLoad G
      (zeroExtendTriangleWeight G proposition72dCanonicalWeight) e = 1 / 2 := by
  classical
  rw [fractionalEdgeLoad_zeroExtend (G := G) le_rfl,
    proposition72dCanonicalWeight,
    show addTriangleWeight _ _ = (fun t ↦ _ + _) by rfl,
    fractionalEdgeLoad_add,
    show addTriangleWeight _ _ = (fun t ↦ _ + _) by rfl,
    fractionalEdgeLoad_add,
    fractionalEdgeLoad_constantTriangleFamilyWeight_of_incident
      (fun t ht het ↦ proposition72dCanonicalFamily_isNClique_of_internalEdge
        hcross (mem_union_left _ (mem_union_left _ ht)) he het),
    fractionalEdgeLoad_constantTriangleFamilyWeight_of_incident
      (fun t ht het ↦ proposition72dCanonicalFamily_isNClique_of_internalEdge
        hcross (mem_union_left _ (mem_union_right _ ht)) he het),
    fractionalEdgeLoad_constantTriangleFamilyWeight_of_incident
      (fun t ht het ↦ proposition72dCanonicalFamily_isNClique_of_internalEdge
        hcross (mem_union_right _ ht) he het)]
  rcases mem_filter.mp he with ⟨heG, heSame⟩
  have hscore := proposition72dCanonicalEdgeScore_eq_three_of_sameSide e
    (G.not_isDiag_of_mem_edgeFinset heG) heSame
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

theorem proposition72dCanonicalPacking_arbitraryInternal
    {G : SimpleGraph Proposition72dVertex}
    (hcross : SameCrossAdj G proposition72dCanonicalGraph
      (proposition72dCanonicalA : Set Proposition72dVertex)) :
    IsFractionalInternalCrossPacking G
        (proposition72dCanonicalA : Set Proposition72dVertex)
        (zeroExtendTriangleWeight G proposition72dCanonicalWeight) ∧
      fractionalSize G
          (zeroExtendTriangleWeight G proposition72dCanonicalWeight) =
        ((internalEdgeFinset G
          (proposition72dCanonicalA : Set Proposition72dVertex)).card : ℝ) / 2 := by
  classical
  have hGH : G ≤ proposition72dCanonicalGraph :=
    le_proposition72dCanonicalGraph_of_sameCross hcross
  have hpacking : IsFractionalInternalCrossPacking G
      (proposition72dCanonicalA : Set Proposition72dVertex)
      (zeroExtendTriangleWeight G proposition72dCanonicalWeight) := by
    refine ⟨isFractionalPacking_proposition72dCanonicalWeight.restrictToSubgraph hGH,
      ?_⟩
    intro t htNot
    by_cases htG : t ∈ G.cliqueFinset 3
    · rw [zeroExtendTriangleWeight_of_mem htG]
      apply proposition72dCanonicalWeight_support
      intro htH
      exact htNot (mem_internalCrossTriangles_of_le_of_isNClique hGH htH
        (SimpleGraph.mem_cliqueFinset_iff.mp htG))
    · exact zeroExtendTriangleWeight_of_not_mem htG
  refine ⟨hpacking, ?_⟩
  calc
    fractionalSize G (zeroExtendTriangleWeight G proposition72dCanonicalWeight) =
        ∑ e ∈ internalEdgeFinset G
          (proposition72dCanonicalA : Set Proposition72dVertex),
            fractionalEdgeLoad G
              (zeroExtendTriangleWeight G proposition72dCanonicalWeight) e := by
      exact (sum_internalEdge_fractionalEdgeLoad_eq_fractionalSize hpacking).symm
    _ = ∑ _e ∈ internalEdgeFinset G
          (proposition72dCanonicalA : Set Proposition72dVertex), (1 / 2 : ℝ) := by
      apply sum_congr rfl
      intro e he
      exact fractionalEdgeLoad_zeroExtend_proposition72dCanonicalWeight_internal
        hcross e he
    _ = ((internalEdgeFinset G
          (proposition72dCanonicalA : Set Proposition72dVertex)).card : ℝ) / 2 := by
      simp [div_eq_mul_inv]

/-- Transport the canonical `(3,5)` certificate across an arbitrary vertex
equivalence which identifies the displayed side with `{0,1,2}`. -/
theorem proposition72dPacking_of_equiv
    {G : SimpleGraph α} {s : Set α} (e : α ≃ Proposition72dVertex)
    (hside : e '' s =
      (proposition72dCanonicalA : Set Proposition72dVertex))
    (hcross : SameCrossAdj (G.map e.toEmbedding)
      proposition72dCanonicalGraph
      (proposition72dCanonicalA : Set Proposition72dVertex)) :
    ∃ w : Finset α → ℝ,
      IsFractionalInternalCrossPacking G s w ∧
        fractionalSize G w = ((internalEdgeFinset G s).card : ℝ) / 2 := by
  classical
  let K := G.map e.toEmbedding
  let u := zeroExtendTriangleWeight K proposition72dCanonicalWeight
  obtain ⟨hu, hsize⟩ := proposition72dCanonicalPacking_arbitraryInternal
    (G := K) hcross
  let w := relabelWeight e.symm u
  have hmap : K.map e.symm.toEmbedding = G := by
    dsimp only [K]
    rw [SimpleGraph.map_map]
    simpa using G.map_id
  have hsideBack : e.symm ''
      (proposition72dCanonicalA : Set Proposition72dVertex) = s := by
    rw [← hside]
    ext x
    simp
  have hw : IsFractionalInternalCrossPacking G s w := by
    have hrel := hu.relabel e.symm
    simpa only [w, hmap, hsideBack] using hrel
  refine ⟨w, hw, ?_⟩
  have hsizeRel : fractionalSize G w = fractionalSize K u := by
    simpa only [w, hmap] using fractionalSize_relabel K e.symm u
  have hIE := internalEdgeFinset_map_equiv G s e
  change internalEdgeFinset K (e '' s) =
    (internalEdgeFinset G s).map e.toEmbedding.sym2Map at hIE
  rw [hside] at hIE
  have hcard := congrArg Finset.card hIE
  simp only [card_map] at hcard
  rw [hsizeRel, hsize, hcard]

end

end Erdos76
