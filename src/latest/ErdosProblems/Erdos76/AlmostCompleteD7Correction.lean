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
import ErdosProblems.Erdos76.AlmostCompleteD7

/-!
# The explicit large-universal-set correction in D7

This file constructs the three triangle families in the large-`m` branch
and proves their feasibility and edge-load formulas.
-/

open Finset
open scoped BigOperators

namespace Erdos76

noncomputable section

attribute [local instance] Classical.propDecidable

variable {A : Type} [Fintype A] [DecidableEq A]

lemma card_top_edgeFinset_filter_mem {B : Type} [Fintype B]
    [DecidableEq B] (x : B) :
    ((⊤ : SimpleGraph B).edgeFinset.filter fun e ↦ x ∈ e).card =
      Fintype.card B - 1 := by
  rw [← SimpleGraph.incidenceFinset_eq_filter,
    SimpleGraph.card_incidenceFinset_eq_degree,
    ← SimpleGraph.card_neighborFinset_eq_degree,
    SimpleGraph.neighborFinset_top]
  rw [Finset.card_compl, Finset.card_singleton]

lemma induce_universalVertices_eq_top (G : SimpleGraph A) :
    G.induce (↑(universalVertices G) : Set A) = ⊤ := by
  ext x y
  change G.Adj (x : A) (y : A) ↔ x ≠ y
  constructor
  · intro hadj hxy
    exact hadj.ne (congrArg Subtype.val hxy)
  · intro hxy
    exact adj_of_mem_universalVertices G x.property
      (fun h ↦ hxy (Subtype.ext h))

lemma inducedEdge_mem_attachedEdgeTriangle_sym2_iff_public
    {S : Finset A} {u : A} {p f : Sym2 S} (hu : u ∉ S)
    (hp : ¬p.IsDiag) (hf : ¬f.IsDiag) :
    (inducedEmbedding S).sym2Map p ∈ (attachedEdgeTriangle S u f).sym2 ↔
      p = f := by
  induction p using Sym2.inductionOn with
  | hf a b =>
      induction f using Sym2.inductionOn with
      | hf x y =>
          simp only [Sym2.mk_isDiag_iff] at hp hf
          have hau : (a : A) ≠ u := by
            intro h
            apply hu
            rw [← h]
            exact a.property
          have hbu : (b : A) ≠ u := by
            intro h
            apply hu
            rw [← h]
            exact b.property
          simp only [attachedEdgeTriangle, Sym2.map_mk,
            Sym2.toFinset_mk_eq, Finset.map_insert, Finset.map_singleton,
            Finset.mk_mem_sym2_iff, Finset.mem_insert, Finset.mem_singleton,
            Sym2.eq_iff]
          aesop

lemma starEdge_mem_attachedEdgeTriangle_sym2_iff_public
    {S : Finset A} {u : A} (hu : u ∉ S) (x : S) (f : Sym2 S) :
    s(u, (x : A)) ∈ (attachedEdgeTriangle S u f).sym2 ↔ x ∈ f := by
  induction f using Sym2.inductionOn with
  | hf a b =>
      have hxu : (x : A) ≠ u := by
        intro h
        apply hu
        rw [← h]
        exact x.property
      simp only [attachedEdgeTriangle, Sym2.toFinset_mk_eq,
        Finset.map_insert, Finset.map_singleton, Finset.mk_mem_sym2_iff,
        Finset.mem_insert, Finset.mem_singleton, Sym2.mem_iff]
      aesop

lemma starEdge_not_mem_attachedEdgeTriangle_of_ne_attachment
    {S : Finset A} {u v : A} (hu : u ∉ S) (hv : v ∉ S)
    (huv : u ≠ v) (x : S) (f : Sym2 S) :
    s(u, (x : A)) ∉ (attachedEdgeTriangle S v f).sym2 := by
  induction f using Sym2.inductionOn with
  | hf a b =>
      have hxv : (x : A) ≠ v := by
        intro h
        apply hv
        rw [← h]
        exact x.property
      have hau : (a : A) ≠ u := by
        intro h
        apply hu
        rw [← h]
        exact a.property
      have hbu : (b : A) ≠ u := by
        intro h
        apply hu
        rw [← h]
        exact b.property
      simp only [attachedEdgeTriangle, Sym2.toFinset_mk_eq,
        Finset.map_insert, Finset.map_singleton, Finset.mk_mem_sym2_iff,
        Finset.mem_insert, Finset.mem_singleton]
      aesop

lemma outsidePair_not_mem_attachedEdgeTriangle
    {S : Finset A} {u x y : A} (hx : x ∉ S) (hy : y ∉ S)
    (hxy : x ≠ y) (f : Sym2 S) :
    s(x, y) ∉ (attachedEdgeTriangle S u f).sym2 := by
  induction f using Sym2.inductionOn with
  | hf a b =>
      have hxa : x ≠ (a : A) := fun h ↦ hx (h ▸ a.property)
      have hxb : x ≠ (b : A) := fun h ↦ hx (h ▸ b.property)
      have hya : y ≠ (a : A) := fun h ↦ hy (h ▸ a.property)
      have hyb : y ≠ (b : A) := fun h ↦ hy (h ▸ b.property)
      simp only [attachedEdgeTriangle, Sym2.toFinset_mk_eq,
        Finset.map_insert, Finset.map_singleton, Finset.mk_mem_sym2_iff,
        Finset.mem_insert, Finset.mem_singleton]
      aesop

lemma fractionalEdgeLoad_weightedAttachedEdgeWeight_induced
    {G : SimpleGraph A} {S : Finset A} {u : A}
    {C : Finset (Sym2 S)} {r : Sym2 S → ℝ}
    (hu : u ∉ S)
    (hnonDiag : ∀ f ∈ C, ¬f.IsDiag)
    (htri : ∀ e ∈ C, attachedEdgeTriangle S u e ∈ G.cliqueFinset 3)
    {p : Sym2 S} (hp : ¬p.IsDiag) :
    fractionalEdgeLoad G (weightedAttachedEdgeWeight S u C r)
        ((inducedEmbedding S).sym2Map p) =
      if p ∈ C then r p else 0 := by
  rw [fractionalEdgeLoad_weightedAttachedEdgeWeight htri]
  by_cases hpC : p ∈ C
  · rw [if_pos hpC]
    let pC : ↑C := ⟨p, hpC⟩
    rw [Fintype.sum_eq_single pC]
    · dsimp [pC]
      rw [if_pos ((inducedEdge_mem_attachedEdgeTriangle_sym2_iff_public
        hu hp (hnonDiag p hpC)).mpr rfl)]
    · intro f hfp
      rw [if_neg]
      intro hmem
      apply hfp
      apply Subtype.ext
      exact ((inducedEdge_mem_attachedEdgeTriangle_sym2_iff_public
        hu hp (hnonDiag f f.property)).mp hmem).symm
  · rw [if_neg hpC]
    apply Fintype.sum_eq_zero
    intro f
    rw [if_neg]
    intro hmem
    exact hpC ((inducedEdge_mem_attachedEdgeTriangle_sym2_iff_public
      hu hp (hnonDiag f f.property)).mp hmem ▸ f.property)

lemma fractionalEdgeLoad_weightedAttachedEdgeWeight_star
    {G : SimpleGraph A} {S : Finset A} {u : A}
    {C : Finset (Sym2 S)} {r : Sym2 S → ℝ}
    (hu : u ∉ S)
    (htri : ∀ e ∈ C, attachedEdgeTriangle S u e ∈ G.cliqueFinset 3)
    (x : S) :
    fractionalEdgeLoad G (weightedAttachedEdgeWeight S u C r)
        s(u, (x : A)) =
      ∑ e ∈ C with x ∈ e, r e := by
  rw [fractionalEdgeLoad_weightedAttachedEdgeWeight htri]
  simp_rw [starEdge_mem_attachedEdgeTriangle_sym2_iff_public hu x]
  calc
    (∑ e : ↑C, if x ∈ (e : Sym2 S) then r e else 0) =
        ∑ e ∈ C, if x ∈ e then r e else 0 :=
      (Finset.sum_subtype C (fun _ ↦ Iff.rfl)
        (fun e ↦ if x ∈ e then r e else 0)).symm
    _ = ∑ e ∈ C with x ∈ e, r e := by rw [Finset.sum_filter]

lemma universalVertex_not_mem_nonUniversalVertices (G : SimpleGraph A)
    {z : A} (hz : z ∈ universalVertices G) :
    z ∉ nonUniversalVertices G := by
  intro hz'
  have hzero := mem_universalVertices.mp hz
  have hpos := mem_nonUniversalVertices.mp hz'
  omega

lemma nonUniversalVertex_not_mem_universalVertices (G : SimpleGraph A)
    {u : A} (hu : u ∈ nonUniversalVertices G) :
    u ∉ universalVertices G := by
  intro hu'
  exact universalVertex_not_mem_nonUniversalVertices G hu' hu

lemma d7UUZTriangle_mem_cliqueFinset (G : SimpleGraph A)
    (z : ↑(universalVertices G))
    (e : ↑((G.induce (↑(nonUniversalVertices G) : Set A)).edgeFinset)) :
    attachedEdgeTriangle (nonUniversalVertices G) (z : A) e ∈
      G.cliqueFinset 3 := by
  rw [SimpleGraph.mem_cliqueFinset_iff]
  apply attachedEdgeTriangle_isNClique
  · exact SimpleGraph.mem_edgeFinset.mp e.property
  · intro x _
    apply adj_of_mem_universalVertices G z.property
    intro h
    have hz0 := mem_universalVertices.mp z.property
    have hxpos := mem_nonUniversalVertices.mp x.property
    rw [← h, hz0] at hxpos
    omega

lemma d7UZZTriangle_mem_cliqueFinset (G : SimpleGraph A)
    (u : ↑(nonUniversalVertices G))
    (e : ↑((⊤ : SimpleGraph (↑(universalVertices G))).edgeFinset)) :
    attachedEdgeTriangle (universalVertices G) (u : A) e ∈
      G.cliqueFinset 3 := by
  rw [SimpleGraph.mem_cliqueFinset_iff]
  apply attachedEdgeTriangle_isNClique
  · rw [induce_universalVertices_eq_top]
    exact SimpleGraph.mem_edgeFinset.mp e.property
  · intro x _
    exact (adj_of_mem_universalVertices G x.property (by
      intro h
      have hx0 := mem_universalVertices.mp x.property
      have hupos := mem_nonUniversalVertices.mp u.property
      rw [← h, hx0] at hupos
      omega)).symm

lemma d7ZZZTriangle_mem_cliqueFinset (G : SimpleGraph A)
    (q : ↑((universalVertices G).powersetCard 3)) :
    (q : Finset A) ∈ G.cliqueFinset 3 := by
  rw [SimpleGraph.mem_cliqueFinset_iff, SimpleGraph.isNClique_iff]
  have hq := mem_powersetCard.mp q.property
  refine ⟨?_, hq.2⟩
  intro x hx y hy hxy
  exact adj_of_mem_universalVertices G (hq.1 hx) hxy

lemma card_universal_triangles_through_induced_edge
    (G : SimpleGraph A) (e : Sym2 (↑(universalVertices G)))
    (heND : ¬e.IsDiag) :
    (((universalVertices G).powersetCard 3).filter fun q ↦
      (inducedEmbedding (universalVertices G)).sym2Map e ∈ q.sym2).card =
      (universalVertices G).card - 2 := by
  let E : Sym2 A :=
    (inducedEmbedding (universalVertices G)).sym2Map e
  have hEND : ¬E.IsDiag := by
    exact (Sym2.isDiag_map (inducedEmbedding
      (universalVertices G)).injective).not.mpr heND
  have hEcard : E.toFinset.card = 2 :=
    Sym2.card_toFinset_of_not_isDiag E hEND
  have hEsub : E.toFinset ⊆ universalVertices G := by
    intro x hx
    have hx' : x ∈ E := Sym2.mem_toFinset.mp hx
    change x ∈ Sym2.map (inducedEmbedding (universalVertices G)) e at hx'
    rw [Sym2.mem_map] at hx'
    rcases hx' with ⟨a, _ha, rfl⟩
    exact a.property
  have hfilter :
      ((universalVertices G).powersetCard 3).filter (fun q ↦ E ∈ q.sym2) =
        ((universalVertices G).powersetCard 3).filter (E.toFinset ⊆ ·) := by
    ext q
    simp only [Finset.mem_filter]
    rw [Finset.mem_sym2_iff]
    simp [Finset.subset_iff]
  change (((universalVertices G).powersetCard 3).filter fun q ↦
    E ∈ q.sym2).card = _
  rw [hfilter, card_filter_powersetCard_subset E.toFinset
    (universalVertices G) 3 hEsub (by omega), hEcard]
  simp

/-- Correction triangles with two nonuniversal vertices and one universal
vertex, carrying the edge-dependent `beta` weights. -/
def d7UUZCorrection (G : SimpleGraph A) (P : D7SeparatedParameters G) :
    Finset A → ℝ :=
  fun t ↦ ∑ z : ↑(universalVertices G),
    weightedAttachedEdgeWeight (nonUniversalVertices G) (z : A)
      (G.induce (↑(nonUniversalVertices G) : Set A)).edgeFinset P.beta t

lemma d7UUZCorrection_nonneg (G : SimpleGraph A)
    (P : D7SeparatedParameters G) :
    ∀ t ∈ G.cliqueFinset 3, 0 ≤ d7UUZCorrection G P t := by
  intro t ht
  unfold d7UUZCorrection
  exact Finset.sum_nonneg fun z _ ↦
    weightedAttachedEdgeWeight_nonneg P.beta_nonneg t ht

lemma fractionalEdgeLoad_d7UUZCorrection (G : SimpleGraph A)
    (P : D7SeparatedParameters G) (p : Sym2 A) :
    fractionalEdgeLoad G (d7UUZCorrection G P) p =
      ∑ z : ↑(universalVertices G),
        ∑ e : ↑((G.induce
          (↑(nonUniversalVertices G) : Set A)).edgeFinset),
          if p ∈ (attachedEdgeTriangle (nonUniversalVertices G) (z : A) e).sym2
          then P.beta e else 0 := by
  unfold d7UUZCorrection
  rw [fractionalEdgeLoad_sum]
  apply Finset.sum_congr rfl
  intro z _
  exact fractionalEdgeLoad_weightedAttachedEdgeWeight
    (fun e he ↦ d7UUZTriangle_mem_cliqueFinset G z ⟨e, he⟩) p

lemma fractionalEdgeLoad_d7UUZCorrection_induced
    (G : SimpleGraph A) (P : D7SeparatedParameters G)
    (e : Sym2 (↑(nonUniversalVertices G)))
    (he : e ∈ (G.induce
      (↑(nonUniversalVertices G) : Set A)).edgeFinset) :
    fractionalEdgeLoad G (d7UUZCorrection G P)
        ((inducedEmbedding (nonUniversalVertices G)).sym2Map e) =
      ((universalVertices G).card : ℝ) * P.beta e := by
  unfold d7UUZCorrection
  rw [fractionalEdgeLoad_sum]
  have heND : ¬e.IsDiag :=
    (G.induce (↑(nonUniversalVertices G) : Set A)).not_isDiag_of_mem_edgeFinset he
  calc
    (∑ z : ↑(universalVertices G),
        fractionalEdgeLoad G
          (weightedAttachedEdgeWeight (nonUniversalVertices G) (z : A)
            (G.induce (↑(nonUniversalVertices G) : Set A)).edgeFinset
            P.beta)
          ((inducedEmbedding (nonUniversalVertices G)).sym2Map e)) =
        ∑ _z : ↑(universalVertices G), P.beta e := by
      apply Fintype.sum_congr
      intro z
      rw [fractionalEdgeLoad_weightedAttachedEdgeWeight_induced
        (G := G)
        (universalVertex_not_mem_nonUniversalVertices G z.property)
        (fun f hf ↦
          (G.induce (↑(nonUniversalVertices G) : Set A)).not_isDiag_of_mem_edgeFinset hf)
        (fun f hf ↦ d7UUZTriangle_mem_cliqueFinset G z ⟨f, hf⟩)
        heND,
        if_pos he]
    _ = ((universalVertices G).card : ℝ) * P.beta e := by simp

lemma fractionalEdgeLoad_d7UUZCorrection_mixed
    (G : SimpleGraph A) (P : D7SeparatedParameters G)
    (z : ↑(universalVertices G)) (u : ↑(nonUniversalVertices G)) :
    fractionalEdgeLoad G (d7UUZCorrection G P) s((z : A), (u : A)) =
      P.betaIncident u := by
  unfold d7UUZCorrection
  rw [fractionalEdgeLoad_sum]
  rw [Fintype.sum_eq_single z]
  · rw [fractionalEdgeLoad_weightedAttachedEdgeWeight_star
      (G := G) (universalVertex_not_mem_nonUniversalVertices G z.property)
      (fun f hf ↦ d7UUZTriangle_mem_cliqueFinset G z ⟨f, hf⟩) u]
    unfold D7SeparatedParameters.betaIncident
    apply Finset.sum_congr
    · apply Finset.filter_congr
      intro e he
      simp only [Sym2.mem_toFinset]
    · intro e he
      rfl
  · intro z' hz'
    rw [fractionalEdgeLoad_weightedAttachedEdgeWeight
      (fun f hf ↦ d7UUZTriangle_mem_cliqueFinset G z' ⟨f, hf⟩)]
    apply Fintype.sum_eq_zero
    intro e
    rw [if_neg]
    exact starEdge_not_mem_attachedEdgeTriangle_of_ne_attachment
      (universalVertex_not_mem_nonUniversalVertices G z.property)
      (universalVertex_not_mem_nonUniversalVertices G z'.property)
      (fun h ↦ hz' (Subtype.ext h.symm)) u e

lemma fractionalEdgeLoad_d7UUZCorrection_universal
    (G : SimpleGraph A) (P : D7SeparatedParameters G)
    (e : Sym2 (↑(universalVertices G))) (heND : ¬e.IsDiag) :
    fractionalEdgeLoad G (d7UUZCorrection G P)
        ((inducedEmbedding (universalVertices G)).sym2Map e) = 0 := by
  induction e using Sym2.inductionOn with
  | hf z y =>
      simp only [Sym2.mk_isDiag_iff] at heND
      rw [fractionalEdgeLoad_d7UUZCorrection]
      apply Fintype.sum_eq_zero
      intro v
      apply Fintype.sum_eq_zero
      intro f
      rw [if_neg]
      exact outsidePair_not_mem_attachedEdgeTriangle
        (universalVertex_not_mem_nonUniversalVertices G z.property)
        (universalVertex_not_mem_nonUniversalVertices G y.property)
        (fun h ↦ heND (Subtype.ext h)) f

/-- Correction triangles with one nonuniversal and two universal vertices. -/
def d7UZZCorrection (G : SimpleGraph A) (P : D7SeparatedParameters G) :
    Finset A → ℝ :=
  fun t ↦ ∑ u : ↑(nonUniversalVertices G),
    weightedAttachedEdgeWeight (universalVertices G) (u : A)
      ((⊤ : SimpleGraph (↑(universalVertices G))).edgeFinset)
      (fun _ ↦ P.largeMixedCoefficient u) t

lemma d7UZZCorrection_nonneg (G : SimpleGraph A)
    (P : D7SeparatedParameters G) (hm : 4 ≤ (universalVertices G).card) :
    ∀ t ∈ G.cliqueFinset 3, 0 ≤ d7UZZCorrection G P t := by
  intro t ht
  unfold d7UZZCorrection
  exact Finset.sum_nonneg fun u _ ↦
    weightedAttachedEdgeWeight_nonneg
      (fun _ _ ↦ P.largeMixedCoefficient_nonneg hm u) t ht

lemma fractionalEdgeLoad_d7UZZCorrection (G : SimpleGraph A)
    (P : D7SeparatedParameters G) (p : Sym2 A) :
    fractionalEdgeLoad G (d7UZZCorrection G P) p =
      ∑ u : ↑(nonUniversalVertices G),
        ∑ e : ↑((⊤ : SimpleGraph
          (↑(universalVertices G))).edgeFinset),
          if p ∈ (attachedEdgeTriangle (universalVertices G) (u : A) e).sym2
          then P.largeMixedCoefficient u else 0 := by
  unfold d7UZZCorrection
  rw [fractionalEdgeLoad_sum]
  apply Finset.sum_congr rfl
  intro u _
  exact fractionalEdgeLoad_weightedAttachedEdgeWeight
    (fun e he ↦ d7UZZTriangle_mem_cliqueFinset G u ⟨e, he⟩) p

lemma fractionalEdgeLoad_d7UZZCorrection_induced
    (G : SimpleGraph A) (P : D7SeparatedParameters G)
    (e : Sym2 (↑(universalVertices G)))
    (he : e ∈ (⊤ : SimpleGraph (↑(universalVertices G))).edgeFinset) :
    fractionalEdgeLoad G (d7UZZCorrection G P)
        ((inducedEmbedding (universalVertices G)).sym2Map e) =
      ∑ u : ↑(nonUniversalVertices G), P.largeMixedCoefficient u := by
  unfold d7UZZCorrection
  rw [fractionalEdgeLoad_sum]
  have heND : ¬e.IsDiag :=
    (⊤ : SimpleGraph (↑(universalVertices G))).not_isDiag_of_mem_edgeFinset he
  apply Fintype.sum_congr
  intro u
  rw [fractionalEdgeLoad_weightedAttachedEdgeWeight_induced
    (G := G)
    (nonUniversalVertex_not_mem_universalVertices G u.property)
    (fun f hf ↦
      (⊤ : SimpleGraph (↑(universalVertices G))).not_isDiag_of_mem_edgeFinset hf)
    (fun f hf ↦ d7UZZTriangle_mem_cliqueFinset G u ⟨f, hf⟩)
    heND,
    if_pos he]

lemma fractionalEdgeLoad_d7UZZCorrection_mixed
    (G : SimpleGraph A) (P : D7SeparatedParameters G)
    (u : ↑(nonUniversalVertices G)) (z : ↑(universalVertices G)) :
    fractionalEdgeLoad G (d7UZZCorrection G P) s((u : A), (z : A)) =
      (((universalVertices G).card : ℝ) - 1) *
        P.largeMixedCoefficient u := by
  unfold d7UZZCorrection
  rw [fractionalEdgeLoad_sum]
  rw [Fintype.sum_eq_single u]
  · rw [fractionalEdgeLoad_weightedAttachedEdgeWeight_star
      (G := G) (nonUniversalVertex_not_mem_universalVertices G u.property)
      (fun f hf ↦ d7UZZTriangle_mem_cliqueFinset G u ⟨f, hf⟩) z]
    have hm : 1 ≤ (universalVertices G).card :=
      Finset.one_le_card.mpr ⟨z, z.property⟩
    rw [Finset.sum_const, card_top_edgeFinset_filter_mem]
    simp only [nsmul_eq_mul]
    rw [Fintype.card_coe, Nat.cast_sub hm, Nat.cast_one]
  · intro u' hu'
    rw [fractionalEdgeLoad_weightedAttachedEdgeWeight
      (fun f hf ↦ d7UZZTriangle_mem_cliqueFinset G u' ⟨f, hf⟩)]
    apply Fintype.sum_eq_zero
    intro e
    rw [if_neg]
    exact starEdge_not_mem_attachedEdgeTriangle_of_ne_attachment
      (nonUniversalVertex_not_mem_universalVertices G u.property)
      (nonUniversalVertex_not_mem_universalVertices G u'.property)
      (fun h ↦ hu' (Subtype.ext h.symm)) z e

lemma fractionalEdgeLoad_d7UZZCorrection_nonUniversal
    (G : SimpleGraph A) (P : D7SeparatedParameters G)
    (e : Sym2 (↑(nonUniversalVertices G))) (heND : ¬e.IsDiag) :
    fractionalEdgeLoad G (d7UZZCorrection G P)
        ((inducedEmbedding (nonUniversalVertices G)).sym2Map e) = 0 := by
  induction e using Sym2.inductionOn with
  | hf u v =>
      simp only [Sym2.mk_isDiag_iff] at heND
      rw [fractionalEdgeLoad_d7UZZCorrection]
      apply Fintype.sum_eq_zero
      intro x
      apply Fintype.sum_eq_zero
      intro f
      rw [if_neg]
      exact outsidePair_not_mem_attachedEdgeTriangle
        (nonUniversalVertex_not_mem_universalVertices G u.property)
        (nonUniversalVertex_not_mem_universalVertices G v.property)
        (fun h ↦ heND (Subtype.ext h)) f

/-- Correction triangles entirely inside the universal set. -/
def d7ZZZCorrection (G : SimpleGraph A) (P : D7SeparatedParameters G) :
    Finset A → ℝ :=
  fun t ↦ ∑ q : ↑((universalVertices G).powersetCard 3),
    singleTriangleWeight q P.largeUniversalCoefficient t

lemma d7ZZZCorrection_nonneg (G : SimpleGraph A)
    (P : D7SeparatedParameters G)
    (hcoeff : 0 ≤ P.largeUniversalCoefficient) :
    ∀ t ∈ G.cliqueFinset 3, 0 ≤ d7ZZZCorrection G P t := by
  intro t _
  unfold d7ZZZCorrection singleTriangleWeight
  exact Finset.sum_nonneg fun q _ ↦ by
    split_ifs
    · exact hcoeff
    · exact le_rfl

lemma fractionalEdgeLoad_d7ZZZCorrection (G : SimpleGraph A)
    (P : D7SeparatedParameters G) (p : Sym2 A) :
    fractionalEdgeLoad G (d7ZZZCorrection G P) p =
      ∑ q : ↑((universalVertices G).powersetCard 3),
        if p ∈ (q : Finset A).sym2 then P.largeUniversalCoefficient else 0 := by
  unfold d7ZZZCorrection
  rw [fractionalEdgeLoad_sum]
  apply Finset.sum_congr rfl
  intro q _
  exact fractionalEdgeLoad_singleTriangle
    (d7ZZZTriangle_mem_cliqueFinset G q) P.largeUniversalCoefficient p

lemma fractionalEdgeLoad_d7ZZZCorrection_induced
    (G : SimpleGraph A) (P : D7SeparatedParameters G)
    (e : Sym2 (↑(universalVertices G))) (heND : ¬e.IsDiag) :
    fractionalEdgeLoad G (d7ZZZCorrection G P)
        ((inducedEmbedding (universalVertices G)).sym2Map e) =
      (((universalVertices G).card : ℝ) - 2) *
        P.largeUniversalCoefficient := by
  rw [fractionalEdgeLoad_d7ZZZCorrection]
  calc
    (∑ q : ↑((universalVertices G).powersetCard 3),
        if (inducedEmbedding (universalVertices G)).sym2Map e ∈
          (q : Finset A).sym2
        then P.largeUniversalCoefficient else 0) =
        ∑ q ∈ (universalVertices G).powersetCard 3,
          if (inducedEmbedding (universalVertices G)).sym2Map e ∈ q.sym2
          then P.largeUniversalCoefficient else 0 :=
      (Finset.sum_subtype ((universalVertices G).powersetCard 3)
        (fun _ ↦ Iff.rfl)
        (fun q ↦ if (inducedEmbedding
          (universalVertices G)).sym2Map e ∈ q.sym2
          then P.largeUniversalCoefficient else 0)).symm
    _ = ∑ q ∈ ((universalVertices G).powersetCard 3).filter
          (fun q ↦ (inducedEmbedding
            (universalVertices G)).sym2Map e ∈ q.sym2),
          P.largeUniversalCoefficient := by rw [Finset.sum_filter]
    _ = (((universalVertices G).card : ℝ) - 2) *
          P.largeUniversalCoefficient := by
      rw [Finset.sum_const,
        card_universal_triangles_through_induced_edge G e heND]
      simp only [nsmul_eq_mul]
      have hm : 2 ≤ (universalVertices G).card := by
        have hcard := Sym2.card_toFinset_of_not_isDiag e heND
        have hle := Finset.card_le_card (Finset.subset_univ e.toFinset)
        rw [hcard] at hle
        simpa only [Finset.card_univ, Fintype.card_coe] using hle
      rw [Nat.cast_sub hm, Nat.cast_ofNat]

lemma fractionalEdgeLoad_d7ZZZCorrection_nonUniversal_left
    (G : SimpleGraph A) (P : D7SeparatedParameters G)
    (u : ↑(nonUniversalVertices G)) (x : A) :
    fractionalEdgeLoad G (d7ZZZCorrection G P) s((u : A), x) = 0 := by
  rw [fractionalEdgeLoad_d7ZZZCorrection]
  apply Fintype.sum_eq_zero
  intro q
  rw [if_neg]
  have hqsub := (Finset.mem_powersetCard.mp q.property).1
  have huq : (u : A) ∉ (q : Finset A) := by
    intro hu
    exact nonUniversalVertex_not_mem_universalVertices G u.property (hqsub hu)
  simpa only [Finset.mk_mem_sym2_iff, not_and_or] using
    (Or.inl huq : (u : A) ∉ (q : Finset A) ∨ x ∉ (q : Finset A))

lemma fractionalEdgeLoad_d7ZZZCorrection_nonUniversal
    (G : SimpleGraph A) (P : D7SeparatedParameters G)
    (e : Sym2 (↑(nonUniversalVertices G))) :
    fractionalEdgeLoad G (d7ZZZCorrection G P)
        ((inducedEmbedding (nonUniversalVertices G)).sym2Map e) = 0 := by
  induction e using Sym2.inductionOn with
  | hf u v =>
      exact fractionalEdgeLoad_d7ZZZCorrection_nonUniversal_left G P u v

/-- The complete explicit large-`m` correction from case D7. -/
def d7LargeCorrection (G : SimpleGraph A) (P : D7SeparatedParameters G) :
    Finset A → ℝ :=
  fun t ↦ d7UUZCorrection G P t + d7UZZCorrection G P t +
    d7ZZZCorrection G P t

lemma d7LargeCorrection_nonneg (G : SimpleGraph A)
    (P : D7SeparatedParameters G) (hn : 14 ≤ Fintype.card A)
    (hm : 4 ≤ (universalVertices G).card)
    (hlarge : Fintype.card A - 7 ≤ (universalVertices G).card) :
    ∀ t ∈ G.cliqueFinset 3, 0 ≤ d7LargeCorrection G P t := by
  intro t ht
  unfold d7LargeCorrection
  exact add_nonneg (add_nonneg (d7UUZCorrection_nonneg G P t ht)
    (d7UZZCorrection_nonneg G P hm t ht))
    (d7ZZZCorrection_nonneg G P
      (P.largeUniversalCoefficient_nonneg hn hm hlarge) t ht)

lemma fractionalEdgeLoad_d7LargeCorrection (G : SimpleGraph A)
    (P : D7SeparatedParameters G) (p : Sym2 A) :
    fractionalEdgeLoad G (d7LargeCorrection G P) p =
      fractionalEdgeLoad G (d7UUZCorrection G P) p +
        fractionalEdgeLoad G (d7UZZCorrection G P) p +
        fractionalEdgeLoad G (d7ZZZCorrection G P) p := by
  unfold d7LargeCorrection
  rw [fractionalEdgeLoad_add, fractionalEdgeLoad_add]

lemma fractionalEdgeLoad_d7LargeCorrection_nonUniversal
    (G : SimpleGraph A) (P : D7SeparatedParameters G)
    (e : Sym2 (↑(nonUniversalVertices G)))
    (he : e ∈ (G.induce
      (↑(nonUniversalVertices G) : Set A)).edgeFinset) :
    fractionalEdgeLoad G (d7LargeCorrection G P)
        ((inducedEmbedding (nonUniversalVertices G)).sym2Map e) =
      ((universalVertices G).card : ℝ) * P.beta e := by
  rw [fractionalEdgeLoad_d7LargeCorrection,
    fractionalEdgeLoad_d7UUZCorrection_induced G P e he,
    fractionalEdgeLoad_d7UZZCorrection_nonUniversal G P e
      ((G.induce (↑(nonUniversalVertices G) : Set A)).not_isDiag_of_mem_edgeFinset he),
    fractionalEdgeLoad_d7ZZZCorrection_nonUniversal G P e]
  ring

lemma fractionalEdgeLoad_d7LargeCorrection_mixed
    (G : SimpleGraph A) (P : D7SeparatedParameters G)
    (hm : 4 ≤ (universalVertices G).card)
    (u : ↑(nonUniversalVertices G)) (z : ↑(universalVertices G)) :
    fractionalEdgeLoad G (d7LargeCorrection G P) s((u : A), (z : A)) =
      1 + (((universalVertices G).card : ℝ) - 1) * P.alpha u := by
  rw [fractionalEdgeLoad_d7LargeCorrection]
  have hUUZ := fractionalEdgeLoad_d7UUZCorrection_mixed G P z u
  rw [Sym2.eq_swap] at hUUZ
  rw [hUUZ, fractionalEdgeLoad_d7UZZCorrection_mixed G P u z,
    fractionalEdgeLoad_d7ZZZCorrection_nonUniversal_left G P u z]
  unfold D7SeparatedParameters.largeMixedCoefficient
  have hden : ((universalVertices G).card : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < ((universalVertices G).card : ℝ) := by
      exact_mod_cast (by omega : 1 < (universalVertices G).card)
    linarith
  field_simp [hden]
  ring

lemma fractionalEdgeLoad_d7LargeCorrection_universal
    (G : SimpleGraph A) (P : D7SeparatedParameters G)
    (e : Sym2 (↑(universalVertices G)))
    (he : e ∈ (⊤ : SimpleGraph (↑(universalVertices G))).edgeFinset) :
    fractionalEdgeLoad G (d7LargeCorrection G P)
        ((inducedEmbedding (universalVertices G)).sym2Map e) =
      (∑ u : ↑(nonUniversalVertices G), P.largeMixedCoefficient u) +
        (((universalVertices G).card : ℝ) - 2) *
          P.largeUniversalCoefficient := by
  have heND : ¬e.IsDiag :=
    (⊤ : SimpleGraph (↑(universalVertices G))).not_isDiag_of_mem_edgeFinset he
  rw [fractionalEdgeLoad_d7LargeCorrection,
    fractionalEdgeLoad_d7UUZCorrection_universal G P e heND,
    fractionalEdgeLoad_d7UZZCorrection_induced G P e he,
    fractionalEdgeLoad_d7ZZZCorrection_induced G P e heND]
  ring

lemma sum_ite_mem_sym2_eq_two_mul {B : Type} [Fintype B]
    [DecidableEq B] (e : Sym2 B) (heND : ¬e.IsDiag) (c : ℝ) :
    (∑ x : B, if x ∈ e then c else 0) = 2 * c := by
  change (∑ x ∈ (Finset.univ : Finset B),
    if x ∈ e then c else 0) = _
  rw [← Finset.sum_filter]
  have hfilter : (Finset.univ : Finset B).filter (fun x ↦ x ∈ e) =
      e.toFinset := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Sym2.mem_toFinset]
  rw [hfilter, Finset.sum_const,
    Sym2.card_toFinset_of_not_isDiag e heND]
  norm_num

lemma D7SeparatedParameters.sum_betaIncident_eq_two_betaMass
    {G : SimpleGraph A} (P : D7SeparatedParameters G) :
    (∑ u : ↑(nonUniversalVertices G), P.betaIncident u) =
      2 * P.betaMass := by
  unfold D7SeparatedParameters.betaIncident D7SeparatedParameters.betaMass
  calc
    (∑ u : ↑(nonUniversalVertices G),
        ∑ e ∈ (G.induce
          (↑(nonUniversalVertices G) : Set A)).edgeFinset with
          u ∈ e.toFinset, P.beta e) =
        ∑ u : ↑(nonUniversalVertices G),
          ∑ e ∈ (G.induce
            (↑(nonUniversalVertices G) : Set A)).edgeFinset,
            if u ∈ e then P.beta e else 0 := by
      apply Fintype.sum_congr
      intro u
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro e he
      simp only [Sym2.mem_toFinset]
    _ = ∑ e ∈ (G.induce
          (↑(nonUniversalVertices G) : Set A)).edgeFinset,
          ∑ u : ↑(nonUniversalVertices G),
            if u ∈ e then P.beta e else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ e ∈ (G.induce
          (↑(nonUniversalVertices G) : Set A)).edgeFinset,
          2 * P.beta e := by
      apply Finset.sum_congr rfl
      intro e he
      exact sum_ite_mem_sym2_eq_two_mul e
        ((G.induce (↑(nonUniversalVertices G) : Set A)).not_isDiag_of_mem_edgeFinset he)
        (P.beta e)
    _ = 2 * ∑ e ∈ (G.induce
          (↑(nonUniversalVertices G) : Set A)).edgeFinset,
          P.beta e := by
      rw [Finset.mul_sum]

lemma D7SeparatedParameters.sum_largeMixedCoefficient
    {G : SimpleGraph A} (P : D7SeparatedParameters G) :
    (∑ u : ↑(nonUniversalVertices G), P.largeMixedCoefficient u) =
      (((Fintype.card A : ℝ) - (universalVertices G).card) +
        P.alphaMass - 2 * P.betaMass) /
        (((universalVertices G).card : ℝ) - 1) := by
  unfold D7SeparatedParameters.largeMixedCoefficient
  rw [← Finset.sum_div]
  congr 1
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  simp only [Finset.sum_const, nsmul_eq_mul, Finset.mul_sum]
  rw [P.sum_betaIncident_eq_two_betaMass]
  unfold D7SeparatedParameters.alphaMass
  have hpart := card_nonUniversalVertices_add_card_universalVertices G
  have hpartR : ((nonUniversalVertices G).card : ℝ) +
      ((universalVertices G).card : ℝ) = (Fintype.card A : ℝ) := by
    exact_mod_cast hpart
  simp only [Finset.card_univ, Fintype.card_coe]
  rw [← Finset.mul_sum]
  ring_nf at ⊢
  linarith

lemma fractionalEdgeLoad_d7LargeCorrection_universal_simplified
    (G : SimpleGraph A) (P : D7SeparatedParameters G)
    (hm : 4 ≤ (universalVertices G).card)
    (e : Sym2 (↑(universalVertices G)))
    (he : e ∈ (⊤ : SimpleGraph (↑(universalVertices G))).edgeFinset) :
    fractionalEdgeLoad G (d7LargeCorrection G P)
        ((inducedEmbedding (universalVertices G)).sym2Map e) =
      2 + (((universalVertices G).card : ℝ) - 2) * P.gamma := by
  rw [fractionalEdgeLoad_d7LargeCorrection_universal G P e he,
    P.sum_largeMixedCoefficient]
  unfold D7SeparatedParameters.largeUniversalCoefficient
  have hden₁ : ((universalVertices G).card : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < ((universalVertices G).card : ℝ) := by
      exact_mod_cast (by omega : 1 < (universalVertices G).card)
    linarith
  have hden₂ : ((universalVertices G).card : ℝ) - 2 ≠ 0 := by
    have : (2 : ℝ) < ((universalVertices G).card : ℝ) := by
      exact_mod_cast (by omega : 2 < (universalVertices G).card)
    linarith
  field_simp [hden₁, hden₂]
  ring

end

end Erdos76
