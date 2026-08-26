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
import ErdosProblems.Erdos76.AlmostCompleteD7Small

/-!
# Case D8 of the almost-complete strong induction

The first operation in case D8 is to delete a universal vertex and add one
fixed missing edge.  This file isolates that operation and the subsequent
deletion of all triangles using the added edge.  Keeping these facts separate
from the Hall redistribution makes the two-unit split in equations (5.12)--
(5.14) explicit.
-/

open Finset
open scoped BigOperators

namespace Erdos76

noncomputable section

attribute [local instance] Classical.propDecidable

variable {A : Type} [Fintype A] [DecidableEq A]

/-- Add the unordered pair `xy` to a simple graph. -/
def addPair (G : SimpleGraph A) (x y : A) : SimpleGraph A :=
  G ⊔ SimpleGraph.fromEdgeSet {s(x, y)}

@[simp] lemma addPair_adj (G : SimpleGraph A) (x y u v : A) :
    (addPair G x y).Adj u v ↔
      G.Adj u v ∨ (s(u, v) = s(x, y) ∧ u ≠ v) := by
  simp [addPair, SimpleGraph.fromEdgeSet_adj]

lemma addPair_comm (G : SimpleGraph A) (x y : A) :
    addPair G x y = addPair G y x := by
  unfold addPair
  rw [Sym2.eq_swap]

lemma edgeFinset_addPair {G : SimpleGraph A} {x y : A}
    (hxy : x ≠ y) :
    (addPair G x y).edgeFinset = insert s(x, y) G.edgeFinset := by
  ext e
  induction e using Sym2.inductionOn with
  | _ u v =>
    simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
      addPair_adj, mem_insert]
    rw [Sym2.eq_iff]
    constructor
    · rintro (huv | ⟨heq, _⟩)
      · exact Or.inr huv
      · exact Or.inl heq
    · rintro (heq | huv)
      · refine Or.inr ⟨heq, ?_⟩
        rcases heq with h | h
        · simpa [h.1, h.2] using hxy
        · simpa [h.1, h.2] using hxy.symm
      · exact Or.inl huv

/-- Adding one genuinely absent nondiagonal pair removes exactly one missing
edge. -/
lemma missingEdgeCount_addPair {G : SimpleGraph A} {x y : A}
    (hxy : x ≠ y) (hmissing : ¬ G.Adj x y) :
    missingEdgeCount (addPair G x y) = missingEdgeCount G - 1 := by
  classical
  have hedge : s(x, y) ∈ Gᶜ.edgeFinset := by
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    exact ⟨hxy, hmissing⟩
  have hfinset : (addPair G x y)ᶜ.edgeFinset =
      Gᶜ.edgeFinset.erase s(x, y) := by
    ext e
    induction e using Sym2.inductionOn with
    | _ u v =>
      simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
        SimpleGraph.compl_adj, addPair_adj, mem_erase]
      rw [Sym2.eq_iff]
      constructor
      · rintro ⟨huv, hnot⟩
        refine ⟨?_, huv, ?_⟩
        · intro heq
          exact hnot (Or.inr ⟨Sym2.eq_iff.mp heq, huv⟩)
        · intro hadj
          exact hnot (Or.inl hadj)
      · rintro ⟨hne, huv, hnot⟩
        refine ⟨huv, ?_⟩
        rintro (hadj | ⟨heq, _⟩)
        · exact hnot hadj
        · exact hne (Sym2.eq_iff.mpr heq)
  unfold missingEdgeCount
  rw [hfinset, card_erase_of_mem hedge]

/-- Delete `z`, then add the fixed pair `xy` on the deletion subtype. -/
def d8AugmentedDeletedGraph (G : SimpleGraph A) (z x y : A)
    (hx : x ≠ z) (hy : y ≠ z) :
    SimpleGraph (↑(d7DeletedFinset (A := A) z)) :=
  addPair (d7DeletedGraph G z)
    (d7DeletedVertex z x hx) (d7DeletedVertex z y hy)

lemma d8AugmentedDeletedGraph_missingEdgeCount
    (G : SimpleGraph A) (z x y : A)
    (hx : x ≠ z) (hy : y ≠ z) (hxy : x ≠ y)
    (hmissing : ¬ G.Adj x y) :
    missingEdgeCount (d8AugmentedDeletedGraph G z x y hx hy) =
      missingEdgeCount G - Gᶜ.degree z - 1 := by
  rw [d8AugmentedDeletedGraph, missingEdgeCount_addPair]
  · change missingEdgeCount
        (G.induce (↑((Finset.univ : Finset A).erase z) : Set A)) - 1 = _
    rw [missingEdgeCount_induce_univ_erase]
  · intro hsub
    apply hxy
    exact congrArg Subtype.val hsub
  · simpa [d7DeletedGraph, d7DeletedVertex] using hmissing

/-- At a universal deletion in D8, adding a missing edge puts the auxiliary
graph exactly in the defect-four range of the `(n-1)` induction hypothesis. -/
theorem d8AugmentedDeletedGraph_hasStrongFractionalPacking {n : ℕ}
    (hcard : Fintype.card A = n) (hn : 14 ≤ n)
    (G : SimpleGraph A) (hexact : missingEdgeCount G = n)
    (z : ↑(universalVertices G)) {x y : A}
    (hx : x ≠ (z : A)) (hy : y ≠ (z : A)) (hxy : Gᶜ.Adj x y)
    (hstrong : AlmostCompleteStrongAt (n - 1)) :
    HasStrongFractionalPacking
      (d8AugmentedDeletedGraph G (z : A) x y hx hy) 4 := by
  classical
  have horder : Fintype.card (↑(d7DeletedFinset (A := A) (z : A))) =
      n - 1 := by
    unfold d7DeletedFinset
    rw [card_univ_erase, hcard]
  have hz0 : Gᶜ.degree (z : A) = 0 := mem_universalVertices.mp z.property
  have hmissing : missingEdgeCount
      (d8AugmentedDeletedGraph G (z : A) x y hx hy) = n - 1 := by
    rw [d8AugmentedDeletedGraph_missingEdgeCount G (z : A) x y hx hy
      hxy.ne hxy.2, hexact, hz0]
    omega
  have hbound : missingEdgeCount
      (d8AugmentedDeletedGraph G (z : A) x y hx hy) ≤
        n - 1 - 4 + 4 := by
    rw [hmissing]
    omega
  exact hstrong _ horder 4 (by omega)
      (d8AugmentedDeletedGraph G (z : A) x y hx hy) hbound

/-! ## Removing every triangle containing the added pair -/

/-- Keep the part of a triangle weighting supported away from `e`. -/
def stripEdgeTriangles (e : Sym2 A) (w : Finset A → ℝ) : Finset A → ℝ :=
  fun t ↦ if e ∈ t.sym2 then 0 else w t

/-- The complementary part, supported on triangles containing `e`. -/
def edgeTrianglesPart (e : Sym2 A) (w : Finset A → ℝ) : Finset A → ℝ :=
  fun t ↦ if e ∈ t.sym2 then w t else 0

lemma relabelWeight_edgeTrianglesPart {B : Type} [Fintype B]
    [DecidableEq B] (q : A ≃ B) (e : Sym2 A) (w : Finset A → ℝ) :
    relabelWeight q (edgeTrianglesPart e w) =
      edgeTrianglesPart (q.toEmbedding.sym2Map e) (relabelWeight q w) := by
  funext t
  unfold relabelWeight edgeTrianglesPart
  have hleft (p : Sym2 A) :
      q.symm.toEmbedding.sym2Map (q.toEmbedding.sym2Map p) = p := by
    induction p using Sym2.inductionOn with
    | hf x y => simp
  have hmem : q.toEmbedding.sym2Map e ∈ t.sym2 ↔
      e ∈ (t.map q.symm.toEmbedding).sym2 := by
    rw [Finset.sym2_map]
    constructor
    · intro he
      rw [Finset.mem_map]
      refine ⟨q.toEmbedding.sym2Map e, he, ?_⟩
      exact hleft e
    · intro he
      obtain ⟨p, hp, hpe⟩ := Finset.mem_map.mp he
      have hpEq : p = q.toEmbedding.sym2Map e := by
        apply q.symm.toEmbedding.sym2Map.injective
        rw [hpe, hleft]
      rwa [← hpEq]
  rw [if_congr hmem.symm rfl rfl]

lemma stripEdgeTriangles_add_edgeTrianglesPart
    (e : Sym2 A) (w : Finset A → ℝ) :
    (fun t ↦ stripEdgeTriangles e w t + edgeTrianglesPart e w t) = w := by
  funext t
  by_cases ht : e ∈ t.sym2 <;>
    simp [stripEdgeTriangles, edgeTrianglesPart, ht]

lemma fractionalEdgeLoad_strip_add_part
    (G : SimpleGraph A) (e p : Sym2 A) (w : Finset A → ℝ) :
    fractionalEdgeLoad G (stripEdgeTriangles e w) p +
        fractionalEdgeLoad G (edgeTrianglesPart e w) p =
      fractionalEdgeLoad G w p := by
  rw [← fractionalEdgeLoad_add]
  exact congrArg (fun v ↦ fractionalEdgeLoad G v p)
    (stripEdgeTriangles_add_edgeTrianglesPart e w)

lemma stripEdgeTriangles_nonneg {G : SimpleGraph A} {e : Sym2 A}
    {w : Finset A → ℝ} (hw : ∀ t ∈ G.cliqueFinset 3, 0 ≤ w t) :
    ∀ t ∈ G.cliqueFinset 3, 0 ≤ stripEdgeTriangles e w t := by
  intro t ht
  simp only [stripEdgeTriangles]
  split_ifs
  · exact le_rfl
  · exact hw t ht

lemma edgeTrianglesPart_nonneg {G : SimpleGraph A} {e : Sym2 A}
    {w : Finset A → ℝ} (hw : ∀ t ∈ G.cliqueFinset 3, 0 ≤ w t) :
    ∀ t ∈ G.cliqueFinset 3, 0 ≤ edgeTrianglesPart e w t := by
  intro t ht
  simp only [edgeTrianglesPart]
  split_ifs
  · exact hw t ht
  · exact le_rfl

def fixedPairEmbedding (u : A) : A ↪ Sym2 A where
  toFun v := s(u, v)
  inj' := by
    intro v w h
    rw [Sym2.eq_iff] at h
    rcases h with h | h
    · exact h.2
    · exact h.2.trans h.1

lemma sym2_filter_mem_fixed_eq_map_erase (t : Finset A) {u : A}
    (hu : u ∈ t) :
    t.sym2.filter (fun e ↦ u ∈ e ∧ ¬e.IsDiag) =
      (t.erase u).map (fixedPairEmbedding u) := by
  ext e
  simp only [Finset.mem_filter, Finset.mem_map, Finset.mem_erase]
  constructor
  · rintro ⟨he, hue, hND⟩
    induction e using Sym2.inductionOn with
    | hf a b =>
        have hab := Finset.mk_mem_sym2_iff.mp he
        simp only [Sym2.mem_iff] at hue
        rcases hue with rfl | rfl
        · refine ⟨b, ⟨?_, hab.2⟩, rfl⟩
          intro h
          subst b
          exact hND (by simp)
        · refine ⟨a, ⟨?_, hab.1⟩, Sym2.eq_swap⟩
          intro h
          subst a
          exact hND (by simp)
  · rintro ⟨v, ⟨hvu, hvt⟩, rfl⟩
    refine ⟨Finset.mk_mem_sym2_iff.mpr ⟨hu, hvt⟩,
      Sym2.mem_mk_left _ _, ?_⟩
    change ¬s(u, v).IsDiag
    simpa only [Sym2.mk_isDiag_iff] using hvu.symm

lemma card_sym2_filter_mem_fixed (t : Finset A) {u : A}
    (hu : u ∈ t) :
    (t.sym2.filter (fun e ↦ u ∈ e ∧ ¬e.IsDiag)).card = t.card - 1 := by
  rw [sym2_filter_mem_fixed_eq_map_erase t hu, Finset.card_map,
    Finset.card_erase_of_mem hu]

def oldIncidentRemovedLoad (G : SimpleGraph A) (x y : A)
    (w : Finset A → ℝ) (u : A) : ℝ :=
  ∑ p ∈ G.edgeFinset.filter (fun p ↦ u ∈ p),
    fractionalEdgeLoad (addPair G x y)
      (edgeTrianglesPart s(x, y) w) p

lemma oldIncidentRemovedLoad_eq_sum (G : SimpleGraph A) (x y : A)
    (w : Finset A → ℝ) (u : A) :
    oldIncidentRemovedLoad G x y w u =
      ∑ t ∈ (addPair G x y).cliqueFinset 3,
        (((G.edgeFinset.filter (fun p ↦ u ∈ p)).filter
          (fun p ↦ p ∈ t.sym2)).card : ℝ) * edgeTrianglesPart s(x, y) w t := by
  unfold oldIncidentRemovedLoad
  have hload (p : Sym2 A) :
      fractionalEdgeLoad (addPair G x y)
          (edgeTrianglesPart s(x, y) w) p =
        ∑ t ∈ (addPair G x y).cliqueFinset 3,
          if p ∈ t.sym2 then edgeTrianglesPart s(x, y) w t else 0 := by
    unfold fractionalEdgeLoad
    rw [Finset.sum_filter]
  simp_rw [hload]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t ht
  rw [show (∑ p ∈ G.edgeFinset.filter (fun p ↦ u ∈ p),
      if p ∈ t.sym2 then edgeTrianglesPart s(x, y) w t else 0) =
      ∑ _p ∈ (G.edgeFinset.filter (fun p ↦ u ∈ p)).filter
        (fun p ↦ p ∈ t.sym2), edgeTrianglesPart s(x, y) w t by
        simp_rw [Finset.sum_filter]]
  rw [Finset.sum_const, nsmul_eq_mul]

lemma card_oldIncidentEdges_in_triangle_le_two
    (G : SimpleGraph A) (u : A) (t : Finset A)
    (ht : t.card = 3) :
    ((G.edgeFinset.filter (fun p ↦ u ∈ p)).filter
      (fun p ↦ p ∈ t.sym2)).card ≤ 2 := by
  by_cases hu : u ∈ t
  · calc
      ((G.edgeFinset.filter (fun p ↦ u ∈ p)).filter
          (fun p ↦ p ∈ t.sym2)).card ≤
          (t.sym2.filter (fun e ↦ u ∈ e ∧ ¬e.IsDiag)).card := by
        apply Finset.card_le_card
        intro p hp
        simp only [Finset.mem_filter] at hp ⊢
        exact ⟨hp.2, hp.1.2,
          G.not_isDiag_of_mem_edgeFinset hp.1.1⟩
      _ = t.card - 1 := card_sym2_filter_mem_fixed t hu
      _ = 2 := by omega
  · have hempty :
        (G.edgeFinset.filter (fun p ↦ u ∈ p)).filter
          (fun p ↦ p ∈ t.sym2) = ∅ := by
      ext p
      simp only [Finset.mem_filter, Finset.notMem_empty, iff_false]
      intro hp
      have hsub := Finset.mem_sym2_iff.mp hp.2 u hp.1.2
      exact hu hsub
    rw [hempty]
    simp

lemma card_oldIncidentEdges_in_triangle_le_one_of_added_endpoint
    (G : SimpleGraph A) {x y u : A} (hxy : x ≠ y)
    (hmissing : ¬G.Adj x y) (hu : u ∈ s(x, y))
    (t : Finset A) (htcard : t.card = 3) (htxy : s(x, y) ∈ t.sym2) :
    ((G.edgeFinset.filter (fun p ↦ u ∈ p)).filter
      (fun p ↦ p ∈ t.sym2)).card ≤ 1 := by
  have hut : u ∈ t := Finset.mem_sym2_iff.mp htxy u hu
  let S := t.sym2.filter (fun p ↦ u ∈ p ∧ ¬p.IsDiag)
  have haddedS : s(x, y) ∈ S := by
    dsimp only [S]
    exact Finset.mem_filter.mpr
      ⟨htxy, hu, by simpa only [Sym2.mk_isDiag_iff]⟩
  have hsubset :
      (G.edgeFinset.filter (fun p ↦ u ∈ p)).filter
          (fun p ↦ p ∈ t.sym2) ⊆ S.erase s(x, y) := by
    intro p hp
    simp only [Finset.mem_filter] at hp
    rw [Finset.mem_erase]
    refine ⟨?_, Finset.mem_filter.mpr
      ⟨hp.2, hp.1.2, G.not_isDiag_of_mem_edgeFinset hp.1.1⟩⟩
    intro hpeq
    subst p
    exact hmissing (SimpleGraph.mem_edgeFinset.mp hp.1.1)
  calc
    ((G.edgeFinset.filter (fun p ↦ u ∈ p)).filter
        (fun p ↦ p ∈ t.sym2)).card ≤ (S.erase s(x, y)).card :=
      Finset.card_le_card hsubset
    _ = S.card - 1 := Finset.card_erase_of_mem haddedS
    _ = 1 := by
      dsimp only [S]
      rw [card_sym2_filter_mem_fixed t hut, htcard]

lemma card_triangles_containing_addedPair_and_vertex_le_one
    (G : SimpleGraph A) {x y u : A} (hxy : x ≠ y)
    (hux : u ≠ x) (huy : u ≠ y) :
    (((addPair G x y).cliqueFinset 3).filter
      (fun t ↦ s(x, y) ∈ t.sym2 ∧ u ∈ t)).card ≤ 1 := by
  have hsubset :
      ((addPair G x y).cliqueFinset 3).filter
          (fun t ↦ s(x, y) ∈ t.sym2 ∧ u ∈ t) ⊆ {{x, y, u}} := by
    intro t ht
    simp only [Finset.mem_filter] at ht
    simp only [Finset.mem_singleton]
    have hcard : t.card = 3 :=
      (SimpleGraph.mem_cliqueFinset_iff.mp ht.1).card_eq
    have hsub : {x, y, u} ⊆ t := by
      intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with hv | hv | hv
      · subst v
        exact Finset.mem_sym2_iff.mp ht.2.1 x (Sym2.mem_mk_left _ _)
      · subst v
        exact Finset.mem_sym2_iff.mp ht.2.1 y (Sym2.mem_mk_right _ _)
      · subst v
        exact ht.2.2
    have hthree : ({x, y, u} : Finset A).card = 3 := by
      exact Finset.card_eq_three.mpr
        ⟨x, y, u, hxy, hux.symm, huy.symm, rfl⟩
    exact (Finset.eq_of_subset_of_card_le hsub (by rw [hcard, hthree])).symm
  calc
    (((addPair G x y).cliqueFinset 3).filter
        (fun t ↦ s(x, y) ∈ t.sym2 ∧ u ∈ t)).card ≤
        ({{x, y, u}} : Finset (Finset A)).card := Finset.card_le_card hsubset
    _ = 1 := Finset.card_singleton _

lemma fractionalEdgeLoad_edgeTrianglesPart_self
    (G : SimpleGraph A) (e : Sym2 A) (w : Finset A → ℝ) :
    fractionalEdgeLoad G (edgeTrianglesPart e w) e =
      fractionalEdgeLoad G w e := by
  unfold fractionalEdgeLoad edgeTrianglesPart
  apply sum_congr rfl
  intro t ht
  simp only [mem_filter] at ht
  rw [if_pos ht.2]

lemma fractionalEdgeLoad_stripEdgeTriangles_self
    (G : SimpleGraph A) (e : Sym2 A) (w : Finset A → ℝ) :
    fractionalEdgeLoad G (stripEdgeTriangles e w) e = 0 := by
  unfold fractionalEdgeLoad stripEdgeTriangles
  apply sum_eq_zero
  intro t ht
  simp only [mem_filter] at ht
  rw [if_pos ht.2]

lemma addPair_clique_not_original_contains {G : SimpleGraph A} {x y : A}
    {t : Finset A} (ht : t ∈ (addPair G x y).cliqueFinset 3)
    (htG : t ∉ G.cliqueFinset 3) : s(x, y) ∈ t.sym2 := by
  have htData := SimpleGraph.mem_cliqueFinset_iff.mp ht
  have hnotClique : ¬ G.IsClique (t : Set A) := by
    intro hclique
    exact htG (SimpleGraph.mem_cliqueFinset_iff.mpr
      ⟨hclique, htData.card_eq⟩)
  obtain ⟨u, v, huv, hnot⟩ := (SimpleGraph.not_isClique_iff _).mp hnotClique
  have huv' : (u : A) ≠ (v : A) := by
    exact fun h ↦ huv (Subtype.ext h)
  have haug : (addPair G x y).Adj u v :=
    htData.isClique u.property v.property huv'
  have heq : s((u : A), (v : A)) = s(x, y) := by
    rcases (addPair_adj G x y u v).mp haug with hadj | ⟨heq, _⟩
    · exact False.elim (hnot hadj)
    · exact heq
  rw [← heq]
  exact Finset.mk_mem_sym2_iff.mpr ⟨u.property, v.property⟩

lemma addPair_clique_avoiding_addedPair_mem_original
    {G : SimpleGraph A} {x y : A} {t : Finset A}
    (ht : t ∈ (addPair G x y).cliqueFinset 3)
    (havoid : s(x, y) ∉ t.sym2) : t ∈ G.cliqueFinset 3 := by
  by_contra htG
  exact havoid (addPair_clique_not_original_contains ht htG)

lemma addedPair_not_mem_original_clique {G : SimpleGraph A} {x y : A}
    (hxy : x ≠ y) (hmissing : ¬ G.Adj x y)
    {t : Finset A} (ht : t ∈ G.cliqueFinset 3) :
    s(x, y) ∉ t.sym2 := by
  intro he
  have htData := SimpleGraph.mem_cliqueFinset_iff.mp ht
  have hmem := Finset.mk_mem_sym2_iff.mp he
  exact hmissing (htData.isClique hmem.1 hmem.2 hxy)

/-- On the original graph, stripping the newly added pair is exactly
restriction of the augmented weighting. -/
lemma fractionalEdgeLoad_stripEdgeTriangles_addPair
    (G : SimpleGraph A) {x y : A} (hxy : x ≠ y)
    (hmissing : ¬ G.Adj x y)
    (w : Finset A → ℝ) (p : Sym2 A) :
    fractionalEdgeLoad (addPair G x y) (stripEdgeTriangles s(x, y) w) p =
      fractionalEdgeLoad G w p := by
  let sG := (G.cliqueFinset 3).filter fun t ↦ p ∈ t.sym2
  let sH := ((addPair G x y).cliqueFinset 3).filter fun t ↦ p ∈ t.sym2
  have hsub : sG ⊆ sH := by
    intro t ht
    rcases mem_filter.mp ht with ⟨htG, hpt⟩
    exact mem_filter.mpr
      ⟨SimpleGraph.cliqueFinset_mono (addPair G x y) le_sup_left htG, hpt⟩
  unfold fractionalEdgeLoad
  change (∑ t ∈ sH, stripEdgeTriangles s(x, y) w t) = ∑ t ∈ sG, w t
  calc
    (∑ t ∈ sH, stripEdgeTriangles s(x, y) w t) =
        ∑ t ∈ sG, stripEdgeTriangles s(x, y) w t := by
      symm
      apply sum_subset hsub
      intro t htH htG
      have htH' := (mem_filter.mp htH).1
      have hadded := addPair_clique_not_original_contains htH'
        (fun h ↦ htG (mem_filter.mpr ⟨h, (mem_filter.mp htH).2⟩))
      simp [stripEdgeTriangles, hadded]
    _ = ∑ t ∈ sG, w t := by
      apply sum_congr rfl
      intro t htG
      have havoid := addedPair_not_mem_original_clique hxy hmissing
        (mem_filter.mp htG).1
      simp [stripEdgeTriangles, havoid]

lemma fractionalEdgeLoad_mono_graph {G H : SimpleGraph A} (hGH : G ≤ H)
    {w : Finset A → ℝ}
    (hw : ∀ t ∈ H.cliqueFinset 3, 0 ≤ w t) (p : Sym2 A) :
    fractionalEdgeLoad G w p ≤ fractionalEdgeLoad H w p := by
  unfold fractionalEdgeLoad
  apply sum_le_sum_of_subset_of_nonneg
  · intro t ht
    rcases mem_filter.mp ht with ⟨htG, hpt⟩
    exact mem_filter.mpr
      ⟨SimpleGraph.cliqueFinset_mono H hGH htG, hpt⟩
  · intro t ht _
    exact hw t (mem_filter.mp ht).1

lemma fractionalEdgeLoad_stripEdgeTriangles_original
    (G : SimpleGraph A) {x y : A} (hxy : x ≠ y)
    (hmissing : ¬ G.Adj x y) (w : Finset A → ℝ) (p : Sym2 A) :
    fractionalEdgeLoad G (stripEdgeTriangles s(x, y) w) p =
      fractionalEdgeLoad G w p := by
  unfold fractionalEdgeLoad
  apply sum_congr rfl
  intro t ht
  have havoid := addedPair_not_mem_original_clique hxy hmissing
    (mem_filter.mp ht).1
  rw [stripEdgeTriangles, if_neg havoid]

lemma IsFractionalPacking.strip_addedPair {G : SimpleGraph A} {x y : A}
    (hxy : x ≠ y) (hmissing : ¬ G.Adj x y) {w : Finset A → ℝ}
    (hw : IsFractionalPacking (addPair G x y) w) :
    IsFractionalPacking G (stripEdgeTriangles s(x, y) w) := by
  constructor
  · intro t ht
    have havoid := addedPair_not_mem_original_clique hxy hmissing ht
    rw [stripEdgeTriangles, if_neg havoid]
    exact hw.nonneg_on
      (SimpleGraph.cliqueFinset_mono (addPair G x y) le_sup_left ht)
  · intro p hp
    calc
      fractionalEdgeLoad G (stripEdgeTriangles s(x, y) w) p =
          fractionalEdgeLoad G w p :=
        fractionalEdgeLoad_stripEdgeTriangles_original G hxy hmissing w p
      _ ≤ fractionalEdgeLoad (addPair G x y) w p :=
        fractionalEdgeLoad_mono_graph le_sup_left hw.1 p
      _ ≤ 1 := hw.edgeLoad_le_one
        (by rw [edgeFinset_addPair hxy]; exact mem_insert_of_mem hp)

lemma IsHalfBounded.strip_addedPair {G : SimpleGraph A} {x y : A}
    (hxy : x ≠ y) (hmissing : ¬ G.Adj x y) {w : Finset A → ℝ}
    (hw : IsHalfBounded (addPair G x y) w) :
    IsHalfBounded G (stripEdgeTriangles s(x, y) w) := by
  intro t ht
  have havoid := addedPair_not_mem_original_clique hxy hmissing ht
  rw [stripEdgeTriangles, if_neg havoid]
  exact hw t (SimpleGraph.cliqueFinset_mono (addPair G x y) le_sup_left ht)

lemma fractionalSize_edgeTrianglesPart
    (G : SimpleGraph A) (e : Sym2 A) (w : Finset A → ℝ) :
    fractionalSize G (edgeTrianglesPart e w) = fractionalEdgeLoad G w e := by
  unfold fractionalSize fractionalEdgeLoad edgeTrianglesPart
  rw [Finset.sum_filter]

lemma oldIncidentRemovedLoad_le_one_of_added_endpoint
    (G : SimpleGraph A) {x y u : A} (hxy : x ≠ y)
    (hmissing : ¬G.Adj x y) (hu : u ∈ s(x, y))
    {w : Finset A → ℝ} (hw : IsFractionalPacking (addPair G x y) w) :
    oldIncidentRemovedLoad G x y w u ≤ 1 := by
  rw [oldIncidentRemovedLoad_eq_sum]
  calc
    (∑ t ∈ (addPair G x y).cliqueFinset 3,
        (((G.edgeFinset.filter (fun p ↦ u ∈ p)).filter
          (fun p ↦ p ∈ t.sym2)).card : ℝ) *
            edgeTrianglesPart s(x, y) w t) ≤
        ∑ t ∈ (addPair G x y).cliqueFinset 3,
          edgeTrianglesPart s(x, y) w t := by
      apply Finset.sum_le_sum
      intro t ht
      by_cases htxy : s(x, y) ∈ t.sym2
      · have hcard := card_oldIncidentEdges_in_triangle_le_one_of_added_endpoint
          G hxy hmissing hu t
            (SimpleGraph.mem_cliqueFinset_iff.mp ht).card_eq htxy
        have hcardR :
            (((G.edgeFinset.filter (fun p ↦ u ∈ p)).filter
              (fun p ↦ p ∈ t.sym2)).card : ℝ) ≤ 1 := by
          exact_mod_cast hcard
        exact mul_le_of_le_one_left
          (edgeTrianglesPart_nonneg hw.1 t ht) hcardR
      · simp [edgeTrianglesPart, htxy]
    _ = fractionalSize (addPair G x y)
          (edgeTrianglesPart s(x, y) w) := rfl
    _ = fractionalEdgeLoad (addPair G x y) w s(x, y) :=
      fractionalSize_edgeTrianglesPart (addPair G x y) s(x, y) w
    _ ≤ 1 := hw.edgeLoad_le_one (by
      rw [edgeFinset_addPair hxy]
      exact Finset.mem_insert_self _ _)

lemma oldIncidentRemovedLoad_le_one_of_not_added_endpoint
    (G : SimpleGraph A) {x y u : A} (hxy : x ≠ y)
    (hux : u ≠ x) (huy : u ≠ y)
    {w : Finset A → ℝ} (hw : IsFractionalPacking (addPair G x y) w)
    (hhalf : IsHalfBounded (addPair G x y) w) :
    oldIncidentRemovedLoad G x y w u ≤ 1 := by
  rw [oldIncidentRemovedLoad_eq_sum]
  let T := ((addPair G x y).cliqueFinset 3).filter
    (fun t ↦ s(x, y) ∈ t.sym2 ∧ u ∈ t)
  have hTcard : T.card ≤ 1 := by
    exact card_triangles_containing_addedPair_and_vertex_le_one
      G hxy hux huy
  calc
    (∑ t ∈ (addPair G x y).cliqueFinset 3,
        (((G.edgeFinset.filter (fun p ↦ u ∈ p)).filter
          (fun p ↦ p ∈ t.sym2)).card : ℝ) *
            edgeTrianglesPart s(x, y) w t) ≤
        ∑ t ∈ (addPair G x y).cliqueFinset 3,
          if s(x, y) ∈ t.sym2 ∧ u ∈ t then 1 else 0 := by
      apply Finset.sum_le_sum
      intro t ht
      by_cases htxy : s(x, y) ∈ t.sym2
      · by_cases hut : u ∈ t
        · rw [if_pos ⟨htxy, hut⟩]
          have hcard := card_oldIncidentEdges_in_triangle_le_two G u t
            (SimpleGraph.mem_cliqueFinset_iff.mp ht).card_eq
          have hcardR :
              (((G.edgeFinset.filter (fun p ↦ u ∈ p)).filter
                (fun p ↦ p ∈ t.sym2)).card : ℝ) ≤ 2 := by
            exact_mod_cast hcard
          have hcard0 : 0 ≤
              (((G.edgeFinset.filter (fun p ↦ u ∈ p)).filter
                (fun p ↦ p ∈ t.sym2)).card : ℝ) := by positivity
          have hw0 : 0 ≤ w t := hw.nonneg_on ht
          have hw12 : w t ≤ (1 / 2 : ℝ) := hhalf t ht
          rw [edgeTrianglesPart, if_pos htxy]
          nlinarith
        · rw [if_neg (fun h ↦ hut h.2)]
          have hempty :
              (G.edgeFinset.filter (fun p ↦ u ∈ p)).filter
                  (fun p ↦ p ∈ t.sym2) = ∅ := by
            ext p
            simp only [Finset.mem_filter, Finset.notMem_empty, iff_false]
            intro hp
            exact hut (Finset.mem_sym2_iff.mp hp.2 u hp.1.2)
          rw [hempty]
          simp
      · rw [if_neg (fun h ↦ htxy h.1)]
        simp [edgeTrianglesPart, htxy]
    _ = (T.card : ℝ) := by
      dsimp only [T]
      rw [← Finset.sum_filter]
      simp
    _ ≤ 1 := by exact_mod_cast hTcard

private lemma d8_card_edgeFinset_filter_triangle {G : SimpleGraph A}
    (t : Finset A) (ht : G.IsNClique 3 t) :
    (G.edgeFinset.filter fun e ↦ e ∈ t.sym2).card = 3 := by
  classical
  rw [show (G.edgeFinset.filter fun e ↦ e ∈ t.sym2) =
      {e ∈ G.edgeFinset | e.toFinset ⊆ t} by
    ext e
    simp [Finset.mem_sym2_iff, subset_iff]]
  rw [G.card_filter_edgeFinset_toFinset_subset t]
  have htop : G.induce (↑t : Set A) = ⊤ := G.induce_eq_top.mpr ht.isClique
  calc
    #(G.induce (↑t : Set A)).edgeFinset =
        Nat.card (G.induce (↑t : Set A)).edgeSet := by
          rw [Nat.card_eq_fintype_card, SimpleGraph.card_edgeSet]
    _ = Nat.card (⊤ : SimpleGraph t).edgeSet :=
      congrArg (fun H : SimpleGraph t ↦ Nat.card H.edgeSet) htop
    _ = #((⊤ : SimpleGraph t).edgeFinset) := by
      rw [Nat.card_eq_fintype_card, SimpleGraph.card_edgeSet]
    _ = (Fintype.card t).choose 2 :=
      SimpleGraph.card_edgeFinset_top_eq_card_choose_two
    _ = 3 := by simp [ht.card_eq]

private lemma d8_sum_fractionalEdgeLoad_eq_three_mul_fractionalSize
    (G : SimpleGraph A) (w : Finset A → ℝ) :
    ∑ e ∈ G.edgeFinset, fractionalEdgeLoad G w e =
      3 * fractionalSize G w := by
  rw [fractionalSize]
  simp_rw [fractionalEdgeLoad, Finset.sum_filter]
  rw [Finset.sum_comm, mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  rw [show (∑ e ∈ G.edgeFinset, if e ∈ t.sym2 then w t else 0) =
      ∑ e ∈ (G.edgeFinset.filter fun e ↦ e ∈ t.sym2), w t by
    rw [Finset.sum_filter]]
  rw [Finset.sum_const, nsmul_eq_mul]
  rw [d8_card_edgeFinset_filter_triangle t
    (SimpleGraph.mem_cliqueFinset_iff.mp ht)]
  norm_num

/-- The total load of the removed triangles on the old edges is exactly
twice their load on the added edge. -/
lemma sum_oldEdgeLoad_edgeTrianglesPart {G : SimpleGraph A} {x y : A}
    (hxy : x ≠ y) (hmissing : ¬ G.Adj x y) (w : Finset A → ℝ) :
    (∑ p ∈ G.edgeFinset,
        fractionalEdgeLoad (addPair G x y)
          (edgeTrianglesPart s(x, y) w) p) =
      2 * fractionalEdgeLoad (addPair G x y) w s(x, y) := by
  let H := addPair G x y
  let e : Sym2 A := s(x, y)
  have heH : e ∈ H.edgeFinset := by
    dsimp only [H]
    rw [edgeFinset_addPair hxy]
    simp [e]
  have heG : e ∉ G.edgeFinset := by
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    exact hmissing
  have hEdges : H.edgeFinset.erase e = G.edgeFinset := by
    dsimp only [H]
    rw [edgeFinset_addPair hxy, erase_insert]
    exact heG
  have htotal := d8_sum_fractionalEdgeLoad_eq_three_mul_fractionalSize
    H (edgeTrianglesPart e w)
  have hself : fractionalEdgeLoad H (edgeTrianglesPart e w) e =
      fractionalEdgeLoad H w e := fractionalEdgeLoad_edgeTrianglesPart_self H e w
  have hsize : fractionalSize H (edgeTrianglesPart e w) =
      fractionalEdgeLoad H w e := fractionalSize_edgeTrianglesPart H e w
  have herase := sum_erase_add H.edgeFinset (fun p ↦
    fractionalEdgeLoad H (edgeTrianglesPart e w) p) heH
  rw [hEdges] at herase
  dsimp only [H, e] at htotal hself hsize herase ⊢
  linarith

lemma sum_oldEdgeLoad_edgeTrianglesPart_le_two {G : SimpleGraph A} {x y : A}
    (hxy : x ≠ y) (hmissing : ¬ G.Adj x y) {w : Finset A → ℝ}
    (hw : IsFractionalPacking (addPair G x y) w) :
    (∑ p ∈ G.edgeFinset,
        fractionalEdgeLoad (addPair G x y)
          (edgeTrianglesPart s(x, y) w) p) ≤ 2 := by
  rw [sum_oldEdgeLoad_edgeTrianglesPart hxy hmissing w]
  have he : s(x, y) ∈ (addPair G x y).edgeFinset := by
    rw [edgeFinset_addPair hxy]
    simp
  have hload := hw.edgeLoad_le_one he
  linarith

/-- The old residual of the augmented packing. -/
def augmentedOldResidual (G : SimpleGraph A) (w : Finset A → ℝ)
    (p : Sym2 A) : ℝ :=
  1 - fractionalEdgeLoad G w p

lemma sum_augmentedOldResidual_le {G : SimpleGraph A} {x y : A}
    (hxy : x ≠ y) {w : Finset A → ℝ}
    (hw : IsFractionalPacking (addPair G x y) w) {b : ℝ}
    (hunc : fractionalUncoveredWeight (addPair G x y) w ≤ b) :
    (∑ p ∈ G.edgeFinset, augmentedOldResidual (addPair G x y) w p) ≤ b := by
  apply le_trans ?_ hunc
  unfold fractionalUncoveredWeight augmentedOldResidual
  apply sum_le_sum_of_subset_of_nonneg
  · intro p hp
    rw [edgeFinset_addPair hxy]
    exact mem_insert_of_mem hp
  · intro p hp _
    exact sub_nonneg.mpr (hw.edgeLoad_le_one hp)

/-- Equation (5.12): on every old edge, the stripped load, the old
uncovered amount, and the removed-triangle load sum to one. -/
lemma strip_oldResidual_removedLoad_eq_one
    (G : SimpleGraph A) {x y : A} (hxy : x ≠ y)
    (hmissing : ¬ G.Adj x y) (w : Finset A → ℝ) (p : Sym2 A) :
    fractionalEdgeLoad G (stripEdgeTriangles s(x, y) w) p +
        augmentedOldResidual (addPair G x y) w p +
        fractionalEdgeLoad (addPair G x y)
          (edgeTrianglesPart s(x, y) w) p = 1 := by
  have hstrip := fractionalEdgeLoad_stripEdgeTriangles_original
    G hxy hmissing w p
  have hrestrict := fractionalEdgeLoad_stripEdgeTriangles_addPair
    G hxy hmissing w p
  have hsplit := fractionalEdgeLoad_strip_add_part
    (addPair G x y) s(x, y) p w
  unfold augmentedOldResidual
  linarith

/-- The induction output used at the start of D8, already split into the
packing on the original deletion graph and the two residual components.
The last two conclusions are precisely the four-unit old-residual bound and
the two-unit removed-triangle bound. -/
theorem exists_d8AugmentedStrippedWeight {n : ℕ}
    (hcard : Fintype.card A = n) (hn : 14 ≤ n)
    (G : SimpleGraph A) (hexact : missingEdgeCount G = n)
    (z : ↑(universalVertices G)) {x y : A}
    (hx : x ≠ (z : A)) (hy : y ≠ (z : A)) (hxy : Gᶜ.Adj x y)
    (hstrong : AlmostCompleteStrongAt (n - 1)) :
    let K := d7DeletedGraph G (z : A)
    let x' := d7DeletedVertex (z : A) x hx
    let y' := d7DeletedVertex (z : A) y hy
    let H := d8AugmentedDeletedGraph G (z : A) x y hx hy
    ∃ w : Finset (↑(d7DeletedFinset (A := A) (z : A))) → ℝ,
      IsFractionalPacking H w ∧
      IsHalfBounded H w ∧
      fractionalUncoveredWeight H w ≤ 4 ∧
      IsFractionalPacking K (stripEdgeTriangles s(x', y') w) ∧
      IsHalfBounded K (stripEdgeTriangles s(x', y') w) ∧
      (∀ p ∈ K.edgeFinset,
        fractionalEdgeLoad K (stripEdgeTriangles s(x', y') w) p +
            augmentedOldResidual H w p +
            fractionalEdgeLoad H (edgeTrianglesPart s(x', y') w) p = 1) ∧
      (∑ p ∈ K.edgeFinset, augmentedOldResidual H w p) ≤ 4 ∧
      (∑ p ∈ K.edgeFinset,
        fractionalEdgeLoad H (edgeTrianglesPart s(x', y') w) p) ≤ 2 := by
  dsimp only
  have haux := d8AugmentedDeletedGraph_hasStrongFractionalPacking
    hcard hn G hexact z hx hy hxy hstrong
  obtain ⟨w, hwPack, hwUncovered, hwHalf⟩ := haux
  have hxy' : d7DeletedVertex (z : A) x hx ≠
      d7DeletedVertex (z : A) y hy := by
    intro h
    exact hxy.ne (congrArg Subtype.val h)
  have hmissing' : ¬ (d7DeletedGraph G (z : A)).Adj
      (d7DeletedVertex (z : A) x hx) (d7DeletedVertex (z : A) y hy) := by
    simpa [d7DeletedGraph, d7DeletedVertex] using hxy.2
  refine ⟨w, hwPack, hwHalf, hwUncovered,
    hwPack.strip_addedPair hxy' hmissing', hwHalf.strip_addedPair hxy' hmissing',
    ?_, ?_, ?_⟩
  · intro p hp
    exact strip_oldResidual_removedLoad_eq_one
      (d7DeletedGraph G (z : A)) hxy' hmissing' w p
  · exact sum_augmentedOldResidual_le hxy' hwPack hwUncovered
  · exact sum_oldEdgeLoad_edgeTrianglesPart_le_two hxy' hmissing' hwPack

/-! ## Symmetry of the augmented deletion packing -/

lemma d8AugmentedDeletedGraph_map_extendUniversalPerm
    (G : SimpleGraph A) (z x y : A) (hx : x ≠ z) (hy : y ≠ z)
    (hxy : Gᶜ.Adj x y)
    (p : Equiv.Perm (d7RemainingUniversalVertices G z)) :
    (d8AugmentedDeletedGraph G z x y hx hy).map
        (d7ExtendUniversalPerm G z p).toEmbedding =
      d8AugmentedDeletedGraph G z x y hx hy := by
  let K := d7DeletedGraph G z
  let q := d7ExtendUniversalPerm G z p
  let x' := d7DeletedVertex z x hx
  let y' := d7DeletedVertex z y hy
  have hxNot : (x' : A) ∉ universalVertices G := by
    rw [mem_universalVertices]
    dsimp only [x']
    exact Nat.ne_of_gt hxy.degree_pos_left
  have hyNot : (y' : A) ∉ universalVertices G := by
    rw [mem_universalVertices]
    dsimp only [y']
    exact Nat.ne_of_gt hxy.degree_pos_right
  have hqx : q x' = x' := d7ExtendUniversalPerm_fixes_nonuniversal
    G z p x' hxNot
  have hqy : q y' = y' := d7ExtendUniversalPerm_fixes_nonuniversal
    G z p y' hyNot
  have hqx' : q.symm x' = x' := by
    have := congrArg q.symm hqx
    simpa using this.symm
  have hqy' : q.symm y' = y' := by
    have := congrArg q.symm hqy
    simpa using this.symm
  have hKmap := d7DeletedGraph_map_extendUniversalPerm G z p
  rw [← SimpleGraph.comap_symm K q] at hKmap
  rw [← SimpleGraph.comap_symm (d8AugmentedDeletedGraph G z x y hx hy) q]
  ext u v
  have hKadj : K.Adj (q.symm u) (q.symm v) = K.Adj u v := by
    have hadj := congrFun (congrFun (SimpleGraph.ext_iff.mp hKmap) u) v
    change K.Adj (q.symm u) (q.symm v) = K.Adj u v at hadj
    exact hadj
  change
    (addPair K x' y').Adj (q.symm u) (q.symm v) ↔
      (addPair K x' y').Adj u v
  rw [addPair_adj, addPair_adj, hKadj]
  have hpair : s(q.symm u, q.symm v) = s(x', y') ↔
      s(u, v) = s(x', y') := by
    constructor
    · intro h
      have hm := congrArg (Sym2.map q) h
      simpa only [Sym2.map_mk, Equiv.apply_symm_apply, hqx, hqy] using hm
    · intro h
      have hm := congrArg (Sym2.map q.symm) h
      simpa only [Sym2.map_mk, hqx', hqy'] using hm
  have hne : q.symm u ≠ q.symm v ↔ u ≠ v := by
    exact not_congr q.symm.injective.eq_iff
  rw [hpair, hne]

lemma d7ExtendUniversalPerm_map_d8AddedPair
    (G : SimpleGraph A) (z x y : A) (hx : x ≠ z) (hy : y ≠ z)
    (hxy : Gᶜ.Adj x y)
    (p : Equiv.Perm (d7RemainingUniversalVertices G z)) :
    (d7ExtendUniversalPerm G z p).toEmbedding.sym2Map
        s(d7DeletedVertex z x hx, d7DeletedVertex z y hy) =
      s(d7DeletedVertex z x hx, d7DeletedVertex z y hy) := by
  change Sym2.map (d7ExtendUniversalPerm G z p)
      s(d7DeletedVertex z x hx, d7DeletedVertex z y hy) = _
  rw [Sym2.map_mk]
  congr 1
  · exact d7ExtendUniversalPerm_fixes_nonuniversal G z p
      (d7DeletedVertex z x hx) (by
        rw [mem_universalVertices]
        exact Nat.ne_of_gt hxy.degree_pos_left)
  · exact d7ExtendUniversalPerm_fixes_nonuniversal G z p
      (d7DeletedVertex z y hy) (by
        rw [mem_universalVertices]
        exact Nat.ne_of_gt hxy.degree_pos_right)

lemma relabelWeight_d8RemovedPart_of_invariant
    (G : SimpleGraph A) (z x y : A) (hx : x ≠ z) (hy : y ≠ z)
    (hxy : Gᶜ.Adj x y)
    (w : Finset (↑(d7DeletedFinset (A := A) z)) → ℝ)
    (p : Equiv.Perm (d7RemainingUniversalVertices G z))
    (hw : relabelWeight (d7ExtendUniversalPerm G z p) w = w) :
    relabelWeight (d7ExtendUniversalPerm G z p)
        (edgeTrianglesPart
          s(d7DeletedVertex z x hx, d7DeletedVertex z y hy) w) =
      edgeTrianglesPart
        s(d7DeletedVertex z x hx, d7DeletedVertex z y hy) w := by
  rw [relabelWeight_edgeTrianglesPart,
    d7ExtendUniversalPerm_map_d8AddedPair G z x y hx hy hxy p, hw]

lemma fractionalEdgeLoad_d8RemovedPart_map_extendUniversalPerm
    (G : SimpleGraph A) (z x y : A) (hx : x ≠ z) (hy : y ≠ z)
    (hxy : Gᶜ.Adj x y)
    (w : Finset (↑(d7DeletedFinset (A := A) z)) → ℝ)
    (hsymm : ∀ p : Equiv.Perm (d7RemainingUniversalVertices G z),
      relabelWeight (d7ExtendUniversalPerm G z p) w = w)
    (p : Equiv.Perm (d7RemainingUniversalVertices G z))
    (e : Sym2 (↑(d7DeletedFinset (A := A) z))) :
    fractionalEdgeLoad (d8AugmentedDeletedGraph G z x y hx hy)
        (edgeTrianglesPart
          s(d7DeletedVertex z x hx, d7DeletedVertex z y hy) w)
        ((d7ExtendUniversalPerm G z p).toEmbedding.sym2Map e) =
      fractionalEdgeLoad (d8AugmentedDeletedGraph G z x y hx hy)
        (edgeTrianglesPart
          s(d7DeletedVertex z x hx, d7DeletedVertex z y hy) w) e := by
  have h := fractionalEdgeLoad_relabel
    (d8AugmentedDeletedGraph G z x y hx hy)
    (d7ExtendUniversalPerm G z p)
    (edgeTrianglesPart
      s(d7DeletedVertex z x hx, d7DeletedVertex z y hy) w) e
  rw [d8AugmentedDeletedGraph_map_extendUniversalPerm
      G z x y hx hy hxy p,
    relabelWeight_d8RemovedPart_of_invariant G z x y hx hy hxy w p (hsymm p)] at h
  exact h

/-- Average an augmented deletion packing over permutations of the remaining
original universal vertices. -/
def d8SymmetrizedAugmentedWeight (G : SimpleGraph A) (z : A)
    (w : Finset (↑(d7DeletedFinset (A := A) z)) → ℝ) :
    Finset (↑(d7DeletedFinset (A := A) z)) → ℝ :=
  d7SymmetrizedWeight G z w

lemma d8SymmetrizedAugmentedWeight_isFractionalPacking
    (G : SimpleGraph A) (z x y : A) (hx : x ≠ z) (hy : y ≠ z)
    (hxy : Gᶜ.Adj x y)
    {w : Finset (↑(d7DeletedFinset (A := A) z)) → ℝ}
    (hw : IsFractionalPacking (d8AugmentedDeletedGraph G z x y hx hy) w) :
    IsFractionalPacking (d8AugmentedDeletedGraph G z x y hx hy)
      (d8SymmetrizedAugmentedWeight G z w) := by
  unfold d8SymmetrizedAugmentedWeight d7SymmetrizedWeight
  apply isFractionalPacking_averageTriangleWeight
  intro p
  have hp := hw.relabel (d7ExtendUniversalPerm G z p)
  rw [d8AugmentedDeletedGraph_map_extendUniversalPerm G z x y hx hy hxy p] at hp
  exact hp

lemma d8SymmetrizedAugmentedWeight_halfBounded
    (G : SimpleGraph A) (z x y : A) (hx : x ≠ z) (hy : y ≠ z)
    (hxy : Gᶜ.Adj x y)
    {w : Finset (↑(d7DeletedFinset (A := A) z)) → ℝ}
    (hw : IsHalfBounded (d8AugmentedDeletedGraph G z x y hx hy) w) :
    IsHalfBounded (d8AugmentedDeletedGraph G z x y hx hy)
      (d8SymmetrizedAugmentedWeight G z w) := by
  unfold d8SymmetrizedAugmentedWeight d7SymmetrizedWeight
  apply averageTriangleWeight_le_half
  intro p
  have hp := hw.relabel (d7ExtendUniversalPerm G z p)
  rw [d8AugmentedDeletedGraph_map_extendUniversalPerm G z x y hx hy hxy p] at hp
  exact hp

lemma fractionalSize_d8SymmetrizedAugmentedWeight
    (G : SimpleGraph A) (z x y : A) (hx : x ≠ z) (hy : y ≠ z)
    (hxy : Gᶜ.Adj x y)
    (w : Finset (↑(d7DeletedFinset (A := A) z)) → ℝ) :
    fractionalSize (d8AugmentedDeletedGraph G z x y hx hy)
        (d8SymmetrizedAugmentedWeight G z w) =
      fractionalSize (d8AugmentedDeletedGraph G z x y hx hy) w := by
  rw [d8SymmetrizedAugmentedWeight, d7SymmetrizedWeight,
    fractionalSize_averageTriangleWeight]
  have hterm : ∀ p : Equiv.Perm (d7RemainingUniversalVertices G z),
      fractionalSize (d8AugmentedDeletedGraph G z x y hx hy)
          (relabelWeight (d7ExtendUniversalPerm G z p) w) =
        fractionalSize (d8AugmentedDeletedGraph G z x y hx hy) w := by
    intro p
    have hp := fractionalSize_relabel
      (d8AugmentedDeletedGraph G z x y hx hy)
      (d7ExtendUniversalPerm G z p) w
    rw [d8AugmentedDeletedGraph_map_extendUniversalPerm
      G z x y hx hy hxy p] at hp
    exact hp
  simp_rw [hterm]
  rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  have hperm : (Fintype.card
      (Equiv.Perm (d7RemainingUniversalVertices G z)) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  field_simp

lemma fractionalUncoveredWeight_d8SymmetrizedAugmentedWeight
    (G : SimpleGraph A) (z x y : A) (hx : x ≠ z) (hy : y ≠ z)
    (hxy : Gᶜ.Adj x y)
    (w : Finset (↑(d7DeletedFinset (A := A) z)) → ℝ) :
    fractionalUncoveredWeight (d8AugmentedDeletedGraph G z x y hx hy)
        (d8SymmetrizedAugmentedWeight G z w) =
      fractionalUncoveredWeight (d8AugmentedDeletedGraph G z x y hx hy) w := by
  rw [fractionalUncoveredWeight_eq_card_sub_general,
    fractionalUncoveredWeight_eq_card_sub_general,
    fractionalSize_d8SymmetrizedAugmentedWeight G z x y hx hy hxy]

lemma relabelWeight_d8SymmetrizedAugmentedWeight
    (G : SimpleGraph A) (z : A)
    (w : Finset (↑(d7DeletedFinset (A := A) z)) → ℝ)
    (p : Equiv.Perm (d7RemainingUniversalVertices G z)) :
    relabelWeight (d7ExtendUniversalPerm G z p)
        (d8SymmetrizedAugmentedWeight G z w) =
      d8SymmetrizedAugmentedWeight G z w := by
  exact relabelWeight_d7SymmetrizedWeight G z w p

/-- The `(n-1)` induction output may be chosen invariant under every
permutation of the remaining original universal vertices. -/
theorem exists_d8SymmetricAugmentedWeight {n : ℕ}
    (hcard : Fintype.card A = n) (hn : 14 ≤ n)
    (G : SimpleGraph A) (hexact : missingEdgeCount G = n)
    (z : ↑(universalVertices G)) {x y : A}
    (hx : x ≠ (z : A)) (hy : y ≠ (z : A)) (hxy : Gᶜ.Adj x y)
    (hstrong : AlmostCompleteStrongAt (n - 1)) :
    ∃ w : Finset (↑(d7DeletedFinset (A := A) (z : A))) → ℝ,
      IsFractionalPacking (d8AugmentedDeletedGraph G (z : A) x y hx hy) w ∧
      IsHalfBounded (d8AugmentedDeletedGraph G (z : A) x y hx hy) w ∧
      fractionalUncoveredWeight
          (d8AugmentedDeletedGraph G (z : A) x y hx hy) w ≤ 4 ∧
      ∀ p : Equiv.Perm (d7RemainingUniversalVertices G (z : A)),
        relabelWeight (d7ExtendUniversalPerm G (z : A) p) w = w := by
  obtain ⟨v, hvPack, hvUncovered, hvHalf⟩ :=
    d8AugmentedDeletedGraph_hasStrongFractionalPacking
      hcard hn G hexact z hx hy hxy hstrong
  let w := d8SymmetrizedAugmentedWeight G (z : A) v
  refine ⟨w, ?_, ?_, ?_, ?_⟩
  · exact d8SymmetrizedAugmentedWeight_isFractionalPacking
      G (z : A) x y hx hy hxy hvPack
  · exact d8SymmetrizedAugmentedWeight_halfBounded
      G (z : A) x y hx hy hxy hvHalf
  · change fractionalUncoveredWeight
        (d8AugmentedDeletedGraph G (z : A) x y hx hy)
        (d8SymmetrizedAugmentedWeight G (z : A) v) ≤ 4
    rw [fractionalUncoveredWeight_d8SymmetrizedAugmentedWeight
      G (z : A) x y hx hy hxy]
    exact hvUncovered
  · intro p
    exact relabelWeight_d8SymmetrizedAugmentedWeight G (z : A) v p

/-- Symmetric version of the full D8 split.  This is the exact input from
which the common `gamma`, vertex `alpha`, and pair `beta` parameters are
extracted. -/
theorem exists_d8SymmetricAugmentedStrippedWeight {n : ℕ}
    (hcard : Fintype.card A = n) (hn : 14 ≤ n)
    (G : SimpleGraph A) (hexact : missingEdgeCount G = n)
    (z : ↑(universalVertices G)) {x y : A}
    (hx : x ≠ (z : A)) (hy : y ≠ (z : A)) (hxy : Gᶜ.Adj x y)
    (hstrong : AlmostCompleteStrongAt (n - 1)) :
    let K := d7DeletedGraph G (z : A)
    let x' := d7DeletedVertex (z : A) x hx
    let y' := d7DeletedVertex (z : A) y hy
    let H := d8AugmentedDeletedGraph G (z : A) x y hx hy
    ∃ w : Finset (↑(d7DeletedFinset (A := A) (z : A))) → ℝ,
      IsFractionalPacking H w ∧
      IsHalfBounded H w ∧
      fractionalUncoveredWeight H w ≤ 4 ∧
      (∀ p : Equiv.Perm (d7RemainingUniversalVertices G (z : A)),
        relabelWeight (d7ExtendUniversalPerm G (z : A) p) w = w) ∧
      IsFractionalPacking K (stripEdgeTriangles s(x', y') w) ∧
      IsHalfBounded K (stripEdgeTriangles s(x', y') w) ∧
      (∀ p ∈ K.edgeFinset,
        fractionalEdgeLoad K (stripEdgeTriangles s(x', y') w) p +
            augmentedOldResidual H w p +
            fractionalEdgeLoad H (edgeTrianglesPart s(x', y') w) p = 1) ∧
      (∑ p ∈ K.edgeFinset, augmentedOldResidual H w p) ≤ 4 ∧
      (∑ p ∈ K.edgeFinset,
        fractionalEdgeLoad H (edgeTrianglesPart s(x', y') w) p) ≤ 2 := by
  dsimp only
  obtain ⟨w, hwPack, hwHalf, hwUncovered, hwInvariant⟩ :=
    exists_d8SymmetricAugmentedWeight
      hcard hn G hexact z hx hy hxy hstrong
  have hxy' : d7DeletedVertex (z : A) x hx ≠
      d7DeletedVertex (z : A) y hy := by
    intro h
    exact hxy.ne (congrArg Subtype.val h)
  have hmissing' : ¬ (d7DeletedGraph G (z : A)).Adj
      (d7DeletedVertex (z : A) x hx) (d7DeletedVertex (z : A) y hy) := by
    simpa [d7DeletedGraph, d7DeletedVertex] using hxy.2
  refine ⟨w, hwPack, hwHalf, hwUncovered, hwInvariant,
    hwPack.strip_addedPair hxy' hmissing', hwHalf.strip_addedPair hxy' hmissing',
    ?_, ?_, ?_⟩
  · intro p hp
    exact strip_oldResidual_removedLoad_eq_one
      (d7DeletedGraph G (z : A)) hxy' hmissing' w p
  · exact sum_augmentedOldResidual_le hxy' hwPack hwUncovered
  · exact sum_oldEdgeLoad_edgeTrianglesPart_le_two hxy' hmissing' hwPack

/-! ## The D8 orbit parameters and shortcut coefficients -/

private lemma d8OtherUniversalFirst_val_ne (G : SimpleGraph A)
    (z₀ : ↑(universalVertices G))
    (hm : 4 ≤ (universalVertices G).card) :
    (d7OtherUniversalFirst G z₀ hm : A) ≠ (z₀ : A) := by
  intro h
  exact d7OtherUniversalFirst_ne G z₀ hm (Subtype.ext h)

private lemma d8OtherUniversalSecond_val_ne (G : SimpleGraph A)
    (z₀ : ↑(universalVertices G))
    (hm : 4 ≤ (universalVertices G).card) :
    (d7OtherUniversalSecond G z₀ hm : A) ≠ (z₀ : A) := by
  intro h
  exact d7OtherUniversalSecond_ne G z₀ hm (Subtype.ext h)

/-- Load contributed to an old edge by the triangles removed around the
added pair in the base D8 deletion. -/
def d8RemovedLoad (G : SimpleGraph A) (z x y : A)
    (hx : x ≠ z) (hy : y ≠ z)
    (w : Finset (↑(d7DeletedFinset (A := A) z)) → ℝ)
    (p : Sym2 (↑(d7DeletedFinset (A := A) z))) : ℝ :=
  fractionalEdgeLoad (d8AugmentedDeletedGraph G z x y hx hy)
    (edgeTrianglesPart
      s(d7DeletedVertex z x hx, d7DeletedVertex z y hy) w) p

lemma d8RemovedLoad_nonneg (G : SimpleGraph A) (z x y : A)
    (hx : x ≠ z) (hy : y ≠ z)
    {w : Finset (↑(d7DeletedFinset (A := A) z)) → ℝ}
    (hw : IsFractionalPacking (d8AugmentedDeletedGraph G z x y hx hy) w)
    (p : Sym2 (↑(d7DeletedFinset (A := A) z))) :
    0 ≤ d8RemovedLoad G z x y hx hy w p := by
  unfold d8RemovedLoad fractionalEdgeLoad
  exact Finset.sum_nonneg fun t ht ↦
    edgeTrianglesPart_nonneg hw.1 t (mem_filter.mp ht).1

lemma d8RemovedLoad_map_extendUniversalPerm
    (G : SimpleGraph A) (z x y : A) (hx : x ≠ z) (hy : y ≠ z)
    (hxy : Gᶜ.Adj x y)
    (w : Finset (↑(d7DeletedFinset (A := A) z)) → ℝ)
    (hsymm : ∀ p : Equiv.Perm (d7RemainingUniversalVertices G z),
      relabelWeight (d7ExtendUniversalPerm G z p) w = w)
    (p : Equiv.Perm (d7RemainingUniversalVertices G z))
    (e : Sym2 (↑(d7DeletedFinset (A := A) z))) :
    d8RemovedLoad G z x y hx hy w
        ((d7ExtendUniversalPerm G z p).toEmbedding.sym2Map e) =
      d8RemovedLoad G z x y hx hy w e := by
  exact fractionalEdgeLoad_d8RemovedPart_map_extendUniversalPerm
    G z x y hx hy hxy w hsymm p e

def d8ExtractedBeta (G : SimpleGraph A)
    (z₀ : ↑(universalVertices G)) (x y : A)
    (hx : x ≠ (z₀ : A)) (hy : y ≠ (z₀ : A))
    (w : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ)
    (e : Sym2 (↑(nonUniversalVertices G))) : ℝ :=
  d8RemovedLoad G (z₀ : A) x y hx hy w
    ((d7NonUniversalDeletedEmbedding G z₀).sym2Map e)

def d8ExtractedAlpha (G : SimpleGraph A)
    (z₀ : ↑(universalVertices G)) (x y : A)
    (hx : x ≠ (z₀ : A)) (hy : y ≠ (z₀ : A))
    (w : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ)
    (hm : 4 ≤ (universalVertices G).card)
    (u : ↑(nonUniversalVertices G)) : ℝ :=
  d8RemovedLoad G (z₀ : A) x y hx hy w
    s(d7NonUniversalDeletedEmbedding G z₀ u,
      d7DeletedVertex (z₀ : A) (d7OtherUniversalFirst G z₀ hm : A)
        (d8OtherUniversalFirst_val_ne G z₀ hm))

def d8ExtractedGamma (G : SimpleGraph A)
    (z₀ : ↑(universalVertices G)) (x y : A)
    (hx : x ≠ (z₀ : A)) (hy : y ≠ (z₀ : A))
    (w : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ)
    (hm : 4 ≤ (universalVertices G).card) : ℝ :=
  d8RemovedLoad G (z₀ : A) x y hx hy w
    s(d7DeletedVertex (z₀ : A) (d7OtherUniversalFirst G z₀ hm : A)
        (d8OtherUniversalFirst_val_ne G z₀ hm),
      d7DeletedVertex (z₀ : A) (d7OtherUniversalSecond G z₀ hm : A)
        (d8OtherUniversalSecond_val_ne G z₀ hm))

lemma d8ExtractedBeta_nonneg (G : SimpleGraph A)
    (z₀ : ↑(universalVertices G)) (x y : A)
    (hx : x ≠ (z₀ : A)) (hy : y ≠ (z₀ : A))
    {w : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ}
    (hw : IsFractionalPacking
      (d8AugmentedDeletedGraph G (z₀ : A) x y hx hy) w)
    (e : Sym2 (↑(nonUniversalVertices G))) :
    0 ≤ d8ExtractedBeta G z₀ x y hx hy w e := by
  exact d8RemovedLoad_nonneg G (z₀ : A) x y hx hy hw _

lemma d8ExtractedBetaIncident_le_oldIncidentRemovedLoad
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G)) (x y : A)
    (hx : x ≠ (z₀ : A)) (hy : y ≠ (z₀ : A))
    {w : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ}
    (hw : IsFractionalPacking
      (d8AugmentedDeletedGraph G (z₀ : A) x y hx hy) w)
    (u : ↑(nonUniversalVertices G)) :
    (∑ e ∈ (G.induce
        (↑(nonUniversalVertices G) : Set A)).edgeFinset with
          u ∈ e.toFinset,
        d8ExtractedBeta G z₀ x y hx hy w e) ≤
      oldIncidentRemovedLoad (d7DeletedGraph G (z₀ : A))
        (d7DeletedVertex (z₀ : A) x hx)
        (d7DeletedVertex (z₀ : A) y hy) w
        (d7NonUniversalDeletedEmbedding G z₀ u) := by
  let E := (G.induce
    (↑(nonUniversalVertices G) : Set A)).edgeFinset
  let ι := d7NonUniversalDeletedEmbedding G z₀
  change (∑ e ∈ E.filter (fun e ↦ u ∈ e.toFinset),
      d8RemovedLoad G (z₀ : A) x y hx hy w (ι.sym2Map e)) ≤ _
  calc
    (∑ e ∈ E.filter (fun e ↦ u ∈ e.toFinset),
        d8RemovedLoad G (z₀ : A) x y hx hy w (ι.sym2Map e)) =
        ∑ p ∈ (E.filter (fun e ↦ u ∈ e.toFinset)).map ι.sym2Map,
          d8RemovedLoad G (z₀ : A) x y hx hy w p := by
      rw [Finset.sum_map]
      rfl
    _ ≤ ∑ p ∈ (d7DeletedGraph G (z₀ : A)).edgeFinset.filter
          (fun p ↦ ι u ∈ p),
          d8RemovedLoad G (z₀ : A) x y hx hy w p := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro p hp
        rw [Finset.mem_map] at hp
        obtain ⟨e, he, rfl⟩ := hp
        simp only [Finset.mem_filter, Sym2.mem_toFinset] at he ⊢
        refine ⟨d7NonUniversalDeletedEdge_mem G z₀ e he.1, ?_⟩
        change ι u ∈ Sym2.map ι e
        rw [Sym2.mem_map]
        exact ⟨u, he.2, rfl⟩
      · intro p hp _
        exact d8RemovedLoad_nonneg G (z₀ : A) x y hx hy hw p
    _ = oldIncidentRemovedLoad (d7DeletedGraph G (z₀ : A))
        (d7DeletedVertex (z₀ : A) x hx)
        (d7DeletedVertex (z₀ : A) y hy) w (ι u) := rfl

lemma d8ExtractedBetaIncident_le_one
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G)) (x y : A)
    (hx : x ≠ (z₀ : A)) (hy : y ≠ (z₀ : A)) (hxy : Gᶜ.Adj x y)
    {w : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ}
    (hw : IsFractionalPacking
      (d8AugmentedDeletedGraph G (z₀ : A) x y hx hy) w)
    (hhalf : IsHalfBounded
      (d8AugmentedDeletedGraph G (z₀ : A) x y hx hy) w)
    (u : ↑(nonUniversalVertices G)) :
    (∑ e ∈ (G.induce
        (↑(nonUniversalVertices G) : Set A)).edgeFinset with
          u ∈ e.toFinset,
        d8ExtractedBeta G z₀ x y hx hy w e) ≤ 1 := by
  let K := d7DeletedGraph G (z₀ : A)
  let x' := d7DeletedVertex (z₀ : A) x hx
  let y' := d7DeletedVertex (z₀ : A) y hy
  let u' := d7NonUniversalDeletedEmbedding G z₀ u
  have hxy' : x' ≠ y' := by
    intro h
    exact hxy.ne (congrArg Subtype.val h)
  have hmissing' : ¬K.Adj x' y' := by
    intro hadj
    apply hxy.2
    exact hadj
  have hbase := d8ExtractedBetaIncident_le_oldIncidentRemovedLoad
    G z₀ x y hx hy hw u
  change _ ≤ oldIncidentRemovedLoad K x' y' w u' at hbase
  apply hbase.trans
  by_cases hux : (u : A) = x
  · have hu' : u' = x' := by
      apply Subtype.ext
      exact hux
    apply oldIncidentRemovedLoad_le_one_of_added_endpoint
      K hxy' hmissing'
    rw [hu']
    exact Sym2.mem_mk_left _ _
    simpa only [d8AugmentedDeletedGraph, K, x', y'] using hw
  · by_cases huy : (u : A) = y
    · have hu' : u' = y' := by
        apply Subtype.ext
        exact huy
      apply oldIncidentRemovedLoad_le_one_of_added_endpoint
        K hxy' hmissing'
      rw [hu']
      exact Sym2.mem_mk_right _ _
      simpa only [d8AugmentedDeletedGraph, K, x', y'] using hw
    · have hux' : u' ≠ x' := by
        intro h
        exact hux (congrArg Subtype.val h)
      have huy' : u' ≠ y' := by
        intro h
        exact huy (congrArg Subtype.val h)
      apply oldIncidentRemovedLoad_le_one_of_not_added_endpoint
        K hxy' hux' huy'
      · simpa only [d8AugmentedDeletedGraph, K, x', y'] using hw
      · simpa only [d8AugmentedDeletedGraph, K, x', y'] using hhalf

lemma d8ExtractedAlpha_nonneg (G : SimpleGraph A)
    (z₀ : ↑(universalVertices G)) (x y : A)
    (hx : x ≠ (z₀ : A)) (hy : y ≠ (z₀ : A))
    {w : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ}
    (hm : 4 ≤ (universalVertices G).card)
    (hw : IsFractionalPacking
      (d8AugmentedDeletedGraph G (z₀ : A) x y hx hy) w)
    (u : ↑(nonUniversalVertices G)) :
    0 ≤ d8ExtractedAlpha G z₀ x y hx hy w hm u := by
  exact d8RemovedLoad_nonneg G (z₀ : A) x y hx hy hw _

lemma d8ExtractedGamma_nonneg (G : SimpleGraph A)
    (z₀ : ↑(universalVertices G)) (x y : A)
    (hx : x ≠ (z₀ : A)) (hy : y ≠ (z₀ : A))
    {w : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ}
    (hm : 4 ≤ (universalVertices G).card)
    (hw : IsFractionalPacking
      (d8AugmentedDeletedGraph G (z₀ : A) x y hx hy) w) :
    0 ≤ d8ExtractedGamma G z₀ x y hx hy w hm := by
  exact d8RemovedLoad_nonneg G (z₀ : A) x y hx hy hw _

lemma d8RemovedLoad_base_mixed_eq_extracted
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G)) (x y : A)
    (hx : x ≠ (z₀ : A)) (hy : y ≠ (z₀ : A)) (hxy : Gᶜ.Adj x y)
    (w : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ)
    (hm : 4 ≤ (universalVertices G).card)
    (hsymm : ∀ p : Equiv.Perm (d7RemainingUniversalVertices G (z₀ : A)),
      relabelWeight (d7ExtendUniversalPerm G (z₀ : A) p) w = w)
    (u : ↑(nonUniversalVertices G)) (v : ↑(universalVertices G))
    (hv : (v : A) ≠ (z₀ : A)) :
    d8RemovedLoad G (z₀ : A) x y hx hy w
        s(d7NonUniversalDeletedEmbedding G z₀ u,
          d7DeletedVertex (z₀ : A) (v : A) hv) =
      d8ExtractedAlpha G z₀ x y hx hy w hm u := by
  let u₀ := d7NonUniversalDeletedEmbedding G z₀ u
  let v₀ := d7DeletedVertex (z₀ : A) (v : A) hv
  let r₀ := d7DeletedVertex (z₀ : A)
    (d7OtherUniversalFirst G z₀ hm : A)
    (d8OtherUniversalFirst_val_ne G z₀ hm)
  have hu₀ : (u₀ : A) ∉ universalVertices G :=
    nonUniversalVertex_not_mem_universalVertices G u.property
  have hv₀ : (v₀ : A) ∈ universalVertices G := v.property
  have hr₀ : (r₀ : A) ∈ universalVertices G :=
    (d7OtherUniversalFirst G z₀ hm).property
  obtain ⟨p, hp⟩ := exists_d7ExtendUniversalPerm_apply_eq
    G (z₀ : A) v₀ r₀ hv₀ hr₀
  have hfix := d7ExtendUniversalPerm_fixes_nonuniversal
    G (z₀ : A) p u₀ hu₀
  have hmap : (d7ExtendUniversalPerm G (z₀ : A) p).toEmbedding.sym2Map
      s(u₀, v₀) = s(u₀, r₀) := by
    change Sym2.map (d7ExtendUniversalPerm G (z₀ : A) p) s(u₀, v₀) = _
    rw [Sym2.map_mk, hfix, hp]
  have hload := d8RemovedLoad_map_extendUniversalPerm
    G (z₀ : A) x y hx hy hxy w hsymm p s(u₀, v₀)
  rw [hmap] at hload
  simpa only [u₀, v₀, r₀, d8ExtractedAlpha] using hload.symm

lemma d8RemovedLoad_base_universal_eq_extracted
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G)) (x y : A)
    (hx : x ≠ (z₀ : A)) (hy : y ≠ (z₀ : A)) (hxy : Gᶜ.Adj x y)
    (w : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ)
    (hm : 4 ≤ (universalVertices G).card)
    (hsymm : ∀ p : Equiv.Perm (d7RemainingUniversalVertices G (z₀ : A)),
      relabelWeight (d7ExtendUniversalPerm G (z₀ : A) p) w = w)
    (v₁ v₂ : ↑(universalVertices G))
    (hv₁ : (v₁ : A) ≠ (z₀ : A)) (hv₂ : (v₂ : A) ≠ (z₀ : A))
    (hv₁v₂ : v₁ ≠ v₂) :
    d8RemovedLoad G (z₀ : A) x y hx hy w
        s(d7DeletedVertex (z₀ : A) (v₁ : A) hv₁,
          d7DeletedVertex (z₀ : A) (v₂ : A) hv₂) =
      d8ExtractedGamma G z₀ x y hx hy w hm := by
  let v₁' := d7DeletedVertex (z₀ : A) (v₁ : A) hv₁
  let v₂' := d7DeletedVertex (z₀ : A) (v₂ : A) hv₂
  let r₁ := d7DeletedVertex (z₀ : A)
    (d7OtherUniversalFirst G z₀ hm : A)
    (d8OtherUniversalFirst_val_ne G z₀ hm)
  let r₂ := d7DeletedVertex (z₀ : A)
    (d7OtherUniversalSecond G z₀ hm : A)
    (d8OtherUniversalSecond_val_ne G z₀ hm)
  have hv₁v₂' : v₁' ≠ v₂' := by
    intro h
    apply hv₁v₂
    apply Subtype.ext
    exact congrArg
      (fun q : ↑(d7DeletedFinset (A := A) (z₀ : A)) ↦ (q : A)) h
  have hr₁r₂ : r₁ ≠ r₂ := by
    intro h
    apply d7OtherUniversalFirst_ne_second G z₀ hm
    apply Subtype.ext
    exact congrArg
      (fun q : ↑(d7DeletedFinset (A := A) (z₀ : A)) ↦ (q : A)) h
  obtain ⟨p, hp₁, hp₂⟩ := exists_d7ExtendUniversalPerm_map_pair
    G (z₀ : A) v₁' v₂' r₁ r₂ v₁.property v₂.property
      (d7OtherUniversalFirst G z₀ hm).property
      (d7OtherUniversalSecond G z₀ hm).property hv₁v₂' hr₁r₂
  have hmap : (d7ExtendUniversalPerm G (z₀ : A) p).toEmbedding.sym2Map
      s(v₁', v₂') = s(r₁, r₂) := by
    change Sym2.map (d7ExtendUniversalPerm G (z₀ : A) p) s(v₁', v₂') = _
    rw [Sym2.map_mk, hp₁, hp₂]
  have hload := d8RemovedLoad_map_extendUniversalPerm
    G (z₀ : A) x y hx hy hxy w hsymm p s(v₁', v₂')
  rw [hmap] at hload
  simpa only [v₁', v₂', r₁, r₂, d8ExtractedGamma] using hload.symm

lemma d8RemovedLoad_base_mixed_remaining_eq_extracted
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G)) (x y : A)
    (hx : x ≠ (z₀ : A)) (hy : y ≠ (z₀ : A)) (hxy : Gᶜ.Adj x y)
    (w : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ)
    (hm : 4 ≤ (universalVertices G).card)
    (hsymm : ∀ p : Equiv.Perm (d7RemainingUniversalVertices G (z₀ : A)),
      relabelWeight (d7ExtendUniversalPerm G (z₀ : A) p) w = w)
    (u : ↑(nonUniversalVertices G))
    (v : d7RemainingUniversalVertices G (z₀ : A)) :
    d8RemovedLoad G (z₀ : A) x y hx hy w
        s(d7NonUniversalDeletedEmbedding G z₀ u,
          d7RemainingUniversalEmbedding G (z₀ : A) v) =
      d8ExtractedAlpha G z₀ x y hx hy w hm u := by
  let vZ : ↑(universalVertices G) := ⟨(v.1 : A), v.property⟩
  have hv : (vZ : A) ≠ (z₀ : A) := by
    have hvDel := v.1.property
    simpa only [d7DeletedFinset, Finset.mem_erase, Finset.mem_univ,
      and_true, vZ] using hvDel
  have h := d8RemovedLoad_base_mixed_eq_extracted
    G z₀ x y hx hy hxy w hm hsymm u vZ hv
  have hvEq : d7RemainingUniversalEmbedding G (z₀ : A) v =
      d7DeletedVertex (z₀ : A) (vZ : A) hv := by
    apply Subtype.ext
    rfl
  rwa [hvEq]

lemma d8RemovedLoad_base_universal_remaining_eq_extracted
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G)) (x y : A)
    (hx : x ≠ (z₀ : A)) (hy : y ≠ (z₀ : A)) (hxy : Gᶜ.Adj x y)
    (w : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ)
    (hm : 4 ≤ (universalVertices G).card)
    (hsymm : ∀ p : Equiv.Perm (d7RemainingUniversalVertices G (z₀ : A)),
      relabelWeight (d7ExtendUniversalPerm G (z₀ : A) p) w = w)
    (v₁ v₂ : d7RemainingUniversalVertices G (z₀ : A))
    (hv₁v₂ : v₁ ≠ v₂) :
    d8RemovedLoad G (z₀ : A) x y hx hy w
        s(d7RemainingUniversalEmbedding G (z₀ : A) v₁,
          d7RemainingUniversalEmbedding G (z₀ : A) v₂) =
      d8ExtractedGamma G z₀ x y hx hy w hm := by
  let v₁Z : ↑(universalVertices G) := ⟨(v₁.1 : A), v₁.property⟩
  let v₂Z : ↑(universalVertices G) := ⟨(v₂.1 : A), v₂.property⟩
  have hv₁ : (v₁Z : A) ≠ (z₀ : A) := by
    have h := v₁.1.property
    simpa only [d7DeletedFinset, Finset.mem_erase, Finset.mem_univ,
      and_true, v₁Z] using h
  have hv₂ : (v₂Z : A) ≠ (z₀ : A) := by
    have h := v₂.1.property
    simpa only [d7DeletedFinset, Finset.mem_erase, Finset.mem_univ,
      and_true, v₂Z] using h
  have hvZ : v₁Z ≠ v₂Z := by
    intro h
    apply hv₁v₂
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun q : ↑(universalVertices G) ↦ (q : A)) h
  have h := d8RemovedLoad_base_universal_eq_extracted
    G z₀ x y hx hy hxy w hm hsymm v₁Z v₂Z hv₁ hv₂ hvZ
  have hv₁Eq : d7RemainingUniversalEmbedding G (z₀ : A) v₁ =
      d7DeletedVertex (z₀ : A) (v₁Z : A) hv₁ := by
    apply Subtype.ext
    rfl
  have hv₂Eq : d7RemainingUniversalEmbedding G (z₀ : A) v₂ =
      d7DeletedVertex (z₀ : A) (v₂Z : A) hv₂ := by
    apply Subtype.ext
    rfl
  rwa [hv₁Eq, hv₂Eq]

lemma sum_d8RemovedLoad_base_nonUniversalEdges
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G)) (x y : A)
    (hx : x ≠ (z₀ : A)) (hy : y ≠ (z₀ : A))
    (w : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ) :
    ∑ e ∈ d7BaseNonUniversalEdges G z₀,
        d8RemovedLoad G (z₀ : A) x y hx hy w e =
      ∑ e ∈ (G.induce
        (↑(nonUniversalVertices G) : Set A)).edgeFinset,
          d8ExtractedBeta G z₀ x y hx hy w e := by
  rw [d7BaseNonUniversalEdges, Finset.sum_map]
  rfl

lemma sum_d8RemovedLoad_base_mixedEdges
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G)) (x y : A)
    (hx : x ≠ (z₀ : A)) (hy : y ≠ (z₀ : A)) (hxy : Gᶜ.Adj x y)
    (w : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ)
    (hm : 4 ≤ (universalVertices G).card)
    (hsymm : ∀ p : Equiv.Perm (d7RemainingUniversalVertices G (z₀ : A)),
      relabelWeight (d7ExtendUniversalPerm G (z₀ : A) p) w = w) :
    ∑ e ∈ d7BaseMixedEdges G z₀,
        d8RemovedLoad G (z₀ : A) x y hx hy w e =
      (((universalVertices G).card : ℝ) - 1) *
        ∑ u, d8ExtractedAlpha G z₀ x y hx hy w hm u := by
  rw [d7BaseMixedEdges, Finset.sum_map]
  change (∑ p : (↑(nonUniversalVertices G) ×
      d7RemainingUniversalVertices G (z₀ : A)),
        d8RemovedLoad G (z₀ : A) x y hx hy w
          ((d7MixedDeletedEdgeEmbedding G z₀) p)) = _
  rw [Fintype.sum_prod_type]
  calc
    (∑ u : ↑(nonUniversalVertices G),
        ∑ v : d7RemainingUniversalVertices G (z₀ : A),
          d8RemovedLoad G (z₀ : A) x y hx hy w
            ((d7MixedDeletedEdgeEmbedding G z₀) (u, v))) =
        ∑ u : ↑(nonUniversalVertices G),
          ∑ _v : d7RemainingUniversalVertices G (z₀ : A),
            d8ExtractedAlpha G z₀ x y hx hy w hm u := by
      apply Fintype.sum_congr
      intro u
      apply Fintype.sum_congr
      intro v
      exact d8RemovedLoad_base_mixed_remaining_eq_extracted
        G z₀ x y hx hy hxy w hm hsymm u v
    _ = ∑ u : ↑(nonUniversalVertices G),
        (Fintype.card (d7RemainingUniversalVertices G (z₀ : A)) : ℝ) *
          d8ExtractedAlpha G z₀ x y hx hy w hm u := by
      apply Fintype.sum_congr
      intro u
      simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
    _ = (((universalVertices G).card : ℝ) - 1) *
        ∑ u, d8ExtractedAlpha G z₀ x y hx hy w hm u := by
      rw [card_d7RemainingUniversalVertices G z₀,
        Nat.cast_sub (by omega : 1 ≤ (universalVertices G).card), Nat.cast_one,
        Finset.mul_sum]

lemma sum_d8RemovedLoad_base_universalEdges
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G)) (x y : A)
    (hx : x ≠ (z₀ : A)) (hy : y ≠ (z₀ : A)) (hxy : Gᶜ.Adj x y)
    (w : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ)
    (hm : 4 ≤ (universalVertices G).card)
    (hsymm : ∀ p : Equiv.Perm (d7RemainingUniversalVertices G (z₀ : A)),
      relabelWeight (d7ExtendUniversalPerm G (z₀ : A) p) w = w) :
    ∑ e ∈ d7BaseUniversalEdges G z₀,
        d8RemovedLoad G (z₀ : A) x y hx hy w e =
      ((((universalVertices G).card : ℝ) - 1) *
          (((universalVertices G).card : ℝ) - 2) / 2) *
        d8ExtractedGamma G z₀ x y hx hy w hm := by
  rw [d7BaseUniversalEdges, Finset.sum_map]
  calc
    (∑ e ∈ (⊤ : SimpleGraph
        (d7RemainingUniversalVertices G (z₀ : A))).edgeFinset,
        d8RemovedLoad G (z₀ : A) x y hx hy w
          ((d7RemainingUniversalEmbedding G (z₀ : A)).sym2Map e)) =
        ∑ _e ∈ (⊤ : SimpleGraph
          (d7RemainingUniversalVertices G (z₀ : A))).edgeFinset,
            d8ExtractedGamma G z₀ x y hx hy w hm := by
      apply Finset.sum_congr rfl
      intro e he
      induction e using Sym2.inductionOn with
      | hf v₁ v₂ =>
          have hv₁v₂ : v₁ ≠ v₂ :=
            (⊤ : SimpleGraph
              (d7RemainingUniversalVertices G (z₀ : A))).ne_of_adj
                (SimpleGraph.mem_edgeFinset.mp he)
          change d8RemovedLoad G (z₀ : A) x y hx hy w
              s(d7RemainingUniversalEmbedding G (z₀ : A) v₁,
                d7RemainingUniversalEmbedding G (z₀ : A) v₂) = _
          exact d8RemovedLoad_base_universal_remaining_eq_extracted
            G z₀ x y hx hy hxy w hm hsymm v₁ v₂ hv₁v₂
    _ = (((⊤ : SimpleGraph
        (d7RemainingUniversalVertices G (z₀ : A))).edgeFinset.card : ℝ) *
          d8ExtractedGamma G z₀ x y hx hy w hm) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ = ((((universalVertices G).card : ℝ) - 1) *
          (((universalVertices G).card : ℝ) - 2) / 2) *
        d8ExtractedGamma G z₀ x y hx hy w hm := by
      rw [SimpleGraph.card_edgeFinset_top_eq_card_choose_two,
        Nat.cast_choose_two, card_d7RemainingUniversalVertices G z₀]
      have hm1 : 1 ≤ (universalVertices G).card := by omega
      rw [Nat.cast_sub hm1, Nat.cast_one]
      ring

lemma d8ExtractedOrbitTotal_le_two
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G)) (x y : A)
    (hx : x ≠ (z₀ : A)) (hy : y ≠ (z₀ : A)) (hxy : Gᶜ.Adj x y)
    (w : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ)
    (hm : 4 ≤ (universalVertices G).card)
    (hsymm : ∀ p : Equiv.Perm (d7RemainingUniversalVertices G (z₀ : A)),
      relabelWeight (d7ExtendUniversalPerm G (z₀ : A) p) w = w)
    (htotal : (∑ p ∈ (d7DeletedGraph G (z₀ : A)).edgeFinset,
      d8RemovedLoad G (z₀ : A) x y hx hy w p) ≤ 2) :
    ((((universalVertices G).card : ℝ) - 1) *
        (((universalVertices G).card : ℝ) - 2) / 2) *
          d8ExtractedGamma G z₀ x y hx hy w hm +
      (((universalVertices G).card : ℝ) - 1) *
        ∑ u, d8ExtractedAlpha G z₀ x y hx hy w hm u +
      ∑ e ∈ (G.induce
        (↑(nonUniversalVertices G) : Set A)).edgeFinset,
          d8ExtractedBeta G z₀ x y hx hy w e ≤ 2 := by
  rw [d7DeletedGraph_edgeFinset_eq_three_orbits G z₀,
    Finset.sum_union (d7BaseNonUniversalUnionMixed_disjoint_universal G z₀),
    Finset.sum_union (d7BaseNonUniversalEdges_disjoint_mixed G z₀),
    sum_d8RemovedLoad_base_nonUniversalEdges G z₀ x y hx hy w,
    sum_d8RemovedLoad_base_mixedEdges G z₀ x y hx hy hxy w hm hsymm,
    sum_d8RemovedLoad_base_universalEdges G z₀ x y hx hy hxy w hm hsymm]
    at htotal
  linarith

/-- The removed-triangle edge loads in D8, after symmetry, have the same
three orbit types as the separated unit in D7.  Their total is only bounded
by two, and the load incident with a fixed nonuniversal vertex is bounded by
one. -/
structure D8SeparatedParameters (G : SimpleGraph A) where
  gamma : ℝ
  alpha : ↑(nonUniversalVertices G) → ℝ
  beta : Sym2 (↑(nonUniversalVertices G)) → ℝ
  gamma_nonneg : 0 ≤ gamma
  alpha_nonneg : ∀ u, 0 ≤ alpha u
  beta_nonneg : ∀ e ∈ (G.induce
    (↑(nonUniversalVertices G) : Set A)).edgeFinset, 0 ≤ beta e
  total_le_two :
    ((((universalVertices G).card : ℝ) - 1) *
        (((universalVertices G).card : ℝ) - 2) / 2) * gamma +
      (((universalVertices G).card : ℝ) - 1) * ∑ u, alpha u +
      ∑ e ∈ (G.induce
        (↑(nonUniversalVertices G) : Set A)).edgeFinset, beta e ≤ 2
  betaIncident_le_one : ∀ u,
    (∑ e ∈ (G.induce
      (↑(nonUniversalVertices G) : Set A)).edgeFinset with
        (u : ↑(nonUniversalVertices G)) ∈ e.toFinset, beta e) ≤ 1

/-- Package the orbit values of a symmetric D8 removed-triangle weighting.
The only local input not implied by the global orbit count is the vertexwise
`beta`-incidence estimate; it is isolated here for the later half-bound
argument. -/
def d8ExtractedSeparatedParameters
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G)) (x y : A)
    (hx : x ≠ (z₀ : A)) (hy : y ≠ (z₀ : A)) (hxy : Gᶜ.Adj x y)
    (w : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ)
    (hm : 4 ≤ (universalVertices G).card)
    (hw : IsFractionalPacking
      (d8AugmentedDeletedGraph G (z₀ : A) x y hx hy) w)
    (hsymm : ∀ p : Equiv.Perm (d7RemainingUniversalVertices G (z₀ : A)),
      relabelWeight (d7ExtendUniversalPerm G (z₀ : A) p) w = w)
    (htotal : (∑ p ∈ (d7DeletedGraph G (z₀ : A)).edgeFinset,
      d8RemovedLoad G (z₀ : A) x y hx hy w p) ≤ 2)
    (hincident : ∀ u : ↑(nonUniversalVertices G),
      (∑ e ∈ (G.induce
        (↑(nonUniversalVertices G) : Set A)).edgeFinset with
          u ∈ e.toFinset,
        d8ExtractedBeta G z₀ x y hx hy w e) ≤ 1) :
    D8SeparatedParameters G where
  gamma := d8ExtractedGamma G z₀ x y hx hy w hm
  alpha := d8ExtractedAlpha G z₀ x y hx hy w hm
  beta := d8ExtractedBeta G z₀ x y hx hy w
  gamma_nonneg := d8ExtractedGamma_nonneg G z₀ x y hx hy hm hw
  alpha_nonneg := d8ExtractedAlpha_nonneg G z₀ x y hx hy hm hw
  beta_nonneg := fun e _ ↦ d8ExtractedBeta_nonneg G z₀ x y hx hy hw e
  total_le_two := d8ExtractedOrbitTotal_le_two
    G z₀ x y hx hy hxy w hm hsymm htotal
  betaIncident_le_one := hincident

lemma d8ExtractedSeparatedParameters_beta
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G)) (x y : A)
    (hx : x ≠ (z₀ : A)) (hy : y ≠ (z₀ : A)) (hxy : Gᶜ.Adj x y)
    (w : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ)
    (hm : 4 ≤ (universalVertices G).card)
    (hw : IsFractionalPacking
      (d8AugmentedDeletedGraph G (z₀ : A) x y hx hy) w)
    (hsymm : ∀ p : Equiv.Perm (d7RemainingUniversalVertices G (z₀ : A)),
      relabelWeight (d7ExtendUniversalPerm G (z₀ : A) p) w = w)
    (htotal) (hincident) (e : Sym2 (↑(nonUniversalVertices G))) :
    (d8ExtractedSeparatedParameters G z₀ x y hx hy hxy w hm hw hsymm
      htotal hincident).beta e = d8ExtractedBeta G z₀ x y hx hy w e := rfl

lemma d8ExtractedSeparatedParameters_alpha
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G)) (x y : A)
    (hx : x ≠ (z₀ : A)) (hy : y ≠ (z₀ : A)) (hxy : Gᶜ.Adj x y)
    (w : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ)
    (hm : 4 ≤ (universalVertices G).card)
    (hw : IsFractionalPacking
      (d8AugmentedDeletedGraph G (z₀ : A) x y hx hy) w)
    (hsymm : ∀ p : Equiv.Perm (d7RemainingUniversalVertices G (z₀ : A)),
      relabelWeight (d7ExtendUniversalPerm G (z₀ : A) p) w = w)
    (htotal) (hincident) (u : ↑(nonUniversalVertices G)) :
    (d8ExtractedSeparatedParameters G z₀ x y hx hy hxy w hm hw hsymm
      htotal hincident).alpha u = d8ExtractedAlpha G z₀ x y hx hy w hm u := rfl

lemma d8ExtractedSeparatedParameters_gamma
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G)) (x y : A)
    (hx : x ≠ (z₀ : A)) (hy : y ≠ (z₀ : A)) (hxy : Gᶜ.Adj x y)
    (w : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ)
    (hm : 4 ≤ (universalVertices G).card)
    (hw : IsFractionalPacking
      (d8AugmentedDeletedGraph G (z₀ : A) x y hx hy) w)
    (hsymm : ∀ p : Equiv.Perm (d7RemainingUniversalVertices G (z₀ : A)),
      relabelWeight (d7ExtendUniversalPerm G (z₀ : A) p) w = w)
    (htotal) (hincident) :
    (d8ExtractedSeparatedParameters G z₀ x y hx hy hxy w hm hw hsymm
      htotal hincident).gamma = d8ExtractedGamma G z₀ x y hx hy w hm := rfl

/-- The symmetric removed-triangle weighting itself supplies the local
`beta`-incidence hypothesis, by the half-bound on the augmented packing. -/
def d8ExtractedSeparatedParametersOfHalf
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G)) (x y : A)
    (hx : x ≠ (z₀ : A)) (hy : y ≠ (z₀ : A)) (hxy : Gᶜ.Adj x y)
    (w : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ)
    (hm : 4 ≤ (universalVertices G).card)
    (hw : IsFractionalPacking
      (d8AugmentedDeletedGraph G (z₀ : A) x y hx hy) w)
    (hhalf : IsHalfBounded
      (d8AugmentedDeletedGraph G (z₀ : A) x y hx hy) w)
    (hsymm : ∀ p : Equiv.Perm (d7RemainingUniversalVertices G (z₀ : A)),
      relabelWeight (d7ExtendUniversalPerm G (z₀ : A) p) w = w)
    (htotal : (∑ p ∈ (d7DeletedGraph G (z₀ : A)).edgeFinset,
      d8RemovedLoad G (z₀ : A) x y hx hy w p) ≤ 2) :
    D8SeparatedParameters G :=
  d8ExtractedSeparatedParameters G z₀ x y hx hy hxy w hm hw hsymm htotal
    (d8ExtractedBetaIncident_le_one G z₀ x y hx hy hxy hw hhalf)

/-- The induction packing on one augmented deletion supplies, without any
extra analytic hypothesis, both the stripped base packing and the complete
separated parameter package used by the D8 shortcut correction. -/
theorem exists_d8SeparatedParameters_and_strippedWeight {n : ℕ}
    (hcard : Fintype.card A = n) (hn : 14 ≤ n)
    (G : SimpleGraph A) (hexact : missingEdgeCount G = n)
    (z₀ : ↑(universalVertices G)) {x y : A}
    (hx : x ≠ (z₀ : A)) (hy : y ≠ (z₀ : A)) (hxy : Gᶜ.Adj x y)
    (hm : 4 ≤ (universalVertices G).card)
    (hstrong : AlmostCompleteStrongAt (n - 1)) :
    let K := d7DeletedGraph G (z₀ : A)
    let x' := d7DeletedVertex (z₀ : A) x hx
    let y' := d7DeletedVertex (z₀ : A) y hy
    let H := d8AugmentedDeletedGraph G (z₀ : A) x y hx hy
    ∃ w : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ,
    ∃ P : D8SeparatedParameters G,
      IsFractionalPacking H w ∧
      IsHalfBounded H w ∧
      fractionalUncoveredWeight H w ≤ 4 ∧
      (∀ p : Equiv.Perm (d7RemainingUniversalVertices G (z₀ : A)),
        relabelWeight (d7ExtendUniversalPerm G (z₀ : A) p) w = w) ∧
      IsFractionalPacking K (stripEdgeTriangles s(x', y') w) ∧
      IsHalfBounded K (stripEdgeTriangles s(x', y') w) ∧
      (∀ p ∈ K.edgeFinset,
        fractionalEdgeLoad K (stripEdgeTriangles s(x', y') w) p +
            augmentedOldResidual H w p +
            fractionalEdgeLoad H (edgeTrianglesPart s(x', y') w) p = 1) ∧
      (∑ p ∈ K.edgeFinset, augmentedOldResidual H w p) ≤ 4 ∧
      (∀ e, P.beta e = d8ExtractedBeta G z₀ x y hx hy w e) ∧
      (∀ u, P.alpha u = d8ExtractedAlpha G z₀ x y hx hy w hm u) ∧
      P.gamma = d8ExtractedGamma G z₀ x y hx hy w hm := by
  dsimp only
  obtain ⟨w, hwPack, hwHalf, hwUncovered, hsymm, hwStrip,
      hwStripHalf, hidentity, hresidual, hremoved⟩ :=
    exists_d8SymmetricAugmentedStrippedWeight
      hcard hn G hexact z₀ hx hy hxy hstrong
  let P := d8ExtractedSeparatedParametersOfHalf
    G z₀ x y hx hy hxy w hm hwPack hwHalf hsymm hremoved
  refine ⟨w, P, hwPack, hwHalf, hwUncovered, hsymm, hwStrip,
    hwStripHalf, hidentity, hresidual, ?_, ?_, ?_⟩
  · intro e
    rfl
  · intro u
    rfl
  · rfl

def D8SeparatedParameters.alphaMass {G : SimpleGraph A}
    (P : D8SeparatedParameters G) : ℝ :=
  (((universalVertices G).card : ℝ) - 1) * ∑ u, P.alpha u

def D8SeparatedParameters.betaMass {G : SimpleGraph A}
    (P : D8SeparatedParameters G) : ℝ :=
  ∑ e ∈ (G.induce
    (↑(nonUniversalVertices G) : Set A)).edgeFinset, P.beta e

def D8SeparatedParameters.betaIncident {G : SimpleGraph A}
    (P : D8SeparatedParameters G) (u : ↑(nonUniversalVertices G)) : ℝ :=
  ∑ e ∈ (G.induce
    (↑(nonUniversalVertices G) : Set A)).edgeFinset with
      (u : ↑(nonUniversalVertices G)) ∈ e.toFinset, P.beta e

lemma D8SeparatedParameters.alphaMass_nonneg {G : SimpleGraph A}
    (P : D8SeparatedParameters G) (hm : 1 ≤ (universalVertices G).card) :
    0 ≤ P.alphaMass := by
  unfold alphaMass
  exact mul_nonneg (sub_nonneg.mpr (by exact_mod_cast hm))
    (Finset.sum_nonneg fun u _ ↦ P.alpha_nonneg u)

lemma D8SeparatedParameters.betaMass_nonneg {G : SimpleGraph A}
    (P : D8SeparatedParameters G) : 0 ≤ P.betaMass := by
  unfold betaMass
  exact Finset.sum_nonneg fun e he ↦ P.beta_nonneg e he

lemma D8SeparatedParameters.gammaTerm_nonneg {G : SimpleGraph A}
    (P : D8SeparatedParameters G) (hm : 2 ≤ (universalVertices G).card) :
    0 ≤ ((((universalVertices G).card : ℝ) - 1) *
      (((universalVertices G).card : ℝ) - 2) / 2) * P.gamma := by
  have h₁ : 0 ≤ ((universalVertices G).card : ℝ) - 1 := by
    exact sub_nonneg.mpr (by exact_mod_cast (show 1 ≤ (universalVertices G).card by omega))
  have h₂ : 0 ≤ ((universalVertices G).card : ℝ) - 2 := by
    exact sub_nonneg.mpr (by exact_mod_cast hm)
  exact mul_nonneg (div_nonneg (mul_nonneg h₁ h₂) (by norm_num))
    P.gamma_nonneg

lemma D8SeparatedParameters.alphaMass_add_betaMass_le_two
    {G : SimpleGraph A} (P : D8SeparatedParameters G)
    (hm : 2 ≤ (universalVertices G).card) :
    P.alphaMass + P.betaMass ≤ 2 := by
  have hgamma := P.gammaTerm_nonneg hm
  have htotal := P.total_le_two
  simpa only [D8SeparatedParameters.alphaMass,
    D8SeparatedParameters.betaMass] using (show
      P.alphaMass + P.betaMass ≤ 2 by
        dsimp only [D8SeparatedParameters.alphaMass,
          D8SeparatedParameters.betaMass]
        linarith)

lemma D8SeparatedParameters.betaIncident_nonneg
    {G : SimpleGraph A} (P : D8SeparatedParameters G)
    (u : ↑(nonUniversalVertices G)) : 0 ≤ P.betaIncident u := by
  unfold betaIncident
  exact Finset.sum_nonneg fun e he ↦ P.beta_nonneg e (mem_filter.mp he).1

lemma D8SeparatedParameters.betaIncident_le_one'
    {G : SimpleGraph A} (P : D8SeparatedParameters G)
    (u : ↑(nonUniversalVertices G)) : P.betaIncident u ≤ 1 := by
  exact P.betaIncident_le_one u

/-- The UZZ coefficient in the explicit D8 shortcut correction. -/
def D8SeparatedParameters.shortcutMixedCoefficient
    {G : SimpleGraph A} (P : D8SeparatedParameters G)
    (u : ↑(nonUniversalVertices G)) : ℝ :=
  (1 + (((universalVertices G).card : ℝ) - 1) * P.alpha u -
      P.betaIncident u) /
    (((universalVertices G).card : ℝ) - 1)

lemma D8SeparatedParameters.shortcutMixedCoefficient_nonneg
    {G : SimpleGraph A} (P : D8SeparatedParameters G)
    (hm : 4 ≤ (universalVertices G).card)
    (u : ↑(nonUniversalVertices G)) :
    0 ≤ P.shortcutMixedCoefficient u := by
  unfold shortcutMixedCoefficient
  have hden : 0 ≤ ((universalVertices G).card : ℝ) - 1 := by
    exact sub_nonneg.mpr (by exact_mod_cast (show 1 ≤ (universalVertices G).card by omega))
  apply div_nonneg
  · have hinc := P.betaIncident_le_one' u
    have halpha := P.alpha_nonneg u
    have hmR : 0 ≤ ((universalVertices G).card : ℝ) - 1 := hden
    nlinarith
  · exact hden

/-- The ZZZ coefficient in the explicit D8 shortcut correction. -/
def D8SeparatedParameters.shortcutUniversalCoefficient
    {G : SimpleGraph A} (P : D8SeparatedParameters G) : ℝ :=
  (2 + (((universalVertices G).card : ℝ) - 2) * P.gamma -
      ((Fintype.card A : ℝ) - (universalVertices G).card) /
        (((universalVertices G).card : ℝ) - 1) -
      P.alphaMass / (((universalVertices G).card : ℝ) - 1) +
      2 * P.betaMass / (((universalVertices G).card : ℝ) - 1)) /
    (((universalVertices G).card : ℝ) - 2)

/-- Inequality (5.15): the shortcut condition makes the only delicate ZZZ
coefficient nonnegative. -/
lemma D8SeparatedParameters.shortcutUniversalCoefficient_nonneg
    {G : SimpleGraph A} (P : D8SeparatedParameters G)
    (hm : 4 ≤ (universalVertices G).card)
    (hshortcut : (Fintype.card A : ℝ) + 4 - 3 * P.betaMass ≤
      3 * ((universalVertices G).card : ℝ)) :
    0 ≤ P.shortcutUniversalCoefficient := by
  let m : ℝ := ((universalVertices G).card : ℝ)
  let q : ℝ := Fintype.card A
  let alpha : ℝ := P.alphaMass
  let beta : ℝ := P.betaMass
  have hm₁ : 0 < m - 1 := by
    dsimp only [m]
    exact sub_pos.mpr (by exact_mod_cast (show 1 < (universalVertices G).card by omega))
  have hm₂ : 0 < m - 2 := by
    dsimp only [m]
    exact sub_pos.mpr (by exact_mod_cast (show 2 < (universalVertices G).card by omega))
  have hab : alpha + beta ≤ 2 := by
    exact P.alphaMass_add_betaMass_le_two (by omega)
  have hgamma : 0 ≤ P.gamma := P.gamma_nonneg
  have hbase : 0 ≤ 2 * (m - 1) - (q - m) - alpha + 2 * beta := by
    change q + 4 - 3 * beta ≤ 3 * m at hshortcut
    nlinarith
  let numerator : ℝ :=
    2 + (m - 2) * P.gamma - (q - m) / (m - 1) -
      alpha / (m - 1) + 2 * beta / (m - 1)
  have heq : (m - 1) * numerator =
      2 * (m - 1) + (m - 1) * (m - 2) * P.gamma -
        (q - m) - alpha + 2 * beta := by
    dsimp only [numerator]
    field_simp [ne_of_gt hm₁]
  have hnum : 0 ≤ numerator := by
    apply nonneg_of_mul_nonneg_right (a := m - 1)
    · rw [heq]
      have hgammaTerm : 0 ≤ (m - 1) * (m - 2) * P.gamma :=
        mul_nonneg (mul_nonneg hm₁.le hm₂.le) hgamma
      linarith
    · exact hm₁
  unfold shortcutUniversalCoefficient
  change 0 ≤ numerator / (m - 2)
  exact div_nonneg hnum hm₂.le

/-! ### The explicit shortcut correction -/

def d8UUZCorrection (G : SimpleGraph A) (P : D8SeparatedParameters G) :
    Finset A → ℝ :=
  fun t ↦ ∑ z : ↑(universalVertices G),
    weightedAttachedEdgeWeight (nonUniversalVertices G) (z : A)
      (G.induce (↑(nonUniversalVertices G) : Set A)).edgeFinset P.beta t

lemma d8UUZCorrection_nonneg (G : SimpleGraph A)
    (P : D8SeparatedParameters G) :
    ∀ t ∈ G.cliqueFinset 3, 0 ≤ d8UUZCorrection G P t := by
  intro t ht
  unfold d8UUZCorrection
  exact Finset.sum_nonneg fun z _ ↦
    weightedAttachedEdgeWeight_nonneg P.beta_nonneg t ht

lemma fractionalEdgeLoad_d8UUZCorrection (G : SimpleGraph A)
    (P : D8SeparatedParameters G) (p : Sym2 A) :
    fractionalEdgeLoad G (d8UUZCorrection G P) p =
      ∑ z : ↑(universalVertices G),
        ∑ e : ↑((G.induce
          (↑(nonUniversalVertices G) : Set A)).edgeFinset),
          if p ∈ (attachedEdgeTriangle (nonUniversalVertices G) (z : A) e).sym2
          then P.beta e else 0 := by
  unfold d8UUZCorrection
  rw [fractionalEdgeLoad_sum]
  apply Finset.sum_congr rfl
  intro z _
  exact fractionalEdgeLoad_weightedAttachedEdgeWeight
    (fun e he ↦ d7UUZTriangle_mem_cliqueFinset G z ⟨e, he⟩) p

lemma fractionalEdgeLoad_d8UUZCorrection_induced
    (G : SimpleGraph A) (P : D8SeparatedParameters G)
    (e : Sym2 (↑(nonUniversalVertices G)))
    (he : e ∈ (G.induce
      (↑(nonUniversalVertices G) : Set A)).edgeFinset) :
    fractionalEdgeLoad G (d8UUZCorrection G P)
        ((inducedEmbedding (nonUniversalVertices G)).sym2Map e) =
      ((universalVertices G).card : ℝ) * P.beta e := by
  unfold d8UUZCorrection
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

lemma fractionalEdgeLoad_d8UUZCorrection_mixed
    (G : SimpleGraph A) (P : D8SeparatedParameters G)
    (z : ↑(universalVertices G)) (u : ↑(nonUniversalVertices G)) :
    fractionalEdgeLoad G (d8UUZCorrection G P) s((z : A), (u : A)) =
      P.betaIncident u := by
  unfold d8UUZCorrection
  rw [fractionalEdgeLoad_sum]
  rw [Fintype.sum_eq_single z]
  · rw [fractionalEdgeLoad_weightedAttachedEdgeWeight_star
      (G := G) (universalVertex_not_mem_nonUniversalVertices G z.property)
      (fun f hf ↦ d7UUZTriangle_mem_cliqueFinset G z ⟨f, hf⟩) u]
    unfold D8SeparatedParameters.betaIncident
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

lemma fractionalEdgeLoad_d8UUZCorrection_universal
    (G : SimpleGraph A) (P : D8SeparatedParameters G)
    (e : Sym2 (↑(universalVertices G))) (heND : ¬e.IsDiag) :
    fractionalEdgeLoad G (d8UUZCorrection G P)
        ((inducedEmbedding (universalVertices G)).sym2Map e) = 0 := by
  induction e using Sym2.inductionOn with
  | hf z y =>
      simp only [Sym2.mk_isDiag_iff] at heND
      rw [fractionalEdgeLoad_d8UUZCorrection]
      apply Fintype.sum_eq_zero
      intro v
      apply Fintype.sum_eq_zero
      intro f
      rw [if_neg]
      exact outsidePair_not_mem_attachedEdgeTriangle
        (universalVertex_not_mem_nonUniversalVertices G z.property)
        (universalVertex_not_mem_nonUniversalVertices G y.property)
        (fun h ↦ heND (Subtype.ext h)) f

def d8UZZCorrection (G : SimpleGraph A) (P : D8SeparatedParameters G) :
    Finset A → ℝ :=
  fun t ↦ ∑ u : ↑(nonUniversalVertices G),
    weightedAttachedEdgeWeight (universalVertices G) (u : A)
      ((⊤ : SimpleGraph (↑(universalVertices G))).edgeFinset)
      (fun _ ↦ P.shortcutMixedCoefficient u) t

lemma d8UZZCorrection_nonneg (G : SimpleGraph A)
    (P : D8SeparatedParameters G)
    (hm : 4 ≤ (universalVertices G).card) :
    ∀ t ∈ G.cliqueFinset 3, 0 ≤ d8UZZCorrection G P t := by
  intro t ht
  unfold d8UZZCorrection
  exact Finset.sum_nonneg fun u _ ↦
    weightedAttachedEdgeWeight_nonneg
      (fun _ _ ↦ P.shortcutMixedCoefficient_nonneg hm u) t ht

lemma fractionalEdgeLoad_d8UZZCorrection (G : SimpleGraph A)
    (P : D8SeparatedParameters G) (p : Sym2 A) :
    fractionalEdgeLoad G (d8UZZCorrection G P) p =
      ∑ u : ↑(nonUniversalVertices G),
        ∑ e : ↑((⊤ : SimpleGraph
          (↑(universalVertices G))).edgeFinset),
          if p ∈ (attachedEdgeTriangle (universalVertices G) (u : A) e).sym2
          then P.shortcutMixedCoefficient u else 0 := by
  unfold d8UZZCorrection
  rw [fractionalEdgeLoad_sum]
  apply Finset.sum_congr rfl
  intro u _
  exact fractionalEdgeLoad_weightedAttachedEdgeWeight
    (fun e he ↦ d7UZZTriangle_mem_cliqueFinset G u ⟨e, he⟩) p

lemma fractionalEdgeLoad_d8UZZCorrection_induced
    (G : SimpleGraph A) (P : D8SeparatedParameters G)
    (e : Sym2 (↑(universalVertices G)))
    (he : e ∈ (⊤ : SimpleGraph (↑(universalVertices G))).edgeFinset) :
    fractionalEdgeLoad G (d8UZZCorrection G P)
        ((inducedEmbedding (universalVertices G)).sym2Map e) =
      ∑ u : ↑(nonUniversalVertices G), P.shortcutMixedCoefficient u := by
  unfold d8UZZCorrection
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

lemma fractionalEdgeLoad_d8UZZCorrection_mixed
    (G : SimpleGraph A) (P : D8SeparatedParameters G)
    (u : ↑(nonUniversalVertices G)) (z : ↑(universalVertices G)) :
    fractionalEdgeLoad G (d8UZZCorrection G P) s((u : A), (z : A)) =
      (((universalVertices G).card : ℝ) - 1) *
        P.shortcutMixedCoefficient u := by
  unfold d8UZZCorrection
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

lemma fractionalEdgeLoad_d8UZZCorrection_nonUniversal
    (G : SimpleGraph A) (P : D8SeparatedParameters G)
    (e : Sym2 (↑(nonUniversalVertices G))) (heND : ¬e.IsDiag) :
    fractionalEdgeLoad G (d8UZZCorrection G P)
        ((inducedEmbedding (nonUniversalVertices G)).sym2Map e) = 0 := by
  induction e using Sym2.inductionOn with
  | hf u v =>
      simp only [Sym2.mk_isDiag_iff] at heND
      rw [fractionalEdgeLoad_d8UZZCorrection]
      apply Fintype.sum_eq_zero
      intro x
      apply Fintype.sum_eq_zero
      intro f
      rw [if_neg]
      exact outsidePair_not_mem_attachedEdgeTriangle
        (nonUniversalVertex_not_mem_universalVertices G u.property)
        (nonUniversalVertex_not_mem_universalVertices G v.property)
        (fun h ↦ heND (Subtype.ext h)) f

def d8ZZZCorrection (G : SimpleGraph A) (P : D8SeparatedParameters G) :
    Finset A → ℝ :=
  fun t ↦ ∑ q : ↑((universalVertices G).powersetCard 3),
    singleTriangleWeight q P.shortcutUniversalCoefficient t

lemma d8ZZZCorrection_nonneg (G : SimpleGraph A)
    (P : D8SeparatedParameters G)
    (hcoeff : 0 ≤ P.shortcutUniversalCoefficient) :
    ∀ t ∈ G.cliqueFinset 3, 0 ≤ d8ZZZCorrection G P t := by
  intro t _
  unfold d8ZZZCorrection singleTriangleWeight
  exact Finset.sum_nonneg fun q _ ↦ by
    split_ifs
    · exact hcoeff
    · exact le_rfl

lemma fractionalEdgeLoad_d8ZZZCorrection (G : SimpleGraph A)
    (P : D8SeparatedParameters G) (p : Sym2 A) :
    fractionalEdgeLoad G (d8ZZZCorrection G P) p =
      ∑ q : ↑((universalVertices G).powersetCard 3),
        if p ∈ (q : Finset A).sym2 then P.shortcutUniversalCoefficient else 0 := by
  unfold d8ZZZCorrection
  rw [fractionalEdgeLoad_sum]
  apply Finset.sum_congr rfl
  intro q _
  exact fractionalEdgeLoad_singleTriangle
    (d7ZZZTriangle_mem_cliqueFinset G q) P.shortcutUniversalCoefficient p

lemma fractionalEdgeLoad_d8ZZZCorrection_induced
    (G : SimpleGraph A) (P : D8SeparatedParameters G)
    (e : Sym2 (↑(universalVertices G))) (heND : ¬e.IsDiag) :
    fractionalEdgeLoad G (d8ZZZCorrection G P)
        ((inducedEmbedding (universalVertices G)).sym2Map e) =
      (((universalVertices G).card : ℝ) - 2) *
        P.shortcutUniversalCoefficient := by
  rw [fractionalEdgeLoad_d8ZZZCorrection]
  calc
    (∑ q : ↑((universalVertices G).powersetCard 3),
        if (inducedEmbedding (universalVertices G)).sym2Map e ∈
          (q : Finset A).sym2
        then P.shortcutUniversalCoefficient else 0) =
        ∑ q ∈ (universalVertices G).powersetCard 3,
          if (inducedEmbedding (universalVertices G)).sym2Map e ∈ q.sym2
          then P.shortcutUniversalCoefficient else 0 :=
      (Finset.sum_subtype ((universalVertices G).powersetCard 3)
        (fun _ ↦ Iff.rfl)
        (fun q ↦ if (inducedEmbedding
          (universalVertices G)).sym2Map e ∈ q.sym2
          then P.shortcutUniversalCoefficient else 0)).symm
    _ = ∑ q ∈ ((universalVertices G).powersetCard 3).filter
          (fun q ↦ (inducedEmbedding
            (universalVertices G)).sym2Map e ∈ q.sym2),
          P.shortcutUniversalCoefficient := by rw [Finset.sum_filter]
    _ = (((universalVertices G).card : ℝ) - 2) *
          P.shortcutUniversalCoefficient := by
      rw [Finset.sum_const,
        card_universal_triangles_through_induced_edge G e heND]
      simp only [nsmul_eq_mul]
      have hm : 2 ≤ (universalVertices G).card := by
        have hcard := Sym2.card_toFinset_of_not_isDiag e heND
        have hle := Finset.card_le_card (Finset.subset_univ e.toFinset)
        rw [hcard] at hle
        simpa only [Finset.card_univ, Fintype.card_coe] using hle
      rw [Nat.cast_sub hm, Nat.cast_ofNat]

lemma fractionalEdgeLoad_d8ZZZCorrection_nonUniversal_left
    (G : SimpleGraph A) (P : D8SeparatedParameters G)
    (u : ↑(nonUniversalVertices G)) (x : A) :
    fractionalEdgeLoad G (d8ZZZCorrection G P) s((u : A), x) = 0 := by
  rw [fractionalEdgeLoad_d8ZZZCorrection]
  apply Fintype.sum_eq_zero
  intro q
  rw [if_neg]
  have hqsub := (Finset.mem_powersetCard.mp q.property).1
  have huq : (u : A) ∉ (q : Finset A) := by
    intro hu
    exact nonUniversalVertex_not_mem_universalVertices G u.property (hqsub hu)
  simpa only [Finset.mk_mem_sym2_iff, not_and_or] using
    (Or.inl huq : (u : A) ∉ (q : Finset A) ∨ x ∉ (q : Finset A))

lemma fractionalEdgeLoad_d8ZZZCorrection_nonUniversal
    (G : SimpleGraph A) (P : D8SeparatedParameters G)
    (e : Sym2 (↑(nonUniversalVertices G))) :
    fractionalEdgeLoad G (d8ZZZCorrection G P)
        ((inducedEmbedding (nonUniversalVertices G)).sym2Map e) = 0 := by
  induction e using Sym2.inductionOn with
  | hf u v =>
      exact fractionalEdgeLoad_d8ZZZCorrection_nonUniversal_left G P u v

def d8ShortcutCorrection (G : SimpleGraph A) (P : D8SeparatedParameters G) :
    Finset A → ℝ :=
  fun t ↦ d8UUZCorrection G P t + d8UZZCorrection G P t +
    d8ZZZCorrection G P t

lemma d8ShortcutCorrection_nonneg (G : SimpleGraph A)
    (P : D8SeparatedParameters G)
    (hm : 4 ≤ (universalVertices G).card)
    (hshortcut : (Fintype.card A : ℝ) + 4 - 3 * P.betaMass ≤
      3 * ((universalVertices G).card : ℝ)) :
    ∀ t ∈ G.cliqueFinset 3, 0 ≤ d8ShortcutCorrection G P t := by
  intro t ht
  unfold d8ShortcutCorrection
  exact add_nonneg (add_nonneg (d8UUZCorrection_nonneg G P t ht)
    (d8UZZCorrection_nonneg G P hm t ht))
    (d8ZZZCorrection_nonneg G P
      (P.shortcutUniversalCoefficient_nonneg hm hshortcut) t ht)

lemma fractionalEdgeLoad_d8ShortcutCorrection (G : SimpleGraph A)
    (P : D8SeparatedParameters G) (p : Sym2 A) :
    fractionalEdgeLoad G (d8ShortcutCorrection G P) p =
      fractionalEdgeLoad G (d8UUZCorrection G P) p +
        fractionalEdgeLoad G (d8UZZCorrection G P) p +
        fractionalEdgeLoad G (d8ZZZCorrection G P) p := by
  unfold d8ShortcutCorrection
  rw [fractionalEdgeLoad_add, fractionalEdgeLoad_add]

lemma fractionalEdgeLoad_d8ShortcutCorrection_nonUniversal
    (G : SimpleGraph A) (P : D8SeparatedParameters G)
    (e : Sym2 (↑(nonUniversalVertices G)))
    (he : e ∈ (G.induce
      (↑(nonUniversalVertices G) : Set A)).edgeFinset) :
    fractionalEdgeLoad G (d8ShortcutCorrection G P)
        ((inducedEmbedding (nonUniversalVertices G)).sym2Map e) =
      ((universalVertices G).card : ℝ) * P.beta e := by
  rw [fractionalEdgeLoad_d8ShortcutCorrection,
    fractionalEdgeLoad_d8UUZCorrection_induced G P e he,
    fractionalEdgeLoad_d8UZZCorrection_nonUniversal G P e
      ((G.induce (↑(nonUniversalVertices G) : Set A)).not_isDiag_of_mem_edgeFinset he),
    fractionalEdgeLoad_d8ZZZCorrection_nonUniversal G P e]
  ring

lemma fractionalEdgeLoad_d8ShortcutCorrection_mixed
    (G : SimpleGraph A) (P : D8SeparatedParameters G)
    (hm : 4 ≤ (universalVertices G).card)
    (u : ↑(nonUniversalVertices G)) (z : ↑(universalVertices G)) :
    fractionalEdgeLoad G (d8ShortcutCorrection G P) s((u : A), (z : A)) =
      1 + (((universalVertices G).card : ℝ) - 1) * P.alpha u := by
  rw [fractionalEdgeLoad_d8ShortcutCorrection]
  have hUUZ := fractionalEdgeLoad_d8UUZCorrection_mixed G P z u
  rw [Sym2.eq_swap] at hUUZ
  rw [hUUZ, fractionalEdgeLoad_d8UZZCorrection_mixed G P u z,
    fractionalEdgeLoad_d8ZZZCorrection_nonUniversal_left G P u z]
  unfold D8SeparatedParameters.shortcutMixedCoefficient
  have hden : ((universalVertices G).card : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < ((universalVertices G).card : ℝ) := by
      exact_mod_cast (by omega : 1 < (universalVertices G).card)
    linarith
  field_simp [hden]
  ring

lemma fractionalEdgeLoad_d8ShortcutCorrection_universal
    (G : SimpleGraph A) (P : D8SeparatedParameters G)
    (e : Sym2 (↑(universalVertices G)))
    (he : e ∈ (⊤ : SimpleGraph (↑(universalVertices G))).edgeFinset) :
    fractionalEdgeLoad G (d8ShortcutCorrection G P)
        ((inducedEmbedding (universalVertices G)).sym2Map e) =
      (∑ u : ↑(nonUniversalVertices G), P.shortcutMixedCoefficient u) +
        (((universalVertices G).card : ℝ) - 2) *
          P.shortcutUniversalCoefficient := by
  have heND : ¬e.IsDiag :=
    (⊤ : SimpleGraph (↑(universalVertices G))).not_isDiag_of_mem_edgeFinset he
  rw [fractionalEdgeLoad_d8ShortcutCorrection,
    fractionalEdgeLoad_d8UUZCorrection_universal G P e heND,
    fractionalEdgeLoad_d8UZZCorrection_induced G P e he,
    fractionalEdgeLoad_d8ZZZCorrection_induced G P e heND]
  ring

lemma D8SeparatedParameters.sum_betaIncident_eq_two_betaMass
    {G : SimpleGraph A} (P : D8SeparatedParameters G) :
    (∑ u : ↑(nonUniversalVertices G), P.betaIncident u) =
      2 * P.betaMass := by
  unfold D8SeparatedParameters.betaIncident D8SeparatedParameters.betaMass
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

lemma D8SeparatedParameters.sum_shortcutMixedCoefficient
    {G : SimpleGraph A} (P : D8SeparatedParameters G) :
    (∑ u : ↑(nonUniversalVertices G), P.shortcutMixedCoefficient u) =
      (((Fintype.card A : ℝ) - (universalVertices G).card) +
        P.alphaMass - 2 * P.betaMass) /
        (((universalVertices G).card : ℝ) - 1) := by
  unfold D8SeparatedParameters.shortcutMixedCoefficient
  rw [← Finset.sum_div]
  congr 1
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  simp only [Finset.sum_const, nsmul_eq_mul, Finset.mul_sum]
  rw [P.sum_betaIncident_eq_two_betaMass]
  unfold D8SeparatedParameters.alphaMass
  have hpart := card_nonUniversalVertices_add_card_universalVertices G
  have hpartR : ((nonUniversalVertices G).card : ℝ) +
      ((universalVertices G).card : ℝ) = (Fintype.card A : ℝ) := by
    exact_mod_cast hpart
  simp only [Finset.card_univ, Fintype.card_coe]
  rw [← Finset.mul_sum]
  ring_nf at ⊢
  linarith

lemma fractionalEdgeLoad_d8ShortcutCorrection_universal_simplified
    (G : SimpleGraph A) (P : D8SeparatedParameters G)
    (hm : 4 ≤ (universalVertices G).card)
    (e : Sym2 (↑(universalVertices G)))
    (he : e ∈ (⊤ : SimpleGraph (↑(universalVertices G))).edgeFinset) :
    fractionalEdgeLoad G (d8ShortcutCorrection G P)
        ((inducedEmbedding (universalVertices G)).sym2Map e) =
      2 + (((universalVertices G).card : ℝ) - 2) * P.gamma := by
  rw [fractionalEdgeLoad_d8ShortcutCorrection_universal G P e he,
    P.sum_shortcutMixedCoefficient]
  unfold D8SeparatedParameters.shortcutUniversalCoefficient
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

/-! ## Coherent transport of the D8 augmented packing -/

lemma d8MissingLeft_ne_universal (G : SimpleGraph A) {x y : A}
    (hxy : Gᶜ.Adj x y) (z : ↑(universalVertices G)) :
    x ≠ (z : A) := by
  intro hxz
  have hpos := hxy.degree_pos_left
  have hzdeg := mem_universalVertices.mp z.property
  rw [hxz, hzdeg] at hpos
  omega

lemma d8MissingRight_ne_universal (G : SimpleGraph A) {x y : A}
    (hxy : Gᶜ.Adj x y) (z : ↑(universalVertices G)) :
    y ≠ (z : A) := by
  exact d8MissingLeft_ne_universal G hxy.symm z

lemma d8AugmentedDeletedGraph_map_d7DeletedSwapEquiv
    (G : SimpleGraph A) (z₀ z : ↑(universalVertices G)) {x y : A}
    (hxy : Gᶜ.Adj x y) :
    (d8AugmentedDeletedGraph G (z₀ : A) x y
        (d8MissingLeft_ne_universal G hxy z₀)
        (d8MissingRight_ne_universal G hxy z₀)).map
        (d7DeletedSwapEquiv (z₀ : A) (z : A)).toEmbedding =
      d8AugmentedDeletedGraph G (z : A) x y
        (d8MissingLeft_ne_universal G hxy z)
        (d8MissingRight_ne_universal G hxy z) := by
  let q := d7DeletedSwapEquiv (z₀ : A) (z : A)
  let K₀ := d7DeletedGraph G (z₀ : A)
  let K := d7DeletedGraph G (z : A)
  let x₀ := d7DeletedVertex (z₀ : A) x
    (d8MissingLeft_ne_universal G hxy z₀)
  let y₀ := d7DeletedVertex (z₀ : A) y
    (d8MissingRight_ne_universal G hxy z₀)
  let x' := d7DeletedVertex (z : A) x
    (d8MissingLeft_ne_universal G hxy z)
  let y' := d7DeletedVertex (z : A) y
    (d8MissingRight_ne_universal G hxy z)
  have hqx : q x₀ = x' := by
    apply Subtype.ext
    simp only [q, x₀, x', d7DeletedSwapEquiv_apply_val,
      d7DeletedVertex_val]
    exact Equiv.swap_apply_of_ne_of_ne
      (d8MissingLeft_ne_universal G hxy z₀)
      (d8MissingLeft_ne_universal G hxy z)
  have hqy : q y₀ = y' := by
    apply Subtype.ext
    simp only [q, y₀, y', d7DeletedSwapEquiv_apply_val,
      d7DeletedVertex_val]
    exact Equiv.swap_apply_of_ne_of_ne
      (d8MissingRight_ne_universal G hxy z₀)
      (d8MissingRight_ne_universal G hxy z)
  have hqx' : q.symm x' = x₀ := by
    apply Subtype.ext
    simp only [q, x₀, x', d7DeletedSwapEquiv_symm_apply_val,
      d7DeletedVertex_val]
    exact Equiv.swap_apply_of_ne_of_ne
      (d8MissingLeft_ne_universal G hxy z₀)
      (d8MissingLeft_ne_universal G hxy z)
  have hqy' : q.symm y' = y₀ := by
    apply Subtype.ext
    simp only [q, y₀, y', d7DeletedSwapEquiv_symm_apply_val,
      d7DeletedVertex_val]
    exact Equiv.swap_apply_of_ne_of_ne
      (d8MissingRight_ne_universal G hxy z₀)
      (d8MissingRight_ne_universal G hxy z)
  have hKmap := d7DeletedGraph_map_d7DeletedSwapEquiv
    G z₀.property z.property
  rw [← SimpleGraph.comap_symm K₀ q] at hKmap
  rw [← SimpleGraph.comap_symm
    (d8AugmentedDeletedGraph G (z₀ : A) x y
      (d8MissingLeft_ne_universal G hxy z₀)
      (d8MissingRight_ne_universal G hxy z₀)) q]
  ext u v
  have hKadj : K₀.Adj (q.symm u) (q.symm v) = K.Adj u v := by
    have hadj := congrFun (congrFun (SimpleGraph.ext_iff.mp hKmap) u) v
    exact hadj
  change (addPair K₀ x₀ y₀).Adj (q.symm u) (q.symm v) ↔
    (addPair K x' y').Adj u v
  rw [addPair_adj, addPair_adj, hKadj]
  have hpair : s(q.symm u, q.symm v) = s(x₀, y₀) ↔
      s(u, v) = s(x', y') := by
    constructor
    · intro h
      have hm := congrArg (Sym2.map q) h
      simpa only [Sym2.map_mk, Equiv.apply_symm_apply, hqx, hqy] using hm
    · intro h
      have hm := congrArg (Sym2.map q.symm) h
      simpa only [Sym2.map_mk, hqx', hqy'] using hm
  have hne : q.symm u ≠ q.symm v ↔ u ≠ v :=
    not_congr q.symm.injective.eq_iff
  rw [hpair, hne]

def d8CoherentAugmentedWeight (G : SimpleGraph A)
    (z₀ : ↑(universalVertices G))
    (w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ)
    (z : ↑(universalVertices G)) :
    Finset (↑(d7DeletedFinset (A := A) (z : A))) → ℝ :=
  d7TransportDeletedWeight (z₀ : A) (z : A) w₀

lemma d8CoherentAugmentedWeight_isFractionalPacking
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G)) {x y : A}
    (hxy : Gᶜ.Adj x y)
    {w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ}
    (hw₀ : IsFractionalPacking
      (d8AugmentedDeletedGraph G (z₀ : A) x y
        (d8MissingLeft_ne_universal G hxy z₀)
        (d8MissingRight_ne_universal G hxy z₀)) w₀)
    (z : ↑(universalVertices G)) :
    IsFractionalPacking
      (d8AugmentedDeletedGraph G (z : A) x y
        (d8MissingLeft_ne_universal G hxy z)
        (d8MissingRight_ne_universal G hxy z))
      (d8CoherentAugmentedWeight G z₀ w₀ z) := by
  have h := hw₀.relabel (d7DeletedSwapEquiv (z₀ : A) (z : A))
  rwa [d8AugmentedDeletedGraph_map_d7DeletedSwapEquiv G z₀ z hxy] at h

lemma d8CoherentAugmentedWeight_halfBounded
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G)) {x y : A}
    (hxy : Gᶜ.Adj x y)
    {w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ}
    (hw₀ : IsHalfBounded
      (d8AugmentedDeletedGraph G (z₀ : A) x y
        (d8MissingLeft_ne_universal G hxy z₀)
        (d8MissingRight_ne_universal G hxy z₀)) w₀)
    (z : ↑(universalVertices G)) :
    IsHalfBounded
      (d8AugmentedDeletedGraph G (z : A) x y
        (d8MissingLeft_ne_universal G hxy z)
        (d8MissingRight_ne_universal G hxy z))
      (d8CoherentAugmentedWeight G z₀ w₀ z) := by
  have h := hw₀.relabel (d7DeletedSwapEquiv (z₀ : A) (z : A))
  rwa [d8AugmentedDeletedGraph_map_d7DeletedSwapEquiv G z₀ z hxy] at h

lemma fractionalUncoveredWeight_d8CoherentAugmentedWeight
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G)) {x y : A}
    (hxy : Gᶜ.Adj x y)
    (w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ)
    (z : ↑(universalVertices G)) :
    fractionalUncoveredWeight
      (d8AugmentedDeletedGraph G (z : A) x y
        (d8MissingLeft_ne_universal G hxy z)
        (d8MissingRight_ne_universal G hxy z))
      (d8CoherentAugmentedWeight G z₀ w₀ z) =
    fractionalUncoveredWeight
      (d8AugmentedDeletedGraph G (z₀ : A) x y
        (d8MissingLeft_ne_universal G hxy z₀)
        (d8MissingRight_ne_universal G hxy z₀)) w₀ := by
  have h := fractionalUncoveredWeight_relabel_general
    (d8AugmentedDeletedGraph G (z₀ : A) x y
      (d8MissingLeft_ne_universal G hxy z₀)
      (d8MissingRight_ne_universal G hxy z₀))
    (d7DeletedSwapEquiv (z₀ : A) (z : A)) w₀
  rwa [d8AugmentedDeletedGraph_map_d7DeletedSwapEquiv G z₀ z hxy] at h

lemma d7DeletedSwapEquiv_map_d8AddedPair
    (G : SimpleGraph A) (z₀ z : ↑(universalVertices G)) {x y : A}
    (hxy : Gᶜ.Adj x y) :
    (d7DeletedSwapEquiv (z₀ : A) (z : A)).toEmbedding.sym2Map
        s(d7DeletedVertex (z₀ : A) x
            (d8MissingLeft_ne_universal G hxy z₀),
          d7DeletedVertex (z₀ : A) y
            (d8MissingRight_ne_universal G hxy z₀)) =
      s(d7DeletedVertex (z : A) x
          (d8MissingLeft_ne_universal G hxy z),
        d7DeletedVertex (z : A) y
          (d8MissingRight_ne_universal G hxy z)) := by
  change Sym2.map (d7DeletedSwapEquiv (z₀ : A) (z : A)) s(_, _) = _
  rw [Sym2.map_mk]
  congr 1
  · apply Subtype.ext
    simp only [d7DeletedSwapEquiv_apply_val, d7DeletedVertex_val]
    exact Equiv.swap_apply_of_ne_of_ne
      (d8MissingLeft_ne_universal G hxy z₀)
      (d8MissingLeft_ne_universal G hxy z)
  · apply Subtype.ext
    simp only [d7DeletedSwapEquiv_apply_val, d7DeletedVertex_val]
    exact Equiv.swap_apply_of_ne_of_ne
      (d8MissingRight_ne_universal G hxy z₀)
      (d8MissingRight_ne_universal G hxy z)

lemma d8RemovedLoad_d8CoherentAugmentedWeight
    (G : SimpleGraph A) (z₀ z : ↑(universalVertices G)) {x y : A}
    (hxy : Gᶜ.Adj x y)
    (w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ)
    (e : Sym2 (↑(d7DeletedFinset (A := A) (z₀ : A)))) :
    d8RemovedLoad G (z : A) x y
        (d8MissingLeft_ne_universal G hxy z)
        (d8MissingRight_ne_universal G hxy z)
        (d8CoherentAugmentedWeight G z₀ w₀ z)
        ((d7DeletedSwapEquiv (z₀ : A) (z : A)).toEmbedding.sym2Map e) =
      d8RemovedLoad G (z₀ : A) x y
        (d8MissingLeft_ne_universal G hxy z₀)
        (d8MissingRight_ne_universal G hxy z₀) w₀ e := by
  have h := fractionalEdgeLoad_relabel
    (d8AugmentedDeletedGraph G (z₀ : A) x y
      (d8MissingLeft_ne_universal G hxy z₀)
      (d8MissingRight_ne_universal G hxy z₀))
    (d7DeletedSwapEquiv (z₀ : A) (z : A))
    (edgeTrianglesPart
      s(d7DeletedVertex (z₀ : A) x
          (d8MissingLeft_ne_universal G hxy z₀),
        d7DeletedVertex (z₀ : A) y
          (d8MissingRight_ne_universal G hxy z₀)) w₀) e
  rw [d8AugmentedDeletedGraph_map_d7DeletedSwapEquiv G z₀ z hxy,
    relabelWeight_edgeTrianglesPart,
    d7DeletedSwapEquiv_map_d8AddedPair G z₀ z hxy] at h
  exact h

lemma d8RemovedLoad_coherent_eq
    (G : SimpleGraph A) (z₀ z : ↑(universalVertices G)) {a b x y : A}
    (hxy : Gᶜ.Adj x y)
    (w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ)
    (ha₀ : a ≠ (z₀ : A)) (haz : a ≠ (z : A))
    (hb₀ : b ≠ (z₀ : A)) (hbz : b ≠ (z : A)) :
    d8RemovedLoad G (z : A) x y
        (d8MissingLeft_ne_universal G hxy z)
        (d8MissingRight_ne_universal G hxy z)
        (d8CoherentAugmentedWeight G z₀ w₀ z)
        s(d7DeletedVertex (z : A) a haz,
          d7DeletedVertex (z : A) b hbz) =
      d8RemovedLoad G (z₀ : A) x y
        (d8MissingLeft_ne_universal G hxy z₀)
        (d8MissingRight_ne_universal G hxy z₀) w₀
        s(d7DeletedVertex (z₀ : A) a ha₀,
          d7DeletedVertex (z₀ : A) b hb₀) := by
  have hmap : (d7DeletedSwapEquiv (z₀ : A) (z : A)).toEmbedding.sym2Map
        s(d7DeletedVertex (z₀ : A) a ha₀,
          d7DeletedVertex (z₀ : A) b hb₀) =
      s(d7DeletedVertex (z : A) a haz,
        d7DeletedVertex (z : A) b hbz) := by
    change Sym2.map (d7DeletedSwapEquiv (z₀ : A) (z : A)) s(_, _) = _
    rw [Sym2.map_mk]
    congr 1
    · apply Subtype.ext
      simp only [d7DeletedSwapEquiv_apply_val, d7DeletedVertex_val]
      exact Equiv.swap_apply_of_ne_of_ne ha₀ haz
    · apply Subtype.ext
      simp only [d7DeletedSwapEquiv_apply_val, d7DeletedVertex_val]
      exact Equiv.swap_apply_of_ne_of_ne hb₀ hbz
  rw [← hmap,
    d8RemovedLoad_d8CoherentAugmentedWeight (hxy := hxy)]

lemma d7DeletedSwapEquiv_map_nonUniversalDeletedEdge
    (G : SimpleGraph A) (z₀ z : ↑(universalVertices G))
    (e : Sym2 (↑(nonUniversalVertices G))) :
    (d7DeletedSwapEquiv (z₀ : A) (z : A)).toEmbedding.sym2Map
        ((d7NonUniversalDeletedEmbedding G z₀).sym2Map e) =
      (d7NonUniversalDeletedEmbedding G z).sym2Map e := by
  induction e using Sym2.inductionOn with
  | hf u v =>
      change Sym2.map (d7DeletedSwapEquiv (z₀ : A) (z : A))
          s(d7NonUniversalDeletedEmbedding G z₀ u,
            d7NonUniversalDeletedEmbedding G z₀ v) = _
      rw [Sym2.map_mk]
      congr 1
      · apply Subtype.ext
        simp only [d7DeletedSwapEquiv_apply_val,
          d7NonUniversalDeletedEmbedding_val]
        apply Equiv.swap_apply_of_ne_of_ne
        · intro h
          exact nonUniversalVertex_not_mem_universalVertices G u.property
            (h ▸ z₀.property)
        · intro h
          exact nonUniversalVertex_not_mem_universalVertices G u.property
            (h ▸ z.property)
      · apply Subtype.ext
        simp only [d7DeletedSwapEquiv_apply_val,
          d7NonUniversalDeletedEmbedding_val]
        apply Equiv.swap_apply_of_ne_of_ne
        · intro h
          exact nonUniversalVertex_not_mem_universalVertices G v.property
            (h ▸ z₀.property)
        · intro h
          exact nonUniversalVertex_not_mem_universalVertices G v.property
            (h ▸ z.property)

lemma d8RemovedLoad_coherent_beta_eq_extracted
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G)) {x y : A}
    (hxy : Gᶜ.Adj x y)
    (w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ)
    (z : ↑(universalVertices G))
    (e : Sym2 (↑(nonUniversalVertices G))) :
    d8RemovedLoad G (z : A) x y
        (d8MissingLeft_ne_universal G hxy z)
        (d8MissingRight_ne_universal G hxy z)
        (d8CoherentAugmentedWeight G z₀ w₀ z)
        ((d7NonUniversalDeletedEmbedding G z).sym2Map e) =
      d8ExtractedBeta G z₀ x y
        (d8MissingLeft_ne_universal G hxy z₀)
        (d8MissingRight_ne_universal G hxy z₀) w₀ e := by
  rw [← d7DeletedSwapEquiv_map_nonUniversalDeletedEdge G z₀ z e,
    d8RemovedLoad_d8CoherentAugmentedWeight (hxy := hxy)]
  rfl

lemma d8RemovedLoad_coherent_swap_endpoint
    (G : SimpleGraph A) (z₀ z : ↑(universalVertices G)) {x y : A}
    (hxy : Gᶜ.Adj x y)
    (w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ)
    (a : A) (ha₀ : a ≠ (z₀ : A)) (haz : a ≠ (z : A))
    (hz₀z : (z₀ : A) ≠ (z : A)) :
    d8RemovedLoad G (z : A) x y
        (d8MissingLeft_ne_universal G hxy z)
        (d8MissingRight_ne_universal G hxy z)
        (d8CoherentAugmentedWeight G z₀ w₀ z)
        s(d7DeletedVertex (z : A) a haz,
          d7DeletedVertex (z : A) (z₀ : A) hz₀z) =
      d8RemovedLoad G (z₀ : A) x y
        (d8MissingLeft_ne_universal G hxy z₀)
        (d8MissingRight_ne_universal G hxy z₀) w₀
        s(d7DeletedVertex (z₀ : A) a ha₀,
          d7DeletedVertex (z₀ : A) (z : A) hz₀z.symm) := by
  let e₀ : Sym2 (↑(d7DeletedFinset (A := A) (z₀ : A))) :=
    s(d7DeletedVertex (z₀ : A) a ha₀,
      d7DeletedVertex (z₀ : A) (z : A) hz₀z.symm)
  have hmap :
      (d7DeletedSwapEquiv (z₀ : A) (z : A)).toEmbedding.sym2Map e₀ =
        s(d7DeletedVertex (z : A) a haz,
          d7DeletedVertex (z : A) (z₀ : A) hz₀z) := by
    change Sym2.map (d7DeletedSwapEquiv (z₀ : A) (z : A)) e₀ = _
    rw [show e₀ = s(d7DeletedVertex (z₀ : A) a ha₀,
      d7DeletedVertex (z₀ : A) (z : A) hz₀z.symm) from rfl,
      Sym2.map_mk]
    congr 1
    · apply Subtype.ext
      simp only [d7DeletedSwapEquiv_apply_val, d7DeletedVertex_val]
      exact Equiv.swap_apply_of_ne_of_ne ha₀ haz
    · apply Subtype.ext
      simp only [d7DeletedSwapEquiv_apply_val, d7DeletedVertex_val,
        Equiv.swap_apply_right]
  rw [← hmap,
    d8RemovedLoad_d8CoherentAugmentedWeight (hxy := hxy)]

lemma d8RemovedLoad_coherent_alpha_eq_extracted
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G)) {x y : A}
    (hxy : Gᶜ.Adj x y)
    (w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ)
    (hm : 4 ≤ (universalVertices G).card)
    (hsymm : ∀ p : Equiv.Perm (d7RemainingUniversalVertices G (z₀ : A)),
      relabelWeight (d7ExtendUniversalPerm G (z₀ : A) p) w₀ = w₀)
    (z v : ↑(universalVertices G))
    (hvz : (v : A) ≠ (z : A)) (u : ↑(nonUniversalVertices G)) :
    d8RemovedLoad G (z : A) x y
        (d8MissingLeft_ne_universal G hxy z)
        (d8MissingRight_ne_universal G hxy z)
        (d8CoherentAugmentedWeight G z₀ w₀ z)
        s(d7NonUniversalDeletedEmbedding G z u,
          d7DeletedVertex (z : A) (v : A) hvz) =
      d8ExtractedAlpha G z₀ x y
        (d8MissingLeft_ne_universal G hxy z₀)
        (d8MissingRight_ne_universal G hxy z₀) w₀ hm u := by
  have hu₀ : (u : A) ≠ (z₀ : A) := by
    intro h
    exact nonUniversalVertex_not_mem_universalVertices G u.property
      (h ▸ z₀.property)
  have huz : (u : A) ≠ (z : A) := by
    intro h
    exact nonUniversalVertex_not_mem_universalVertices G u.property
      (h ▸ z.property)
  have huEq : d7NonUniversalDeletedEmbedding G z u =
      d7DeletedVertex (z : A) (u : A) huz := by
    apply Subtype.ext
    rfl
  by_cases hv₀ : (v : A) ≠ (z₀ : A)
  · have hcoh := d8RemovedLoad_coherent_eq G z₀ z hxy w₀
      hu₀ huz hv₀ hvz
    have hbase := d8RemovedLoad_base_mixed_eq_extracted G z₀ x y
      (d8MissingLeft_ne_universal G hxy z₀)
      (d8MissingRight_ne_universal G hxy z₀) hxy w₀ hm hsymm u v hv₀
    have hu₀Eq : d7NonUniversalDeletedEmbedding G z₀ u =
        d7DeletedVertex (z₀ : A) (u : A) hu₀ := by
      apply Subtype.ext
      rfl
    rw [huEq, hcoh, ← hu₀Eq]
    exact hbase
  · have hvEq : v = z₀ := by
      apply Subtype.ext
      exact not_ne_iff.mp hv₀
    subst v
    have hz₀z : (z₀ : A) ≠ (z : A) := hvz
    have hswap := d8RemovedLoad_coherent_swap_endpoint
      G z₀ z hxy w₀ (u : A) hu₀ huz hz₀z
    have hbase := d8RemovedLoad_base_mixed_eq_extracted G z₀ x y
      (d8MissingLeft_ne_universal G hxy z₀)
      (d8MissingRight_ne_universal G hxy z₀) hxy w₀ hm hsymm
      u z hz₀z.symm
    have hu₀Eq : d7NonUniversalDeletedEmbedding G z₀ u =
        d7DeletedVertex (z₀ : A) (u : A) hu₀ := by
      apply Subtype.ext
      rfl
    rw [huEq, hswap, ← hu₀Eq]
    exact hbase

lemma d8RemovedLoad_coherent_gamma_eq_extracted
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G)) {a b : A}
    (hab : Gᶜ.Adj a b)
    (w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ)
    (hm : 4 ≤ (universalVertices G).card)
    (hsymm : ∀ p : Equiv.Perm (d7RemainingUniversalVertices G (z₀ : A)),
      relabelWeight (d7ExtendUniversalPerm G (z₀ : A) p) w₀ = w₀)
    (z x y : ↑(universalVertices G))
    (hxz : (x : A) ≠ (z : A)) (hyz : (y : A) ≠ (z : A))
    (hxy : (x : A) ≠ (y : A)) :
    d8RemovedLoad G (z : A) a b
        (d8MissingLeft_ne_universal G hab z)
        (d8MissingRight_ne_universal G hab z)
        (d8CoherentAugmentedWeight G z₀ w₀ z)
        s(d7DeletedVertex (z : A) (x : A) hxz,
          d7DeletedVertex (z : A) (y : A) hyz) =
      d8ExtractedGamma G z₀ a b
        (d8MissingLeft_ne_universal G hab z₀)
        (d8MissingRight_ne_universal G hab z₀) w₀ hm := by
  by_cases hx₀ : (x : A) ≠ (z₀ : A)
  · by_cases hy₀ : (y : A) ≠ (z₀ : A)
    · have hcoh := d8RemovedLoad_coherent_eq G z₀ z hab w₀
        hx₀ hxz hy₀ hyz
      have hbase := d8RemovedLoad_base_universal_eq_extracted G z₀ a b
        (d8MissingLeft_ne_universal G hab z₀)
        (d8MissingRight_ne_universal G hab z₀) hab w₀ hm hsymm
        x y hx₀ hy₀ (by
          intro h
          exact hxy (congrArg Subtype.val h))
      rw [hcoh]
      exact hbase
    · have hyEq : y = z₀ := by
        apply Subtype.ext
        exact not_ne_iff.mp hy₀
      subst y
      have hz₀z : (z₀ : A) ≠ (z : A) := hyz
      have hswap := d8RemovedLoad_coherent_swap_endpoint
        G z₀ z hab w₀ (x : A) hx₀ hxz hz₀z
      have hxzSub : x ≠ z := by
        intro h
        exact hxz (congrArg Subtype.val h)
      have hbase := d8RemovedLoad_base_universal_eq_extracted G z₀ a b
        (d8MissingLeft_ne_universal G hab z₀)
        (d8MissingRight_ne_universal G hab z₀) hab w₀ hm hsymm
        x z hx₀ hz₀z.symm hxzSub
      rw [hswap]
      exact hbase
  · have hxEq : x = z₀ := by
      apply Subtype.ext
      exact not_ne_iff.mp hx₀
    subst x
    have hz₀z : (z₀ : A) ≠ (z : A) := hxz
    have hy₀ : (y : A) ≠ (z₀ : A) := hxy.symm
    have hswap := d8RemovedLoad_coherent_swap_endpoint
      G z₀ z hab w₀ (y : A) hy₀ hyz hz₀z
    have hyzSub : y ≠ z := by
      intro h
      exact hyz (congrArg Subtype.val h)
    have hbase := d8RemovedLoad_base_universal_eq_extracted G z₀ a b
      (d8MissingLeft_ne_universal G hab z₀)
      (d8MissingRight_ne_universal G hab z₀) hab w₀ hm hsymm
      y z hy₀ hz₀z.symm hyzSub
    rw [show s(d7DeletedVertex (z : A) (z₀ : A) hz₀z,
          d7DeletedVertex (z : A) (y : A) hyz) =
        s(d7DeletedVertex (z : A) (y : A) hyz,
          d7DeletedVertex (z : A) (z₀ : A) hz₀z) from Sym2.eq_swap,
      hswap]
    exact hbase

/-- The three removed-load orbit values described by `P` agree with every
member of the coherently transported augmented-deletion family. -/
structure D8SeparatedParameters.RealizesCoherentRemovedFamily
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G)) {a b : A}
    (hab : Gᶜ.Adj a b)
    (w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ)
    (P : D8SeparatedParameters G) : Prop where
  beta_eq : ∀ (z : ↑(universalVertices G))
    (e : Sym2 (↑(nonUniversalVertices G))),
    d8RemovedLoad G (z : A) a b
      (d8MissingLeft_ne_universal G hab z)
      (d8MissingRight_ne_universal G hab z)
      (d8CoherentAugmentedWeight G z₀ w₀ z)
      ((d7NonUniversalDeletedEmbedding G z).sym2Map e) = P.beta e
  alpha_eq : ∀ (z v : ↑(universalVertices G))
    (hvz : (v : A) ≠ (z : A)) (u : ↑(nonUniversalVertices G)),
    d8RemovedLoad G (z : A) a b
      (d8MissingLeft_ne_universal G hab z)
      (d8MissingRight_ne_universal G hab z)
      (d8CoherentAugmentedWeight G z₀ w₀ z)
      s(d7NonUniversalDeletedEmbedding G z u,
        d7DeletedVertex (z : A) (v : A) hvz) = P.alpha u
  gamma_eq : ∀ (z x y : ↑(universalVertices G))
    (hxz : (x : A) ≠ (z : A)) (hyz : (y : A) ≠ (z : A))
    (hxy : (x : A) ≠ (y : A)),
    d8RemovedLoad G (z : A) a b
      (d8MissingLeft_ne_universal G hab z)
      (d8MissingRight_ne_universal G hab z)
      (d8CoherentAugmentedWeight G z₀ w₀ z)
      s(d7DeletedVertex (z : A) (x : A) hxz,
        d7DeletedVertex (z : A) (y : A) hyz) = P.gamma

lemma d8ExtractedSeparatedParametersOfHalf_realizes
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G)) {a b : A}
    (hab : Gᶜ.Adj a b)
    (w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ)
    (hm : 4 ≤ (universalVertices G).card)
    (hw : IsFractionalPacking
      (d8AugmentedDeletedGraph G (z₀ : A) a b
        (d8MissingLeft_ne_universal G hab z₀)
        (d8MissingRight_ne_universal G hab z₀)) w₀)
    (hhalf : IsHalfBounded
      (d8AugmentedDeletedGraph G (z₀ : A) a b
        (d8MissingLeft_ne_universal G hab z₀)
        (d8MissingRight_ne_universal G hab z₀)) w₀)
    (hsymm : ∀ p : Equiv.Perm (d7RemainingUniversalVertices G (z₀ : A)),
      relabelWeight (d7ExtendUniversalPerm G (z₀ : A) p) w₀ = w₀)
    (htotal : (∑ p ∈ (d7DeletedGraph G (z₀ : A)).edgeFinset,
      d8RemovedLoad G (z₀ : A) a b
        (d8MissingLeft_ne_universal G hab z₀)
        (d8MissingRight_ne_universal G hab z₀) w₀ p) ≤ 2) :
    (d8ExtractedSeparatedParametersOfHalf G z₀ a b
      (d8MissingLeft_ne_universal G hab z₀)
      (d8MissingRight_ne_universal G hab z₀) hab w₀ hm
      hw hhalf hsymm htotal).RealizesCoherentRemovedFamily
        G z₀ hab w₀ := by
  constructor
  · intro z e
    exact d8RemovedLoad_coherent_beta_eq_extracted G z₀ hab w₀ z e
  · intro z v hvz u
    exact d8RemovedLoad_coherent_alpha_eq_extracted
      G z₀ hab w₀ hm hsymm z v hvz u
  · intro z x y hxz hyz hxy
    exact d8RemovedLoad_coherent_gamma_eq_extracted
      G z₀ hab w₀ hm hsymm z x y hxz hyz hxy

/-- A separated parameter package identified pointwise with the values
extracted from the base augmented-deletion packing realizes the whole
coherently transported family.  This is the interface used after opening
`exists_d8SeparatedParameters_and_strippedWeight`: it avoids depending on
the particular constructor chosen inside that existential theorem. -/
lemma D8SeparatedParameters.realizesCoherentRemovedFamily_of_eq_extracted
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G)) {a b : A}
    (hab : Gᶜ.Adj a b)
    (w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ)
    (P : D8SeparatedParameters G)
    (hm : 4 ≤ (universalVertices G).card)
    (hsymm : ∀ p : Equiv.Perm (d7RemainingUniversalVertices G (z₀ : A)),
      relabelWeight (d7ExtendUniversalPerm G (z₀ : A) p) w₀ = w₀)
    (hbeta : ∀ e, P.beta e = d8ExtractedBeta G z₀ a b
      (d8MissingLeft_ne_universal G hab z₀)
      (d8MissingRight_ne_universal G hab z₀) w₀ e)
    (halpha : ∀ u, P.alpha u = d8ExtractedAlpha G z₀ a b
      (d8MissingLeft_ne_universal G hab z₀)
      (d8MissingRight_ne_universal G hab z₀) w₀ hm u)
    (hgamma : P.gamma = d8ExtractedGamma G z₀ a b
      (d8MissingLeft_ne_universal G hab z₀)
      (d8MissingRight_ne_universal G hab z₀) w₀ hm) :
    P.RealizesCoherentRemovedFamily G z₀ hab w₀ := by
  constructor
  · intro z e
    rw [d8RemovedLoad_coherent_beta_eq_extracted G z₀ hab w₀ z e]
    exact (hbeta e).symm
  · intro z v hvz u
    rw [d8RemovedLoad_coherent_alpha_eq_extracted
      G z₀ hab w₀ hm hsymm z v hvz u]
    exact (halpha u).symm
  · intro z x y hxz hyz hxy
    rw [d8RemovedLoad_coherent_gamma_eq_extracted
      G z₀ hab w₀ hm hsymm z x y hxz hyz hxy]
    exact hgamma.symm

/-- The total load of the removed triangles on the old edges is the same
orbit sum in every coherently transported deletion. -/
lemma sum_d8RemovedLoad_coherent_eq_orbitTotal
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G)) {a b : A}
    (hab : Gᶜ.Adj a b)
    (w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ)
    (P : D8SeparatedParameters G)
    (hreal : P.RealizesCoherentRemovedFamily G z₀ hab w₀)
    (z : ↑(universalVertices G)) :
    (∑ e ∈ (d7DeletedGraph G (z : A)).edgeFinset,
        d8RemovedLoad G (z : A) a b
          (d8MissingLeft_ne_universal G hab z)
          (d8MissingRight_ne_universal G hab z)
          (d8CoherentAugmentedWeight G z₀ w₀ z) e) =
      ((((universalVertices G).card : ℝ) - 1) *
          (((universalVertices G).card : ℝ) - 2) / 2) * P.gamma +
        P.alphaMass + P.betaMass := by
  have hnonUniversal :
      (∑ e ∈ d7BaseNonUniversalEdges G z,
          d8RemovedLoad G (z : A) a b
            (d8MissingLeft_ne_universal G hab z)
            (d8MissingRight_ne_universal G hab z)
            (d8CoherentAugmentedWeight G z₀ w₀ z) e) = P.betaMass := by
    rw [d7BaseNonUniversalEdges, Finset.sum_map]
    unfold D8SeparatedParameters.betaMass
    apply Finset.sum_congr rfl
    intro e he
    exact hreal.beta_eq z e
  have hmixed :
      (∑ e ∈ d7BaseMixedEdges G z,
          d8RemovedLoad G (z : A) a b
            (d8MissingLeft_ne_universal G hab z)
            (d8MissingRight_ne_universal G hab z)
            (d8CoherentAugmentedWeight G z₀ w₀ z) e) = P.alphaMass := by
    rw [d7BaseMixedEdges, Finset.sum_map]
    change (∑ p : (↑(nonUniversalVertices G) ×
        d7RemainingUniversalVertices G (z : A)),
      d8RemovedLoad G (z : A) a b
        (d8MissingLeft_ne_universal G hab z)
        (d8MissingRight_ne_universal G hab z)
        (d8CoherentAugmentedWeight G z₀ w₀ z)
        ((d7MixedDeletedEdgeEmbedding G z) p)) = P.alphaMass
    rw [Fintype.sum_prod_type]
    calc
      (∑ u : ↑(nonUniversalVertices G),
          ∑ v : d7RemainingUniversalVertices G (z : A),
            d8RemovedLoad G (z : A) a b
              (d8MissingLeft_ne_universal G hab z)
              (d8MissingRight_ne_universal G hab z)
              (d8CoherentAugmentedWeight G z₀ w₀ z)
              ((d7MixedDeletedEdgeEmbedding G z) (u, v))) =
          ∑ u : ↑(nonUniversalVertices G),
            ∑ _v : d7RemainingUniversalVertices G (z : A), P.alpha u := by
        apply Fintype.sum_congr
        intro u
        apply Fintype.sum_congr
        intro v
        let vZ : ↑(universalVertices G) := ⟨(v.1 : A), v.property⟩
        have hvz : (vZ : A) ≠ (z : A) := by
          have hv := v.1.property
          simpa only [d7DeletedFinset, Finset.mem_erase, Finset.mem_univ,
            and_true, vZ] using hv
        have hvEq : d7RemainingUniversalEmbedding G (z : A) v =
            d7DeletedVertex (z : A) (vZ : A) hvz := by
          apply Subtype.ext
          rfl
        change d8RemovedLoad G (z : A) a b
            (d8MissingLeft_ne_universal G hab z)
            (d8MissingRight_ne_universal G hab z)
            (d8CoherentAugmentedWeight G z₀ w₀ z)
            s(d7NonUniversalDeletedEmbedding G z u,
              d7RemainingUniversalEmbedding G (z : A) v) = _
        rw [hvEq]
        exact hreal.alpha_eq z vZ hvz u
      _ = (((universalVertices G).card : ℝ) - 1) * ∑ u, P.alpha u := by
        simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
          card_d7RemainingUniversalVertices G z]
        have hm1 : 1 ≤ (universalVertices G).card := by
          exact Finset.card_pos.mpr ⟨(z : A), z.property⟩
        rw [Nat.cast_sub hm1, Nat.cast_one, Finset.mul_sum]
      _ = P.alphaMass := by rfl
  have huniversal :
      (∑ e ∈ d7BaseUniversalEdges G z,
          d8RemovedLoad G (z : A) a b
            (d8MissingLeft_ne_universal G hab z)
            (d8MissingRight_ne_universal G hab z)
            (d8CoherentAugmentedWeight G z₀ w₀ z) e) =
        ((((universalVertices G).card : ℝ) - 1) *
          (((universalVertices G).card : ℝ) - 2) / 2) * P.gamma := by
    rw [d7BaseUniversalEdges, Finset.sum_map]
    calc
      (∑ e ∈ (⊤ : SimpleGraph
            (d7RemainingUniversalVertices G (z : A))).edgeFinset,
          d8RemovedLoad G (z : A) a b
            (d8MissingLeft_ne_universal G hab z)
            (d8MissingRight_ne_universal G hab z)
            (d8CoherentAugmentedWeight G z₀ w₀ z)
            ((d7RemainingUniversalEmbedding G (z : A)).sym2Map e)) =
        ∑ _e ∈ (⊤ : SimpleGraph
            (d7RemainingUniversalVertices G (z : A))).edgeFinset,
          P.gamma := by
        apply Finset.sum_congr rfl
        intro e he
        induction e using Sym2.inductionOn with
        | hf x y =>
            have hxy : x ≠ y :=
              (⊤ : SimpleGraph
                (d7RemainingUniversalVertices G (z : A))).ne_of_adj
                  (SimpleGraph.mem_edgeFinset.mp he)
            let xZ : ↑(universalVertices G) := ⟨(x.1 : A), x.property⟩
            let yZ : ↑(universalVertices G) := ⟨(y.1 : A), y.property⟩
            have hxz : (xZ : A) ≠ (z : A) := by
              have hx := x.1.property
              simpa only [d7DeletedFinset, Finset.mem_erase, Finset.mem_univ,
                and_true, xZ] using hx
            have hyz : (yZ : A) ≠ (z : A) := by
              have hy := y.1.property
              simpa only [d7DeletedFinset, Finset.mem_erase, Finset.mem_univ,
                and_true, yZ] using hy
            have hxyZ : (xZ : A) ≠ (yZ : A) := by
              intro h
              apply hxy
              apply Subtype.ext
              apply Subtype.ext
              exact h
            have hxEq : d7RemainingUniversalEmbedding G (z : A) x =
                d7DeletedVertex (z : A) (xZ : A) hxz := by
              apply Subtype.ext
              rfl
            have hyEq : d7RemainingUniversalEmbedding G (z : A) y =
                d7DeletedVertex (z : A) (yZ : A) hyz := by
              apply Subtype.ext
              rfl
            change d8RemovedLoad G (z : A) a b
                (d8MissingLeft_ne_universal G hab z)
                (d8MissingRight_ne_universal G hab z)
                (d8CoherentAugmentedWeight G z₀ w₀ z)
                s(d7RemainingUniversalEmbedding G (z : A) x,
                  d7RemainingUniversalEmbedding G (z : A) y) = _
            rw [hxEq, hyEq]
            exact hreal.gamma_eq z xZ yZ hxz hyz hxyZ
      _ = ((⊤ : SimpleGraph
            (d7RemainingUniversalVertices G (z : A))).edgeFinset.card : ℝ) *
          P.gamma := by
        simp only [Finset.sum_const, nsmul_eq_mul]
      _ = ((((universalVertices G).card : ℝ) - 1) *
          (((universalVertices G).card : ℝ) - 2) / 2) * P.gamma := by
        rw [SimpleGraph.card_edgeFinset_top_eq_card_choose_two,
          Nat.cast_choose_two, card_d7RemainingUniversalVertices G z]
        have hm1 : 1 ≤ (universalVertices G).card := by
          exact Finset.card_pos.mpr ⟨(z : A), z.property⟩
        rw [Nat.cast_sub hm1, Nat.cast_one]
        ring
  rw [d7DeletedGraph_edgeFinset_eq_three_orbits G z,
    Finset.sum_union (d7BaseNonUniversalUnionMixed_disjoint_universal G z),
    Finset.sum_union (d7BaseNonUniversalEdges_disjoint_mixed G z),
    hnonUniversal, hmixed, huniversal]
  ring

def d8CoherentStrippedWeight (G : SimpleGraph A)
    (z₀ : ↑(universalVertices G)) {a b : A} (hab : Gᶜ.Adj a b)
    (w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ)
    (z : ↑(universalVertices G)) :
    Finset (↑(d7DeletedFinset (A := A) (z : A))) → ℝ :=
  stripEdgeTriangles
    s(d7DeletedVertex (z : A) a (d8MissingLeft_ne_universal G hab z),
      d7DeletedVertex (z : A) b (d8MissingRight_ne_universal G hab z))
    (d8CoherentAugmentedWeight G z₀ w₀ z)

lemma d8CoherentStrippedWeight_isFractionalPacking
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G)) {a b : A}
    (hab : Gᶜ.Adj a b)
    {w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ}
    (hw₀ : IsFractionalPacking
      (d8AugmentedDeletedGraph G (z₀ : A) a b
        (d8MissingLeft_ne_universal G hab z₀)
        (d8MissingRight_ne_universal G hab z₀)) w₀)
    (z : ↑(universalVertices G)) :
    IsFractionalPacking (d7DeletedGraph G (z : A))
      (d8CoherentStrippedWeight G z₀ hab w₀ z) := by
  have htarget := d8CoherentAugmentedWeight_isFractionalPacking
    G z₀ hab hw₀ z
  apply htarget.strip_addedPair
  · intro h
    exact hab.ne (congrArg Subtype.val h)
  · intro hadj
    exact hab.2 hadj

lemma d8CoherentStrippedWeight_halfBounded
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G)) {a b : A}
    (hab : Gᶜ.Adj a b)
    {w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ}
    (hw₀ : IsHalfBounded
      (d8AugmentedDeletedGraph G (z₀ : A) a b
        (d8MissingLeft_ne_universal G hab z₀)
        (d8MissingRight_ne_universal G hab z₀)) w₀)
    (z : ↑(universalVertices G)) :
    IsHalfBounded (d7DeletedGraph G (z : A))
      (d8CoherentStrippedWeight G z₀ hab w₀ z) := by
  have htarget := d8CoherentAugmentedWeight_halfBounded
    G z₀ hab hw₀ z
  apply htarget.strip_addedPair
  · intro h
    exact hab.ne (congrArg Subtype.val h)
  · intro hadj
    exact hab.2 hadj

def d8CoherentOldResidual (G : SimpleGraph A)
    (z₀ : ↑(universalVertices G)) {a b : A} (hab : Gᶜ.Adj a b)
    (w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ)
    (z : ↑(universalVertices G))
    (p : Sym2 (↑(d7DeletedFinset (A := A) (z : A)))) : ℝ :=
  augmentedOldResidual
    (d8AugmentedDeletedGraph G (z : A) a b
      (d8MissingLeft_ne_universal G hab z)
      (d8MissingRight_ne_universal G hab z))
    (d8CoherentAugmentedWeight G z₀ w₀ z) p

lemma d8CoherentOldResidual_nonneg
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G)) {a b : A}
    (hab : Gᶜ.Adj a b)
    {w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ}
    (hw₀ : IsFractionalPacking
      (d8AugmentedDeletedGraph G (z₀ : A) a b
        (d8MissingLeft_ne_universal G hab z₀)
        (d8MissingRight_ne_universal G hab z₀)) w₀)
    (z : ↑(universalVertices G)) {p : Sym2 _}
    (hp : p ∈ (d7DeletedGraph G (z : A)).edgeFinset) :
    0 ≤ d8CoherentOldResidual G z₀ hab w₀ z p := by
  unfold d8CoherentOldResidual augmentedOldResidual
  apply sub_nonneg.mpr
  apply (d8CoherentAugmentedWeight_isFractionalPacking
    G z₀ hab hw₀ z).edgeLoad_le_one
  change p ∈ (addPair (d7DeletedGraph G (z : A))
    (d7DeletedVertex (z : A) a (d8MissingLeft_ne_universal G hab z))
    (d7DeletedVertex (z : A) b
      (d8MissingRight_ne_universal G hab z))).edgeFinset
  rw [edgeFinset_addPair (by
    intro h
    exact hab.ne (congrArg Subtype.val h))]
  exact Finset.mem_insert_of_mem hp

def d8ShortcutAverageWeight (G : SimpleGraph A)
    (z₀ : ↑(universalVertices G)) {a b : A} (hab : Gᶜ.Adj a b)
    (w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ)
    (P : D8SeparatedParameters G) : Finset A → ℝ :=
  fun t ↦ (((universalVertices G).card : ℝ)⁻¹) *
    ((∑ z : ↑(universalVertices G),
      d7LiftedWeight (z : A)
        (d8CoherentStrippedWeight G z₀ hab w₀ z) t) +
      d8ShortcutCorrection G P t)

lemma fractionalEdgeLoad_d8ShortcutAverageWeight
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G)) {a b : A}
    (hab : Gᶜ.Adj a b)
    (w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ)
    (P : D8SeparatedParameters G) (e : Sym2 A) :
    fractionalEdgeLoad G (d8ShortcutAverageWeight G z₀ hab w₀ P) e =
      (((universalVertices G).card : ℝ)⁻¹) *
        ((∑ z : ↑(universalVertices G),
          fractionalEdgeLoad G
            (d7LiftedWeight (z : A)
              (d8CoherentStrippedWeight G z₀ hab w₀ z)) e) +
          fractionalEdgeLoad G (d8ShortcutCorrection G P) e) := by
  unfold d8ShortcutAverageWeight
  rw [fractionalEdgeLoad_smul, fractionalEdgeLoad_add,
    fractionalEdgeLoad_sum]

lemma d8ShortcutCorrection_numerator_nonUniversal
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G)) {a b : A}
    (hab : Gᶜ.Adj a b)
    (w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ)
    (P : D8SeparatedParameters G)
    (hreal : P.RealizesCoherentRemovedFamily G z₀ hab w₀)
    (e : Sym2 (↑(nonUniversalVertices G)))
    (he : e ∈ (G.induce
      (↑(nonUniversalVertices G) : Set A)).edgeFinset) :
    (∑ z : ↑(universalVertices G),
        fractionalEdgeLoad G
          (d7LiftedWeight (z : A)
            (d8CoherentStrippedWeight G z₀ hab w₀ z))
          ((inducedEmbedding (nonUniversalVertices G)).sym2Map e)) +
        fractionalEdgeLoad G (d8ShortcutCorrection G P)
          ((inducedEmbedding (nonUniversalVertices G)).sym2Map e) =
      ((universalVertices G).card : ℝ) -
        ∑ z : ↑(universalVertices G),
          d8CoherentOldResidual G z₀ hab w₀ z
            ((d7NonUniversalDeletedEmbedding G z).sym2Map e) := by
  rw [fractionalEdgeLoad_d8ShortcutCorrection_nonUniversal G P e he]
  have hterms : ∀ z : ↑(universalVertices G),
      fractionalEdgeLoad G
          (d7LiftedWeight (z : A)
            (d8CoherentStrippedWeight G z₀ hab w₀ z))
          ((inducedEmbedding (nonUniversalVertices G)).sym2Map e) =
        1 - P.beta e -
          d8CoherentOldResidual G z₀ hab w₀ z
            ((d7NonUniversalDeletedEmbedding G z).sym2Map e) := by
    intro z
    rw [fractionalEdgeLoad_d7LiftedWeight_nonUniversal]
    have hne : d7DeletedVertex (z : A) a
        (d8MissingLeft_ne_universal G hab z) ≠
        d7DeletedVertex (z : A) b
          (d8MissingRight_ne_universal G hab z) := by
      intro h
      exact hab.ne (congrArg Subtype.val h)
    have hmissing : ¬(d7DeletedGraph G (z : A)).Adj
        (d7DeletedVertex (z : A) a
          (d8MissingLeft_ne_universal G hab z))
        (d7DeletedVertex (z : A) b
          (d8MissingRight_ne_universal G hab z)) := by
      intro hadj
      exact hab.2 hadj
    have hone := strip_oldResidual_removedLoad_eq_one
      (d7DeletedGraph G (z : A)) hne hmissing
      (d8CoherentAugmentedWeight G z₀ w₀ z)
      ((d7NonUniversalDeletedEmbedding G z).sym2Map e)
    change fractionalEdgeLoad (d7DeletedGraph G (z : A))
          (d8CoherentStrippedWeight G z₀ hab w₀ z)
          ((d7NonUniversalDeletedEmbedding G z).sym2Map e) +
        d8CoherentOldResidual G z₀ hab w₀ z
          ((d7NonUniversalDeletedEmbedding G z).sym2Map e) +
        d8RemovedLoad G (z : A) a b
          (d8MissingLeft_ne_universal G hab z)
          (d8MissingRight_ne_universal G hab z)
          (d8CoherentAugmentedWeight G z₀ w₀ z)
          ((d7NonUniversalDeletedEmbedding G z).sym2Map e) = 1 at hone
    rw [hreal.beta_eq z e] at hone
    linarith
  simp_rw [hterms]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
    Fintype.card_coe]
  ring

def d8MixedOldResidual (G : SimpleGraph A)
    (z₀ : ↑(universalVertices G)) {a b : A} (hab : Gᶜ.Adj a b)
    (w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ)
    (u : ↑(nonUniversalVertices G))
    (y z : ↑(universalVertices G)) : ℝ :=
  if h : z = y then 0 else
    d8CoherentOldResidual G z₀ hab w₀ z
      s(d7NonUniversalDeletedEmbedding G z u,
        d7DeletedVertex (z : A) (y : A) (by
          intro hval
          exact h (Subtype.ext hval.symm)))

lemma d8ShortcutCorrection_numerator_mixed
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G)) {a b : A}
    (hab : Gᶜ.Adj a b)
    (w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ)
    (P : D8SeparatedParameters G)
    (hreal : P.RealizesCoherentRemovedFamily G z₀ hab w₀)
    (hm : 4 ≤ (universalVertices G).card)
    (u : ↑(nonUniversalVertices G)) (y : ↑(universalVertices G)) :
    (∑ z : ↑(universalVertices G),
        fractionalEdgeLoad G
          (d7LiftedWeight (z : A)
            (d8CoherentStrippedWeight G z₀ hab w₀ z))
          s((u : A), (y : A))) +
        fractionalEdgeLoad G (d8ShortcutCorrection G P)
          s((u : A), (y : A)) =
      ((universalVertices G).card : ℝ) -
        ∑ z : ↑(universalVertices G),
          d8MixedOldResidual G z₀ hab w₀ u y z := by
  rw [fractionalEdgeLoad_d8ShortcutCorrection_mixed G P hm u y]
  have hterms : ∀ z : ↑(universalVertices G),
      fractionalEdgeLoad G
          (d7LiftedWeight (z : A)
            (d8CoherentStrippedWeight G z₀ hab w₀ z))
          s((u : A), (y : A)) =
        if z = y then 0 else 1 - P.alpha u -
          d8MixedOldResidual G z₀ hab w₀ u y z := by
    intro z
    by_cases hzy : z = y
    · subst z
      rw [if_pos rfl]
      simpa only [Sym2.eq_swap] using
        (fractionalEdgeLoad_d7LiftedWeight_eq_zero_of_endpoint
          G (y : A) (u : A)
            (d8CoherentStrippedWeight G z₀ hab w₀ y))
    · rw [if_neg hzy]
      have hyz : (y : A) ≠ (z : A) := by
        intro h
        exact hzy (Subtype.ext h.symm)
      rw [fractionalEdgeLoad_d7LiftedWeight_mixed G z y hyz]
      have hne : d7DeletedVertex (z : A) a
          (d8MissingLeft_ne_universal G hab z) ≠
          d7DeletedVertex (z : A) b
            (d8MissingRight_ne_universal G hab z) := by
        intro h
        exact hab.ne (congrArg Subtype.val h)
      have hmissing : ¬(d7DeletedGraph G (z : A)).Adj
          (d7DeletedVertex (z : A) a
            (d8MissingLeft_ne_universal G hab z))
          (d7DeletedVertex (z : A) b
            (d8MissingRight_ne_universal G hab z)) := by
        intro hadj
        exact hab.2 hadj
      have hone := strip_oldResidual_removedLoad_eq_one
        (d7DeletedGraph G (z : A)) hne hmissing
        (d8CoherentAugmentedWeight G z₀ w₀ z)
        s(d7NonUniversalDeletedEmbedding G z u,
          d7DeletedVertex (z : A) (y : A) hyz)
      change fractionalEdgeLoad (d7DeletedGraph G (z : A))
            (d8CoherentStrippedWeight G z₀ hab w₀ z)
            s(d7NonUniversalDeletedEmbedding G z u,
              d7DeletedVertex (z : A) (y : A) hyz) +
          d8CoherentOldResidual G z₀ hab w₀ z
            s(d7NonUniversalDeletedEmbedding G z u,
              d7DeletedVertex (z : A) (y : A) hyz) +
          d8RemovedLoad G (z : A) a b
            (d8MissingLeft_ne_universal G hab z)
            (d8MissingRight_ne_universal G hab z)
            (d8CoherentAugmentedWeight G z₀ w₀ z)
            s(d7NonUniversalDeletedEmbedding G z u,
              d7DeletedVertex (z : A) (y : A) hyz) = 1 at hone
      rw [hreal.alpha_eq z y hyz u] at hone
      simp only [d8MixedOldResidual, hzy, dite_false]
      linarith
  simp_rw [hterms]
  have hsplit : ∀ z : ↑(universalVertices G),
      (if z = y then 0 else 1 - P.alpha u -
        d8MixedOldResidual G z₀ hab w₀ u y z) =
        (if z = y then 0 else 1 - P.alpha u) -
          d8MixedOldResidual G z₀ hab w₀ u y z := by
    intro z
    by_cases h : z = y <;> simp [h, d8MixedOldResidual]
  simp_rw [hsplit]
  rw [Finset.sum_sub_distrib, sum_ite_eq_zero_else]
  simp only [Fintype.card_coe]
  ring

def d8UniversalOldResidual (G : SimpleGraph A)
    (z₀ : ↑(universalVertices G)) {a b : A} (hab : Gᶜ.Adj a b)
    (w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ)
    (x y z : ↑(universalVertices G)) : ℝ :=
  if h : z = x ∨ z = y then 0 else
    d8CoherentOldResidual G z₀ hab w₀ z
      s(d7DeletedVertex (z : A) (x : A) (by
          intro hval
          exact h (Or.inl (Subtype.ext hval.symm))),
        d7DeletedVertex (z : A) (y : A) (by
          intro hval
          exact h (Or.inr (Subtype.ext hval.symm))))

lemma d8ShortcutCorrection_numerator_universal
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G)) {a b : A}
    (hab : Gᶜ.Adj a b)
    (w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ)
    (P : D8SeparatedParameters G)
    (hreal : P.RealizesCoherentRemovedFamily G z₀ hab w₀)
    (hm : 4 ≤ (universalVertices G).card)
    (x y : ↑(universalVertices G)) (hxy : x ≠ y) :
    (∑ z : ↑(universalVertices G),
        fractionalEdgeLoad G
          (d7LiftedWeight (z : A)
            (d8CoherentStrippedWeight G z₀ hab w₀ z))
          s((x : A), (y : A))) +
        fractionalEdgeLoad G (d8ShortcutCorrection G P)
          s((x : A), (y : A)) =
      ((universalVertices G).card : ℝ) -
        ∑ z : ↑(universalVertices G),
          d8UniversalOldResidual G z₀ hab w₀ x y z := by
  let e : Sym2 (↑(universalVertices G)) := s(x, y)
  have he : e ∈ (⊤ : SimpleGraph
      (↑(universalVertices G))).edgeFinset := by
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    exact hxy
  have hcorr := fractionalEdgeLoad_d8ShortcutCorrection_universal_simplified
    G P hm e he
  change fractionalEdgeLoad G (d8ShortcutCorrection G P)
      s((x : A), (y : A)) =
    2 + (((universalVertices G).card : ℝ) - 2) * P.gamma at hcorr
  rw [hcorr]
  have hterms : ∀ z : ↑(universalVertices G),
      fractionalEdgeLoad G
          (d7LiftedWeight (z : A)
            (d8CoherentStrippedWeight G z₀ hab w₀ z))
          s((x : A), (y : A)) =
        if z = x ∨ z = y then 0 else 1 - P.gamma -
          d8UniversalOldResidual G z₀ hab w₀ x y z := by
    intro z
    by_cases hz : z = x ∨ z = y
    · rw [if_pos hz]
      rcases hz with hzx | hzy
      · rw [hzx]
        exact fractionalEdgeLoad_d7LiftedWeight_eq_zero_of_endpoint
          G (x : A) (y : A)
            (d8CoherentStrippedWeight G z₀ hab w₀ x)
      · rw [hzy]
        simpa only [Sym2.eq_swap] using
          (fractionalEdgeLoad_d7LiftedWeight_eq_zero_of_endpoint
            G (y : A) (x : A)
              (d8CoherentStrippedWeight G z₀ hab w₀ y))
    · rw [if_neg hz]
      have hxz : (x : A) ≠ (z : A) := by
        intro h
        exact hz (Or.inl (Subtype.ext h.symm))
      have hyz : (y : A) ≠ (z : A) := by
        intro h
        exact hz (Or.inr (Subtype.ext h.symm))
      have hxyA : (x : A) ≠ (y : A) := fun h ↦ hxy (Subtype.ext h)
      rw [fractionalEdgeLoad_d7LiftedWeight_universal G z x y hxz hyz]
      have hne : d7DeletedVertex (z : A) a
          (d8MissingLeft_ne_universal G hab z) ≠
          d7DeletedVertex (z : A) b
            (d8MissingRight_ne_universal G hab z) := by
        intro h
        exact hab.ne (congrArg Subtype.val h)
      have hmissing : ¬(d7DeletedGraph G (z : A)).Adj
          (d7DeletedVertex (z : A) a
            (d8MissingLeft_ne_universal G hab z))
          (d7DeletedVertex (z : A) b
            (d8MissingRight_ne_universal G hab z)) := by
        intro hadj
        exact hab.2 hadj
      have hone := strip_oldResidual_removedLoad_eq_one
        (d7DeletedGraph G (z : A)) hne hmissing
        (d8CoherentAugmentedWeight G z₀ w₀ z)
        s(d7DeletedVertex (z : A) (x : A) hxz,
          d7DeletedVertex (z : A) (y : A) hyz)
      change fractionalEdgeLoad (d7DeletedGraph G (z : A))
            (d8CoherentStrippedWeight G z₀ hab w₀ z)
            s(d7DeletedVertex (z : A) (x : A) hxz,
              d7DeletedVertex (z : A) (y : A) hyz) +
          d8CoherentOldResidual G z₀ hab w₀ z
            s(d7DeletedVertex (z : A) (x : A) hxz,
              d7DeletedVertex (z : A) (y : A) hyz) +
          d8RemovedLoad G (z : A) a b
            (d8MissingLeft_ne_universal G hab z)
            (d8MissingRight_ne_universal G hab z)
            (d8CoherentAugmentedWeight G z₀ w₀ z)
            s(d7DeletedVertex (z : A) (x : A) hxz,
              d7DeletedVertex (z : A) (y : A) hyz) = 1 at hone
      rw [hreal.gamma_eq z x y hxz hyz hxyA] at hone
      simp only [d8UniversalOldResidual, hz, dite_false]
      linarith
  simp_rw [hterms]
  have hsplit : ∀ z : ↑(universalVertices G),
      (if z = x ∨ z = y then 0 else 1 - P.gamma -
        d8UniversalOldResidual G z₀ hab w₀ x y z) =
        (if z = x ∨ z = y then 0 else 1 - P.gamma) -
          d8UniversalOldResidual G z₀ hab w₀ x y z := by
    intro z
    by_cases h : z = x ∨ z = y <;> simp [h, d8UniversalOldResidual]
  simp_rw [hsplit]
  rw [Finset.sum_sub_distrib,
    sum_ite_eq_zero_else_two x y hxy]
  simp only [Fintype.card_coe]
  ring

lemma d8ShortcutAverageWeight_edgeLoad_le_one_nonUniversal
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G)) {a b : A}
    (hab : Gᶜ.Adj a b)
    (w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ)
    (P : D8SeparatedParameters G)
    (hreal : P.RealizesCoherentRemovedFamily G z₀ hab w₀)
    (hw₀ : IsFractionalPacking
      (d8AugmentedDeletedGraph G (z₀ : A) a b
        (d8MissingLeft_ne_universal G hab z₀)
        (d8MissingRight_ne_universal G hab z₀)) w₀)
    (e : Sym2 (↑(nonUniversalVertices G)))
    (he : e ∈ (G.induce
      (↑(nonUniversalVertices G) : Set A)).edgeFinset) :
    fractionalEdgeLoad G (d8ShortcutAverageWeight G z₀ hab w₀ P)
        ((inducedEmbedding (nonUniversalVertices G)).sym2Map e) ≤ 1 := by
  rw [fractionalEdgeLoad_d8ShortcutAverageWeight,
    d8ShortcutCorrection_numerator_nonUniversal
      G z₀ hab w₀ P hreal e he]
  have hrem : 0 ≤ ∑ z : ↑(universalVertices G),
      d8CoherentOldResidual G z₀ hab w₀ z
        ((d7NonUniversalDeletedEmbedding G z).sym2Map e) := by
    exact Finset.sum_nonneg fun z _ ↦
      d8CoherentOldResidual_nonneg G z₀ hab hw₀ z
        (d7NonUniversalDeletedEdge_mem G z e he)
  have hmR : 0 < ((universalVertices G).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr ⟨(z₀ : A), z₀.property⟩
  calc
    ((universalVertices G).card : ℝ)⁻¹ *
        (((universalVertices G).card : ℝ) - ∑ z,
          d8CoherentOldResidual G z₀ hab w₀ z
            ((d7NonUniversalDeletedEmbedding G z).sym2Map e)) ≤
      ((universalVertices G).card : ℝ)⁻¹ *
        ((universalVertices G).card : ℝ) :=
      mul_le_mul_of_nonneg_left (by linarith) (inv_nonneg.mpr hmR.le)
    _ = 1 := by field_simp

lemma d8ShortcutAverageWeight_edgeLoad_le_one_mixed
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G)) {a b : A}
    (hab : Gᶜ.Adj a b)
    (w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ)
    (P : D8SeparatedParameters G)
    (hreal : P.RealizesCoherentRemovedFamily G z₀ hab w₀)
    (hm : 4 ≤ (universalVertices G).card)
    (hw₀ : IsFractionalPacking
      (d8AugmentedDeletedGraph G (z₀ : A) a b
        (d8MissingLeft_ne_universal G hab z₀)
        (d8MissingRight_ne_universal G hab z₀)) w₀)
    (u : ↑(nonUniversalVertices G)) (y : ↑(universalVertices G)) :
    fractionalEdgeLoad G (d8ShortcutAverageWeight G z₀ hab w₀ P)
        s((u : A), (y : A)) ≤ 1 := by
  rw [fractionalEdgeLoad_d8ShortcutAverageWeight,
    d8ShortcutCorrection_numerator_mixed
      G z₀ hab w₀ P hreal hm u y]
  have hrem : 0 ≤ ∑ z : ↑(universalVertices G),
      d8MixedOldResidual G z₀ hab w₀ u y z := by
    apply Finset.sum_nonneg
    intro z _
    unfold d8MixedOldResidual
    split
    · exact le_rfl
    · rename_i hzy
      have hyz : (y : A) ≠ (z : A) := by
        intro h
        exact hzy (Subtype.ext h.symm)
      exact d8CoherentOldResidual_nonneg G z₀ hab hw₀ z
        (d7MixedDeletedEdge_mem G z y hyz u)
  have hmR : 0 < ((universalVertices G).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr ⟨(z₀ : A), z₀.property⟩
  calc
    ((universalVertices G).card : ℝ)⁻¹ *
        (((universalVertices G).card : ℝ) - ∑ z,
          d8MixedOldResidual G z₀ hab w₀ u y z) ≤
      ((universalVertices G).card : ℝ)⁻¹ *
        ((universalVertices G).card : ℝ) :=
      mul_le_mul_of_nonneg_left (by linarith) (inv_nonneg.mpr hmR.le)
    _ = 1 := by field_simp

lemma d8ShortcutAverageWeight_edgeLoad_le_one_universal
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G)) {a b : A}
    (hab : Gᶜ.Adj a b)
    (w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ)
    (P : D8SeparatedParameters G)
    (hreal : P.RealizesCoherentRemovedFamily G z₀ hab w₀)
    (hm : 4 ≤ (universalVertices G).card)
    (hw₀ : IsFractionalPacking
      (d8AugmentedDeletedGraph G (z₀ : A) a b
        (d8MissingLeft_ne_universal G hab z₀)
        (d8MissingRight_ne_universal G hab z₀)) w₀)
    (x y : ↑(universalVertices G)) (hxy : x ≠ y) :
    fractionalEdgeLoad G (d8ShortcutAverageWeight G z₀ hab w₀ P)
        s((x : A), (y : A)) ≤ 1 := by
  rw [fractionalEdgeLoad_d8ShortcutAverageWeight,
    d8ShortcutCorrection_numerator_universal
      G z₀ hab w₀ P hreal hm x y hxy]
  have hrem : 0 ≤ ∑ z : ↑(universalVertices G),
      d8UniversalOldResidual G z₀ hab w₀ x y z := by
    apply Finset.sum_nonneg
    intro z _
    unfold d8UniversalOldResidual
    split
    · exact le_rfl
    · rename_i hz
      have hxz : (x : A) ≠ (z : A) := by
        intro h
        exact hz (Or.inl (Subtype.ext h.symm))
      have hyz : (y : A) ≠ (z : A) := by
        intro h
        exact hz (Or.inr (Subtype.ext h.symm))
      have hxyA : (x : A) ≠ (y : A) := fun h ↦ hxy (Subtype.ext h)
      exact d8CoherentOldResidual_nonneg G z₀ hab hw₀ z
        (d7UniversalDeletedEdge_mem G z x y hxz hyz hxyA)
  have hmR : 0 < ((universalVertices G).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr ⟨(z₀ : A), z₀.property⟩
  calc
    ((universalVertices G).card : ℝ)⁻¹ *
        (((universalVertices G).card : ℝ) - ∑ z,
          d8UniversalOldResidual G z₀ hab w₀ x y z) ≤
      ((universalVertices G).card : ℝ)⁻¹ *
        ((universalVertices G).card : ℝ) :=
      mul_le_mul_of_nonneg_left (by linarith) (inv_nonneg.mpr hmR.le)
    _ = 1 := by field_simp

lemma d8ShortcutAverageWeight_isFractionalPacking
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G)) {a b : A}
    (hab : Gᶜ.Adj a b)
    (w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ)
    (P : D8SeparatedParameters G)
    (hreal : P.RealizesCoherentRemovedFamily G z₀ hab w₀)
    (hm : 4 ≤ (universalVertices G).card)
    (hshortcut : (Fintype.card A : ℝ) + 4 - 3 * P.betaMass ≤
      3 * ((universalVertices G).card : ℝ))
    (hw₀ : IsFractionalPacking
      (d8AugmentedDeletedGraph G (z₀ : A) a b
        (d8MissingLeft_ne_universal G hab z₀)
        (d8MissingRight_ne_universal G hab z₀)) w₀) :
    IsFractionalPacking G
      (d8ShortcutAverageWeight G z₀ hab w₀ P) := by
  constructor
  · intro t ht
    unfold d8ShortcutAverageWeight
    apply mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
    apply add_nonneg
    · apply Finset.sum_nonneg
      intro z _
      exact (IsFractionalPacking.extendInduced
        (G := G) (S := d7DeletedFinset (z : A))
        (d8CoherentStrippedWeight_isFractionalPacking
          G z₀ hab hw₀ z)).1 t ht
    · exact d8ShortcutCorrection_nonneg G P hm hshortcut t ht
  · intro e he
    induction e using Sym2.inductionOn with
    | _ x y =>
      have hxy : x ≠ y := by
        have hnd := G.not_isDiag_of_mem_edgeFinset he
        simpa only [Sym2.mk_isDiag_iff] using hnd
      have nonUniversal_of_not_universal : ∀ {v : A},
          v ∉ universalVertices G → v ∈ nonUniversalVertices G := by
        intro v hv
        apply mem_nonUniversalVertices.mpr
        have hvne : Gᶜ.degree v ≠ 0 := by
          intro hz
          exact hv (mem_universalVertices.mpr hz)
        exact Nat.pos_of_ne_zero hvne
      by_cases hxZ : x ∈ universalVertices G
      · let zx : ↑(universalVertices G) := ⟨x, hxZ⟩
        by_cases hyZ : y ∈ universalVertices G
        · let zy : ↑(universalVertices G) := ⟨y, hyZ⟩
          have hzxy : zx ≠ zy := by
            intro h
            exact hxy (congrArg Subtype.val h)
          exact d8ShortcutAverageWeight_edgeLoad_le_one_universal
            G z₀ hab w₀ P hreal hm hw₀ zx zy hzxy
        · let uy : ↑(nonUniversalVertices G) :=
            ⟨y, nonUniversal_of_not_universal hyZ⟩
          rw [show s(x, y) = s(y, x) from Sym2.eq_swap]
          exact d8ShortcutAverageWeight_edgeLoad_le_one_mixed
            G z₀ hab w₀ P hreal hm hw₀ uy zx
      · let ux : ↑(nonUniversalVertices G) :=
          ⟨x, nonUniversal_of_not_universal hxZ⟩
        by_cases hyZ : y ∈ universalVertices G
        · let zy : ↑(universalVertices G) := ⟨y, hyZ⟩
          exact d8ShortcutAverageWeight_edgeLoad_le_one_mixed
            G z₀ hab w₀ P hreal hm hw₀ ux zy
        · let uy : ↑(nonUniversalVertices G) :=
            ⟨y, nonUniversal_of_not_universal hyZ⟩
          let q : Sym2 (↑(nonUniversalVertices G)) := s(ux, uy)
          have hq : q ∈ (G.induce
              (↑(nonUniversalVertices G) : Set A)).edgeFinset := by
            rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
            change G.Adj x y
            simpa only [SimpleGraph.mem_edgeFinset,
              SimpleGraph.mem_edgeSet] using he
          exact d8ShortcutAverageWeight_edgeLoad_le_one_nonUniversal
            G z₀ hab w₀ P hreal hw₀ q hq

lemma fractionalSize_d8UUZCorrection (G : SimpleGraph A)
    (P : D8SeparatedParameters G) :
    fractionalSize G (d8UUZCorrection G P) =
      ((universalVertices G).card : ℝ) * P.betaMass := by
  unfold fractionalSize d8UUZCorrection
  rw [Finset.sum_comm]
  calc
    (∑ z : ↑(universalVertices G),
        ∑ t ∈ G.cliqueFinset 3,
          weightedAttachedEdgeWeight (nonUniversalVertices G) (z : A)
            (G.induce (↑(nonUniversalVertices G) : Set A)).edgeFinset
            P.beta t) =
        ∑ _z : ↑(universalVertices G), P.betaMass := by
      apply Fintype.sum_congr
      intro z
      change fractionalSize G
        (weightedAttachedEdgeWeight (nonUniversalVertices G) (z : A)
          (G.induce (↑(nonUniversalVertices G) : Set A)).edgeFinset
          P.beta) = P.betaMass
      rw [fractionalSize_weightedAttachedEdgeWeight
        (fun e he ↦ d7UUZTriangle_mem_cliqueFinset G z ⟨e, he⟩)]
      rfl
    _ = ((universalVertices G).card : ℝ) * P.betaMass := by simp

lemma fractionalSize_d8UZZCorrection (G : SimpleGraph A)
    (P : D8SeparatedParameters G) :
    fractionalSize G (d8UZZCorrection G P) =
      (((universalVertices G).card.choose 2 : ℕ) : ℝ) *
        ∑ u : ↑(nonUniversalVertices G), P.shortcutMixedCoefficient u := by
  unfold fractionalSize d8UZZCorrection
  rw [Finset.sum_comm]
  calc
    (∑ u : ↑(nonUniversalVertices G),
        ∑ t ∈ G.cliqueFinset 3,
          weightedAttachedEdgeWeight (universalVertices G) (u : A)
            (⊤ : SimpleGraph (↑(universalVertices G))).edgeFinset
            (fun _ ↦ P.shortcutMixedCoefficient u) t) =
        ∑ u : ↑(nonUniversalVertices G),
          (((universalVertices G).card.choose 2 : ℕ) : ℝ) *
            P.shortcutMixedCoefficient u := by
      apply Fintype.sum_congr
      intro u
      change fractionalSize G
        (weightedAttachedEdgeWeight (universalVertices G) (u : A)
          (⊤ : SimpleGraph (↑(universalVertices G))).edgeFinset
          (fun _ ↦ P.shortcutMixedCoefficient u)) = _
      rw [fractionalSize_weightedAttachedEdgeWeight
        (fun e he ↦ d7UZZTriangle_mem_cliqueFinset G u ⟨e, he⟩),
        Finset.sum_const, SimpleGraph.card_edgeFinset_top_eq_card_choose_two]
      simp only [Fintype.card_coe, nsmul_eq_mul]
    _ = (((universalVertices G).card.choose 2 : ℕ) : ℝ) *
          ∑ u : ↑(nonUniversalVertices G),
            P.shortcutMixedCoefficient u := by
      rw [Finset.mul_sum]

lemma fractionalSize_d8ZZZCorrection (G : SimpleGraph A)
    (P : D8SeparatedParameters G) :
    fractionalSize G (d8ZZZCorrection G P) =
      (((universalVertices G).card.choose 3 : ℕ) : ℝ) *
        P.shortcutUniversalCoefficient := by
  unfold fractionalSize d8ZZZCorrection singleTriangleWeight
  rw [Finset.sum_comm]
  calc
    (∑ q : ↑((universalVertices G).powersetCard 3),
        ∑ t ∈ G.cliqueFinset 3,
          if t = (q : Finset A) then P.shortcutUniversalCoefficient else 0) =
        ∑ _q : ↑((universalVertices G).powersetCard 3),
          P.shortcutUniversalCoefficient := by
      apply Fintype.sum_congr
      intro q
      calc
        (∑ t ∈ G.cliqueFinset 3,
            if t = (q : Finset A) then P.shortcutUniversalCoefficient else 0) =
            (if (q : Finset A) = (q : Finset A)
              then P.shortcutUniversalCoefficient else 0) := by
          apply Finset.sum_eq_single (q : Finset A)
          · intro t _ hne
            rw [if_neg hne]
          · intro hnot
            exact (hnot (d7ZZZTriangle_mem_cliqueFinset G q)).elim
        _ = P.shortcutUniversalCoefficient := by simp
    _ = (((universalVertices G).card.choose 3 : ℕ) : ℝ) *
          P.shortcutUniversalCoefficient := by
      simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
        Fintype.card_coe, Finset.card_powersetCard]

lemma fractionalSize_d8ShortcutCorrection (G : SimpleGraph A)
    (P : D8SeparatedParameters G) :
    fractionalSize G (d8ShortcutCorrection G P) =
      ((universalVertices G).card : ℝ) * P.betaMass +
      (((universalVertices G).card.choose 2 : ℕ) : ℝ) *
        ∑ u : ↑(nonUniversalVertices G), P.shortcutMixedCoefficient u +
      (((universalVertices G).card.choose 3 : ℕ) : ℝ) *
        P.shortcutUniversalCoefficient := by
  unfold fractionalSize d8ShortcutCorrection
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  exact congrArg₂ (· + ·)
    (congrArg₂ (· + ·)
      (fractionalSize_d8UUZCorrection G P)
      (fractionalSize_d8UZZCorrection G P))
    (fractionalSize_d8ZZZCorrection G P)

lemma three_mul_fractionalSize_d8ShortcutCorrection
    (G : SimpleGraph A) (P : D8SeparatedParameters G)
    (hm : 4 ≤ (universalVertices G).card) :
    3 * fractionalSize G (d8ShortcutCorrection G P) =
      ((universalVertices G).card : ℝ) *
        ((Fintype.card A : ℝ) - 1 +
          (((universalVertices G).card : ℝ) - 1) *
            (((universalVertices G).card : ℝ) - 2) / 2 * P.gamma +
          P.alphaMass + P.betaMass) := by
  rw [fractionalSize_d8ShortcutCorrection,
    P.sum_shortcutMixedCoefficient, Nat.cast_choose_two,
    cast_choose_three_d7]
  unfold D8SeparatedParameters.shortcutUniversalCoefficient
  let m : ℝ := ((universalVertices G).card : ℝ)
  have hm₁ : m - 1 ≠ 0 := by
    dsimp only [m]
    have : (1 : ℝ) < ((universalVertices G).card : ℝ) := by
      exact_mod_cast (by omega : 1 < (universalVertices G).card)
    linarith
  have hm₂ : m - 2 ≠ 0 := by
    dsimp only [m]
    have : (2 : ℝ) < ((universalVertices G).card : ℝ) := by
      exact_mod_cast (by omega : 2 < (universalVertices G).card)
    linarith
  change 3 * (m * P.betaMass +
      (m * (m - 1) / 2) *
        (((Fintype.card A : ℝ) - m + P.alphaMass - 2 * P.betaMass) /
          (m - 1)) +
      (m * (m - 1) * (m - 2) / 6) *
        ((2 + (m - 2) * P.gamma -
          ((Fintype.card A : ℝ) - m) / (m - 1) -
          P.alphaMass / (m - 1) + 2 * P.betaMass / (m - 1)) /
          (m - 2))) = _
  field_simp [hm₁, hm₂]
  ring

/-- For one universal-vertex deletion, the stripped packing size, old
residual, and removed-triangle orbit mass partition the old edge set. -/
lemma d8CoherentStrippedWeight_size_residual_identity
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G)) {a b : A}
    (hab : Gᶜ.Adj a b)
    (w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ)
    (P : D8SeparatedParameters G)
    (hreal : P.RealizesCoherentRemovedFamily G z₀ hab w₀)
    (z : ↑(universalVertices G)) :
    3 * fractionalSize (d7DeletedGraph G (z : A))
          (d8CoherentStrippedWeight G z₀ hab w₀ z) +
        (∑ e ∈ (d7DeletedGraph G (z : A)).edgeFinset,
          d8CoherentOldResidual G z₀ hab w₀ z e) +
        ((((universalVertices G).card : ℝ) - 1) *
            (((universalVertices G).card : ℝ) - 2) / 2) * P.gamma +
          P.alphaMass + P.betaMass =
      (Nat.card (d7DeletedGraph G (z : A)).edgeSet : ℝ) := by
  let K := d7DeletedGraph G (z : A)
  let x' := d7DeletedVertex (z : A) a
    (d8MissingLeft_ne_universal G hab z)
  let y' := d7DeletedVertex (z : A) b
    (d8MissingRight_ne_universal G hab z)
  let H := d8AugmentedDeletedGraph G (z : A) a b
    (d8MissingLeft_ne_universal G hab z)
    (d8MissingRight_ne_universal G hab z)
  let w := d8CoherentAugmentedWeight G z₀ w₀ z
  have hxy : x' ≠ y' := by
    intro h
    exact hab.ne (congrArg Subtype.val h)
  have hmissing : ¬ K.Adj x' y' := by
    intro h
    exact hab.2 h
  have hsum :
      (∑ e ∈ K.edgeFinset,
        (fractionalEdgeLoad K (stripEdgeTriangles s(x', y') w) e +
          augmentedOldResidual H w e +
          fractionalEdgeLoad H (edgeTrianglesPart s(x', y') w) e)) =
        ∑ _e ∈ K.edgeFinset, (1 : ℝ) := by
    apply Finset.sum_congr rfl
    intro e _he
    simpa only [K, H, x', y', d8AugmentedDeletedGraph] using
      (strip_oldResidual_removedLoad_eq_one K hxy hmissing w e)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    d8_sum_fractionalEdgeLoad_eq_three_mul_fractionalSize] at hsum
  change 3 * fractionalSize K
        (d8CoherentStrippedWeight G z₀ hab w₀ z) +
      (∑ e ∈ K.edgeFinset,
        d8CoherentOldResidual G z₀ hab w₀ z e) +
      (∑ e ∈ K.edgeFinset,
        d8RemovedLoad G (z : A) a b
          (d8MissingLeft_ne_universal G hab z)
          (d8MissingRight_ne_universal G hab z) w e) =
      ∑ _e ∈ K.edgeFinset, (1 : ℝ) at hsum
  rw [sum_d8RemovedLoad_coherent_eq_orbitTotal
    G z₀ hab w₀ P hreal z] at hsum
  simp only [Finset.sum_const, nsmul_one] at hsum
  have hcard : (K.edgeFinset.card : ℝ) =
      (Nat.card K.edgeSet : ℝ) := by
    rw [Nat.card_eq_fintype_card, SimpleGraph.card_edgeSet]
  rw [hcard] at hsum
  simpa only [K, add_assoc] using hsum

lemma fractionalSize_d8ShortcutAverageWeight
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G)) {a b : A}
    (hab : Gᶜ.Adj a b)
    (w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ)
    (P : D8SeparatedParameters G) :
    fractionalSize G (d8ShortcutAverageWeight G z₀ hab w₀ P) =
      (((universalVertices G).card : ℝ)⁻¹) *
        ((∑ z : ↑(universalVertices G),
          fractionalSize (d7DeletedGraph G (z : A))
            (d8CoherentStrippedWeight G z₀ hab w₀ z)) +
          fractionalSize G (d8ShortcutCorrection G P)) := by
  have hmain :
      (∑ t ∈ G.cliqueFinset 3,
        ∑ z : ↑(universalVertices G),
          d7LiftedWeight (z : A)
            (d8CoherentStrippedWeight G z₀ hab w₀ z) t) =
        ∑ z : ↑(universalVertices G),
          fractionalSize (d7DeletedGraph G (z : A))
            (d8CoherentStrippedWeight G z₀ hab w₀ z) := by
    rw [Finset.sum_comm]
    apply Fintype.sum_congr
    intro z
    exact fractionalSize_extendInducedWeight G
      (d7DeletedFinset (z : A))
      (d8CoherentStrippedWeight G z₀ hab w₀ z)
  unfold fractionalSize d8ShortcutAverageWeight
  rw [← Finset.mul_sum, Finset.sum_add_distrib, hmain]
  rfl

/-- Exact budget identity for the D8 shortcut: the ambient uncovered weight
is the average of the old residuals of the augmented deletion packings. -/
lemma fractionalUncoveredWeight_d8ShortcutAverageWeight
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G)) {a b : A}
    (hab : Gᶜ.Adj a b)
    (w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ)
    (P : D8SeparatedParameters G)
    (hreal : P.RealizesCoherentRemovedFamily G z₀ hab w₀)
    (hm : 4 ≤ (universalVertices G).card) :
    fractionalUncoveredWeight G
        (d8ShortcutAverageWeight G z₀ hab w₀ P) =
      (((universalVertices G).card : ℝ)⁻¹) *
        ∑ z : ↑(universalVertices G),
          ∑ e ∈ (d7DeletedGraph G (z : A)).edgeFinset,
            d8CoherentOldResidual G z₀ hab w₀ z e := by
  let m : ℝ := ((universalVertices G).card : ℝ)
  let q : ℝ := (Fintype.card A : ℝ)
  let E : ℝ := (Nat.card G.edgeSet : ℝ)
  let T : ℝ :=
    ((((universalVertices G).card : ℝ) - 1) *
        (((universalVertices G).card : ℝ) - 2) / 2) * P.gamma +
      P.alphaMass + P.betaMass
  let S : ℝ := ∑ z : ↑(universalVertices G),
    fractionalSize (d7DeletedGraph G (z : A))
      (d8CoherentStrippedWeight G z₀ hab w₀ z)
  let R : ℝ := ∑ z : ↑(universalVertices G),
    ∑ e ∈ (d7DeletedGraph G (z : A)).edgeFinset,
      d8CoherentOldResidual G z₀ hab w₀ z e
  let C : ℝ := fractionalSize G (d8ShortcutCorrection G P)
  have hm0 : m ≠ 0 := by
    dsimp only [m]
    exact_mod_cast (by omega : (universalVertices G).card ≠ 0)
  have hpoint : ∀ z : ↑(universalVertices G),
      3 * fractionalSize (d7DeletedGraph G (z : A))
            (d8CoherentStrippedWeight G z₀ hab w₀ z) +
          (∑ e ∈ (d7DeletedGraph G (z : A)).edgeFinset,
            d8CoherentOldResidual G z₀ hab w₀ z e) + T =
        E - q + 1 := by
    intro z
    have hpartition := d8CoherentStrippedWeight_size_residual_identity
      G z₀ hab w₀ P hreal z
    have hedgeNat := card_edgeSet_induce_univ_erase_add_degree G (z : A)
    have hdegree := degree_eq_card_sub_one_of_mem_universalVertices
      G z.property
    rw [hdegree] at hedgeNat
    have hcardPos : 1 ≤ Fintype.card A :=
      Fintype.card_pos_iff.mpr ⟨(z : A)⟩
    have hedge : E =
        (Nat.card (d7DeletedGraph G (z : A)).edgeSet : ℝ) + q - 1 := by
      dsimp only [E, q]
      have hcast := congrArg (fun n : ℕ ↦ (n : ℝ)) hedgeNat
      rw [Nat.cast_add, Nat.cast_sub hcardPos, Nat.cast_one] at hcast
      change (Nat.card G.edgeSet : ℝ) =
        (Nat.card (d7DeletedGraph G (z : A)).edgeSet : ℝ) +
          ((Fintype.card A : ℝ) - 1) at hcast
      linarith
    dsimp only [T]
    linarith
  have hsum : 3 * S + R + m * T = m * (E - q + 1) := by
    have h := show
        (∑ z : ↑(universalVertices G),
          (3 * fractionalSize (d7DeletedGraph G (z : A))
              (d8CoherentStrippedWeight G z₀ hab w₀ z) +
            (∑ e ∈ (d7DeletedGraph G (z : A)).edgeFinset,
              d8CoherentOldResidual G z₀ hab w₀ z e) + T)) =
          ∑ _z : ↑(universalVertices G), (E - q + 1) by
      apply Fintype.sum_congr
      exact hpoint
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum] at h
    simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
      Fintype.card_coe] at h
    simpa only [S, R, m] using h
  have hcorr : 3 * C = m * (q - 1 + T) := by
    simpa only [C, m, q, T, add_assoc] using
      (three_mul_fractionalSize_d8ShortcutCorrection G P hm)
  rw [fractionalUncoveredWeight_eq_card_sub_general,
    fractionalSize_d8ShortcutAverageWeight]
  change E - 3 * (m⁻¹ * (S + C)) = m⁻¹ * R
  field_simp [hm0]
  linarith

lemma sum_d8CoherentOldResidual_le_four
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G)) {a b : A}
    (hab : Gᶜ.Adj a b)
    {w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ}
    (hw₀ : IsFractionalPacking
      (d8AugmentedDeletedGraph G (z₀ : A) a b
        (d8MissingLeft_ne_universal G hab z₀)
        (d8MissingRight_ne_universal G hab z₀)) w₀)
    (hunc : fractionalUncoveredWeight
      (d8AugmentedDeletedGraph G (z₀ : A) a b
        (d8MissingLeft_ne_universal G hab z₀)
        (d8MissingRight_ne_universal G hab z₀)) w₀ ≤ 4)
    (z : ↑(universalVertices G)) :
    (∑ e ∈ (d7DeletedGraph G (z : A)).edgeFinset,
      d8CoherentOldResidual G z₀ hab w₀ z e) ≤ 4 := by
  have hxy : d7DeletedVertex (z : A) a
      (d8MissingLeft_ne_universal G hab z) ≠
      d7DeletedVertex (z : A) b
        (d8MissingRight_ne_universal G hab z) := by
    intro h
    exact hab.ne (congrArg Subtype.val h)
  have hpack := d8CoherentAugmentedWeight_isFractionalPacking
    G z₀ hab hw₀ z
  have hunc' : fractionalUncoveredWeight
      (d8AugmentedDeletedGraph G (z : A) a b
        (d8MissingLeft_ne_universal G hab z)
        (d8MissingRight_ne_universal G hab z))
      (d8CoherentAugmentedWeight G z₀ w₀ z) ≤ 4 := by
    rw [fractionalUncoveredWeight_d8CoherentAugmentedWeight
      G z₀ hab w₀ z]
    exact hunc
  exact sum_augmentedOldResidual_le hxy hpack hunc'

lemma fractionalUncoveredWeight_d8ShortcutAverageWeight_le_four
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G)) {a b : A}
    (hab : Gᶜ.Adj a b)
    {w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ}
    (P : D8SeparatedParameters G)
    (hreal : P.RealizesCoherentRemovedFamily G z₀ hab w₀)
    (hm : 4 ≤ (universalVertices G).card)
    (hw₀ : IsFractionalPacking
      (d8AugmentedDeletedGraph G (z₀ : A) a b
        (d8MissingLeft_ne_universal G hab z₀)
        (d8MissingRight_ne_universal G hab z₀)) w₀)
    (hunc : fractionalUncoveredWeight
      (d8AugmentedDeletedGraph G (z₀ : A) a b
        (d8MissingLeft_ne_universal G hab z₀)
        (d8MissingRight_ne_universal G hab z₀)) w₀ ≤ 4) :
    fractionalUncoveredWeight G
      (d8ShortcutAverageWeight G z₀ hab w₀ P) ≤ 4 := by
  rw [fractionalUncoveredWeight_d8ShortcutAverageWeight
    G z₀ hab w₀ P hreal hm]
  have hsum : (∑ z : ↑(universalVertices G),
      ∑ e ∈ (d7DeletedGraph G (z : A)).edgeFinset,
        d8CoherentOldResidual G z₀ hab w₀ z e) ≤
      ((universalVertices G).card : ℝ) * 4 := by
    calc
      _ ≤ ∑ _z : ↑(universalVertices G), (4 : ℝ) := by
        apply Finset.sum_le_sum
        intro z _
        exact sum_d8CoherentOldResidual_le_four G z₀ hab hw₀ hunc z
      _ = ((universalVertices G).card : ℝ) * 4 := by
        simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
          Fintype.card_coe]
  have hmR : 0 < ((universalVertices G).card : ℝ) := by
    exact_mod_cast (by omega : 0 < (universalVertices G).card)
  calc
    ((universalVertices G).card : ℝ)⁻¹ *
        (∑ z : ↑(universalVertices G),
          ∑ e ∈ (d7DeletedGraph G (z : A)).edgeFinset,
            d8CoherentOldResidual G z₀ hab w₀ z e) ≤
      ((universalVertices G).card : ℝ)⁻¹ *
        (((universalVertices G).card : ℝ) * 4) :=
      mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hmR.le)
    _ = 4 := by field_simp

lemma D8SeparatedParameters.shortcutMixedCoefficient_le_one
    {G : SimpleGraph A} (P : D8SeparatedParameters G)
    (hm : 4 ≤ (universalVertices G).card)
    (u : ↑(nonUniversalVertices G)) :
    P.shortcutMixedCoefficient u ≤ 1 := by
  let m : ℝ := ((universalVertices G).card : ℝ)
  have hm1 : 0 < m - 1 := by
    dsimp only [m]
    exact sub_pos.mpr (by exact_mod_cast (by omega :
      1 < (universalVertices G).card))
  have halphaSingle : P.alpha u ≤ ∑ v, P.alpha v := by
    apply Finset.single_le_sum
    · intro v _
      exact P.alpha_nonneg v
    · exact Finset.mem_univ u
  have halphaTerm : (m - 1) * P.alpha u ≤ P.alphaMass := by
    unfold D8SeparatedParameters.alphaMass
    exact mul_le_mul_of_nonneg_left halphaSingle hm1.le
  have hmass : P.alphaMass ≤ 2 := by
    have h := P.alphaMass_add_betaMass_le_two (by omega)
    have hb := P.betaMass_nonneg
    linarith
  have hbetaIncident : 0 ≤ P.betaIncident u := P.betaIncident_nonneg u
  unfold D8SeparatedParameters.shortcutMixedCoefficient
  change (1 + (m - 1) * P.alpha u - P.betaIncident u) / (m - 1) ≤ 1
  apply (div_le_one hm1).2
  have hm4 : (4 : ℝ) ≤ m := by
    dsimp only [m]
    exact_mod_cast hm
  linarith

lemma D8SeparatedParameters.shortcutUniversalCoefficient_le_three_halves
    {G : SimpleGraph A} (P : D8SeparatedParameters G)
    (hn : 14 ≤ Fintype.card A)
    (hm : 4 ≤ (universalVertices G).card) :
    P.shortcutUniversalCoefficient ≤ 3 / 2 := by
  let m : ℝ := ((universalVertices G).card : ℝ)
  let q : ℝ := (Fintype.card A : ℝ)
  let alpha : ℝ := P.alphaMass
  let beta : ℝ := P.betaMass
  have hm1 : 0 < m - 1 := by
    dsimp only [m]
    exact sub_pos.mpr (by exact_mod_cast (by omega :
      1 < (universalVertices G).card))
  have hm2 : 0 < m - 2 := by
    dsimp only [m]
    exact sub_pos.mpr (by exact_mod_cast (by omega :
      2 < (universalVertices G).card))
  have hq14 : (14 : ℝ) ≤ q := by
    dsimp only [q]
    exact_mod_cast hn
  have htotal : ((m - 1) * (m - 2) / 2) * P.gamma + alpha + beta ≤ 2 := by
    simpa only [m, alpha, beta, D8SeparatedParameters.alphaMass,
      D8SeparatedParameters.betaMass] using P.total_le_two
  have halpha0 : 0 ≤ alpha := P.alphaMass_nonneg (by omega)
  have hbeta0 : 0 ≤ beta := P.betaMass_nonneg
  have hm4 : (4 : ℝ) ≤ m := by
    dsimp only [m]
    exact_mod_cast hm
  have htotal2 : (m - 1) * (m - 2) * P.gamma +
      2 * alpha + 2 * beta ≤ 4 := by
    nlinarith [htotal]
  let numerator : ℝ :=
    2 + (m - 2) * P.gamma - (q - m) / (m - 1) -
      alpha / (m - 1) + 2 * beta / (m - 1)
  have heq : (m - 1) * numerator =
      2 * (m - 1) + (m - 1) * (m - 2) * P.gamma -
        (q - m) - alpha + 2 * beta := by
    dsimp only [numerator]
    field_simp [ne_of_gt hm1]
  have hnum : numerator ≤ (3 / 2) * (m - 2) := by
    have hmul : (m - 1) * numerator ≤
        (m - 1) * ((3 / 2) * (m - 2)) := by
      rw [heq]
      calc
        2 * (m - 1) + (m - 1) * (m - 2) * P.gamma -
              (q - m) - alpha + 2 * beta ≤
            3 * m + 2 - q - 3 * alpha := by
          linarith
        _ ≤ (m - 1) * ((3 / 2) * (m - 2)) := by
          nlinarith [sq_nonneg (m - 5 / 2)]
    nlinarith
  unfold D8SeparatedParameters.shortcutUniversalCoefficient
  change numerator / (m - 2) ≤ 3 / 2
  exact (div_le_iff₀ hm2).2 hnum

lemma d8UUZCorrection_apply
    (G : SimpleGraph A) (P : D8SeparatedParameters G)
    (u v : ↑(nonUniversalVertices G)) (huv : u ≠ v)
    (z : ↑(universalVertices G))
    (he : s(u, v) ∈ (G.induce
      (↑(nonUniversalVertices G) : Set A)).edgeFinset) :
    d8UUZCorrection G P {(z : A), (u : A), (v : A)} = P.beta s(u, v) := by
  let e : Sym2 (↑(nonUniversalVertices G)) := s(u, v)
  have heND : ¬e.IsDiag := by
    simpa only [e, Sym2.mk_isDiag_iff] using huv
  have htriangle : attachedEdgeTriangle (nonUniversalVertices G) (z : A) e =
      ({(z : A), (u : A), (v : A)} : Finset A) := by
    simp only [attachedEdgeTriangle, e, Sym2.toFinset_mk_eq,
      Finset.map_insert, Finset.map_singleton, inducedEmbedding_apply]
  unfold d8UUZCorrection
  rw [Fintype.sum_eq_single z]
  · rw [← htriangle]
    exact weightedAttachedEdgeWeight_apply_d7
      (universalVertex_not_mem_nonUniversalVertices G z.property)
      (fun f hf ↦
        (G.induce (↑(nonUniversalVertices G) : Set A)).not_isDiag_of_mem_edgeFinset hf)
      he
  · intro z' hz'
    unfold weightedAttachedEdgeWeight singleTriangleWeight
    apply Fintype.sum_eq_zero
    intro f
    rw [if_neg]
    intro hEq
    apply hz'
    apply Subtype.ext
    have hzmem : (z' : A) ∈ ({(z : A), (u : A), (v : A)} : Finset A) := by
      rw [hEq]
      simp [attachedEdgeTriangle]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hzmem
    rcases hzmem with h | h | h
    · exact h
    · exact (universalVertex_not_mem_nonUniversalVertices G z'.property
        (h ▸ u.property)).elim
    · exact (universalVertex_not_mem_nonUniversalVertices G z'.property
        (h ▸ v.property)).elim

lemma d8UZZCorrection_apply_UUZ_eq_zero
    (G : SimpleGraph A) (P : D8SeparatedParameters G)
    (u v : ↑(nonUniversalVertices G))
    (z : ↑(universalVertices G)) :
    d8UZZCorrection G P {(z : A), (u : A), (v : A)} = 0 := by
  unfold d8UZZCorrection weightedAttachedEdgeWeight singleTriangleWeight
  apply Fintype.sum_eq_zero
  intro u'
  apply Fintype.sum_eq_zero
  intro f
  rw [if_neg]
  intro hEq
  have hfND : ¬(f : Sym2 (↑(universalVertices G))).IsDiag :=
    (⊤ : SimpleGraph (↑(universalVertices G))).not_isDiag_of_mem_edgeFinset
      f.property
  have hmapSub : (f : Sym2 (↑(universalVertices G))).toFinset.map
      (inducedEmbedding (universalVertices G)) ⊆
        ({(z : A), (u : A), (v : A)} : Finset A) := by
    intro x hx
    rw [hEq]
    simp only [attachedEdgeTriangle, Finset.mem_insert]
    exact Or.inr hx
  have hmapSingleton : (f : Sym2 (↑(universalVertices G))).toFinset.map
      (inducedEmbedding (universalVertices G)) ⊆ ({(z : A)} : Finset A) := by
    intro x hx
    have hxTarget := hmapSub hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxTarget ⊢
    rcases hxTarget with hxz | hxu | hxv
    · exact hxz
    · obtain ⟨x', hx', rfl⟩ := Finset.mem_map.mp hx
      apply (universalVertex_not_mem_nonUniversalVertices G x'.property).elim
      change (x' : A) = (u : A) at hxu
      rw [hxu]
      exact u.property
    · obtain ⟨x', hx', rfl⟩ := Finset.mem_map.mp hx
      apply (universalVertex_not_mem_nonUniversalVertices G x'.property).elim
      change (x' : A) = (v : A) at hxv
      rw [hxv]
      exact v.property
  have hcardMap : ((f : Sym2 (↑(universalVertices G))).toFinset.map
      (inducedEmbedding (universalVertices G))).card = 2 := by
    rw [Finset.card_map, Sym2.card_toFinset_of_not_isDiag _ hfND]
  have hcardLe := Finset.card_le_card hmapSingleton
  rw [hcardMap, Finset.card_singleton] at hcardLe
  omega

lemma d8ZZZCorrection_apply_UUZ_eq_zero
    (G : SimpleGraph A) (P : D8SeparatedParameters G)
    (u v : ↑(nonUniversalVertices G))
    (z : ↑(universalVertices G)) :
    d8ZZZCorrection G P {(z : A), (u : A), (v : A)} = 0 := by
  unfold d8ZZZCorrection singleTriangleWeight
  apply Fintype.sum_eq_zero
  intro q
  rw [if_neg]
  intro hEq
  have huq : (u : A) ∈ (q : Finset A) := by
    rw [← hEq]
    simp
  have huZ := (Finset.mem_powersetCard.mp q.property).1 huq
  exact nonUniversalVertex_not_mem_universalVertices G u.property huZ

lemma d8ShortcutCorrection_apply_UUZ
    (G : SimpleGraph A) (P : D8SeparatedParameters G)
    (u v : ↑(nonUniversalVertices G)) (huv : u ≠ v)
    (z : ↑(universalVertices G))
    (he : s(u, v) ∈ (G.induce
      (↑(nonUniversalVertices G) : Set A)).edgeFinset) :
    d8ShortcutCorrection G P {(z : A), (u : A), (v : A)} =
      P.beta s(u, v) := by
  unfold d8ShortcutCorrection
  rw [d8UUZCorrection_apply G P u v huv z he,
    d8UZZCorrection_apply_UUZ_eq_zero G P u v z,
    d8ZZZCorrection_apply_UUZ_eq_zero G P u v z]
  ring

lemma d8UUZCorrection_apply_UZZ_eq_zero
    (G : SimpleGraph A) (P : D8SeparatedParameters G)
    (u : ↑(nonUniversalVertices G))
    (x y : ↑(universalVertices G)) :
    d8UUZCorrection G P {(u : A), (x : A), (y : A)} = 0 := by
  unfold d8UUZCorrection weightedAttachedEdgeWeight singleTriangleWeight
  apply Fintype.sum_eq_zero
  intro z
  apply Fintype.sum_eq_zero
  intro e
  rw [if_neg]
  intro hEq
  have heND : ¬(e : Sym2 (↑(nonUniversalVertices G))).IsDiag :=
    (G.induce (↑(nonUniversalVertices G) : Set A)).not_isDiag_of_mem_edgeFinset
      e.property
  have hmapSub : (e : Sym2 (↑(nonUniversalVertices G))).toFinset.map
      (inducedEmbedding (nonUniversalVertices G)) ⊆
        ({(u : A), (x : A), (y : A)} : Finset A) := by
    intro a ha
    rw [hEq]
    simp only [attachedEdgeTriangle, Finset.mem_insert]
    exact Or.inr ha
  have hmapSingleton : (e : Sym2 (↑(nonUniversalVertices G))).toFinset.map
      (inducedEmbedding (nonUniversalVertices G)) ⊆ ({(u : A)} : Finset A) := by
    intro a ha
    have haTarget := hmapSub ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at haTarget ⊢
    rcases haTarget with hau | hax | hay
    · exact hau
    · obtain ⟨a', ha', rfl⟩ := Finset.mem_map.mp ha
      apply (nonUniversalVertex_not_mem_universalVertices G a'.property).elim
      change (a' : A) = (x : A) at hax
      rw [hax]
      exact x.property
    · obtain ⟨a', ha', rfl⟩ := Finset.mem_map.mp ha
      apply (nonUniversalVertex_not_mem_universalVertices G a'.property).elim
      change (a' : A) = (y : A) at hay
      rw [hay]
      exact y.property
  have hcardMap : ((e : Sym2 (↑(nonUniversalVertices G))).toFinset.map
      (inducedEmbedding (nonUniversalVertices G))).card = 2 := by
    rw [Finset.card_map, Sym2.card_toFinset_of_not_isDiag _ heND]
  have hcardLe := Finset.card_le_card hmapSingleton
  rw [hcardMap, Finset.card_singleton] at hcardLe
  omega

lemma d8UZZCorrection_apply
    (G : SimpleGraph A) (P : D8SeparatedParameters G)
    (u : ↑(nonUniversalVertices G))
    (x y : ↑(universalVertices G)) (hxy : x ≠ y) :
    d8UZZCorrection G P {(u : A), (x : A), (y : A)} =
      P.shortcutMixedCoefficient u := by
  let e : Sym2 (↑(universalVertices G)) := s(x, y)
  have he : e ∈ (⊤ : SimpleGraph
      (↑(universalVertices G))).edgeFinset := by
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    exact hxy
  have htriangle : attachedEdgeTriangle (universalVertices G) (u : A) e =
      ({(u : A), (x : A), (y : A)} : Finset A) := by
    simp only [attachedEdgeTriangle, e, Sym2.toFinset_mk_eq,
      Finset.map_insert, Finset.map_singleton, inducedEmbedding_apply]
  unfold d8UZZCorrection
  rw [Fintype.sum_eq_single u]
  · rw [← htriangle]
    exact weightedAttachedEdgeWeight_apply_d7
      (nonUniversalVertex_not_mem_universalVertices G u.property)
      (fun f hf ↦
        (⊤ : SimpleGraph (↑(universalVertices G))).not_isDiag_of_mem_edgeFinset hf)
      he
  · intro u' hu'
    unfold weightedAttachedEdgeWeight singleTriangleWeight
    apply Fintype.sum_eq_zero
    intro f
    rw [if_neg]
    intro hEq
    apply hu'
    apply Subtype.ext
    have humem : (u' : A) ∈ ({(u : A), (x : A), (y : A)} : Finset A) := by
      rw [hEq]
      simp [attachedEdgeTriangle]
    simp only [Finset.mem_insert, Finset.mem_singleton] at humem
    rcases humem with h | h | h
    · exact h
    · exact (nonUniversalVertex_not_mem_universalVertices G u'.property
        (h ▸ x.property)).elim
    · exact (nonUniversalVertex_not_mem_universalVertices G u'.property
        (h ▸ y.property)).elim

lemma d8ZZZCorrection_apply_UZZ_eq_zero
    (G : SimpleGraph A) (P : D8SeparatedParameters G)
    (u : ↑(nonUniversalVertices G))
    (x y : ↑(universalVertices G)) :
    d8ZZZCorrection G P {(u : A), (x : A), (y : A)} = 0 := by
  unfold d8ZZZCorrection singleTriangleWeight
  apply Fintype.sum_eq_zero
  intro q
  rw [if_neg]
  intro hEq
  have huq : (u : A) ∈ (q : Finset A) := by
    rw [← hEq]
    simp
  have huZ := (Finset.mem_powersetCard.mp q.property).1 huq
  exact nonUniversalVertex_not_mem_universalVertices G u.property huZ

lemma d8ShortcutCorrection_apply_UZZ
    (G : SimpleGraph A) (P : D8SeparatedParameters G)
    (u : ↑(nonUniversalVertices G))
    (x y : ↑(universalVertices G)) (hxy : x ≠ y) :
    d8ShortcutCorrection G P {(u : A), (x : A), (y : A)} =
      P.shortcutMixedCoefficient u := by
  unfold d8ShortcutCorrection
  rw [d8UUZCorrection_apply_UZZ_eq_zero G P u x y,
    d8UZZCorrection_apply G P u x y hxy,
    d8ZZZCorrection_apply_UZZ_eq_zero G P u x y]
  ring

lemma d8UUZCorrection_apply_ZZZ_eq_zero
    (G : SimpleGraph A) (P : D8SeparatedParameters G)
    (x y z : ↑(universalVertices G)) :
    d8UUZCorrection G P {(x : A), (y : A), (z : A)} = 0 := by
  unfold d8UUZCorrection weightedAttachedEdgeWeight singleTriangleWeight
  apply Fintype.sum_eq_zero
  intro z'
  apply Fintype.sum_eq_zero
  intro e
  rw [if_neg]
  intro hEq
  obtain ⟨u, hu⟩ := Finset.nonempty_iff_ne_empty.mpr
    (Sym2.toFinset_ne_empty (e : Sym2 (↑(nonUniversalVertices G))))
  have huMap : (u : A) ∈ ({(x : A), (y : A), (z : A)} : Finset A) := by
    rw [hEq]
    simp only [attachedEdgeTriangle, Finset.mem_insert]
    right
    exact Finset.mem_map.mpr ⟨u, hu, rfl⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at huMap
  rcases huMap with h | h | h
  · apply (nonUniversalVertex_not_mem_universalVertices G u.property).elim
    change (u : A) = (x : A) at h
    rw [h]
    exact x.property
  · apply (nonUniversalVertex_not_mem_universalVertices G u.property).elim
    change (u : A) = (y : A) at h
    rw [h]
    exact y.property
  · apply (nonUniversalVertex_not_mem_universalVertices G u.property).elim
    change (u : A) = (z : A) at h
    rw [h]
    exact z.property

lemma d8UZZCorrection_apply_ZZZ_eq_zero
    (G : SimpleGraph A) (P : D8SeparatedParameters G)
    (x y z : ↑(universalVertices G)) :
    d8UZZCorrection G P {(x : A), (y : A), (z : A)} = 0 := by
  unfold d8UZZCorrection weightedAttachedEdgeWeight singleTriangleWeight
  apply Fintype.sum_eq_zero
  intro u
  apply Fintype.sum_eq_zero
  intro e
  rw [if_neg]
  intro hEq
  have huTarget : (u : A) ∈
      ({(x : A), (y : A), (z : A)} : Finset A) := by
    rw [hEq]
    simp [attachedEdgeTriangle]
  simp only [Finset.mem_insert, Finset.mem_singleton] at huTarget
  rcases huTarget with h | h | h
  · exact (nonUniversalVertex_not_mem_universalVertices G u.property
      (h ▸ x.property)).elim
  · exact (nonUniversalVertex_not_mem_universalVertices G u.property
      (h ▸ y.property)).elim
  · exact (nonUniversalVertex_not_mem_universalVertices G u.property
      (h ▸ z.property)).elim

lemma d8ZZZCorrection_apply
    (G : SimpleGraph A) (P : D8SeparatedParameters G)
    (x y z : ↑(universalVertices G))
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    d8ZZZCorrection G P {(x : A), (y : A), (z : A)} =
      P.shortcutUniversalCoefficient := by
  have hxyA : (x : A) ≠ (y : A) := fun h ↦ hxy (Subtype.ext h)
  have hxzA : (x : A) ≠ (z : A) := fun h ↦ hxz (Subtype.ext h)
  have hyzA : (y : A) ≠ (z : A) := fun h ↦ hyz (Subtype.ext h)
  let q0 : Finset A := {(x : A), (y : A), (z : A)}
  have hqsub : q0 ⊆ universalVertices G := by
    intro a ha
    simp only [q0, Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl
    · exact x.property
    · exact y.property
    · exact z.property
  have hqcard : q0.card = 3 := by
    simp [q0, hxyA, hxzA, hyzA]
  let q : ↑((universalVertices G).powersetCard 3) :=
    ⟨q0, Finset.mem_powersetCard.mpr ⟨hqsub, hqcard⟩⟩
  unfold d8ZZZCorrection singleTriangleWeight
  rw [Fintype.sum_eq_single q]
  · dsimp only [q, q0]
    rw [if_pos rfl]
  · intro q' hne
    rw [if_neg]
    intro hEq
    apply hne
    apply Subtype.ext
    exact hEq.symm

lemma d8ShortcutCorrection_apply_ZZZ
    (G : SimpleGraph A) (P : D8SeparatedParameters G)
    (x y z : ↑(universalVertices G))
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    d8ShortcutCorrection G P {(x : A), (y : A), (z : A)} =
      P.shortcutUniversalCoefficient := by
  unfold d8ShortcutCorrection
  rw [d8UUZCorrection_apply_ZZZ_eq_zero G P x y z,
    d8UZZCorrection_apply_ZZZ_eq_zero G P x y z,
    d8ZZZCorrection_apply G P x y z hxy hxz hyz]
  ring

lemma d8UUZCorrection_apply_UUU_eq_zero
    (G : SimpleGraph A) (P : D8SeparatedParameters G)
    (u v w : ↑(nonUniversalVertices G)) :
    d8UUZCorrection G P {(u : A), (v : A), (w : A)} = 0 := by
  unfold d8UUZCorrection weightedAttachedEdgeWeight singleTriangleWeight
  apply Fintype.sum_eq_zero
  intro z
  apply Fintype.sum_eq_zero
  intro e
  rw [if_neg]
  intro hEq
  have hzTarget : (z : A) ∈
      ({(u : A), (v : A), (w : A)} : Finset A) := by
    rw [hEq]
    simp [attachedEdgeTriangle]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hzTarget
  rcases hzTarget with h | h | h
  · exact (universalVertex_not_mem_nonUniversalVertices G z.property
      (h ▸ u.property)).elim
  · exact (universalVertex_not_mem_nonUniversalVertices G z.property
      (h ▸ v.property)).elim
  · exact (universalVertex_not_mem_nonUniversalVertices G z.property
      (h ▸ w.property)).elim

private lemma weightedAttachedEdgeWeight_eq_zero_of_not_exists_d8
    {S : Finset A} {u : A} {C : Finset (Sym2 S)}
    {r : Sym2 S → ℝ} {t : Finset A}
    (ht : ¬ ∃ e ∈ C, t = attachedEdgeTriangle S u e) :
    weightedAttachedEdgeWeight S u C r t = 0 := by
  unfold weightedAttachedEdgeWeight singleTriangleWeight
  apply Fintype.sum_eq_zero
  intro e
  rw [if_neg]
  intro h
  exact ht ⟨e, e.property, h⟩

lemma d8UZZCorrection_apply_UUU_eq_zero
    (G : SimpleGraph A) (P : D8SeparatedParameters G)
    (u v w : ↑(nonUniversalVertices G)) :
    d8UZZCorrection G P {(u : A), (v : A), (w : A)} = 0 := by
  unfold d8UZZCorrection
  apply Fintype.sum_eq_zero
  intro u'
  apply weightedAttachedEdgeWeight_eq_zero_of_not_exists_d8
  rintro ⟨e, he, hEq⟩
  obtain ⟨z, hz⟩ := Finset.nonempty_iff_ne_empty.mpr
    (Sym2.toFinset_ne_empty e)
  have hzMap : (z : A) ∈ ({(u : A), (v : A), (w : A)} : Finset A) := by
    rw [hEq]
    simp only [attachedEdgeTriangle, Finset.mem_insert]
    right
    exact Finset.mem_map.mpr ⟨z, hz, rfl⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hzMap
  rcases hzMap with h | h | h
  · exact (nonUniversalVertex_not_mem_universalVertices G u.property
      (by rw [← h]; exact z.property)).elim
  · exact (nonUniversalVertex_not_mem_universalVertices G v.property
      (by rw [← h]; exact z.property)).elim
  · exact (nonUniversalVertex_not_mem_universalVertices G w.property
      (by rw [← h]; exact z.property)).elim

lemma d8ZZZCorrection_apply_UUU_eq_zero
    (G : SimpleGraph A) (P : D8SeparatedParameters G)
    (u v w : ↑(nonUniversalVertices G)) :
    d8ZZZCorrection G P {(u : A), (v : A), (w : A)} = 0 := by
  unfold d8ZZZCorrection singleTriangleWeight
  apply Fintype.sum_eq_zero
  intro q
  rw [if_neg]
  intro hEq
  have hqne : (q : Finset A) ≠ ∅ := by
    intro hzero
    have hcard := (Finset.mem_powersetCard.mp q.property).2
    rw [hzero, Finset.card_empty] at hcard
    omega
  obtain ⟨z, hzq⟩ := Finset.nonempty_iff_ne_empty.mpr hqne
  have hzTarget : z ∈ ({(u : A), (v : A), (w : A)} : Finset A) := by
    rw [hEq]
    exact hzq
  have hzZ := (Finset.mem_powersetCard.mp q.property).1 hzq
  simp only [Finset.mem_insert, Finset.mem_singleton] at hzTarget
  rcases hzTarget with h | h | h
  · exact (nonUniversalVertex_not_mem_universalVertices G u.property
      (h ▸ hzZ)).elim
  · exact (nonUniversalVertex_not_mem_universalVertices G v.property
      (h ▸ hzZ)).elim
  · exact (nonUniversalVertex_not_mem_universalVertices G w.property
      (h ▸ hzZ)).elim

lemma d8ShortcutCorrection_apply_UUU_eq_zero
    (G : SimpleGraph A) (P : D8SeparatedParameters G)
    (u v w : ↑(nonUniversalVertices G)) :
    d8ShortcutCorrection G P {(u : A), (v : A), (w : A)} = 0 := by
  unfold d8ShortcutCorrection
  rw [d8UUZCorrection_apply_UUU_eq_zero G P u v w,
    d8UZZCorrection_apply_UUU_eq_zero G P u v w,
    d8ZZZCorrection_apply_UUU_eq_zero G P u v w]
  ring

lemma d8CoherentLiftedStrippedWeight_add_beta_le_one
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G)) {a b : A}
    (hab : Gᶜ.Adj a b)
    {w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ}
    (P : D8SeparatedParameters G)
    (hreal : P.RealizesCoherentRemovedFamily G z₀ hab w₀)
    (hw₀ : IsFractionalPacking
      (d8AugmentedDeletedGraph G (z₀ : A) a b
        (d8MissingLeft_ne_universal G hab z₀)
        (d8MissingRight_ne_universal G hab z₀)) w₀)
    (u v : ↑(nonUniversalVertices G)) (huv : u ≠ v)
    (z y : ↑(universalVertices G)) (hyz : y ≠ z)
    (he : s(u, v) ∈ (G.induce
      (↑(nonUniversalVertices G) : Set A)).edgeFinset)
    (ht : ({(z : A), (u : A), (v : A)} : Finset A) ∈
      G.cliqueFinset 3) :
    d7LiftedWeight (y : A)
        (d8CoherentStrippedWeight G z₀ hab w₀ y)
        {(z : A), (u : A), (v : A)} + P.beta s(u, v) ≤ 1 := by
  let e : Sym2 (↑(nonUniversalVertices G)) := s(u, v)
  let K := d7DeletedGraph G (y : A)
  let w := d8CoherentAugmentedWeight G z₀ w₀ y
  let ws := d8CoherentStrippedWeight G z₀ hab w₀ y
  have hwStrip := d8CoherentStrippedWeight_isFractionalPacking
    G z₀ hab hw₀ y
  have hwLift : IsFractionalPacking G (d7LiftedWeight (y : A) ws) := by
    exact IsFractionalPacking.extendInduced (G := G)
      (S := d7DeletedFinset (y : A)) hwStrip
  have het : (inducedEmbedding (nonUniversalVertices G)).sym2Map e ∈
      ({(z : A), (u : A), (v : A)} : Finset A).sym2 := by
    simp only [e, Sym2.map_mk, inducedEmbedding_apply,
      Finset.mk_mem_sym2_iff]
    simp
  have hweight := hwLift.weight_le_fractionalEdgeLoad ht het
  rw [fractionalEdgeLoad_d7LiftedWeight_nonUniversal G y ws e] at hweight
  have hne : d7DeletedVertex (y : A) a
      (d8MissingLeft_ne_universal G hab y) ≠
      d7DeletedVertex (y : A) b
        (d8MissingRight_ne_universal G hab y) := by
    intro h
    exact hab.ne (congrArg Subtype.val h)
  have hmissing : ¬K.Adj
      (d7DeletedVertex (y : A) a (d8MissingLeft_ne_universal G hab y))
      (d7DeletedVertex (y : A) b (d8MissingRight_ne_universal G hab y)) := by
    intro h
    exact hab.2 h
  have hone := strip_oldResidual_removedLoad_eq_one K hne hmissing w
    ((d7NonUniversalDeletedEmbedding G y).sym2Map e)
  change fractionalEdgeLoad K ws
        ((d7NonUniversalDeletedEmbedding G y).sym2Map e) +
      d8CoherentOldResidual G z₀ hab w₀ y
        ((d7NonUniversalDeletedEmbedding G y).sym2Map e) +
      d8RemovedLoad G (y : A) a b
        (d8MissingLeft_ne_universal G hab y)
        (d8MissingRight_ne_universal G hab y) w
        ((d7NonUniversalDeletedEmbedding G y).sym2Map e) = 1 at hone
  rw [hreal.beta_eq y e] at hone
  have hres := d8CoherentOldResidual_nonneg G z₀ hab hw₀ y
    (d7NonUniversalDeletedEdge_mem G y e he)
  change _ + P.beta e ≤ 1
  linarith

lemma d8ShortcutAverageWeight_UUZ_numerator_le
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G)) {a b : A}
    (hab : Gᶜ.Adj a b)
    {w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ}
    (P : D8SeparatedParameters G)
    (hreal : P.RealizesCoherentRemovedFamily G z₀ hab w₀)
    (hm : 4 ≤ (universalVertices G).card)
    (hw₀ : IsFractionalPacking
      (d8AugmentedDeletedGraph G (z₀ : A) a b
        (d8MissingLeft_ne_universal G hab z₀)
        (d8MissingRight_ne_universal G hab z₀)) w₀)
    (hw₀Half : IsHalfBounded
      (d8AugmentedDeletedGraph G (z₀ : A) a b
        (d8MissingLeft_ne_universal G hab z₀)
        (d8MissingRight_ne_universal G hab z₀)) w₀)
    (u v : ↑(nonUniversalVertices G)) (huv : u ≠ v)
    (z : ↑(universalVertices G))
    (he : s(u, v) ∈ (G.induce
      (↑(nonUniversalVertices G) : Set A)).edgeFinset)
    (ht : ({(z : A), (u : A), (v : A)} : Finset A) ∈
      G.cliqueFinset 3) :
    (∑ y : ↑(universalVertices G),
      d7LiftedWeight (y : A)
        (d8CoherentStrippedWeight G z₀ hab w₀ y)
        {(z : A), (u : A), (v : A)}) +
      d8ShortcutCorrection G P {(z : A), (u : A), (v : A)} ≤
        ((universalVertices G).card : ℝ) / 2 := by
  obtain ⟨y, hyz⟩ := Fintype.exists_ne_of_one_lt_card
    (by simpa only [Fintype.card_coe] using
      (show 1 < (universalVertices G).card by omega)) z
  rw [d8ShortcutCorrection_apply_UUZ G P u v huv z he]
  let f : ↑(universalVertices G) → ℝ := fun x ↦
    d7LiftedWeight (x : A)
      (d8CoherentStrippedWeight G z₀ hab w₀ x)
      {(z : A), (u : A), (v : A)}
  have hfz : f z ≤ 0 := by
    rw [show f z = 0 by
      exact d7LiftedWeight_eq_zero_of_mem G z _ (by simp)]
  have hfy : f y ≤ 1 - P.beta s(u, v) := by
    have hpair := d8CoherentLiftedStrippedWeight_add_beta_le_one
      G z₀ hab P hreal hw₀ u v huv z y hyz he ht
    dsimp only [f]
    linarith
  have hrest : ∀ x, x ≠ z → x ≠ y → f x ≤ 1 / 2 := by
    intro x _ _
    exact d7LiftedWeight_le_half G x
      (d8CoherentStrippedWeight_halfBounded G z₀ hab hw₀Half x) ht
  have hsum := sum_le_two_exception f z y hyz.symm 0
    (1 - P.beta s(u, v)) (1 / 2) hfz hfy hrest
  dsimp only [f] at hsum
  rw [Fintype.card_coe] at hsum
  linarith

lemma d8ShortcutAverageWeight_UZZ_numerator_le
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G)) {a b : A}
    (hab : Gᶜ.Adj a b)
    {w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ}
    (P : D8SeparatedParameters G)
    (hm : 4 ≤ (universalVertices G).card)
    (hw₀Half : IsHalfBounded
      (d8AugmentedDeletedGraph G (z₀ : A) a b
        (d8MissingLeft_ne_universal G hab z₀)
        (d8MissingRight_ne_universal G hab z₀)) w₀)
    (u : ↑(nonUniversalVertices G))
    (x y : ↑(universalVertices G)) (hxy : x ≠ y)
    (ht : ({(u : A), (x : A), (y : A)} : Finset A) ∈
      G.cliqueFinset 3) :
    (∑ z : ↑(universalVertices G),
      d7LiftedWeight (z : A)
        (d8CoherentStrippedWeight G z₀ hab w₀ z)
        {(u : A), (x : A), (y : A)}) +
      d8ShortcutCorrection G P {(u : A), (x : A), (y : A)} ≤
        ((universalVertices G).card : ℝ) / 2 := by
  rw [d8ShortcutCorrection_apply_UZZ G P u x y hxy]
  let f : ↑(universalVertices G) → ℝ := fun z ↦
    d7LiftedWeight (z : A)
      (d8CoherentStrippedWeight G z₀ hab w₀ z)
      {(u : A), (x : A), (y : A)}
  have hfx : f x ≤ 0 := by
    rw [show f x = 0 by
      exact d7LiftedWeight_eq_zero_of_mem G x _ (by simp)]
  have hfy : f y ≤ 0 := by
    rw [show f y = 0 by
      exact d7LiftedWeight_eq_zero_of_mem G y _ (by simp)]
  have hrest : ∀ z, z ≠ x → z ≠ y → f z ≤ 1 / 2 := by
    intro z _ _
    exact d7LiftedWeight_le_half G z
      (d8CoherentStrippedWeight_halfBounded G z₀ hab hw₀Half z) ht
  have hsum := sum_le_two_exception f x y hxy 0 0 (1 / 2)
    hfx hfy hrest
  dsimp only [f] at hsum
  rw [Fintype.card_coe] at hsum
  have hcorr := P.shortcutMixedCoefficient_le_one hm u
  linarith

lemma d8ShortcutAverageWeight_ZZZ_numerator_le
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G)) {a b : A}
    (hab : Gᶜ.Adj a b)
    {w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ}
    (P : D8SeparatedParameters G)
    (hn : 14 ≤ Fintype.card A)
    (hm : 4 ≤ (universalVertices G).card)
    (hw₀Half : IsHalfBounded
      (d8AugmentedDeletedGraph G (z₀ : A) a b
        (d8MissingLeft_ne_universal G hab z₀)
        (d8MissingRight_ne_universal G hab z₀)) w₀)
    (x y z : ↑(universalVertices G))
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (ht : ({(x : A), (y : A), (z : A)} : Finset A) ∈
      G.cliqueFinset 3) :
    (∑ w : ↑(universalVertices G),
      d7LiftedWeight (w : A)
        (d8CoherentStrippedWeight G z₀ hab w₀ w)
        {(x : A), (y : A), (z : A)}) +
      d8ShortcutCorrection G P {(x : A), (y : A), (z : A)} ≤
        ((universalVertices G).card : ℝ) / 2 := by
  rw [d8ShortcutCorrection_apply_ZZZ G P x y z hxy hxz hyz]
  let f : ↑(universalVertices G) → ℝ := fun w ↦
    d7LiftedWeight (w : A)
      (d8CoherentStrippedWeight G z₀ hab w₀ w)
      {(x : A), (y : A), (z : A)}
  have hfx : f x ≤ 0 := by
    rw [show f x = 0 by
      exact d7LiftedWeight_eq_zero_of_mem G x _ (by simp)]
  have hfy : f y ≤ 0 := by
    rw [show f y = 0 by
      exact d7LiftedWeight_eq_zero_of_mem G y _ (by simp)]
  have hfz : f z ≤ 0 := by
    rw [show f z = 0 by
      exact d7LiftedWeight_eq_zero_of_mem G z _ (by simp)]
  have hrest : ∀ w, w ≠ x → w ≠ y → w ≠ z → f w ≤ 1 / 2 := by
    intro w _ _ _
    exact d7LiftedWeight_le_half G w
      (d8CoherentStrippedWeight_halfBounded G z₀ hab hw₀Half w) ht
  have hsum := sum_le_three_zero f x y z hxy hxz hyz
    hfx hfy hfz hrest
  dsimp only [f] at hsum
  rw [Fintype.card_coe] at hsum
  have hcorr := P.shortcutUniversalCoefficient_le_three_halves hn hm
  linarith

lemma d8ShortcutAverageWeight_UUU_numerator_le
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G)) {a b : A}
    (hab : Gᶜ.Adj a b)
    {w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ}
    (P : D8SeparatedParameters G)
    (hw₀Half : IsHalfBounded
      (d8AugmentedDeletedGraph G (z₀ : A) a b
        (d8MissingLeft_ne_universal G hab z₀)
        (d8MissingRight_ne_universal G hab z₀)) w₀)
    (u v w : ↑(nonUniversalVertices G))
    (ht : ({(u : A), (v : A), (w : A)} : Finset A) ∈
      G.cliqueFinset 3) :
    (∑ z : ↑(universalVertices G),
      d7LiftedWeight (z : A)
        (d8CoherentStrippedWeight G z₀ hab w₀ z)
        {(u : A), (v : A), (w : A)}) +
      d8ShortcutCorrection G P {(u : A), (v : A), (w : A)} ≤
        ((universalVertices G).card : ℝ) / 2 := by
  rw [d8ShortcutCorrection_apply_UUU_eq_zero G P u v w, add_zero]
  calc
    (∑ z : ↑(universalVertices G),
      d7LiftedWeight (z : A)
        (d8CoherentStrippedWeight G z₀ hab w₀ z)
        {(u : A), (v : A), (w : A)}) ≤
        ∑ _z : ↑(universalVertices G), (1 / 2 : ℝ) := by
      apply Finset.sum_le_sum
      intro z _
      exact d7LiftedWeight_le_half G z
        (d8CoherentStrippedWeight_halfBounded G z₀ hab hw₀Half z) ht
    _ = ((universalVertices G).card : ℝ) / 2 := by
      simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
        Fintype.card_coe]
      ring

private lemma d8ShortcutAverageWeight_numerator_le_of_mem_universal_left
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G)) {x y : A}
    (hxy : Gᶜ.Adj x y)
    {w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ}
    (P : D8SeparatedParameters G)
    (hreal : P.RealizesCoherentRemovedFamily G z₀ hxy w₀)
    (hn : 14 ≤ Fintype.card A)
    (hm : 4 ≤ (universalVertices G).card)
    (hw₀ : IsFractionalPacking
      (d8AugmentedDeletedGraph G (z₀ : A) x y
        (d8MissingLeft_ne_universal G hxy z₀)
        (d8MissingRight_ne_universal G hxy z₀)) w₀)
    (hw₀Half : IsHalfBounded
      (d8AugmentedDeletedGraph G (z₀ : A) x y
        (d8MissingLeft_ne_universal G hxy z₀)
        (d8MissingRight_ne_universal G hxy z₀)) w₀)
    {a b c : A} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ht : ({a, b, c} : Finset A) ∈ G.cliqueFinset 3)
    (haZ : a ∈ universalVertices G) :
    (∑ z : ↑(universalVertices G),
      d7LiftedWeight (z : A)
        (d8CoherentStrippedWeight G z₀ hxy w₀ z) {a, b, c}) +
        d8ShortcutCorrection G P {a, b, c} ≤
          ((universalVertices G).card : ℝ) / 2 := by
  have htri := SimpleGraph.mem_cliqueFinset_iff.mp ht
  have hadj := SimpleGraph.is3Clique_triple_iff.mp htri
  have nonUniversal_of_not_universal : ∀ {v : A},
      v ∉ universalVertices G → v ∈ nonUniversalVertices G := by
    intro v hv
    apply mem_nonUniversalVertices.mpr
    have hvne : Gᶜ.degree v ≠ 0 := by
      intro hz
      exact hv (mem_universalVertices.mpr hz)
    exact Nat.pos_of_ne_zero hvne
  let za : ↑(universalVertices G) := ⟨a, haZ⟩
  by_cases hbZ : b ∈ universalVertices G
  · let zb : ↑(universalVertices G) := ⟨b, hbZ⟩
    by_cases hcZ : c ∈ universalVertices G
    · let zc : ↑(universalVertices G) := ⟨c, hcZ⟩
      have hzab : za ≠ zb := fun h ↦ hab (congrArg Subtype.val h)
      have hzac : za ≠ zc := fun h ↦ hac (congrArg Subtype.val h)
      have hzbc : zb ≠ zc := fun h ↦ hbc (congrArg Subtype.val h)
      exact d8ShortcutAverageWeight_ZZZ_numerator_le G z₀ hxy P hn hm
        hw₀Half za zb zc hzab hzac hzbc ht
    · let uc : ↑(nonUniversalVertices G) :=
        ⟨c, nonUniversal_of_not_universal hcZ⟩
      have hzab : za ≠ zb := fun h ↦ hab (congrArg Subtype.val h)
      have hset : ({(uc : A), (za : A), (zb : A)} : Finset A) =
          ({a, b, c} : Finset A) := by
        ext q
        simp only [uc, za, zb, Finset.mem_insert, Finset.mem_singleton]
        tauto
      have htri' : ({(uc : A), (za : A), (zb : A)} : Finset A) ∈
          G.cliqueFinset 3 := by
        rw [hset]
        exact ht
      have hnum := d8ShortcutAverageWeight_UZZ_numerator_le
        G z₀ hxy P hm hw₀Half uc za zb hzab htri'
      rwa [hset] at hnum
  · let ub : ↑(nonUniversalVertices G) :=
      ⟨b, nonUniversal_of_not_universal hbZ⟩
    by_cases hcZ : c ∈ universalVertices G
    · let zc : ↑(universalVertices G) := ⟨c, hcZ⟩
      have hzac : za ≠ zc := fun h ↦ hac (congrArg Subtype.val h)
      have hset : ({(ub : A), (za : A), (zc : A)} : Finset A) =
          ({a, b, c} : Finset A) := by
        ext q
        simp only [ub, za, zc, Finset.mem_insert, Finset.mem_singleton]
        tauto
      have htri' : ({(ub : A), (za : A), (zc : A)} : Finset A) ∈
          G.cliqueFinset 3 := by
        rw [hset]
        exact ht
      have hnum := d8ShortcutAverageWeight_UZZ_numerator_le
        G z₀ hxy P hm hw₀Half ub za zc hzac htri'
      rwa [hset] at hnum
    · let uc : ↑(nonUniversalVertices G) :=
        ⟨c, nonUniversal_of_not_universal hcZ⟩
      have hubc : ub ≠ uc := fun h ↦ hbc (congrArg Subtype.val h)
      have he : s(ub, uc) ∈ (G.induce
          (↑(nonUniversalVertices G) : Set A)).edgeFinset := by
        rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
        change G.Adj b c
        exact hadj.2.2
      exact d8ShortcutAverageWeight_UUZ_numerator_le
        G z₀ hxy P hreal hm hw₀ hw₀Half ub uc hubc za he ht

private lemma d8ShortcutAverageWeight_numerator_le_of_not_mem_universal_left
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G)) {x y : A}
    (hxy : Gᶜ.Adj x y)
    {w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ}
    (P : D8SeparatedParameters G)
    (hreal : P.RealizesCoherentRemovedFamily G z₀ hxy w₀)
    (hm : 4 ≤ (universalVertices G).card)
    (hw₀ : IsFractionalPacking
      (d8AugmentedDeletedGraph G (z₀ : A) x y
        (d8MissingLeft_ne_universal G hxy z₀)
        (d8MissingRight_ne_universal G hxy z₀)) w₀)
    (hw₀Half : IsHalfBounded
      (d8AugmentedDeletedGraph G (z₀ : A) x y
        (d8MissingLeft_ne_universal G hxy z₀)
        (d8MissingRight_ne_universal G hxy z₀)) w₀)
    {a b c : A} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ht : ({a, b, c} : Finset A) ∈ G.cliqueFinset 3)
    (haZ : a ∉ universalVertices G) :
    (∑ z : ↑(universalVertices G),
      d7LiftedWeight (z : A)
        (d8CoherentStrippedWeight G z₀ hxy w₀ z) {a, b, c}) +
        d8ShortcutCorrection G P {a, b, c} ≤
          ((universalVertices G).card : ℝ) / 2 := by
  have htri := SimpleGraph.mem_cliqueFinset_iff.mp ht
  have hadj := SimpleGraph.is3Clique_triple_iff.mp htri
  have nonUniversal_of_not_universal : ∀ {v : A},
      v ∉ universalVertices G → v ∈ nonUniversalVertices G := by
    intro v hv
    apply mem_nonUniversalVertices.mpr
    have hvne : Gᶜ.degree v ≠ 0 := by
      intro hz
      exact hv (mem_universalVertices.mpr hz)
    exact Nat.pos_of_ne_zero hvne
  let ua : ↑(nonUniversalVertices G) :=
    ⟨a, nonUniversal_of_not_universal haZ⟩
  by_cases hbZ : b ∈ universalVertices G
  · let zb : ↑(universalVertices G) := ⟨b, hbZ⟩
    by_cases hcZ : c ∈ universalVertices G
    · let zc : ↑(universalVertices G) := ⟨c, hcZ⟩
      have hzbc : zb ≠ zc := fun h ↦ hbc (congrArg Subtype.val h)
      exact d8ShortcutAverageWeight_UZZ_numerator_le
        G z₀ hxy P hm hw₀Half ua zb zc hzbc ht
    · let uc : ↑(nonUniversalVertices G) :=
        ⟨c, nonUniversal_of_not_universal hcZ⟩
      have huac : ua ≠ uc := fun h ↦ hac (congrArg Subtype.val h)
      have he : s(ua, uc) ∈ (G.induce
          (↑(nonUniversalVertices G) : Set A)).edgeFinset := by
        rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
        change G.Adj a c
        exact hadj.2.1
      have hset : ({(zb : A), (ua : A), (uc : A)} : Finset A) =
          ({a, b, c} : Finset A) := by
        ext q
        simp only [zb, ua, uc, Finset.mem_insert, Finset.mem_singleton]
        tauto
      have htri' : ({(zb : A), (ua : A), (uc : A)} : Finset A) ∈
          G.cliqueFinset 3 := by
        rw [hset]
        exact ht
      have hnum := d8ShortcutAverageWeight_UUZ_numerator_le
        G z₀ hxy P hreal hm hw₀ hw₀Half ua uc huac zb he htri'
      rwa [hset] at hnum
  · let ub : ↑(nonUniversalVertices G) :=
      ⟨b, nonUniversal_of_not_universal hbZ⟩
    by_cases hcZ : c ∈ universalVertices G
    · let zc : ↑(universalVertices G) := ⟨c, hcZ⟩
      have huab : ua ≠ ub := fun h ↦ hab (congrArg Subtype.val h)
      have he : s(ua, ub) ∈ (G.induce
          (↑(nonUniversalVertices G) : Set A)).edgeFinset := by
        rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
        change G.Adj a b
        exact hadj.1
      have hset : ({(zc : A), (ua : A), (ub : A)} : Finset A) =
          ({a, b, c} : Finset A) := by
        ext q
        simp only [zc, ua, ub, Finset.mem_insert, Finset.mem_singleton]
        tauto
      have htri' : ({(zc : A), (ua : A), (ub : A)} : Finset A) ∈
          G.cliqueFinset 3 := by
        rw [hset]
        exact ht
      have hnum := d8ShortcutAverageWeight_UUZ_numerator_le
        G z₀ hxy P hreal hm hw₀ hw₀Half ua ub huab zc he htri'
      rwa [hset] at hnum
    · let uc : ↑(nonUniversalVertices G) :=
        ⟨c, nonUniversal_of_not_universal hcZ⟩
      exact d8ShortcutAverageWeight_UUU_numerator_le
        G z₀ hxy P hw₀Half ua ub uc ht

lemma d8ShortcutAverageWeight_halfBounded
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G)) {a b : A}
    (hab : Gᶜ.Adj a b)
    {w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ}
    (P : D8SeparatedParameters G)
    (hreal : P.RealizesCoherentRemovedFamily G z₀ hab w₀)
    (hn : 14 ≤ Fintype.card A)
    (hm : 4 ≤ (universalVertices G).card)
    (hw₀ : IsFractionalPacking
      (d8AugmentedDeletedGraph G (z₀ : A) a b
        (d8MissingLeft_ne_universal G hab z₀)
        (d8MissingRight_ne_universal G hab z₀)) w₀)
    (hw₀Half : IsHalfBounded
      (d8AugmentedDeletedGraph G (z₀ : A) a b
        (d8MissingLeft_ne_universal G hab z₀)
        (d8MissingRight_ne_universal G hab z₀)) w₀) :
    IsHalfBounded G (d8ShortcutAverageWeight G z₀ hab w₀ P) := by
  intro t ht
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Finset.card_eq_three.mp
    (SimpleGraph.mem_cliqueFinset_iff.mp ht).card_eq
  have finish :
      (∑ q : ↑(universalVertices G),
        d7LiftedWeight (q : A)
          (d8CoherentStrippedWeight G z₀ hab w₀ q) {x, y, z}) +
          d8ShortcutCorrection G P {x, y, z} ≤
            ((universalVertices G).card : ℝ) / 2 →
        d8ShortcutAverageWeight G z₀ hab w₀ P {x, y, z} ≤ 1 / 2 := by
    intro hnum
    unfold d8ShortcutAverageWeight
    have hmR : 0 < ((universalVertices G).card : ℝ) := by
      exact_mod_cast (by omega : 0 < (universalVertices G).card)
    calc
      ((universalVertices G).card : ℝ)⁻¹ *
          ((∑ q : ↑(universalVertices G),
            d7LiftedWeight (q : A)
              (d8CoherentStrippedWeight G z₀ hab w₀ q) {x, y, z}) +
            d8ShortcutCorrection G P {x, y, z}) ≤
          ((universalVertices G).card : ℝ)⁻¹ *
            (((universalVertices G).card : ℝ) / 2) :=
        mul_le_mul_of_nonneg_left hnum (inv_nonneg.mpr hmR.le)
      _ = 1 / 2 := by field_simp
  by_cases hxZ : x ∈ universalVertices G
  · apply finish
    exact d8ShortcutAverageWeight_numerator_le_of_mem_universal_left
      G z₀ hab P hreal hn hm hw₀ hw₀Half hxy hxz hyz ht hxZ
  · apply finish
    exact d8ShortcutAverageWeight_numerator_le_of_not_mem_universal_left
      G z₀ hab P hreal hm hw₀ hw₀Half hxy hxz hyz ht hxZ

/-- The shortcut inequality in D8 yields the required strong packing from
one symmetric augmented-deletion packing. -/
lemma hasStrongFractionalPacking_d8ShortcutAverageWeight
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G)) {a b : A}
    (hab : Gᶜ.Adj a b)
    {w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ}
    (P : D8SeparatedParameters G)
    (hreal : P.RealizesCoherentRemovedFamily G z₀ hab w₀)
    (hn : 14 ≤ Fintype.card A)
    (hm : 4 ≤ (universalVertices G).card)
    (hshortcut : (Fintype.card A : ℝ) + 4 - 3 * P.betaMass ≤
      3 * ((universalVertices G).card : ℝ))
    (hw₀ : IsFractionalPacking
      (d8AugmentedDeletedGraph G (z₀ : A) a b
        (d8MissingLeft_ne_universal G hab z₀)
        (d8MissingRight_ne_universal G hab z₀)) w₀)
    (hw₀Half : IsHalfBounded
      (d8AugmentedDeletedGraph G (z₀ : A) a b
        (d8MissingLeft_ne_universal G hab z₀)
        (d8MissingRight_ne_universal G hab z₀)) w₀)
    (hunc : fractionalUncoveredWeight
      (d8AugmentedDeletedGraph G (z₀ : A) a b
        (d8MissingLeft_ne_universal G hab z₀)
        (d8MissingRight_ne_universal G hab z₀)) w₀ ≤ 4) :
    HasStrongFractionalPacking G 4 := by
  exact ⟨d8ShortcutAverageWeight G z₀ hab w₀ P,
    d8ShortcutAverageWeight_isFractionalPacking
      G z₀ hab w₀ P hreal hm hshortcut hw₀,
    fractionalUncoveredWeight_d8ShortcutAverageWeight_le_four
      G z₀ hab P hreal hm hw₀ hunc,
    d8ShortcutAverageWeight_halfBounded
      G z₀ hab P hreal hn hm hw₀ hw₀Half⟩

/-! ### The complementary Hall redistribution -/

/-- The right-hand capacity at a nonuniversal vertex in the D8 Hall graph.
The integer subtraction matches the residual allowance left after assigning
`sigma u` units of the final uncovered-weight budget to `u`. -/
def d8HallCapacity (G : SimpleGraph A) (sigma : A → ℕ)
    (u : ↑(nonUniversalVertices G)) : ℝ :=
  (Gᶜ.degree (u : A) - 1 - sigma u : ℕ)

/-- The quotient `rho / beta`, with the paper's explicit convention that it
is zero when `beta = 0`. -/
def D8SeparatedParameters.rhoRatio {G : SimpleGraph A}
    (P : D8SeparatedParameters G) (rho : ℝ) : ℝ :=
  if P.betaMass = 0 then 0 else rho / P.betaMass

/-- The D8 Hall source indexed by a nonuniversal vertex. -/
def d8HallBetaSource (G : SimpleGraph A) (P : D8SeparatedParameters G)
    (rho : ℝ) (u : ↑(nonUniversalVertices G)) : ℝ :=
  (((universalVertices G).card : ℝ) - P.rhoRatio rho) * P.betaIncident u

/-- The unrestricted D8 Hall source arising from the `alpha` orbit. -/
def d8HallAlphaSource (G : SimpleGraph A)
    (P : D8SeparatedParameters G) : ℝ :=
  ((universalVertices G).card : ℝ) / 2 * P.alphaMass

lemma d8HallCapacity_nonneg (G : SimpleGraph A) (sigma : A → ℕ)
    (u : ↑(nonUniversalVertices G)) : 0 ≤ d8HallCapacity G sigma u := by
  unfold d8HallCapacity
  positivity

lemma D8SeparatedParameters.rhoRatio_nonneg {G : SimpleGraph A}
    (P : D8SeparatedParameters G) {rho : ℝ} (hrho : 0 ≤ rho) :
    0 ≤ P.rhoRatio rho := by
  unfold rhoRatio
  split_ifs
  · exact le_rfl
  · exact div_nonneg hrho P.betaMass_nonneg

lemma D8SeparatedParameters.rhoRatio_le_card {G : SimpleGraph A}
    (P : D8SeparatedParameters G) {rho : ℝ}
    (hrho : rho ≤ ((universalVertices G).card : ℝ) * P.betaMass) :
    P.rhoRatio rho ≤ ((universalVertices G).card : ℝ) := by
  unfold rhoRatio
  by_cases hbeta : P.betaMass = 0
  · simp only [hbeta, if_pos, Nat.cast_nonneg]
  · rw [if_neg hbeta]
    have hbetaPos : 0 < P.betaMass :=
      lt_of_le_of_ne P.betaMass_nonneg (Ne.symm hbeta)
    rw [div_le_iff₀ hbetaPos]
    exact hrho

lemma d8HallBetaSource_nonneg (G : SimpleGraph A)
    (P : D8SeparatedParameters G) {rho : ℝ}
    (hrho : rho ≤ ((universalVertices G).card : ℝ) * P.betaMass)
    (u : ↑(nonUniversalVertices G)) :
    0 ≤ d8HallBetaSource G P rho u := by
  unfold d8HallBetaSource
  exact mul_nonneg
    (sub_nonneg.mpr (P.rhoRatio_le_card hrho))
    (P.betaIncident_nonneg u)

lemma d8HallAlphaSource_nonneg (G : SimpleGraph A)
    (P : D8SeparatedParameters G) (hm : 1 ≤ (universalVertices G).card) :
    0 ≤ d8HallAlphaSource G P := by
  unfold d8HallAlphaSource
  exact mul_nonneg (div_nonneg (Nat.cast_nonneg _) (by norm_num))
    (P.alphaMass_nonneg hm)

lemma sum_d8HallBetaSource (G : SimpleGraph A)
    (P : D8SeparatedParameters G) {rho : ℝ} (hrho : 0 ≤ rho)
    (hrhoLe : rho ≤ ((universalVertices G).card : ℝ) * P.betaMass) :
    (∑ u, d8HallBetaSource G P rho u) =
      2 * (((universalVertices G).card : ℝ) * P.betaMass - rho) := by
  unfold d8HallBetaSource
  rw [← Finset.mul_sum, P.sum_betaIncident_eq_two_betaMass]
  unfold D8SeparatedParameters.rhoRatio
  by_cases hbeta : P.betaMass = 0
  · have hrhoZero : rho = 0 := by
      have : rho ≤ 0 := by simpa [hbeta] using hrhoLe
      linarith
    simp [hbeta, hrhoZero]
  · rw [if_neg hbeta]
    field_simp

lemma d8Hall_totalSource_le_four_mul_sub_two_rho
    (G : SimpleGraph A) (P : D8SeparatedParameters G)
    {rho : ℝ} (hm : 4 ≤ (universalVertices G).card)
    (hrho : 0 ≤ rho)
    (hrhoLe : rho ≤ ((universalVertices G).card : ℝ) * P.betaMass) :
    (∑ u, d8HallBetaSource G P rho u) + d8HallAlphaSource G P ≤
      4 * ((universalVertices G).card : ℝ) - 2 * rho := by
  rw [sum_d8HallBetaSource G P hrho hrhoLe]
  unfold d8HallAlphaSource
  have hab := P.alphaMass_add_betaMass_le_two (by omega)
  have hm0 : 0 ≤ ((universalVertices G).card : ℝ) := Nat.cast_nonneg _
  have halpha0 := P.alphaMass_nonneg (by omega)
  nlinarith

/-- Exact total target capacity in the D8 Hall graph. -/
lemma sum_d8HallCapacity {n s : ℕ}
    (hcard : Fintype.card A = n)
    (G : SimpleGraph A) (hexact : missingEdgeCount G = n)
    (sigma : A → ℕ)
    (hsigma : ∀ u, sigma u ≤ d7ResidualAllowance G 4 u)
    (hsupport : ∀ u ∉ nonUniversalVertices G, sigma u = 0)
    (hsum : ∑ u ∈ nonUniversalVertices G, sigma u = 8 + s) :
    (∑ u : ↑(nonUniversalVertices G), d8HallCapacity G sigma u) =
      (n : ℝ) + (universalVertices G).card - 8 - s := by
  have hpoint : ∀ u : ↑(nonUniversalVertices G),
      d8HallCapacity G sigma u =
        (Gᶜ.degree (u : A) : ℝ) - 1 - sigma u := by
    intro u
    unfold d8HallCapacity
    have hpos : 0 < Gᶜ.degree (u : A) :=
      mem_nonUniversalVertices.mp u.property
    have hs : sigma u ≤ Gᶜ.degree (u : A) - 1 :=
      (hsigma u).trans (Nat.min_le_right _ _)
    rw [Nat.cast_sub hs,
      Nat.cast_sub (by omega : 1 ≤ Gᶜ.degree (u : A)), Nat.cast_one]
  rw [Finset.sum_congr rfl fun u _ ↦ hpoint u,
    Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  have hdegrees : (∑ u : ↑(nonUniversalVertices G),
      (Gᶜ.degree (u : A) : ℝ)) = 2 * n := by
    norm_cast
    calc
      (∑ u : ↑(nonUniversalVertices G), Gᶜ.degree (u : A)) =
          ∑ u ∈ nonUniversalVertices G, Gᶜ.degree u :=
        (Finset.sum_subtype (nonUniversalVertices G) (fun _ ↦ Iff.rfl)
          (fun u : A ↦ Gᶜ.degree u)).symm
      _ = 2 * n := by
        simpa only [hexact] using sum_nonUniversalVertices_compl_degree G
  have hsigmaSubtype :
      (∑ u : ↑(nonUniversalVertices G), (sigma u : ℝ)) = 8 + s := by
    norm_cast
    calc
      (∑ u : ↑(nonUniversalVertices G), sigma (u : A)) =
          ∑ u ∈ nonUniversalVertices G, sigma u :=
        (Finset.sum_subtype (nonUniversalVertices G) (fun _ ↦ Iff.rfl)
          sigma).symm
      _ = 8 + s := hsum
  have hparts := card_nonUniversalVertices_add_card_universalVertices G
  rw [hcard] at hparts
  have hpartsR : ((nonUniversalVertices G).card : ℝ) +
      ((universalVertices G).card : ℝ) = n := by
    exact_mod_cast hparts
  simp only [hdegrees, hsigmaSubtype, Finset.sum_const, Finset.card_univ,
    Fintype.card_coe, nsmul_eq_mul, mul_one, Nat.cast_add, Nat.cast_ofNat]
  linarith

/-- Claim 5.7 in graph form.  The first component is the basic eight-unit
allowance.  In the range `3m ≥ n-7`, the second component strengthens this
to fourteen units, exactly the amount needed in the `rho = 6` Hall case. -/
theorem d8_claim57 {n : ℕ}
    (hcard : Fintype.card A = n) (hn : 14 ≤ n)
    (G : SimpleGraph A) (hexact : missingEdgeCount G = n)
    (hm : 4 ≤ (universalVertices G).card)
    (hnoD5 : ∀ u : A, 3 * Gᶜ.degree u ≤ n + 4) :
    8 ≤ ∑ u ∈ nonUniversalVertices G, d7ResidualAllowance G 4 u ∧
      (3 * (universalVertices G).card ≥ n - 7 →
        14 ≤ ∑ u ∈ nonUniversalVertices G,
          d7ResidualAllowance G 4 u) := by
  let U := nonUniversalVertices G
  let m := (universalVertices G).card
  let K := d7SaturatedVertices G 4
  let k := K.card
  let R := ∑ u ∈ U, d7ResidualAllowance G 4 u
  let c := n - 11
  have hc : 11 ≤ n := by omega
  have hclass : ∀ u ∈ U,
      3 * Gᶜ.degree u ≤
        3 * d7ResidualAllowance G 4 u + 3 +
          (if u ∈ K then c else 0) := by
    intro u hu
    by_cases hs : 5 ≤ Gᶜ.degree u
    · have huK : u ∈ K := by
        exact Finset.mem_filter.mpr ⟨by simpa only [U] using hu, hs⟩
      have hr : d7ResidualAllowance G 4 u = 4 := by
        unfold d7ResidualAllowance
        rw [Nat.min_eq_left]
        omega
      rw [if_pos huK, hr]
      have hdu := hnoD5 u
      dsimp only [c]
      omega
    · have huK : u ∉ K := by
        intro h
        exact hs (Finset.mem_filter.mp h).2
      have hduPos : 0 < Gᶜ.degree u := by
        simpa only [U, mem_nonUniversalVertices] using hu
      have hr : d7ResidualAllowance G 4 u = Gᶜ.degree u - 1 := by
        unfold d7ResidualAllowance
        rw [Nat.min_eq_right]
        omega
      rw [if_neg huK, hr]
      omega
  have hindicator :
      (∑ u ∈ U, if u ∈ K then c else 0) = k * c := by
    have hfilter : U.filter (fun u ↦ u ∈ K) = K := by
      ext u
      simp [U, K, d7SaturatedVertices]
    rw [← Finset.sum_filter, hfilter]
    simp only [k, Finset.sum_const, Nat.nsmul_eq_mul]
  have hsumUpper :
      (∑ u ∈ U, 3 * Gᶜ.degree u) ≤
        3 * R + 3 * U.card + k * c := by
    calc
      (∑ u ∈ U, 3 * Gᶜ.degree u) ≤
          ∑ u ∈ U, (3 * d7ResidualAllowance G 4 u + 3 +
            (if u ∈ K then c else 0)) :=
        Finset.sum_le_sum fun u hu ↦ hclass u hu
      _ = 3 * R + 3 * U.card + k * c := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum,
          Finset.sum_const, Nat.nsmul_eq_mul, R, hindicator]
        omega
  have hsumDegrees : 6 * n ≤ 3 * R + 3 * U.card + k * c := by
    have heq : (∑ u ∈ U, 3 * Gᶜ.degree u) = 6 * n := by
      rw [← Finset.mul_sum]
      simp only [U, sum_nonUniversalVertices_compl_degree, hexact]
      omega
    rw [← heq]
    exact hsumUpper
  have hKa : k * 4 ≤ R := by
    calc
      k * 4 = ∑ _u ∈ K, 4 := by simp [k]
      _ = ∑ u ∈ K, d7ResidualAllowance G 4 u := by
        apply Finset.sum_congr rfl
        intro u hu
        unfold d7ResidualAllowance
        rw [Nat.min_eq_left]
        have hs := (Finset.mem_filter.mp hu).2
        omega
      _ ≤ ∑ u ∈ U, d7ResidualAllowance G 4 u := by
        apply Finset.sum_le_sum_of_subset
        exact Finset.filter_subset _ _
      _ = R := rfl
  have hpart : U.card + m = n := by
    simpa only [U, m, hcard] using
      card_nonUniversalVertices_add_card_universalVertices G
  have hsumDegrees' :
      6 * n ≤ 3 * R + 3 * U.card + k * (n - 11) := by
    simpa only [c] using hsumDegrees
  constructor
  · change 8 ≤ R
    by_contra hres
    have hR : R < 8 := Nat.lt_of_not_ge hres
    have hk : k ≤ 1 := by omega
    have haggregate :
        (3 - k) * n + (6 + 2 * k) * 4 + 3 * m ≤
          3 * R + 24 - 3 * k := by
      interval_cases k <;> simp_all only [Nat.zero_mul, Nat.mul_zero,
        Nat.add_zero, Nat.sub_zero, Nat.one_mul, Nat.mul_one] <;> omega
    exact d7_claim53_arithmetic hn hm hk hR haggregate
  · intro hlarge
    change 14 ≤ R
    by_contra hres
    have hR : R ≤ 2 * 4 + 5 := by omega
    have hk : k ≤ 3 := by omega
    have haggregate :
        2 * k * 4 + (4 - k) * n + 3 * k + 6 * 4 ≤
          3 * R + 31 := by
      interval_cases k <;> omega
    exact d8_claim57_strong_arithmetic hn rfl hk hR haggregate

private lemma exists_boundedAssignment_on_finset_d8
    {B : Type*} [DecidableEq B]
    (S : Finset B) (r : B → ℕ) {t : ℕ}
    (ht : t ≤ ∑ u ∈ S, r u) :
    ∃ sigma : B → ℕ,
      (∀ u ∈ S, sigma u ≤ r u) ∧
      ∑ u ∈ S, sigma u = t := by
  induction S using Finset.induction_on generalizing t with
  | empty =>
      have ht0 : t = 0 := by simpa using ht
      exact ⟨fun _ ↦ 0, by simp, by simp [ht0]⟩
  | @insert a S ha ih =>
      rw [Finset.sum_insert ha] at ht
      let x := min (r a) t
      have hx : x ≤ r a := min_le_left _ _
      have hremaining : t - x ≤ ∑ u ∈ S, r u := by
        dsimp only [x]
        by_cases htr : t ≤ r a
        · rw [min_eq_right htr]
          simp
        · rw [min_eq_left (Nat.le_of_lt (Nat.lt_of_not_ge htr))]
          omega
      obtain ⟨sigma, hsigma, hsum⟩ := ih hremaining
      let tau : B → ℕ := fun u ↦ if u = a then x else sigma u
      refine ⟨tau, ?_, ?_⟩
      · intro u hu
        rcases Finset.mem_insert.mp hu with rfl | hu
        · simpa [tau] using hx
        · have hua : u ≠ a := by
            intro hua
            subst u
            exact ha hu
          simpa [tau, hua] using hsigma u hu
      · rw [Finset.sum_insert ha]
        have hsumTau : (∑ u ∈ S, tau u) = ∑ u ∈ S, sigma u := by
          apply Finset.sum_congr rfl
          intro u hu
          have hua : u ≠ a := by
            intro hua
            subst u
            exact ha hu
          simp [tau, hua]
        rw [hsumTau, hsum]
        simp only [tau, if_pos]
        omega

/-- Allocate any prescribed total residual budget supported on the
nonuniversal vertices. -/
lemma exists_d8ResidualAllocation (G : SimpleGraph A) {t : ℕ}
    (ht : t ≤ ∑ u ∈ nonUniversalVertices G,
      d7ResidualAllowance G 4 u) :
    ∃ sigma : A → ℕ,
      (∀ u, sigma u ≤ d7ResidualAllowance G 4 u) ∧
      (∀ u ∉ nonUniversalVertices G, sigma u = 0) ∧
      ∑ u ∈ nonUniversalVertices G, sigma u = t := by
  obtain ⟨tau, htau, hsum⟩ :=
    exists_boundedAssignment_on_finset_d8
      (nonUniversalVertices G) (d7ResidualAllowance G 4) ht
  let sigma : A → ℕ := fun u ↦
    if u ∈ nonUniversalVertices G then tau u else 0
  refine ⟨sigma, ?_, ?_, ?_⟩
  · intro u
    by_cases hu : u ∈ nonUniversalVertices G
    · simpa only [sigma, if_pos hu] using htau u hu
    · simp only [sigma, if_neg hu, Nat.zero_le]
  · intro u hu
    simp only [sigma, if_neg hu]
  · calc
      ∑ u ∈ nonUniversalVertices G, sigma u =
          ∑ u ∈ nonUniversalVertices G, tau u := by
        apply Finset.sum_congr rfl
        intro u hu
        simp only [sigma, if_pos hu]
      _ = t := hsum

/-- The high-defect nonuniversal vertices used in the `rho = 6` singleton
Hall inequalities. -/
def d8HighDefectVertices (G : SimpleGraph A) (n : ℕ) :
    Finset (↑(nonUniversalVertices G)) :=
  Finset.univ.filter fun u ↦ n - 2 ≤ 3 * Gᶜ.degree (u : A)

/-- The strengthened fourteen-unit allocation from Claim 5.7, with two
units reserved at every high-defect vertex. -/
theorem exists_d8ResidualAllocation_fourteen {n : ℕ}
    (hcard : Fintype.card A = n) (hn : 14 ≤ n)
    (G : SimpleGraph A) (hexact : missingEdgeCount G = n)
    (hm : 4 ≤ (universalVertices G).card)
    (hlarge : n - 7 ≤ 3 * (universalVertices G).card)
    (hnoD5 : ∀ u : A, 3 * Gᶜ.degree u ≤ n + 4) :
    ∃ sigma : A → ℕ,
      (∀ u, sigma u ≤ d7ResidualAllowance G 4 u) ∧
      (∀ u ∉ nonUniversalVertices G, sigma u = 0) ∧
      (∑ u ∈ nonUniversalVertices G, sigma u = 14) ∧
      (∀ u : ↑(nonUniversalVertices G),
        n - 2 ≤ 3 * Gᶜ.degree (u : A) → 2 ≤ sigma u) := by
  let U := nonUniversalVertices G
  let r : ↑U → ℕ := fun u ↦ d7ResidualAllowance G 4 (u : A)
  let S : Finset (↑U) := d8HighDefectVertices G n
  have hdegreeSum : ∑ u : ↑U, Gᶜ.degree (u : A) = 2 * n := by
    calc
      ∑ u : ↑U, Gᶜ.degree (u : A) =
          ∑ u ∈ nonUniversalVertices G, Gᶜ.degree u := by
        exact (Finset.sum_subtype (nonUniversalVertices G)
          (fun _ ↦ Iff.rfl) (fun u : A ↦ Gᶜ.degree u)).symm
      _ = 2 * n := by
        simpa only [hexact] using sum_nonUniversalVertices_compl_degree G
  have hScard : S.card ≤ 7 := by
    apply d8_highDefectSet_card_le_seven
      (fun u : ↑U ↦ Gᶜ.degree (u : A)) S hn hdegreeSum
    intro u hu
    exact (Finset.mem_filter.mp hu).2
  have hSallow : ∀ u ∈ S, 2 ≤ r u := by
    intro u hu
    have hhigh := (Finset.mem_filter.mp hu).2
    have hdegree : 4 ≤ Gᶜ.degree (u : A) := by omega
    dsimp only [r]
    unfold d7ResidualAllowance
    omega
  have htotal : 14 ≤ ∑ u : ↑U, r u := by
    have hclaim := (d8_claim57 hcard hn G hexact hm hnoD5).2 hlarge
    dsimp only [r]
    calc
      14 ≤ ∑ u ∈ nonUniversalVertices G,
          d7ResidualAllowance G 4 u := hclaim
      _ = ∑ u : ↑U, d7ResidualAllowance G 4 (u : A) :=
        Finset.sum_subtype (nonUniversalVertices G)
          (fun _ ↦ Iff.rfl) (d7ResidualAllowance G 4)
  obtain ⟨tau, htau, hhighTau, hsumTau⟩ :=
    exists_d8_sigma_assignment r S hScard hSallow htotal
  let sigma : A → ℕ := fun u ↦
    if hu : u ∈ U then tau ⟨u, hu⟩ else 0
  refine ⟨sigma, ?_, ?_, ?_, ?_⟩
  · intro u
    by_cases hu : u ∈ U
    · simpa only [sigma, dif_pos hu, r] using htau ⟨u, hu⟩
    · simp only [sigma, dif_neg hu, Nat.zero_le]
  · intro u hu
    simp only [sigma, U, dif_neg hu]
  · calc
      ∑ u ∈ nonUniversalVertices G, sigma u =
          ∑ u : ↑U, tau u := by
        rw [Finset.sum_subtype (nonUniversalVertices G)
          (fun _ ↦ Iff.rfl) sigma]
        apply Fintype.sum_congr
        intro u
        simp only [sigma, U, dif_pos u.property]
      _ = 14 := hsumTau
  · intro u hu
    have huS : u ∈ S := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ u, hu⟩
    have := hhighTau u huS
    simpa only [sigma, U, dif_pos u.property] using this

lemma D8SeparatedParameters.betaIncident_eq_zero_of_betaMass_eq_zero
    {G : SimpleGraph A} (P : D8SeparatedParameters G)
    (hbeta : P.betaMass = 0) (u : ↑(nonUniversalVertices G)) :
    P.betaIncident u = 0 := by
  have hle : P.betaIncident u ≤ ∑ v, P.betaIncident v := by
    apply Finset.single_le_sum (fun v _ ↦ P.betaIncident_nonneg v)
    exact Finset.mem_univ u
  rw [P.sum_betaIncident_eq_two_betaMass, hbeta] at hle
  exact le_antisymm (by simpa using hle) (P.betaIncident_nonneg u)

lemma d8HallAlphaSource_le_card (G : SimpleGraph A)
    (P : D8SeparatedParameters G) (hm : 2 ≤ (universalVertices G).card) :
    d8HallAlphaSource G P ≤ ((universalVertices G).card : ℝ) := by
  unfold d8HallAlphaSource
  have hab := P.alphaMass_add_betaMass_le_two hm
  have hbeta0 := P.betaMass_nonneg
  have hm0 : 0 ≤ ((universalVertices G).card : ℝ) := Nat.cast_nonneg _
  nlinarith

lemma d8HallBetaSource_eq_zero_of_rho_eq_mul
    (G : SimpleGraph A) (P : D8SeparatedParameters G) {rho : ℝ}
    (hrho : rho = ((universalVertices G).card : ℝ) * P.betaMass)
    (u : ↑(nonUniversalVertices G)) :
    d8HallBetaSource G P rho u = 0 := by
  subst rho
  unfold d8HallBetaSource D8SeparatedParameters.rhoRatio
  by_cases hbeta : P.betaMass = 0
  · rw [if_pos hbeta,
      P.betaIncident_eq_zero_of_betaMass_eq_zero hbeta u]
    ring
  · rw [if_neg hbeta]
    field_simp
    ring

lemma d8HallCapacity_le_degree_sub_one
    (G : SimpleGraph A) (sigma : A → ℕ)
    (u : ↑(nonUniversalVertices G)) :
    d8HallCapacity G sigma u ≤ (Gᶜ.degree (u : A) - 1 : ℕ) := by
  unfold d8HallCapacity
  exact_mod_cast Nat.sub_le _ _

lemma d8HallCapacity_eq_degree_sub_one_sub
    (G : SimpleGraph A) (sigma : A → ℕ)
    (hsigma : ∀ u, sigma u ≤ d7ResidualAllowance G 4 u)
    (u : ↑(nonUniversalVertices G)) :
    d8HallCapacity G sigma u =
      (Gᶜ.degree (u : A) : ℝ) - 1 - sigma u := by
  unfold d8HallCapacity
  have hpos : 1 ≤ Gᶜ.degree (u : A) :=
    mem_nonUniversalVertices.mp u.property
  have hs : sigma u ≤ Gᶜ.degree (u : A) - 1 :=
    (hsigma u).trans (Nat.min_le_right _ _)
  rw [Nat.cast_sub hs, Nat.cast_sub hpos, Nat.cast_one]

lemma d8HallBetaSource_zero_le_card (G : SimpleGraph A)
    (P : D8SeparatedParameters G) (u : ↑(nonUniversalVertices G)) :
    d8HallBetaSource G P 0 u ≤ ((universalVertices G).card : ℝ) := by
  unfold d8HallBetaSource D8SeparatedParameters.rhoRatio
  have hinc0 := P.betaIncident_nonneg u
  have hinc1 := P.betaIncident_le_one' u
  simp only [zero_div, ite_self, sub_zero]
  exact mul_le_of_le_one_right (Nat.cast_nonneg _) hinc1

lemma d8HallBetaSource_six_le_card_sub_three
    (G : SimpleGraph A) (P : D8SeparatedParameters G)
    (hm : 4 ≤ (universalVertices G).card)
    (hsix : (6 : ℝ) ≤
      ((universalVertices G).card : ℝ) * P.betaMass)
    (u : ↑(nonUniversalVertices G)) :
    d8HallBetaSource G P 6 u ≤
      ((universalVertices G).card : ℝ) - 3 := by
  have hbeta0 := P.betaMass_nonneg
  have halpha0 := P.alphaMass_nonneg (by omega)
  have hab := P.alphaMass_add_betaMass_le_two (by omega)
  have hbeta2 : P.betaMass ≤ 2 := by linarith
  have hbetaPos : 0 < P.betaMass := by
    have hm0 : 0 ≤ ((universalVertices G).card : ℝ) := Nat.cast_nonneg _
    nlinarith
  have hratio3 : (3 : ℝ) ≤ 6 / P.betaMass := by
    rw [le_div_iff₀ hbetaPos]
    nlinarith
  have hcoeff0 : 0 ≤
      ((universalVertices G).card : ℝ) - 6 / P.betaMass := by
    have := P.rhoRatio_le_card hsix
    simpa [D8SeparatedParameters.rhoRatio, ne_of_gt hbetaPos] using this
  have hmul :
      (((universalVertices G).card : ℝ) - 6 / P.betaMass) *
          P.betaIncident u ≤
        ((universalVertices G).card : ℝ) - 6 / P.betaMass :=
    mul_le_of_le_one_right hcoeff0 (P.betaIncident_le_one' u)
  unfold d8HallBetaSource D8SeparatedParameters.rhoRatio
  rw [if_neg (ne_of_gt hbetaPos)]
  linarith

/-- The exact output of Claim 5.8.  `betaFlow u v` is the amount of the
source indexed by `v` assigned to the deletion at `u`; `alphaFlow` is the
corresponding unrestricted source. -/
structure D8HallRedistribution (G : SimpleGraph A)
    (P : D8SeparatedParameters G) (rho : ℝ) (sigma : A → ℕ) where
  betaFlow : ↑(nonUniversalVertices G) →
    ↑(nonUniversalVertices G) → ℝ
  alphaFlow : ↑(nonUniversalVertices G) → ℝ
  beta_nonneg : ∀ u v, 0 ≤ betaFlow u v
  alpha_nonneg : ∀ u, 0 ≤ alphaFlow u
  beta_source_sum : ∀ v, ∑ u, betaFlow u v = d8HallBetaSource G P rho v
  alpha_sum : ∑ u, alphaFlow u = d8HallAlphaSource G P
  diagonal_zero : ∀ u, betaFlow u u = 0
  target_le : ∀ u,
    (∑ v, betaFlow u v) + alphaFlow u ≤ d8HallCapacity G sigma u

/-- The fractional Hall construction once its whole-set and singleton
inequalities have been established.  Keeping those two numerical
obligations explicit makes this transport theorem reusable in all three
values of `rho` from Claim 5.8. -/
theorem exists_d8HallRedistribution_of_bounds
    (G : SimpleGraph A) (P : D8SeparatedParameters G)
    (rho : ℝ) (sigma : A → ℕ)
    (hm : 1 ≤ (universalVertices G).card)
    (hrho : rho ≤ ((universalVertices G).card : ℝ) * P.betaMass)
    (htotal :
      (∑ v, d8HallBetaSource G P rho v) + d8HallAlphaSource G P ≤
        ∑ u, d8HallCapacity G sigma u)
    (hsingle : ∀ u : ↑(nonUniversalVertices G),
      d8HallBetaSource G P rho u ≤
        (∑ v, d8HallCapacity G sigma v) - d8HallCapacity G sigma u) :
    ∃ R : D8HallRedistribution G P rho sigma, True := by
  let d : Option ↑(nonUniversalVertices G) → ℝ := fun src ↦
    match src with
    | none => d8HallAlphaSource G P
    | some u => d8HallBetaSource G P rho u
  let c : ↑(nonUniversalVertices G) → ℝ := d8HallCapacity G sigma
  have hd : ∀ src, 0 ≤ d src := by
    intro src
    rcases src with _ | u
    · exact d8HallAlphaSource_nonneg G P hm
    · exact d8HallBetaSource_nonneg G P hrho u
  have hc : ∀ u, 0 ≤ c u := d8HallCapacity_nonneg G sigma
  have htotal' : (∑ src, d src) ≤ ∑ u, c u := by
    rw [Fintype.sum_option]
    simpa only [d, c, add_comm] using htotal
  have hsingle' : ∀ u, d (some u) ≤ (∑ v, c v) - c u := by
    intro u
    simpa only [d, c] using hsingle u
  obtain ⟨mu, hmu0, hrow, hdiag, hcol⟩ :=
    exists_offDiagonalTransport_real d c hd hc htotal' hsingle'
  let R : D8HallRedistribution G P rho sigma :=
    { betaFlow := fun u v ↦ mu (some v) u
      alphaFlow := fun u ↦ mu none u
      beta_nonneg := fun u v ↦ hmu0 (some v) u
      alpha_nonneg := fun u ↦ hmu0 none u
      beta_source_sum := fun v ↦ by simpa [d] using hrow (some v)
      alpha_sum := by simpa [d] using hrow none
      diagonal_zero := fun u ↦ hdiag u
      target_le := fun u ↦ by
        simpa [c, Fintype.sum_option, add_comm] using hcol u }
  exact ⟨R, trivial⟩

/-- Claim 5.8 in the regime `3m ≤ n-8`, where `rho = 0` and the
eight-unit residual allocation is sufficient. -/
theorem exists_d8HallRedistribution_zero {n : ℕ}
    (hcard : Fintype.card A = n) (hn : 14 ≤ n)
    (G : SimpleGraph A) (hexact : missingEdgeCount G = n)
    (hm : 4 ≤ (universalVertices G).card)
    (hsmall : 3 * (universalVertices G).card ≤ n - 8)
    (hnoD5 : ∀ u : A, 3 * Gᶜ.degree u ≤ n + 4)
    (P : D8SeparatedParameters G) :
    ∃ sigma : A → ℕ,
    ∃ R : D8HallRedistribution G P 0 sigma,
      (∀ u, sigma u ≤ d7ResidualAllowance G 4 u) ∧
      (∀ u ∉ nonUniversalVertices G, sigma u = 0) ∧
      ∑ u ∈ nonUniversalVertices G, sigma u = 8 := by
  have hallow := (d8_claim57 hcard hn G hexact hm hnoD5).1
  obtain ⟨sigma, hsigma, hsupport, hsum⟩ :=
    exists_d8ResidualAllocation G hallow
  have hcapSum :
      (∑ u : ↑(nonUniversalVertices G), d8HallCapacity G sigma u) =
        (n : ℝ) + (universalVertices G).card - 8 := by
    simpa using sum_d8HallCapacity (s := 0) hcard G hexact sigma
      hsigma hsupport (by simpa using hsum)
  have hrhoLe : (0 : ℝ) ≤
      ((universalVertices G).card : ℝ) * P.betaMass :=
    mul_nonneg (Nat.cast_nonneg _) P.betaMass_nonneg
  have htotal :
      (∑ v, d8HallBetaSource G P 0 v) + d8HallAlphaSource G P ≤
        ∑ u, d8HallCapacity G sigma u := by
    calc
      (∑ v, d8HallBetaSource G P 0 v) + d8HallAlphaSource G P ≤
          4 * ((universalVertices G).card : ℝ) := by
        simpa using d8Hall_totalSource_le_four_mul_sub_two_rho
          G P hm (show (0 : ℝ) ≤ 0 by norm_num) hrhoLe
      _ ≤ (n : ℝ) + (universalVertices G).card - 8 := by
        have hbound := d8_claim58_whole_zero_arithmetic hsmall
        have hboundR : ((4 * (universalVertices G).card : ℕ) : ℝ) ≤
            ((n + (universalVertices G).card - 8 : ℕ) : ℝ) := by
          exact_mod_cast hbound
        calc
          4 * ((universalVertices G).card : ℝ) =
              ((4 * (universalVertices G).card : ℕ) : ℝ) := by norm_num
          _ ≤ ((n + (universalVertices G).card - 8 : ℕ) : ℝ) := hboundR
          _ = (n : ℝ) + (universalVertices G).card - 8 := by
            rw [Nat.cast_sub (by omega : 8 ≤ n + (universalVertices G).card),
              Nat.cast_add]
            norm_num
      _ = ∑ u, d8HallCapacity G sigma u := hcapSum.symm
  have hsingle : ∀ u : ↑(nonUniversalVertices G),
      d8HallBetaSource G P 0 u ≤
        (∑ v, d8HallCapacity G sigma v) - d8HallCapacity G sigma u := by
    intro u
    have hsource := d8HallBetaSource_zero_le_card G P u
    have hcap := d8HallCapacity_le_degree_sub_one G sigma u
    have hdegree : (3 : ℝ) * Gᶜ.degree (u : A) ≤ n + 4 := by
      exact_mod_cast hnoD5 (u : A)
    have hcapR : d8HallCapacity G sigma u ≤
        (Gᶜ.degree (u : A) : ℝ) - 1 := by
      have hpos : 1 ≤ Gᶜ.degree (u : A) :=
        mem_nonUniversalVertices.mp u.property
      exact_mod_cast hcap
    rw [hcapSum]
    have hnR : (14 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  obtain ⟨R, _⟩ := exists_d8HallRedistribution_of_bounds
    G P 0 sigma (by omega) hrhoLe htotal hsingle
  exact ⟨sigma, R, hsigma, hsupport, hsum⟩

/-- Claim 5.8 in the large-`m` subcase `rho = m * beta`.  Every beta source
vanishes identically, so only the unrestricted alpha source remains. -/
theorem exists_d8HallRedistribution_full_beta {n : ℕ}
    (hcard : Fintype.card A = n) (hn : 14 ≤ n)
    (G : SimpleGraph A) (hexact : missingEdgeCount G = n)
    (hm : 4 ≤ (universalVertices G).card)
    (hlarge : n - 7 ≤ 3 * (universalVertices G).card)
    (hnoD5 : ∀ u : A, 3 * Gᶜ.degree u ≤ n + 4)
    (P : D8SeparatedParameters G) :
    let rho := ((universalVertices G).card : ℝ) * P.betaMass
    ∃ sigma : A → ℕ,
    ∃ R : D8HallRedistribution G P rho sigma,
      (∀ u, sigma u ≤ d7ResidualAllowance G 4 u) ∧
      (∀ u ∉ nonUniversalVertices G, sigma u = 0) ∧
      ∑ u ∈ nonUniversalVertices G, sigma u = 14 := by
  dsimp only
  obtain ⟨sigma, hsigma, hsupport, hsum, _hhigh⟩ :=
    exists_d8ResidualAllocation_fourteen
      hcard hn G hexact hm hlarge hnoD5
  let rho : ℝ := ((universalVertices G).card : ℝ) * P.betaMass
  have hcapSum :
      (∑ u : ↑(nonUniversalVertices G), d8HallCapacity G sigma u) =
        (n : ℝ) + (universalVertices G).card - 14 := by
    have h := sum_d8HallCapacity (s := 6) hcard G hexact sigma hsigma hsupport
      (by simpa using hsum)
    norm_num at h ⊢
    linarith
  have hbetaZero : ∀ u : ↑(nonUniversalVertices G),
      d8HallBetaSource G P rho u = 0 := by
    intro u
    exact d8HallBetaSource_eq_zero_of_rho_eq_mul G P rfl u
  have hrhoLe : rho ≤
      ((universalVertices G).card : ℝ) * P.betaMass := le_rfl
  have htotal :
      (∑ v, d8HallBetaSource G P rho v) + d8HallAlphaSource G P ≤
        ∑ u, d8HallCapacity G sigma u := by
    rw [Finset.sum_congr rfl fun u _ ↦ hbetaZero u, Finset.sum_const_zero,
      zero_add, hcapSum]
    have halpha := d8HallAlphaSource_le_card G P (by omega)
    have hnR : (14 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hsingle : ∀ u : ↑(nonUniversalVertices G),
      d8HallBetaSource G P rho u ≤
        (∑ v, d8HallCapacity G sigma v) - d8HallCapacity G sigma u := by
    intro u
    rw [hbetaZero u]
    exact sub_nonneg.mpr (Finset.single_le_sum
      (fun v _ ↦ d8HallCapacity_nonneg G sigma v) (Finset.mem_univ u))
  obtain ⟨R, _⟩ := exists_d8HallRedistribution_of_bounds
    G P rho sigma (by omega) hrhoLe htotal hsingle
  exact ⟨sigma, R, hsigma, hsupport, hsum⟩

/-- Claim 5.8 in the remaining large-`m` subcase `rho = 6`.  Shortcut
failure supplies the whole-set quadratic estimate; the high-defect reserve
in `sigma` supplies every singleton Hall inequality. -/
theorem exists_d8HallRedistribution_six {n : ℕ}
    (hcard : Fintype.card A = n) (hn : 14 ≤ n)
    (G : SimpleGraph A) (hexact : missingEdgeCount G = n)
    (hm : 4 ≤ (universalVertices G).card)
    (hlarge : n - 7 ≤ 3 * (universalVertices G).card)
    (hnoD5 : ∀ u : A, 3 * Gᶜ.degree u ≤ n + 4)
    (P : D8SeparatedParameters G)
    (hsix : (6 : ℝ) ≤
      ((universalVertices G).card : ℝ) * P.betaMass)
    (hfail : 3 * ((universalVertices G).card : ℝ) <
      (n : ℝ) + 4 - 3 * P.betaMass) :
    ∃ sigma : A → ℕ,
    ∃ R : D8HallRedistribution G P 6 sigma,
      (∀ u, sigma u ≤ d7ResidualAllowance G 4 u) ∧
      (∀ u ∉ nonUniversalVertices G, sigma u = 0) ∧
      ∑ u ∈ nonUniversalVertices G, sigma u = 14 := by
  obtain ⟨sigma, hsigma, hsupport, hsum, hhigh⟩ :=
    exists_d8ResidualAllocation_fourteen
      hcard hn G hexact hm hlarge hnoD5
  have hcapSum :
      (∑ u : ↑(nonUniversalVertices G), d8HallCapacity G sigma u) =
        (n : ℝ) + (universalVertices G).card - 14 := by
    have h := sum_d8HallCapacity (s := 6) hcard G hexact sigma hsigma hsupport
      (by simpa using hsum)
    norm_num at h ⊢
    linarith
  have hbeta0 := P.betaMass_nonneg
  have halpha0 := P.alphaMass_nonneg (by omega)
  have hab := P.alphaMass_add_betaMass_le_two (by omega)
  have hbeta2 : P.betaMass ≤ 2 := by linarith
  have hquad := d8_claim58_beta_quadratic hn hbeta0 hbeta2 hfail
  have htotal :
      (∑ v, d8HallBetaSource G P 6 v) + d8HallAlphaSource G P ≤
        ∑ u, d8HallCapacity G sigma u := by
    rw [sum_d8HallBetaSource G P (by norm_num) hsix, hcapSum]
    unfold d8HallAlphaSource
    have hm0 : 0 ≤ ((universalVertices G).card : ℝ) := Nat.cast_nonneg _
    nlinarith
  have hsingle : ∀ u : ↑(nonUniversalVertices G),
      d8HallBetaSource G P 6 u ≤
        (∑ v, d8HallCapacity G sigma v) - d8HallCapacity G sigma u := by
    intro u
    have hsource := d8HallBetaSource_six_le_card_sub_three G P hm hsix u
    have hcapEq := d8HallCapacity_eq_degree_sub_one_sub G sigma hsigma u
    have hdegree : (3 : ℝ) * Gᶜ.degree (u : A) ≤ n + 4 := by
      exact_mod_cast hnoD5 (u : A)
    have hnR : (14 : ℝ) ≤ n := by exact_mod_cast hn
    have hcapBound : d8HallCapacity G sigma u ≤ (n : ℝ) - 11 := by
      by_cases huHigh : n - 2 ≤ 3 * Gᶜ.degree (u : A)
      · have hsigmaTwo : (2 : ℝ) ≤ sigma u := by
          exact_mod_cast hhigh u huHigh
        linarith
      · have huLow : 3 * Gᶜ.degree (u : A) ≤ n - 3 := by omega
        have huLowCast : ((3 * Gᶜ.degree (u : A) : ℕ) : ℝ) ≤
            ((n - 3 : ℕ) : ℝ) := by exact_mod_cast huLow
        have huLowR : (3 : ℝ) * Gᶜ.degree (u : A) ≤ n - 3 := by
          calc
            (3 : ℝ) * Gᶜ.degree (u : A) =
                ((3 * Gᶜ.degree (u : A) : ℕ) : ℝ) := by norm_num
            _ ≤ ((n - 3 : ℕ) : ℝ) := huLowCast
            _ = (n : ℝ) - 3 := by
              rw [Nat.cast_sub (by omega : 3 ≤ n)]
              norm_num
        have hsigma0 : (0 : ℝ) ≤ sigma u := Nat.cast_nonneg _
        linarith
    rw [hcapSum]
    linarith
  obtain ⟨R, _⟩ := exists_d8HallRedistribution_of_bounds
    G P 6 sigma (by omega) hsix htotal hsingle
  exact ⟨sigma, R, hsigma, hsupport, hsum⟩

/-- Claim 5.8, with the three definitions of `rho` assembled into a single
output.  The final inequality is the invariant used by the normalized
uncovered-weight calculation: the allocated residual mass is at least
`8 + rho`. -/
theorem exists_d8HallRedistribution {n : ℕ}
    (hcard : Fintype.card A = n) (hn : 14 ≤ n)
    (G : SimpleGraph A) (hexact : missingEdgeCount G = n)
    (hm : 4 ≤ (universalVertices G).card)
    (hnoD5 : ∀ u : A, 3 * Gᶜ.degree u ≤ n + 4)
    (P : D8SeparatedParameters G)
    (hfail : 3 * ((universalVertices G).card : ℝ) <
      (n : ℝ) + 4 - 3 * P.betaMass) :
    ∃ rho : ℝ,
    ∃ sigma : A → ℕ,
    ∃ R : D8HallRedistribution G P rho sigma,
      0 ≤ rho ∧ rho ≤ 6 ∧
      rho ≤ ((universalVertices G).card : ℝ) * P.betaMass ∧
      (∀ u, sigma u ≤ d7ResidualAllowance G 4 u) ∧
      (∀ u ∉ nonUniversalVertices G, sigma u = 0) ∧
      8 + rho ≤ ∑ u ∈ nonUniversalVertices G, (sigma u : ℝ) := by
  by_cases hsmall : 3 * (universalVertices G).card ≤ n - 8
  · obtain ⟨sigma, R, hsigma, hsupport, hsum⟩ :=
      exists_d8HallRedistribution_zero
        hcard hn G hexact hm hsmall hnoD5 P
    refine ⟨0, sigma, R, by norm_num, by norm_num, ?_, hsigma,
      hsupport, ?_⟩
    · exact mul_nonneg (Nat.cast_nonneg _) P.betaMass_nonneg
    · have hsumR :
          (∑ u ∈ nonUniversalVertices G, (sigma u : ℝ)) = 8 := by
        exact_mod_cast hsum
      linarith
  · have hlarge : n - 7 ≤ 3 * (universalVertices G).card := by omega
    by_cases hsix : (6 : ℝ) ≤
        ((universalVertices G).card : ℝ) * P.betaMass
    · obtain ⟨sigma, R, hsigma, hsupport, hsum⟩ :=
        exists_d8HallRedistribution_six
          hcard hn G hexact hm hlarge hnoD5 P hsix hfail
      refine ⟨6, sigma, R, by norm_num, le_rfl, hsix, hsigma,
        hsupport, ?_⟩
      have hsumR :
          (∑ u ∈ nonUniversalVertices G, (sigma u : ℝ)) = 14 := by
        exact_mod_cast hsum
      linarith
    · have hrhoSix :
          ((universalVertices G).card : ℝ) * P.betaMass ≤ 6 :=
        le_of_not_ge hsix
      obtain ⟨sigma, R, hsigma, hsupport, hsum⟩ :=
        exists_d8HallRedistribution_full_beta
          hcard hn G hexact hm hlarge hnoD5 P
      let rho : ℝ := ((universalVertices G).card : ℝ) * P.betaMass
      refine ⟨rho, sigma, R, ?_, hrhoSix, le_rfl, hsigma, hsupport, ?_⟩
      · exact mul_nonneg (Nat.cast_nonneg _) P.betaMass_nonneg
      · have hsumR :
            (∑ u ∈ nonUniversalVertices G, (sigma u : ℝ)) = 14 := by
          exact_mod_cast hsum
        rw [hsumR]
        dsimp only [rho]
        linarith

/-! ### Hall-adjusted capacities on nonuniversal deletions -/

private lemma mem_nonUniversalVertices_of_not_mem_universalVertices_d8
    (G : SimpleGraph A) {v : A} (hv : v ∉ universalVertices G) :
    v ∈ nonUniversalVertices G := by
  apply mem_nonUniversalVertices.mpr
  apply Nat.pos_of_ne_zero
  intro hz
  exact hv (mem_universalVertices.mpr hz)

/-- The capacity deducted from an edge of `G-u` by the D8 Hall flow
targeted at `u`. -/
def d8HallDeduction (G : SimpleGraph A) (P : D8SeparatedParameters G)
    (rho : ℝ) (sigma : A → ℕ)
    (R : D8HallRedistribution G P rho sigma)
    (u : ↑(nonUniversalVertices G)) :
    Sym2 (↑(d7DeletedFinset (u : A))) → ℝ :=
  Sym2.lift ⟨fun x y ↦
    if hx : (x : A) ∈ universalVertices G then
      if hy : (y : A) ∈ universalVertices G then
        R.alphaFlow u / (((universalVertices G).card.choose 2 : ℕ) : ℝ)
      else
        R.betaFlow u ⟨(y : A),
          mem_nonUniversalVertices_of_not_mem_universalVertices_d8 G hy⟩ /
            ((universalVertices G).card : ℝ)
    else if hy : (y : A) ∈ universalVertices G then
      R.betaFlow u ⟨(x : A),
        mem_nonUniversalVertices_of_not_mem_universalVertices_d8 G hx⟩ /
          ((universalVertices G).card : ℝ)
    else 0,
    by
      intro x y
      by_cases hx : (x : A) ∈ universalVertices G <;>
        by_cases hy : (y : A) ∈ universalVertices G <;>
        simp [hx, hy]⟩

lemma d8HallDeduction_nonneg (G : SimpleGraph A)
    (P : D8SeparatedParameters G) (rho : ℝ) (sigma : A → ℕ)
    (R : D8HallRedistribution G P rho sigma)
    (u : ↑(nonUniversalVertices G))
    (e : Sym2 (↑(d7DeletedFinset (u : A)))) :
    0 ≤ d8HallDeduction G P rho sigma R u e := by
  induction e using Sym2.inductionOn with
  | hf x y =>
      unfold d8HallDeduction
      simp only [Sym2.lift_mk]
      by_cases hx : (x : A) ∈ universalVertices G <;>
        by_cases hy : (y : A) ∈ universalVertices G <;>
        simp only [hx, hy, dite_true, dite_false]
      · exact div_nonneg (R.alpha_nonneg u) (Nat.cast_nonneg _)
      · exact div_nonneg (R.beta_nonneg u _) (Nat.cast_nonneg _)
      · exact div_nonneg (R.beta_nonneg u _) (Nat.cast_nonneg _)
      · exact le_rfl

lemma d8HallBetaSource_le_card (G : SimpleGraph A)
    (P : D8SeparatedParameters G) {rho : ℝ}
    (hrho0 : 0 ≤ rho)
    (hrhoLe : rho ≤ ((universalVertices G).card : ℝ) * P.betaMass)
    (u : ↑(nonUniversalVertices G)) :
    d8HallBetaSource G P rho u ≤ ((universalVertices G).card : ℝ) := by
  unfold d8HallBetaSource
  have hratio0 := P.rhoRatio_nonneg hrho0
  have hcoeff0 : 0 ≤
      ((universalVertices G).card : ℝ) - P.rhoRatio rho :=
    sub_nonneg.mpr (P.rhoRatio_le_card hrhoLe)
  have hmul := mul_le_of_le_one_right hcoeff0 (P.betaIncident_le_one' u)
  linarith

lemma D8HallRedistribution.betaFlow_le_card
    (G : SimpleGraph A) (P : D8SeparatedParameters G)
    {rho : ℝ} (sigma : A → ℕ)
    (R : D8HallRedistribution G P rho sigma)
    (hrho0 : 0 ≤ rho)
    (hrhoLe : rho ≤ ((universalVertices G).card : ℝ) * P.betaMass)
    (u v : ↑(nonUniversalVertices G)) :
    R.betaFlow u v ≤ ((universalVertices G).card : ℝ) := by
  have hle : R.betaFlow u v ≤ ∑ x, R.betaFlow x v := by
    apply Finset.single_le_sum (fun x _ ↦ R.beta_nonneg x v)
    exact Finset.mem_univ u
  rw [R.beta_source_sum v] at hle
  exact hle.trans (d8HallBetaSource_le_card G P hrho0 hrhoLe v)

lemma D8HallRedistribution.alphaFlow_le_choose_two
    (G : SimpleGraph A) (P : D8SeparatedParameters G)
    (rho : ℝ) (sigma : A → ℕ)
    (R : D8HallRedistribution G P rho sigma)
    (hm : 4 ≤ (universalVertices G).card)
    (u : ↑(nonUniversalVertices G)) :
    R.alphaFlow u ≤
      (((universalVertices G).card.choose 2 : ℕ) : ℝ) := by
  have hle : R.alphaFlow u ≤ ∑ x, R.alphaFlow x := by
    apply Finset.single_le_sum (fun x _ ↦ R.alpha_nonneg x)
    exact Finset.mem_univ u
  rw [R.alpha_sum] at hle
  have hsource := d8HallAlphaSource_le_card G P (by omega)
  have hchoose : ((universalVertices G).card : ℝ) ≤
      (((universalVertices G).card.choose 2 : ℕ) : ℝ) := by
    rw [Nat.cast_choose_two]
    have hmR : (4 : ℝ) ≤ ((universalVertices G).card : ℝ) := by
      exact_mod_cast hm
    nlinarith
  exact hle.trans (hsource.trans hchoose)

lemma d8HallDeduction_le_one (G : SimpleGraph A)
    (P : D8SeparatedParameters G) {rho : ℝ} (sigma : A → ℕ)
    (R : D8HallRedistribution G P rho sigma)
    (hm : 4 ≤ (universalVertices G).card)
    (hrho0 : 0 ≤ rho)
    (hrhoLe : rho ≤ ((universalVertices G).card : ℝ) * P.betaMass)
    (u : ↑(nonUniversalVertices G))
    (e : Sym2 (↑(d7DeletedFinset (u : A)))) :
    d8HallDeduction G P rho sigma R u e ≤ 1 := by
  have hmR : (0 : ℝ) < ((universalVertices G).card : ℝ) := by positivity
  have hchooseR : (0 : ℝ) <
      (((universalVertices G).card.choose 2 : ℕ) : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega : 2 ≤ (universalVertices G).card)
  induction e using Sym2.inductionOn with
  | hf x y =>
      unfold d8HallDeduction
      simp only [Sym2.lift_mk]
      by_cases hx : (x : A) ∈ universalVertices G <;>
        by_cases hy : (y : A) ∈ universalVertices G <;>
        simp only [hx, hy, dite_true, dite_false]
      · exact (div_le_one hchooseR).mpr
          (R.alphaFlow_le_choose_two G P rho sigma hm u)
      · exact (div_le_one hmR).mpr
          (R.betaFlow_le_card G P sigma hrho0 hrhoLe u _)
      · exact (div_le_one hmR).mpr
          (R.betaFlow_le_card G P sigma hrho0 hrhoLe u _)
      · norm_num

/-- The Hall-adjusted complete-graph capacity used for weighted induction
on the deletion of a nonuniversal vertex. -/
def d8HallDeletedCapacity (G : SimpleGraph A)
    (P : D8SeparatedParameters G) (rho : ℝ) (sigma : A → ℕ)
    (R : D8HallRedistribution G P rho sigma)
    (u : ↑(nonUniversalVertices G))
    (e : Sym2 (↑(d7DeletedFinset (u : A)))) : ℝ :=
  if e ∈ (d7DeletedGraph G (u : A)).edgeFinset then
    1 - d8HallDeduction G P rho sigma R u e
  else 0

lemma d8HallDeletedCapacity_isEdgeCapacity
    (G : SimpleGraph A) (P : D8SeparatedParameters G)
    {rho : ℝ} (sigma : A → ℕ)
    (R : D8HallRedistribution G P rho sigma)
    (hm : 4 ≤ (universalVertices G).card)
    (hrho0 : 0 ≤ rho)
    (hrhoLe : rho ≤ ((universalVertices G).card : ℝ) * P.betaMass)
    (u : ↑(nonUniversalVertices G)) :
    IsEdgeCapacity (⊤ : SimpleGraph (↑(d7DeletedFinset (u : A))))
      (d8HallDeletedCapacity G P rho sigma R u) := by
  constructor
  · intro e _heTop
    by_cases he : e ∈ (d7DeletedGraph G (u : A)).edgeFinset
    · rw [d8HallDeletedCapacity, if_pos he]
      exact ⟨sub_nonneg.mpr
          (d8HallDeduction_le_one G P sigma R hm hrho0 hrhoLe u e),
        by linarith [d8HallDeduction_nonneg G P rho sigma R u e]⟩
    · simp [d8HallDeletedCapacity, he]
  · intro e heTop
    have hdiag : e.IsDiag := by
      induction e using Sym2.inductionOn with
      | hf x y =>
          simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
            SimpleGraph.top_adj, Sym2.mk_isDiag_iff] at heTop ⊢
          exact not_ne_iff.mp heTop
    rw [d8HallDeletedCapacity, if_neg]
    intro he
    exact (d7DeletedGraph G (u : A)).not_isDiag_of_mem_edgeFinset he hdiag

/-! ### Reduction of the Hall-deduction sum to the checked D7 identity -/

/-- The fraction of each beta orbit retained in the explicit D8 correction.
The complementary fraction is routed through the Hall-adjusted deletion
packings. -/
def D8SeparatedParameters.hallScale {G : SimpleGraph A}
    (P : D8SeparatedParameters G) (rho : ℝ) : ℝ :=
  1 - P.rhoRatio rho / ((universalVertices G).card : ℝ)

lemma D8SeparatedParameters.hallScale_nonneg {G : SimpleGraph A}
    (P : D8SeparatedParameters G) {rho : ℝ}
    (hm : 1 ≤ (universalVertices G).card)
    (hrhoLe : rho ≤ ((universalVertices G).card : ℝ) * P.betaMass) :
    0 ≤ P.hallScale rho := by
  unfold hallScale
  have hmR : (0 : ℝ) < ((universalVertices G).card : ℝ) := by positivity
  have hratio := P.rhoRatio_le_card hrhoLe
  rw [sub_nonneg, div_le_one hmR]
  exact hratio

lemma D8SeparatedParameters.hallScale_le_one {G : SimpleGraph A}
    (P : D8SeparatedParameters G) {rho : ℝ} (hrho0 : 0 ≤ rho) :
    P.hallScale rho ≤ 1 := by
  unfold hallScale
  have hratio := P.rhoRatio_nonneg hrho0
  have hdiv : 0 ≤ P.rhoRatio rho /
      ((universalVertices G).card : ℝ) :=
    div_nonneg hratio (Nat.cast_nonneg _)
  linarith

/-- The D8 orbit parameters, scaled by one half, form a normalized D7
parameter package.  Its beta orbit is additionally multiplied by the Hall
retention factor.  The unused normalization mass is put in the gamma orbit. -/
def D8SeparatedParameters.toD7HallParameters {G : SimpleGraph A}
    (P : D8SeparatedParameters G) (rho : ℝ)
    (hm : 4 ≤ (universalVertices G).card)
    (hrho0 : 0 ≤ rho)
    (hrhoLe : rho ≤ ((universalVertices G).card : ℝ) * P.betaMass) :
    D7SeparatedParameters G := by
  let scale : ℝ := P.hallScale rho
  let alpha7 : ↑(nonUniversalVertices G) → ℝ := fun u ↦ P.alpha u / 2
  let beta7 : Sym2 (↑(nonUniversalVertices G)) → ℝ :=
    fun e ↦ scale * P.beta e / 2
  let C : ℝ := (((universalVertices G).card : ℝ) - 1) *
    (((universalVertices G).card : ℝ) - 2) / 2
  let alphaMass7 : ℝ := P.alphaMass / 2
  let betaMass7 : ℝ := scale * P.betaMass / 2
  let gamma7 : ℝ := (1 - alphaMass7 - betaMass7) / C
  have hscale0 : 0 ≤ scale := P.hallScale_nonneg (by omega) hrhoLe
  have hscale1 : scale ≤ 1 := P.hallScale_le_one hrho0
  have halpha0 := P.alphaMass_nonneg (by omega)
  have hbeta0 := P.betaMass_nonneg
  have hab := P.alphaMass_add_betaMass_le_two (by omega)
  have hscaledBeta : scale * P.betaMass ≤ P.betaMass :=
    mul_le_of_le_one_left hbeta0 hscale1
  have hnumerator : 0 ≤ 1 - alphaMass7 - betaMass7 := by
    dsimp only [alphaMass7, betaMass7]
    nlinarith
  have hC : 0 < C := by
    dsimp only [C]
    have hm1 : (1 : ℝ) < (universalVertices G).card := by exact_mod_cast (by omega)
    have hm2 : (2 : ℝ) < (universalVertices G).card := by exact_mod_cast (by omega)
    positivity
  refine
    { gamma := gamma7
      alpha := alpha7
      beta := beta7
      gamma_nonneg := div_nonneg hnumerator hC.le
      alpha_nonneg := fun u ↦ div_nonneg (P.alpha_nonneg u) (by norm_num)
      beta_nonneg := fun e he ↦
        div_nonneg (mul_nonneg hscale0 (P.beta_nonneg e he)) (by norm_num)
      normalization := ?_ }
  have halphaSum :
      (((universalVertices G).card : ℝ) - 1) * ∑ u, alpha7 u =
        alphaMass7 := by
    dsimp only [alpha7, alphaMass7, D8SeparatedParameters.alphaMass]
    rw [← Finset.sum_div]
    ring
  have hbetaSum :
      (∑ e ∈ (G.induce
        (↑(nonUniversalVertices G) : Set A)).edgeFinset, beta7 e) =
        betaMass7 := by
    dsimp only [beta7, betaMass7, D8SeparatedParameters.betaMass]
    calc
      (∑ e ∈ (G.induce
          (↑(nonUniversalVertices G) : Set A)).edgeFinset,
            scale * P.beta e / 2) =
          (∑ e ∈ (G.induce
            (↑(nonUniversalVertices G) : Set A)).edgeFinset,
              scale * P.beta e) / 2 := by rw [Finset.sum_div]
      _ = (scale * ∑ e ∈ (G.induce
            (↑(nonUniversalVertices G) : Set A)).edgeFinset,
              P.beta e) / 2 := by rw [Finset.mul_sum]
  change C * gamma7 +
      (((universalVertices G).card : ℝ) - 1) * ∑ u, alpha7 u +
      ∑ e ∈ (G.induce
        (↑(nonUniversalVertices G) : Set A)).edgeFinset, beta7 e = 1
  rw [halphaSum, hbetaSum]
  dsimp only [gamma7]
  field_simp [ne_of_gt hC]
  ring

lemma D8SeparatedParameters.toD7HallParameters_alpha
    {G : SimpleGraph A} (P : D8SeparatedParameters G) (rho : ℝ)
    (hm : 4 ≤ (universalVertices G).card) (hrho0 : 0 ≤ rho)
    (hrhoLe : rho ≤ ((universalVertices G).card : ℝ) * P.betaMass)
    (u : ↑(nonUniversalVertices G)) :
    (P.toD7HallParameters rho hm hrho0 hrhoLe).alpha u = P.alpha u / 2 := by
  rfl

lemma D8SeparatedParameters.toD7HallParameters_beta
    {G : SimpleGraph A} (P : D8SeparatedParameters G) (rho : ℝ)
    (hm : 4 ≤ (universalVertices G).card) (hrho0 : 0 ≤ rho)
    (hrhoLe : rho ≤ ((universalVertices G).card : ℝ) * P.betaMass)
    (e : Sym2 (↑(nonUniversalVertices G))) :
    (P.toD7HallParameters rho hm hrho0 hrhoLe).beta e =
      P.hallScale rho * P.beta e / 2 := by
  rfl

lemma D8SeparatedParameters.toD7HallParameters_alphaMass
    {G : SimpleGraph A} (P : D8SeparatedParameters G) (rho : ℝ)
    (hm : 4 ≤ (universalVertices G).card) (hrho0 : 0 ≤ rho)
    (hrhoLe : rho ≤ ((universalVertices G).card : ℝ) * P.betaMass) :
    (P.toD7HallParameters rho hm hrho0 hrhoLe).alphaMass =
      P.alphaMass / 2 := by
  unfold D7SeparatedParameters.alphaMass D8SeparatedParameters.alphaMass
  rw [Finset.sum_congr rfl fun u _ ↦
    P.toD7HallParameters_alpha rho hm hrho0 hrhoLe u,
    ← Finset.sum_div]
  ring

lemma D8SeparatedParameters.toD7HallParameters_betaIncident
    {G : SimpleGraph A} (P : D8SeparatedParameters G) (rho : ℝ)
    (hm : 4 ≤ (universalVertices G).card) (hrho0 : 0 ≤ rho)
    (hrhoLe : rho ≤ ((universalVertices G).card : ℝ) * P.betaMass)
    (u : ↑(nonUniversalVertices G)) :
    (P.toD7HallParameters rho hm hrho0 hrhoLe).betaIncident u =
      P.hallScale rho * P.betaIncident u / 2 := by
  unfold D7SeparatedParameters.betaIncident D8SeparatedParameters.betaIncident
  rw [Finset.sum_congr rfl fun e he ↦
    P.toD7HallParameters_beta rho hm hrho0 hrhoLe e]
  calc
    (∑ e ∈ (G.induce
        (↑(nonUniversalVertices G) : Set A)).edgeFinset with
          (u : ↑(nonUniversalVertices G)) ∈ e.toFinset,
        P.hallScale rho * P.beta e / 2) =
      (∑ e ∈ (G.induce
        (↑(nonUniversalVertices G) : Set A)).edgeFinset with
          (u : ↑(nonUniversalVertices G)) ∈ e.toFinset,
        P.hallScale rho * P.beta e) / 2 := by rw [Finset.sum_div]
    _ = (P.hallScale rho *
        ∑ e ∈ (G.induce
          (↑(nonUniversalVertices G) : Set A)).edgeFinset with
            (u : ↑(nonUniversalVertices G)) ∈ e.toFinset,
          P.beta e) / 2 := by rw [Finset.mul_sum]

/-- Halve a D8 Hall flow and regard it as a D7 Hall flow for the normalized
adapter parameters. -/
def D8HallRedistribution.toD7Half
    (G : SimpleGraph A) (P : D8SeparatedParameters G)
    {rho : ℝ} (sigma : A → ℕ)
    (R : D8HallRedistribution G P rho sigma)
    (hm : 4 ≤ (universalVertices G).card) (hrho0 : 0 ≤ rho)
    (hrhoLe : rho ≤ ((universalVertices G).card : ℝ) * P.betaMass) :
    D7HallRedistribution G (P.toD7HallParameters rho hm hrho0 hrhoLe) sigma := by
  let P7 := P.toD7HallParameters rho hm hrho0 hrhoLe
  refine
    { betaFlow := fun u v ↦ R.betaFlow u v / 2
      alphaFlow := fun u ↦ R.alphaFlow u / 2
      beta_nonneg := fun u v ↦ div_nonneg (R.beta_nonneg u v) (by norm_num)
      alpha_nonneg := fun u ↦ div_nonneg (R.alpha_nonneg u) (by norm_num)
      beta_source_sum := ?_
      alpha_sum := ?_
      diagonal_zero := fun u ↦ by rw [R.diagonal_zero]; norm_num
      target_le := ?_ }
  · intro v
    rw [← Finset.sum_div, R.beta_source_sum]
    unfold d7HallBetaSource d8HallBetaSource
    rw [P.toD7HallParameters_betaIncident rho hm hrho0 hrhoLe v]
    unfold D8SeparatedParameters.hallScale
    have hmR : ((universalVertices G).card : ℝ) ≠ 0 := by positivity
    field_simp [hmR]
  · rw [← Finset.sum_div, R.alpha_sum]
    unfold d7HallAlphaSource d8HallAlphaSource
    rw [P.toD7HallParameters_alphaMass rho hm hrho0 hrhoLe]
    ring
  · intro u
    have htarget := R.target_le u
    have hcap0 := d8HallCapacity_nonneg G sigma u
    rw [← Finset.sum_div]
    change (∑ v, R.betaFlow u v) / 2 + R.alphaFlow u / 2 ≤
      d8HallCapacity G sigma u
    nlinarith

@[simp] lemma D8HallRedistribution.toD7Half_betaFlow
    (G : SimpleGraph A) (P : D8SeparatedParameters G)
    {rho : ℝ} (sigma : A → ℕ)
    (R : D8HallRedistribution G P rho sigma)
    (hm : 4 ≤ (universalVertices G).card) (hrho0 : 0 ≤ rho)
    (hrhoLe : rho ≤ ((universalVertices G).card : ℝ) * P.betaMass)
    (u v : ↑(nonUniversalVertices G)) :
    (R.toD7Half G P sigma hm hrho0 hrhoLe).betaFlow u v =
      R.betaFlow u v / 2 := by
  rfl

@[simp] lemma D8HallRedistribution.toD7Half_alphaFlow
    (G : SimpleGraph A) (P : D8SeparatedParameters G)
    {rho : ℝ} (sigma : A → ℕ)
    (R : D8HallRedistribution G P rho sigma)
    (hm : 4 ≤ (universalVertices G).card) (hrho0 : 0 ≤ rho)
    (hrhoLe : rho ≤ ((universalVertices G).card : ℝ) * P.betaMass)
    (u : ↑(nonUniversalVertices G)) :
    (R.toD7Half G P sigma hm hrho0 hrhoLe).alphaFlow u =
      R.alphaFlow u / 2 := by
  rfl

lemma two_mul_d7SmallHallDeduction_toD7Half
    (G : SimpleGraph A) (P : D8SeparatedParameters G)
    {rho : ℝ} (sigma : A → ℕ)
    (R : D8HallRedistribution G P rho sigma)
    (hm : 4 ≤ (universalVertices G).card) (hrho0 : 0 ≤ rho)
    (hrhoLe : rho ≤ ((universalVertices G).card : ℝ) * P.betaMass)
    (u : ↑(nonUniversalVertices G))
    (e : Sym2 (↑(d7DeletedFinset (u : A)))) :
    2 * d7SmallHallDeduction G
        (P.toD7HallParameters rho hm hrho0 hrhoLe) sigma
        (R.toD7Half G P sigma hm hrho0 hrhoLe) u e =
      d8HallDeduction G P rho sigma R u e := by
  induction e using Sym2.inductionOn with
  | hf x y =>
      unfold d7SmallHallDeduction d8HallDeduction
      simp only [Sym2.lift_mk]
      by_cases hx : (x : A) ∈ universalVertices G <;>
        by_cases hy : (y : A) ∈ universalVertices G <;>
        simp only [hx, hy, dite_true, dite_false]
      all_goals try rw [D8HallRedistribution.toD7Half_alphaFlow]
      all_goals try rw [D8HallRedistribution.toD7Half_betaFlow]
      all_goals ring

/-- Exact total Hall deduction at a deleted nonuniversal vertex.  The proof
reduces to the already checked D7 summation identity through the normalized
half-flow adapter. -/
lemma sum_d8HallDeduction
    (G : SimpleGraph A) (P : D8SeparatedParameters G)
    {rho : ℝ} (sigma : A → ℕ)
    (R : D8HallRedistribution G P rho sigma)
    (hm : 4 ≤ (universalVertices G).card) (hrho0 : 0 ≤ rho)
    (hrhoLe : rho ≤ ((universalVertices G).card : ℝ) * P.betaMass)
    (u : ↑(nonUniversalVertices G)) :
    (∑ e ∈ (⊤ : SimpleGraph
        (↑(d7DeletedFinset (u : A)))).edgeFinset,
      d8HallDeduction G P rho sigma R u e) =
      (∑ v : ↑(nonUniversalVertices G), R.betaFlow u v) +
        R.alphaFlow u := by
  let P7 := P.toD7HallParameters rho hm hrho0 hrhoLe
  let R7 := R.toD7Half G P sigma hm hrho0 hrhoLe
  have hd7 := sum_d7SmallHallDeduction G P7 sigma R7 hm u
  calc
    (∑ e ∈ (⊤ : SimpleGraph
        (↑(d7DeletedFinset (u : A)))).edgeFinset,
      d8HallDeduction G P rho sigma R u e) =
        ∑ e ∈ (⊤ : SimpleGraph
          (↑(d7DeletedFinset (u : A)))).edgeFinset,
          2 * d7SmallHallDeduction G P7 sigma R7 u e := by
      apply Finset.sum_congr rfl
      intro e he
      exact (two_mul_d7SmallHallDeduction_toD7Half
        G P sigma R hm hrho0 hrhoLe u e).symm
    _ = 2 * (∑ e ∈ (⊤ : SimpleGraph
          (↑(d7DeletedFinset (u : A)))).edgeFinset,
          d7SmallHallDeduction G P7 sigma R7 u e) := by
      rw [Finset.mul_sum]
    _ = 2 * ((∑ v : ↑(nonUniversalVertices G), R.betaFlow u v / 2) +
          R.alphaFlow u / 2) := by
      rw [hd7]
      rfl
    _ = (∑ v : ↑(nonUniversalVertices G), R.betaFlow u v) +
          R.alphaFlow u := by
      rw [← Finset.sum_div]
      ring

lemma d8HallDeletedCapacity_support
    (G : SimpleGraph A) (P : D8SeparatedParameters G)
    (rho : ℝ) (sigma : A → ℕ)
    (R : D8HallRedistribution G P rho sigma)
    (u : ↑(nonUniversalVertices G))
    (e : Sym2 (↑(d7DeletedFinset (u : A))))
    (he : e ∉ (d7DeletedGraph G (u : A)).edgeSet) :
    d8HallDeletedCapacity G P rho sigma R u e = 0 := by
  rw [d8HallDeletedCapacity, if_neg]
  simpa only [SimpleGraph.mem_edgeFinset] using he

private lemma filter_topEdgeFinset_graph_eq_d8
    {B : Type} [Fintype B] [DecidableEq B] (H : SimpleGraph B) :
    (⊤ : SimpleGraph B).edgeFinset.filter (fun e ↦ e ∈ H.edgeFinset) =
      H.edgeFinset := by
  apply Finset.Subset.antisymm
  · intro e he
    exact (Finset.mem_filter.mp he).2
  · intro e he
    exact Finset.mem_filter.mpr ⟨SimpleGraph.edgeFinset_mono le_top he, he⟩

private lemma filter_topEdgeFinset_not_graph_eq_d8
    {B : Type} [Fintype B] [DecidableEq B] (H : SimpleGraph B) :
    (⊤ : SimpleGraph B).edgeFinset.filter (fun e ↦ e ∉ H.edgeFinset) =
      Hᶜ.edgeFinset := by
  ext e
  simp only [Finset.mem_filter, SimpleGraph.mem_edgeFinset]
  induction e using Sym2.inductionOn with
  | hf x y => simp [SimpleGraph.compl_adj]

lemma capacityMissingWeight_d8HallDeletedCapacity
    (G : SimpleGraph A) (P : D8SeparatedParameters G)
    (rho : ℝ) (sigma : A → ℕ)
    (R : D8HallRedistribution G P rho sigma)
    (u : ↑(nonUniversalVertices G)) :
    capacityMissingWeight (d8HallDeletedCapacity G P rho sigma R u) =
      (missingEdgeCount (d7DeletedGraph G (u : A)) : ℝ) +
        ∑ e ∈ (d7DeletedGraph G (u : A)).edgeFinset,
          d8HallDeduction G P rho sigma R u e := by
  let H := d7DeletedGraph G (u : A)
  let E := (⊤ : SimpleGraph (↑(d7DeletedFinset (u : A)))).edgeFinset
  unfold capacityMissingWeight
  rw [← Finset.sum_filter_add_sum_filter_not E
    (fun e ↦ e ∈ H.edgeFinset)]
  change
    (∑ e ∈ E.filter (fun e ↦ e ∈ H.edgeFinset),
        (1 - d8HallDeletedCapacity G P rho sigma R u e)) +
      (∑ e ∈ E.filter (fun e ↦ e ∉ H.edgeFinset),
        (1 - d8HallDeletedCapacity G P rho sigma R u e)) = _
  rw [show E.filter (fun e ↦ e ∈ H.edgeFinset) = H.edgeFinset by
        simpa only [E] using filter_topEdgeFinset_graph_eq_d8 H,
      show E.filter (fun e ↦ e ∉ H.edgeFinset) = Hᶜ.edgeFinset by
        simpa only [E] using filter_topEdgeFinset_not_graph_eq_d8 H]
  have hedge :
      (∑ e ∈ H.edgeFinset,
        (1 - d8HallDeletedCapacity G P rho sigma R u e)) =
        ∑ e ∈ H.edgeFinset, d8HallDeduction G P rho sigma R u e := by
    apply Finset.sum_congr rfl
    intro e he
    rw [d8HallDeletedCapacity, if_pos]
    · ring
    · simpa only [H] using he
  have hnonedge :
      (∑ e ∈ Hᶜ.edgeFinset,
        (1 - d8HallDeletedCapacity G P rho sigma R u e)) =
        (Hᶜ.edgeFinset.card : ℝ) := by
    calc
      (∑ e ∈ Hᶜ.edgeFinset,
          (1 - d8HallDeletedCapacity G P rho sigma R u e)) =
          ∑ _e ∈ Hᶜ.edgeFinset, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro e he
        rw [d8HallDeletedCapacity, if_neg]
        · ring
        · intro heH
          induction e using Sym2.inductionOn with
          | hf x y =>
              simp only [SimpleGraph.mem_edgeFinset,
                SimpleGraph.mem_edgeSet, SimpleGraph.compl_adj] at he
              exact he.2 (SimpleGraph.mem_edgeFinset.mp heH)
      _ = (Hᶜ.edgeFinset.card : ℝ) := by simp
  rw [hedge, hnonedge]
  change _ + (Hᶜ.edgeFinset.card : ℝ) =
    (Hᶜ.edgeFinset.card : ℝ) + _
  exact add_comm _ _

lemma capacityMissingWeight_d8HallDeletedCapacity_le
    (G : SimpleGraph A) (P : D8SeparatedParameters G)
    {rho : ℝ} (sigma : A → ℕ)
    (R : D8HallRedistribution G P rho sigma)
    (hm : 4 ≤ (universalVertices G).card) (hrho0 : 0 ≤ rho)
    (hrhoLe : rho ≤ ((universalVertices G).card : ℝ) * P.betaMass)
    (u : ↑(nonUniversalVertices G)) :
    capacityMissingWeight (d8HallDeletedCapacity G P rho sigma R u) ≤
      (missingEdgeCount (d7DeletedGraph G (u : A)) : ℝ) +
        d8HallCapacity G sigma u := by
  rw [capacityMissingWeight_d8HallDeletedCapacity]
  refine add_le_add_right ?_ _
  calc
    (∑ e ∈ (d7DeletedGraph G (u : A)).edgeFinset,
        d8HallDeduction G P rho sigma R u e) ≤
        ∑ e ∈ (⊤ : SimpleGraph
          (↑(d7DeletedFinset (u : A)))).edgeFinset,
          d8HallDeduction G P rho sigma R u e := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact SimpleGraph.edgeFinset_mono le_top
      · intro e _heTop _heNot
        exact d8HallDeduction_nonneg G P rho sigma R u e
    _ = (∑ v : ↑(nonUniversalVertices G), R.betaFlow u v) +
          R.alphaFlow u :=
      sum_d8HallDeduction G P sigma R hm hrho0 hrhoLe u
    _ ≤ d8HallCapacity G sigma u := R.target_le u

lemma capacityMissingWeight_d8HallDeletedCapacity_inductionBound
    {n : ℕ} (hcard : Fintype.card A = n) (hn : 14 ≤ n)
    (G : SimpleGraph A) (hexact : missingEdgeCount G = n)
    (P : D8SeparatedParameters G) {rho : ℝ} (sigma : A → ℕ)
    (hsigma : ∀ v, sigma v ≤ d7ResidualAllowance G 4 v)
    (R : D8HallRedistribution G P rho sigma)
    (hm : 4 ≤ (universalVertices G).card) (hrho0 : 0 ≤ rho)
    (hrhoLe : rho ≤ ((universalVertices G).card : ℝ) * P.betaMass)
    (u : ↑(nonUniversalVertices G)) :
    capacityMissingWeight (d8HallDeletedCapacity G P rho sigma R u) ≤
      ((n - 1) - 4 + (4 - sigma u) : ℕ) := by
  have hdegreePos : 0 < Gᶜ.degree (u : A) :=
    mem_nonUniversalVertices.mp u.property
  have hsigmaFour : sigma u ≤ 4 :=
    (hsigma u).trans (Nat.min_le_left _ _)
  have hsigmaDegree : sigma u + 1 ≤ Gᶜ.degree (u : A) := by
    have h := (hsigma u).trans (Nat.min_le_right _ _)
    omega
  have hmissingExact : missingEdgeCount (d7DeletedGraph G (u : A)) =
      missingEdgeCount G - Gᶜ.degree (u : A) := by
    change missingEdgeCount
      (G.induce (↑((Finset.univ : Finset A).erase (u : A)) : Set A)) = _
    exact missingEdgeCount_induce_univ_erase G (u : A)
  have hdegreeLe : Gᶜ.degree (u : A) ≤ missingEdgeCount G := by
    simpa only [missingEdgeCount, Nat.card_eq_fintype_card,
      SimpleGraph.card_edgeSet] using
      (Gᶜ.degree_le_card_edgeFinset (v := (u : A)))
  have hnat : missingEdgeCount (d7DeletedGraph G (u : A)) +
      (Gᶜ.degree (u : A) - 1 - sigma u) =
        (n - 1) - 4 + (4 - sigma u) := by
    rw [hmissingExact, hexact]
    omega
  calc
    capacityMissingWeight (d8HallDeletedCapacity G P rho sigma R u) ≤
        (missingEdgeCount (d7DeletedGraph G (u : A)) : ℝ) +
          d8HallCapacity G sigma u :=
      capacityMissingWeight_d8HallDeletedCapacity_le
        G P sigma R hm hrho0 hrhoLe u
    _ = ((n - 1) - 4 + (4 - sigma u) : ℕ) := by
      unfold d8HallCapacity
      exact_mod_cast hnat

/-- Weighted induction on every Hall-adjusted nonuniversal deletion. -/
theorem exists_d8HallSupportedWeightedPacking
    {n : ℕ} (hcard : Fintype.card A = n) (hn : 14 ≤ n)
    (G : SimpleGraph A) (hexact : missingEdgeCount G = n)
    (P : D8SeparatedParameters G) {rho : ℝ} (sigma : A → ℕ)
    (hsigma : ∀ v, sigma v ≤ d7ResidualAllowance G 4 v)
    (R : D8HallRedistribution G P rho sigma)
    (hm : 4 ≤ (universalVertices G).card) (hrho0 : 0 ≤ rho)
    (hrhoLe : rho ≤ ((universalVertices G).card : ℝ) * P.betaMass)
    (hstrong : AlmostCompleteStrongAt (n - 1))
    (u : ↑(nonUniversalVertices G)) :
    ∃ w : Finset (↑(d7DeletedFinset (u : A))) → ℝ,
      IsCapacityPacking (d7DeletedGraph G (u : A))
        (d8HallDeletedCapacity G P rho sigma R u) w ∧
      IsCapacityPacking (⊤ : SimpleGraph (↑(d7DeletedFinset (u : A))))
        (d8HallDeletedCapacity G P rho sigma R u) w ∧
      capacityUncoveredWeight
          (⊤ : SimpleGraph (↑(d7DeletedFinset (u : A))))
          (d8HallDeletedCapacity G P rho sigma R u) w ≤
        ((4 - sigma u : ℕ) : ℝ) ∧
      IsHalfBounded (⊤ : SimpleGraph
        (↑(d7DeletedFinset (u : A)))) w := by
  have horder : Fintype.card (↑(d7DeletedFinset (u : A))) = n - 1 := by
    unfold d7DeletedFinset
    rw [card_univ_erase, hcard]
  have hdefect : 4 - sigma u ≤ 4 := Nat.sub_le _ _
  obtain ⟨w, hw, hunc, hhalf⟩ := weightedPacking_of_strongAt
    hstrong horder hdefect (d8HallDeletedCapacity G P rho sigma R u)
      (d8HallDeletedCapacity_isEdgeCapacity
        G P sigma R hm hrho0 hrhoLe u)
      (capacityMissingWeight_d8HallDeletedCapacity_inductionBound
        hcard hn G hexact P sigma hsigma R hm hrho0 hrhoLe u)
  let H := d7DeletedGraph G (u : A)
  let v := zeroExtendTriangleWeight H w
  have hsupport : ∀ e, e ∉ H.edgeSet →
      d8HallDeletedCapacity G P rho sigma R u e = 0 := by
    intro e he
    exact d8HallDeletedCapacity_support G P rho sigma R u e (by
      simpa only [H] using he)
  have hvTop : IsCapacityPacking
      (⊤ : SimpleGraph (↑(d7DeletedFinset (u : A))))
      (d8HallDeletedCapacity G P rho sigma R u) v := by
    constructor
    · intro t htTop
      dsimp only [v]
      by_cases htH : t ∈ H.cliqueFinset 3
      · rw [zeroExtendTriangleWeight_of_mem htH]
        exact hw.1 t htTop
      · rw [zeroExtendTriangleWeight_of_not_mem htH]
    · intro e heTop
      dsimp only [v]
      rw [fractionalEdgeLoad_zeroExtend_eq_of_capacity_support hw hsupport]
      exact hw.2 e heTop
  refine ⟨v, hw.zeroExtend_support hsupport, hvTop, ?_, ?_⟩
  · rw [show capacityUncoveredWeight
        (⊤ : SimpleGraph (↑(d7DeletedFinset (u : A))))
          (d8HallDeletedCapacity G P rho sigma R u) v =
        capacityUncoveredWeight
        (⊤ : SimpleGraph (↑(d7DeletedFinset (u : A))))
          (d8HallDeletedCapacity G P rho sigma R u) w by
      exact capacityUncoveredWeight_zeroExtend_eq_of_capacity_support
        hw hsupport]
    exact hunc
  · intro t htTop
    dsimp only [v]
    by_cases htH : t ∈ H.cliqueFinset 3
    · rw [zeroExtendTriangleWeight_of_mem htH]
      exact hhalf t htTop
    · rw [zeroExtendTriangleWeight_of_not_mem htH]
      norm_num

/-! ### The explicit Hall-branch correction -/

lemma D8SeparatedParameters.rhoRatio_mul_betaMass
    {G : SimpleGraph A} (P : D8SeparatedParameters G) {rho : ℝ}
    (hrho0 : 0 ≤ rho)
    (hrhoLe : rho ≤ ((universalVertices G).card : ℝ) * P.betaMass) :
    P.rhoRatio rho * P.betaMass = rho := by
  unfold D8SeparatedParameters.rhoRatio
  by_cases hbeta : P.betaMass = 0
  · rw [hbeta, if_pos rfl, mul_zero]
    have hm0 : 0 ≤ ((universalVertices G).card : ℝ) := Nat.cast_nonneg _
    nlinarith
  · rw [if_neg hbeta]
    field_simp

/-- The `UUZ` part of the complementary D8 correction.  The Hall flow
removes the fraction `rhoRatio / m` from each beta orbit, so this correction
retains precisely the complementary `hallScale` fraction. -/
def d8HallUUZCorrection (G : SimpleGraph A) (P : D8SeparatedParameters G)
    (rho : ℝ) : Finset A → ℝ :=
  fun t ↦ P.hallScale rho * d8UUZCorrection G P t

/-- The `UZZ` part of the complementary D8 correction. -/
def d8HallUZZCorrection (G : SimpleGraph A)
    (P : D8SeparatedParameters G) : Finset A → ℝ :=
  fun t ↦ ∑ u : ↑(nonUniversalVertices G),
    weightedAttachedEdgeWeight (universalVertices G) (u : A)
      ((⊤ : SimpleGraph (↑(universalVertices G))).edgeFinset)
      (fun _ ↦ P.alpha u) t

/-- The `ZZZ` part of the complementary D8 correction. -/
def d8HallZZZCorrection (G : SimpleGraph A)
    (P : D8SeparatedParameters G) : Finset A → ℝ :=
  fun t ↦ ∑ q : ↑((universalVertices G).powersetCard 3),
    singleTriangleWeight q P.gamma t

/-- The explicit correction `omega'` in the Hall branch of D8. -/
def d8HallCorrection (G : SimpleGraph A) (P : D8SeparatedParameters G)
    (rho : ℝ) : Finset A → ℝ :=
  fun t ↦ d8HallUUZCorrection G P rho t +
    d8HallUZZCorrection G P t + d8HallZZZCorrection G P t

lemma d8HallCorrection_nonneg (G : SimpleGraph A)
    (P : D8SeparatedParameters G) {rho : ℝ}
    (hm : 4 ≤ (universalVertices G).card)
    (hrhoLe : rho ≤ ((universalVertices G).card : ℝ) * P.betaMass) :
    ∀ t ∈ G.cliqueFinset 3, 0 ≤ d8HallCorrection G P rho t := by
  intro t ht
  have hscale0 : 0 ≤ P.hallScale rho :=
    P.hallScale_nonneg (by omega) hrhoLe
  have hUUZ : 0 ≤ d8HallUUZCorrection G P rho t :=
    mul_nonneg hscale0 (d8UUZCorrection_nonneg G P t ht)
  have hUZZ : 0 ≤ d8HallUZZCorrection G P t := by
    unfold d8HallUZZCorrection
    exact Finset.sum_nonneg fun u _ ↦
      weightedAttachedEdgeWeight_nonneg
        (fun _ _ ↦ P.alpha_nonneg u) t ht
  have hZZZ : 0 ≤ d8HallZZZCorrection G P t := by
    unfold d8HallZZZCorrection singleTriangleWeight
    exact Finset.sum_nonneg fun q _ ↦ by
      split_ifs
      · exact P.gamma_nonneg
      · exact le_rfl
  exact add_nonneg (add_nonneg hUUZ hUZZ) hZZZ

lemma fractionalSize_d8HallUUZCorrection (G : SimpleGraph A)
    (P : D8SeparatedParameters G) (rho : ℝ) :
    fractionalSize G (d8HallUUZCorrection G P rho) =
      P.hallScale rho *
        (((universalVertices G).card : ℝ) * P.betaMass) := by
  unfold d8HallUUZCorrection
  rw [fractionalSize_smulWeight, fractionalSize_d8UUZCorrection]

lemma fractionalSize_d8HallUZZCorrection (G : SimpleGraph A)
    (P : D8SeparatedParameters G) :
    fractionalSize G (d8HallUZZCorrection G P) =
      (((universalVertices G).card.choose 2 : ℕ) : ℝ) *
        ∑ u : ↑(nonUniversalVertices G), P.alpha u := by
  unfold fractionalSize d8HallUZZCorrection
  rw [Finset.sum_comm]
  calc
    (∑ u : ↑(nonUniversalVertices G),
        ∑ t ∈ G.cliqueFinset 3,
          weightedAttachedEdgeWeight (universalVertices G) (u : A)
            (⊤ : SimpleGraph (↑(universalVertices G))).edgeFinset
            (fun _ ↦ P.alpha u) t) =
        ∑ u : ↑(nonUniversalVertices G),
          (((universalVertices G).card.choose 2 : ℕ) : ℝ) *
            P.alpha u := by
      apply Fintype.sum_congr
      intro u
      change fractionalSize G
        (weightedAttachedEdgeWeight (universalVertices G) (u : A)
          (⊤ : SimpleGraph (↑(universalVertices G))).edgeFinset
          (fun _ ↦ P.alpha u)) = _
      rw [fractionalSize_weightedAttachedEdgeWeight
        (fun e he ↦ d7UZZTriangle_mem_cliqueFinset G u ⟨e, he⟩),
        Finset.sum_const, SimpleGraph.card_edgeFinset_top_eq_card_choose_two]
      simp only [Fintype.card_coe, nsmul_eq_mul]
    _ = (((universalVertices G).card.choose 2 : ℕ) : ℝ) *
          ∑ u : ↑(nonUniversalVertices G), P.alpha u := by
      rw [Finset.mul_sum]

lemma fractionalSize_d8HallZZZCorrection (G : SimpleGraph A)
    (P : D8SeparatedParameters G) :
    fractionalSize G (d8HallZZZCorrection G P) =
      (((universalVertices G).card.choose 3 : ℕ) : ℝ) * P.gamma := by
  unfold fractionalSize d8HallZZZCorrection singleTriangleWeight
  rw [Finset.sum_comm]
  calc
    (∑ q : ↑((universalVertices G).powersetCard 3),
        ∑ t ∈ G.cliqueFinset 3,
          if t = (q : Finset A) then P.gamma else 0) =
        ∑ _q : ↑((universalVertices G).powersetCard 3), P.gamma := by
      apply Fintype.sum_congr
      intro q
      rw [Finset.sum_eq_single (q : Finset A)]
      · simp
      · intro t _ hne
        rw [if_neg hne]
      · intro hnot
        exact (hnot (d7ZZZTriangle_mem_cliqueFinset G q)).elim
    _ = (((universalVertices G).card.choose 3 : ℕ) : ℝ) *
          P.gamma := by
      simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
        Fintype.card_coe, Finset.card_powersetCard]

lemma fractionalSize_d8HallCorrection (G : SimpleGraph A)
    (P : D8SeparatedParameters G) (rho : ℝ) :
    fractionalSize G (d8HallCorrection G P rho) =
      P.hallScale rho *
          (((universalVertices G).card : ℝ) * P.betaMass) +
        (((universalVertices G).card.choose 2 : ℕ) : ℝ) *
          ∑ u : ↑(nonUniversalVertices G), P.alpha u +
        (((universalVertices G).card.choose 3 : ℕ) : ℝ) *
          P.gamma := by
  unfold fractionalSize d8HallCorrection
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    show (∑ x ∈ G.cliqueFinset 3, d8HallUUZCorrection G P rho x) =
        P.hallScale rho *
          (((universalVertices G).card : ℝ) * P.betaMass) by
      exact fractionalSize_d8HallUUZCorrection G P rho,
    show (∑ x ∈ G.cliqueFinset 3, d8HallUZZCorrection G P x) =
        (((universalVertices G).card.choose 2 : ℕ) : ℝ) *
          ∑ u : ↑(nonUniversalVertices G), P.alpha u by
      exact fractionalSize_d8HallUZZCorrection G P,
    show (∑ x ∈ G.cliqueFinset 3, d8HallZZZCorrection G P x) =
        (((universalVertices G).card.choose 3 : ℕ) : ℝ) * P.gamma by
      exact fractionalSize_d8HallZZZCorrection G P]

/-- Exact correction mass in the form needed for the final cancellation. -/
lemma three_mul_fractionalSize_d8HallCorrection
    (G : SimpleGraph A) (P : D8SeparatedParameters G) {rho : ℝ}
    (hm : 4 ≤ (universalVertices G).card)
    (hrho0 : 0 ≤ rho)
    (hrhoLe : rho ≤ ((universalVertices G).card : ℝ) * P.betaMass) :
    3 * fractionalSize G (d8HallCorrection G P rho) =
      ((universalVertices G).card : ℝ) *
          ((((universalVertices G).card : ℝ) - 1) *
              (((universalVertices G).card : ℝ) - 2) / 2 * P.gamma +
            P.alphaMass + P.betaMass) +
        2 * ((universalVertices G).card : ℝ) * P.betaMass -
        3 * rho + ((universalVertices G).card : ℝ) / 2 * P.alphaMass := by
  rw [fractionalSize_d8HallCorrection, Nat.cast_choose_two,
    cast_choose_three_d7]
  let m : ℝ := ((universalVertices G).card : ℝ)
  have hm0 : m ≠ 0 := by
    dsimp only [m]
    positivity
  have hratio := P.rhoRatio_mul_betaMass hrho0 hrhoLe
  have halpha : P.alphaMass =
      (m - 1) * ∑ u : ↑(nonUniversalVertices G), P.alpha u := rfl
  unfold D8SeparatedParameters.hallScale
  change 3 * ((1 - P.rhoRatio rho / m) * (m * P.betaMass) +
      (m * (m - 1) / 2) *
        (∑ u : ↑(nonUniversalVertices G), P.alpha u) +
      (m * (m - 1) * (m - 2) / 6) * P.gamma) = _
  rw [halpha] at ⊢
  field_simp [hm0]
  nlinarith

lemma fractionalEdgeLoad_d8HallUUZCorrection
    (G : SimpleGraph A) (P : D8SeparatedParameters G) (rho : ℝ)
    (e : Sym2 A) :
    fractionalEdgeLoad G (d8HallUUZCorrection G P rho) e =
      P.hallScale rho * fractionalEdgeLoad G (d8UUZCorrection G P) e := by
  unfold d8HallUUZCorrection
  rw [fractionalEdgeLoad_smul]

lemma fractionalEdgeLoad_d8HallUZZCorrection
    (G : SimpleGraph A) (P : D8SeparatedParameters G) (p : Sym2 A) :
    fractionalEdgeLoad G (d8HallUZZCorrection G P) p =
      ∑ u : ↑(nonUniversalVertices G),
        ∑ e : ↑((⊤ : SimpleGraph
          (↑(universalVertices G))).edgeFinset),
          if p ∈ (attachedEdgeTriangle (universalVertices G) (u : A) e).sym2
          then P.alpha u else 0 := by
  unfold d8HallUZZCorrection
  rw [fractionalEdgeLoad_sum]
  apply Finset.sum_congr rfl
  intro u _
  exact fractionalEdgeLoad_weightedAttachedEdgeWeight
    (fun e he ↦ d7UZZTriangle_mem_cliqueFinset G u ⟨e, he⟩) p

lemma fractionalEdgeLoad_d8HallUZZCorrection_induced
    (G : SimpleGraph A) (P : D8SeparatedParameters G)
    (e : Sym2 (↑(universalVertices G)))
    (he : e ∈ (⊤ : SimpleGraph (↑(universalVertices G))).edgeFinset) :
    fractionalEdgeLoad G (d8HallUZZCorrection G P)
        ((inducedEmbedding (universalVertices G)).sym2Map e) =
      ∑ u : ↑(nonUniversalVertices G), P.alpha u := by
  unfold d8HallUZZCorrection
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

lemma fractionalEdgeLoad_d8HallUZZCorrection_mixed
    (G : SimpleGraph A) (P : D8SeparatedParameters G)
    (u : ↑(nonUniversalVertices G)) (z : ↑(universalVertices G)) :
    fractionalEdgeLoad G (d8HallUZZCorrection G P) s((u : A), (z : A)) =
      (((universalVertices G).card : ℝ) - 1) * P.alpha u := by
  unfold d8HallUZZCorrection
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

lemma fractionalEdgeLoad_d8HallUZZCorrection_nonUniversal
    (G : SimpleGraph A) (P : D8SeparatedParameters G)
    (e : Sym2 (↑(nonUniversalVertices G))) (heND : ¬e.IsDiag) :
    fractionalEdgeLoad G (d8HallUZZCorrection G P)
        ((inducedEmbedding (nonUniversalVertices G)).sym2Map e) = 0 := by
  induction e using Sym2.inductionOn with
  | hf u v =>
      simp only [Sym2.mk_isDiag_iff] at heND
      rw [fractionalEdgeLoad_d8HallUZZCorrection]
      apply Fintype.sum_eq_zero
      intro x
      apply Fintype.sum_eq_zero
      intro f
      rw [if_neg]
      exact outsidePair_not_mem_attachedEdgeTriangle
        (nonUniversalVertex_not_mem_universalVertices G u.property)
        (nonUniversalVertex_not_mem_universalVertices G v.property)
        (fun h ↦ heND (Subtype.ext h)) f

lemma fractionalEdgeLoad_d8HallZZZCorrection
    (G : SimpleGraph A) (P : D8SeparatedParameters G) (p : Sym2 A) :
    fractionalEdgeLoad G (d8HallZZZCorrection G P) p =
      ∑ q : ↑((universalVertices G).powersetCard 3),
        if p ∈ (q : Finset A).sym2 then P.gamma else 0 := by
  unfold d8HallZZZCorrection
  rw [fractionalEdgeLoad_sum]
  apply Finset.sum_congr rfl
  intro q _
  exact fractionalEdgeLoad_singleTriangle
    (d7ZZZTriangle_mem_cliqueFinset G q) P.gamma p

lemma fractionalEdgeLoad_d8HallZZZCorrection_induced
    (G : SimpleGraph A) (P : D8SeparatedParameters G)
    (e : Sym2 (↑(universalVertices G))) (heND : ¬e.IsDiag) :
    fractionalEdgeLoad G (d8HallZZZCorrection G P)
        ((inducedEmbedding (universalVertices G)).sym2Map e) =
      (((universalVertices G).card : ℝ) - 2) * P.gamma := by
  rw [fractionalEdgeLoad_d8HallZZZCorrection]
  calc
    (∑ q : ↑((universalVertices G).powersetCard 3),
        if (inducedEmbedding (universalVertices G)).sym2Map e ∈
          (q : Finset A).sym2 then P.gamma else 0) =
        ∑ q ∈ (universalVertices G).powersetCard 3,
          if (inducedEmbedding (universalVertices G)).sym2Map e ∈ q.sym2
          then P.gamma else 0 :=
      (Finset.sum_subtype ((universalVertices G).powersetCard 3)
        (fun _ ↦ Iff.rfl)
        (fun q ↦ if (inducedEmbedding
          (universalVertices G)).sym2Map e ∈ q.sym2
          then P.gamma else 0)).symm
    _ = ∑ q ∈ ((universalVertices G).powersetCard 3).filter
          (fun q ↦ (inducedEmbedding
            (universalVertices G)).sym2Map e ∈ q.sym2), P.gamma := by
      rw [Finset.sum_filter]
    _ = (((universalVertices G).card : ℝ) - 2) * P.gamma := by
      rw [Finset.sum_const,
        card_universal_triangles_through_induced_edge G e heND]
      simp only [nsmul_eq_mul]
      have hm : 2 ≤ (universalVertices G).card := by
        have hcard := Sym2.card_toFinset_of_not_isDiag e heND
        have hle := Finset.card_le_card (Finset.subset_univ e.toFinset)
        rw [hcard] at hle
        simpa only [Finset.card_univ, Fintype.card_coe] using hle
      rw [Nat.cast_sub hm, Nat.cast_ofNat]

lemma fractionalEdgeLoad_d8HallZZZCorrection_nonUniversal_left
    (G : SimpleGraph A) (P : D8SeparatedParameters G)
    (u : ↑(nonUniversalVertices G)) (x : A) :
    fractionalEdgeLoad G (d8HallZZZCorrection G P) s((u : A), x) = 0 := by
  rw [fractionalEdgeLoad_d8HallZZZCorrection]
  apply Fintype.sum_eq_zero
  intro q
  rw [if_neg]
  have hqsub := (Finset.mem_powersetCard.mp q.property).1
  have huq : (u : A) ∉ (q : Finset A) := by
    intro hu
    exact nonUniversalVertex_not_mem_universalVertices G u.property (hqsub hu)
  simpa only [Finset.mk_mem_sym2_iff, not_and_or] using
    (Or.inl huq : (u : A) ∉ (q : Finset A) ∨ x ∉ (q : Finset A))

lemma fractionalEdgeLoad_d8HallZZZCorrection_nonUniversal
    (G : SimpleGraph A) (P : D8SeparatedParameters G)
    (e : Sym2 (↑(nonUniversalVertices G))) :
    fractionalEdgeLoad G (d8HallZZZCorrection G P)
        ((inducedEmbedding (nonUniversalVertices G)).sym2Map e) = 0 := by
  induction e using Sym2.inductionOn with
  | hf u v =>
      exact fractionalEdgeLoad_d8HallZZZCorrection_nonUniversal_left G P u v

lemma fractionalEdgeLoad_d8HallCorrection (G : SimpleGraph A)
    (P : D8SeparatedParameters G) (rho : ℝ) (p : Sym2 A) :
    fractionalEdgeLoad G (d8HallCorrection G P rho) p =
      fractionalEdgeLoad G (d8HallUUZCorrection G P rho) p +
        fractionalEdgeLoad G (d8HallUZZCorrection G P) p +
        fractionalEdgeLoad G (d8HallZZZCorrection G P) p := by
  unfold d8HallCorrection
  rw [fractionalEdgeLoad_add, fractionalEdgeLoad_add]

lemma fractionalEdgeLoad_d8HallCorrection_nonUniversal
    (G : SimpleGraph A) (P : D8SeparatedParameters G) (rho : ℝ)
    (e : Sym2 (↑(nonUniversalVertices G)))
    (he : e ∈ (G.induce
      (↑(nonUniversalVertices G) : Set A)).edgeFinset) :
    fractionalEdgeLoad G (d8HallCorrection G P rho)
        ((inducedEmbedding (nonUniversalVertices G)).sym2Map e) =
      ((universalVertices G).card : ℝ) * P.hallScale rho * P.beta e := by
  have heND : ¬e.IsDiag :=
    (G.induce (↑(nonUniversalVertices G) : Set A)).not_isDiag_of_mem_edgeFinset he
  rw [fractionalEdgeLoad_d8HallCorrection,
    fractionalEdgeLoad_d8HallUUZCorrection,
    fractionalEdgeLoad_d8UUZCorrection_induced G P e he,
    fractionalEdgeLoad_d8HallUZZCorrection_nonUniversal G P e heND,
    fractionalEdgeLoad_d8HallZZZCorrection_nonUniversal G P e]
  ring

lemma fractionalEdgeLoad_d8HallCorrection_mixed
    (G : SimpleGraph A) (P : D8SeparatedParameters G) (rho : ℝ)
    (u : ↑(nonUniversalVertices G)) (z : ↑(universalVertices G)) :
    fractionalEdgeLoad G (d8HallCorrection G P rho) s((u : A), (z : A)) =
      P.hallScale rho * P.betaIncident u +
        (((universalVertices G).card : ℝ) - 1) * P.alpha u := by
  rw [fractionalEdgeLoad_d8HallCorrection,
    fractionalEdgeLoad_d8HallUUZCorrection]
  have hUUZ := fractionalEdgeLoad_d8UUZCorrection_mixed G P z u
  rw [Sym2.eq_swap] at hUUZ
  rw [hUUZ, fractionalEdgeLoad_d8HallUZZCorrection_mixed G P u z,
    fractionalEdgeLoad_d8HallZZZCorrection_nonUniversal_left G P u z]
  ring

lemma fractionalEdgeLoad_d8HallCorrection_universal
    (G : SimpleGraph A) (P : D8SeparatedParameters G) (rho : ℝ)
    (e : Sym2 (↑(universalVertices G)))
    (he : e ∈ (⊤ : SimpleGraph (↑(universalVertices G))).edgeFinset) :
    fractionalEdgeLoad G (d8HallCorrection G P rho)
        ((inducedEmbedding (universalVertices G)).sym2Map e) =
      (∑ u : ↑(nonUniversalVertices G), P.alpha u) +
        (((universalVertices G).card : ℝ) - 2) * P.gamma := by
  have heND : ¬e.IsDiag :=
    (⊤ : SimpleGraph (↑(universalVertices G))).not_isDiag_of_mem_edgeFinset he
  rw [fractionalEdgeLoad_d8HallCorrection,
    fractionalEdgeLoad_d8HallUUZCorrection,
    fractionalEdgeLoad_d8UUZCorrection_universal G P e heND,
    fractionalEdgeLoad_d8HallUZZCorrection_induced G P e he,
    fractionalEdgeLoad_d8HallZZZCorrection_induced G P e heND]
  ring

/-! ### The final Hall-branch average and its uncovered-weight budget -/

/-- The final D8 Hall numerator, averaged over all vertex deletions and the
explicit correction by the usual factor `1 / (|V|-2)`. -/
def d8HallAverageWeight (G : SimpleGraph A)
    (z₀ : ↑(universalVertices G)) {a b : A} (hab : Gᶜ.Adj a b)
    (w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ)
    (P : D8SeparatedParameters G) (rho : ℝ)
    (w : ∀ u : ↑(nonUniversalVertices G),
      Finset (↑(d7DeletedFinset (u : A))) → ℝ) : Finset A → ℝ :=
  fun t ↦ (((Fintype.card A - 2 : ℕ) : ℝ)⁻¹) *
    ((∑ u : ↑(nonUniversalVertices G),
        d7LiftedWeight (u : A) (w u) t) +
      (∑ z : ↑(universalVertices G),
        d7LiftedWeight (z : A)
          (d8CoherentStrippedWeight G z₀ hab w₀ z) t) +
      d8HallCorrection G P rho t)

lemma fractionalEdgeLoad_d8HallAverageWeight
    (G : SimpleGraph A)
    (z₀ : ↑(universalVertices G)) {a b : A} (hab : Gᶜ.Adj a b)
    (w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ)
    (P : D8SeparatedParameters G) (rho : ℝ)
    (w : ∀ u : ↑(nonUniversalVertices G),
      Finset (↑(d7DeletedFinset (u : A))) → ℝ)
    (e : Sym2 A) :
    fractionalEdgeLoad G
        (d8HallAverageWeight G z₀ hab w₀ P rho w) e =
      (((Fintype.card A - 2 : ℕ) : ℝ)⁻¹) *
        ((∑ u : ↑(nonUniversalVertices G),
          fractionalEdgeLoad G (d7LiftedWeight (u : A) (w u)) e) +
        (∑ z : ↑(universalVertices G),
          fractionalEdgeLoad G
            (d7LiftedWeight (z : A)
              (d8CoherentStrippedWeight G z₀ hab w₀ z)) e) +
        fractionalEdgeLoad G (d8HallCorrection G P rho) e) := by
  unfold d8HallAverageWeight
  rw [fractionalEdgeLoad_smul, fractionalEdgeLoad_add,
    fractionalEdgeLoad_add, fractionalEdgeLoad_sum, fractionalEdgeLoad_sum]

lemma fractionalSize_d8HallAverageWeight
    (G : SimpleGraph A)
    (z₀ : ↑(universalVertices G)) {a b : A} (hab : Gᶜ.Adj a b)
    (w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ)
    (P : D8SeparatedParameters G) (rho : ℝ)
    (w : ∀ u : ↑(nonUniversalVertices G),
      Finset (↑(d7DeletedFinset (u : A))) → ℝ) :
    fractionalSize G (d8HallAverageWeight G z₀ hab w₀ P rho w) =
      (((Fintype.card A - 2 : ℕ) : ℝ)⁻¹) *
        ((∑ u : ↑(nonUniversalVertices G),
            fractionalSize (d7DeletedGraph G (u : A)) (w u)) +
          (∑ z : ↑(universalVertices G),
            fractionalSize (d7DeletedGraph G (z : A))
              (d8CoherentStrippedWeight G z₀ hab w₀ z)) +
          fractionalSize G (d8HallCorrection G P rho)) := by
  have hnonUniversal :
      (∑ t ∈ G.cliqueFinset 3,
        ∑ u : ↑(nonUniversalVertices G),
          d7LiftedWeight (u : A) (w u) t) =
        ∑ u : ↑(nonUniversalVertices G),
          fractionalSize (d7DeletedGraph G (u : A)) (w u) := by
    rw [Finset.sum_comm]
    apply Fintype.sum_congr
    intro u
    exact fractionalSize_extendInducedWeight G
      (d7DeletedFinset (u : A)) (w u)
  have huniversal :
      (∑ t ∈ G.cliqueFinset 3,
        ∑ z : ↑(universalVertices G),
          d7LiftedWeight (z : A)
            (d8CoherentStrippedWeight G z₀ hab w₀ z) t) =
        ∑ z : ↑(universalVertices G),
          fractionalSize (d7DeletedGraph G (z : A))
            (d8CoherentStrippedWeight G z₀ hab w₀ z) := by
    rw [Finset.sum_comm]
    apply Fintype.sum_congr
    intro z
    exact fractionalSize_extendInducedWeight G
      (d7DeletedFinset (z : A))
      (d8CoherentStrippedWeight G z₀ hab w₀ z)
  unfold fractionalSize d8HallAverageWeight
  rw [← Finset.mul_sum, Finset.sum_add_distrib,
    Finset.sum_add_distrib, hnonUniversal, huniversal]
  rfl

lemma fractionalUncoveredWeight_d8HallAverageWeight
    (G : SimpleGraph A)
    (z₀ : ↑(universalVertices G)) {a b : A} (hab : Gᶜ.Adj a b)
    (w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ)
    (P : D8SeparatedParameters G) (rho : ℝ)
    (w : ∀ u : ↑(nonUniversalVertices G),
      Finset (↑(d7DeletedFinset (u : A))) → ℝ)
    (hcard : 2 < Fintype.card A) :
    fractionalUncoveredWeight G
        (d8HallAverageWeight G z₀ hab w₀ P rho w) =
      (((Fintype.card A - 2 : ℕ) : ℝ)⁻¹) *
        ((∑ u : ↑(nonUniversalVertices G),
            fractionalUncoveredWeight
              (d7DeletedGraph G (u : A)) (w u)) +
          (∑ z : ↑(universalVertices G),
            fractionalUncoveredWeight (d7DeletedGraph G (z : A))
              (d8CoherentStrippedWeight G z₀ hab w₀ z)) -
          3 * fractionalSize G (d8HallCorrection G P rho)) := by
  let d : ℝ := ((Fintype.card A - 2 : ℕ) : ℝ)
  have hd : 0 < d := by
    dsimp only [d]
    exact_mod_cast (Nat.sub_pos_of_lt hcard)
  have hedge := sum_d7DeletedGraph_edgeSet_card G (by omega)
  have hedgeD :
      (∑ u : ↑(nonUniversalVertices G),
          (Nat.card (d7DeletedGraph G (u : A)).edgeSet : ℝ)) +
        (∑ z : ↑(universalVertices G),
          (Nat.card (d7DeletedGraph G (z : A)).edgeSet : ℝ)) =
        d * (Nat.card G.edgeSet : ℝ) := by
    simpa only [d] using hedge
  rw [fractionalUncoveredWeight_eq_card_sub_general,
    fractionalSize_d8HallAverageWeight]
  simp_rw [fractionalUncoveredWeight_eq_card_sub_general]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum]
  change (Nat.card G.edgeSet : ℝ) -
      3 * (d⁻¹ *
        ((∑ u : ↑(nonUniversalVertices G),
            fractionalSize (d7DeletedGraph G (u : A)) (w u)) +
          (∑ z : ↑(universalVertices G),
            fractionalSize (d7DeletedGraph G (z : A))
              (d8CoherentStrippedWeight G z₀ hab w₀ z)) +
          fractionalSize G (d8HallCorrection G P rho))) =
      d⁻¹ *
        (((∑ u : ↑(nonUniversalVertices G),
              (Nat.card (d7DeletedGraph G (u : A)).edgeSet : ℝ)) -
            3 * (∑ u : ↑(nonUniversalVertices G),
              fractionalSize (d7DeletedGraph G (u : A)) (w u))) +
          ((∑ z : ↑(universalVertices G),
              (Nat.card (d7DeletedGraph G (z : A)).edgeSet : ℝ)) -
            3 * (∑ z : ↑(universalVertices G),
              fractionalSize (d7DeletedGraph G (z : A))
                (d8CoherentStrippedWeight G z₀ hab w₀ z))) -
          3 * fractionalSize G (d8HallCorrection G P rho))
  field_simp [ne_of_gt hd]
  linarith [hedgeD]

lemma sum_d8HallRedistribution_outflow
    (G : SimpleGraph A) (P : D8SeparatedParameters G) {rho : ℝ}
    (sigma : A → ℕ) (R : D8HallRedistribution G P rho sigma)
    (hrho0 : 0 ≤ rho)
    (hrhoLe : rho ≤ ((universalVertices G).card : ℝ) * P.betaMass) :
    (∑ u : ↑(nonUniversalVertices G),
      ((∑ v : ↑(nonUniversalVertices G), R.betaFlow u v) +
        R.alphaFlow u)) =
      2 * ((universalVertices G).card : ℝ) * P.betaMass - 2 * rho +
        ((universalVertices G).card : ℝ) / 2 * P.alphaMass := by
  rw [Finset.sum_add_distrib, Finset.sum_comm]
  simp_rw [R.beta_source_sum]
  rw [R.alpha_sum]
  unfold d8HallBetaSource d8HallAlphaSource
  rw [← Finset.mul_sum, P.sum_betaIncident_eq_two_betaMass]
  have hratio := P.rhoRatio_mul_betaMass hrho0 hrhoLe
  ring_nf at hratio ⊢
  linarith

lemma fractionalUncoveredWeight_d8CoherentStrippedWeight
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G)) {a b : A}
    (hab : Gᶜ.Adj a b)
    (w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ)
    (P : D8SeparatedParameters G)
    (hreal : P.RealizesCoherentRemovedFamily G z₀ hab w₀)
    (z : ↑(universalVertices G)) :
    fractionalUncoveredWeight (d7DeletedGraph G (z : A))
        (d8CoherentStrippedWeight G z₀ hab w₀ z) =
      (∑ e ∈ (d7DeletedGraph G (z : A)).edgeFinset,
        d8CoherentOldResidual G z₀ hab w₀ z e) +
      (((universalVertices G).card : ℝ) - 1) *
          (((universalVertices G).card : ℝ) - 2) / 2 * P.gamma +
        P.alphaMass + P.betaMass := by
  rw [fractionalUncoveredWeight_eq_card_sub_general]
  have h := d8CoherentStrippedWeight_size_residual_identity
    G z₀ hab w₀ P hreal z
  linarith

lemma sum_fractionalUncoveredWeight_d8CoherentStrippedWeight_le
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G)) {a b : A}
    (hab : Gᶜ.Adj a b)
    {w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ}
    (P : D8SeparatedParameters G)
    (hreal : P.RealizesCoherentRemovedFamily G z₀ hab w₀)
    (hw₀ : IsFractionalPacking
      (d8AugmentedDeletedGraph G (z₀ : A) a b
        (d8MissingLeft_ne_universal G hab z₀)
        (d8MissingRight_ne_universal G hab z₀)) w₀)
    (hunc : fractionalUncoveredWeight
      (d8AugmentedDeletedGraph G (z₀ : A) a b
        (d8MissingLeft_ne_universal G hab z₀)
        (d8MissingRight_ne_universal G hab z₀)) w₀ ≤ 4) :
    (∑ z : ↑(universalVertices G),
      fractionalUncoveredWeight (d7DeletedGraph G (z : A))
        (d8CoherentStrippedWeight G z₀ hab w₀ z)) ≤
      ((universalVertices G).card : ℝ) *
        (4 + (((universalVertices G).card : ℝ) - 1) *
            (((universalVertices G).card : ℝ) - 2) / 2 * P.gamma +
          P.alphaMass + P.betaMass) := by
  simp_rw [fractionalUncoveredWeight_d8CoherentStrippedWeight
    G z₀ hab w₀ P hreal]
  calc
    _ ≤ ∑ _z : ↑(universalVertices G),
        (4 + (((universalVertices G).card : ℝ) - 1) *
            (((universalVertices G).card : ℝ) - 2) / 2 * P.gamma +
          P.alphaMass + P.betaMass) := by
      apply Finset.sum_le_sum
      intro z _
      have hz := sum_d8CoherentOldResidual_le_four
        G z₀ hab hw₀ hunc z
      linarith
    _ = _ := by
      simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
        Fintype.card_coe]

lemma fractionalUncoveredWeight_d8HallDeleted_eq
    (G : SimpleGraph A) (P : D8SeparatedParameters G) {rho : ℝ}
    (sigma : A → ℕ) (R : D8HallRedistribution G P rho sigma)
    (hm : 4 ≤ (universalVertices G).card)
    (hrho0 : 0 ≤ rho)
    (hrhoLe : rho ≤ ((universalVertices G).card : ℝ) * P.betaMass)
    (u : ↑(nonUniversalVertices G))
    (w : Finset (↑(d7DeletedFinset (u : A))) → ℝ)
    (hwTop : IsCapacityPacking
      (⊤ : SimpleGraph (↑(d7DeletedFinset (u : A))))
      (d8HallDeletedCapacity G P rho sigma R u) w) :
    fractionalUncoveredWeight (d7DeletedGraph G (u : A)) w =
      capacityUncoveredWeight
          (⊤ : SimpleGraph (↑(d7DeletedFinset (u : A))))
          (d8HallDeletedCapacity G P rho sigma R u) w +
        ∑ e ∈ (d7DeletedGraph G (u : A)).edgeFinset,
          d8HallDeduction G P rho sigma R u e := by
  letI : DecidableRel
      (⊤ : SimpleGraph (↑(d7DeletedFinset (u : A)))).Adj := Classical.decRel _
  let H := d7DeletedGraph G (u : A)
  let c := d8HallDeletedCapacity G P rho sigma R u
  have hcSupport : ∀ e, e ∉ H.edgeSet → c e = 0 := by
    intro e he
    exact d8HallDeletedCapacity_support G P rho sigma R u e (by
      simpa only [H, SimpleGraph.mem_edgeSet] using he)
  have hIndicatorPacking : IsCapacityPacking
      (⊤ : SimpleGraph (↑(d7DeletedFinset (u : A))))
      (fun e ↦ if e ∈ H.edgeFinset then 1 else 0) w := by
    refine ⟨hwTop.1, ?_⟩
    intro e heTop
    change fractionalEdgeLoad (⊤ : SimpleGraph _) w e ≤
      (if e ∈ H.edgeFinset then 1 else 0)
    by_cases heH : e ∈ H.edgeFinset
    · rw [if_pos heH]
      calc
        fractionalEdgeLoad (⊤ : SimpleGraph _) w e ≤ c e := hwTop.2 e heTop
        _ ≤ 1 := by
          dsimp only [c]
          rw [d8HallDeletedCapacity, if_pos heH]
          exact sub_le_self 1
            (d8HallDeduction_nonneg G P rho sigma R u e)
    · rw [if_neg heH]
      have hc0 : c e = 0 := hcSupport e (by
        simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using heH)
      exact (hwTop.2 e heTop).trans_eq hc0
  have hIndicatorSupport : ∀ e, e ∉ H.edgeSet →
      (if e ∈ H.edgeFinset then (1 : ℝ) else 0) = 0 := by
    intro e he
    rw [if_neg]
    simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using he
  have hindicator : fractionalUncoveredWeight H w =
      capacityUncoveredWeight (⊤ : SimpleGraph _)
        (fun e ↦ if e ∈ H.edgeFinset then 1 else 0) w := by
    calc
      fractionalUncoveredWeight H w =
          capacityUncoveredWeight (⊤ : SimpleGraph _)
            (fun e ↦ if e ∈ H.edgeFinset then 1 else 0)
            (zeroExtendTriangleWeight H w) :=
        (capacityUncoveredWeight_indicator_zeroExtend H w).symm
      _ = capacityUncoveredWeight (⊤ : SimpleGraph _)
            (fun e ↦ if e ∈ H.edgeFinset then 1 else 0) w :=
        capacityUncoveredWeight_zeroExtend_eq_of_capacity_support
          hIndicatorPacking hIndicatorSupport
  rw [show fractionalUncoveredWeight (d7DeletedGraph G (u : A)) w =
      capacityUncoveredWeight (⊤ : SimpleGraph _)
        (fun e ↦ if e ∈ H.edgeFinset then 1 else 0) w by
      simpa only [H] using hindicator]
  unfold capacityUncoveredWeight
  have hsub : H.edgeFinset ⊆
      (⊤ : SimpleGraph (↑(d7DeletedFinset (u : A)))).edgeFinset :=
    SimpleGraph.edgeFinset_mono le_top
  have hfilter : ((⊤ : SimpleGraph
      (↑(d7DeletedFinset (u : A)))).edgeFinset.filter
        (fun e ↦ e ∈ H.edgeFinset)) = H.edgeFinset := by
    ext e
    simp only [Finset.mem_filter]
    constructor
    · exact fun h ↦ h.2
    · exact fun h ↦ ⟨hsub h, h⟩
  calc
    (∑ e ∈ (⊤ : SimpleGraph (↑(d7DeletedFinset (u : A)))).edgeFinset,
        ((if e ∈ H.edgeFinset then 1 else 0) -
          fractionalEdgeLoad (⊤ : SimpleGraph _) w e)) =
      ∑ e ∈ (⊤ : SimpleGraph (↑(d7DeletedFinset (u : A)))).edgeFinset,
        ((c e - fractionalEdgeLoad (⊤ : SimpleGraph _) w e) +
          if e ∈ H.edgeFinset then
            d8HallDeduction G P rho sigma R u e else 0) := by
      apply Finset.sum_congr rfl
      intro e heTop
      by_cases heH : e ∈ H.edgeFinset
      · simp only [if_pos heH]
        dsimp only [c]
        rw [d8HallDeletedCapacity, if_pos heH]
        ring
      · simp only [if_neg heH]
        have hc0 : c e = 0 := hcSupport e (by
          simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using heH)
        rw [hc0]
        ring
    _ = (∑ e ∈ (⊤ : SimpleGraph
          (↑(d7DeletedFinset (u : A)))).edgeFinset,
          (c e - fractionalEdgeLoad (⊤ : SimpleGraph _) w e)) +
        ∑ e ∈ (⊤ : SimpleGraph
          (↑(d7DeletedFinset (u : A)))).edgeFinset,
          if e ∈ H.edgeFinset then
            d8HallDeduction G P rho sigma R u e else 0 := by
      rw [Finset.sum_add_distrib]
    _ = (∑ e ∈ (⊤ : SimpleGraph
          (↑(d7DeletedFinset (u : A)))).edgeFinset,
          (c e - fractionalEdgeLoad (⊤ : SimpleGraph _) w e)) +
        ∑ e ∈ H.edgeFinset,
          d8HallDeduction G P rho sigma R u e := by
      congr 1
      rw [← Finset.sum_filter, hfilter]

lemma fractionalUncoveredWeight_d8HallDeleted_le
    (G : SimpleGraph A) (P : D8SeparatedParameters G) {rho : ℝ}
    (sigma : A → ℕ) (R : D8HallRedistribution G P rho sigma)
    (hm : 4 ≤ (universalVertices G).card)
    (hrho0 : 0 ≤ rho)
    (hrhoLe : rho ≤ ((universalVertices G).card : ℝ) * P.betaMass)
    (hsigma : ∀ u, sigma u ≤ 4)
    (u : ↑(nonUniversalVertices G))
    (w : Finset (↑(d7DeletedFinset (u : A))) → ℝ)
    (hwTop : IsCapacityPacking
      (⊤ : SimpleGraph (↑(d7DeletedFinset (u : A))))
      (d8HallDeletedCapacity G P rho sigma R u) w)
    (hunc : capacityUncoveredWeight
      (⊤ : SimpleGraph (↑(d7DeletedFinset (u : A))))
      (d8HallDeletedCapacity G P rho sigma R u) w ≤
        ((4 - sigma u : ℕ) : ℝ)) :
    fractionalUncoveredWeight (d7DeletedGraph G (u : A)) w ≤
      (4 : ℝ) - sigma u +
        (∑ v : ↑(nonUniversalVertices G), R.betaFlow u v) +
        R.alphaFlow u := by
  rw [fractionalUncoveredWeight_d8HallDeleted_eq
    G P sigma R hm hrho0 hrhoLe u w hwTop]
  have hsum : (∑ e ∈ (d7DeletedGraph G (u : A)).edgeFinset,
      d8HallDeduction G P rho sigma R u e) ≤
      ∑ e ∈ (⊤ : SimpleGraph
        (↑(d7DeletedFinset (u : A)))).edgeFinset,
        d8HallDeduction G P rho sigma R u e := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact SimpleGraph.edgeFinset_mono le_top
    · intro e _heTop _heNot
      exact d8HallDeduction_nonneg G P rho sigma R u e
  rw [sum_d8HallDeduction G P sigma R hm hrho0 hrhoLe u] at hsum
  have hcast : (((4 - sigma u : ℕ) : ℝ)) =
      (4 : ℝ) - sigma u := by
    rw [Nat.cast_sub (hsigma u)]
    norm_num
  rw [hcast] at hunc
  linarith

lemma sum_fractionalUncoveredWeight_d8HallDeleted_le
    (G : SimpleGraph A) (P : D8SeparatedParameters G) {rho : ℝ}
    (sigma : A → ℕ) (R : D8HallRedistribution G P rho sigma)
    (hm : 4 ≤ (universalVertices G).card)
    (hrho0 : 0 ≤ rho)
    (hrhoLe : rho ≤ ((universalVertices G).card : ℝ) * P.betaMass)
    (hsigma : ∀ u, sigma u ≤ 4)
    (w : ∀ u : ↑(nonUniversalVertices G),
      Finset (↑(d7DeletedFinset (u : A))) → ℝ)
    (hwTop : ∀ u : ↑(nonUniversalVertices G), IsCapacityPacking
      (⊤ : SimpleGraph (↑(d7DeletedFinset (u : A))))
      (d8HallDeletedCapacity G P rho sigma R u) (w u))
    (hunc : ∀ u : ↑(nonUniversalVertices G), capacityUncoveredWeight
      (⊤ : SimpleGraph (↑(d7DeletedFinset (u : A))))
      (d8HallDeletedCapacity G P rho sigma R u) (w u) ≤
        ((4 - sigma u : ℕ) : ℝ)) :
    (∑ u : ↑(nonUniversalVertices G),
      fractionalUncoveredWeight (d7DeletedGraph G (u : A)) (w u)) ≤
      ((nonUniversalVertices G).card : ℝ) * 4 -
        ∑ u : ↑(nonUniversalVertices G), (sigma u : ℝ) +
        (2 * ((universalVertices G).card : ℝ) * P.betaMass - 2 * rho +
          ((universalVertices G).card : ℝ) / 2 * P.alphaMass) := by
  calc
    (∑ u : ↑(nonUniversalVertices G),
        fractionalUncoveredWeight (d7DeletedGraph G (u : A)) (w u)) ≤
      ∑ u : ↑(nonUniversalVertices G),
        ((4 : ℝ) - sigma u +
          (∑ v : ↑(nonUniversalVertices G), R.betaFlow u v) +
          R.alphaFlow u) := by
      apply Finset.sum_le_sum
      intro u _
      exact fractionalUncoveredWeight_d8HallDeleted_le
        G P sigma R hm hrho0 hrhoLe hsigma u (w u) (hwTop u) (hunc u)
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
        Finset.sum_sub_distrib]
      have hout := sum_d8HallRedistribution_outflow
        G P sigma R hrho0 hrhoLe
      rw [Finset.sum_add_distrib] at hout
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe,
        nsmul_eq_mul, mul_one]
      linarith

lemma fractionalUncoveredWeight_d8HallAverageWeight_le_four
    (G : SimpleGraph A)
    (z₀ : ↑(universalVertices G)) {a b : A} (hab : Gᶜ.Adj a b)
    {w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ}
    (P : D8SeparatedParameters G)
    (hreal : P.RealizesCoherentRemovedFamily G z₀ hab w₀)
    {rho : ℝ} (sigma : A → ℕ)
    (R : D8HallRedistribution G P rho sigma)
    (hm : 4 ≤ (universalVertices G).card)
    (hrho0 : 0 ≤ rho)
    (hrhoLe : rho ≤ ((universalVertices G).card : ℝ) * P.betaMass)
    (hsigma : ∀ u, sigma u ≤ 4)
    (hsigmaSum : 8 + rho ≤
      ∑ u ∈ nonUniversalVertices G, (sigma u : ℝ))
    (w : ∀ u : ↑(nonUniversalVertices G),
      Finset (↑(d7DeletedFinset (u : A))) → ℝ)
    (hwTop : ∀ u : ↑(nonUniversalVertices G), IsCapacityPacking
      (⊤ : SimpleGraph (↑(d7DeletedFinset (u : A))))
      (d8HallDeletedCapacity G P rho sigma R u) (w u))
    (hunc : ∀ u : ↑(nonUniversalVertices G), capacityUncoveredWeight
      (⊤ : SimpleGraph (↑(d7DeletedFinset (u : A))))
      (d8HallDeletedCapacity G P rho sigma R u) (w u) ≤
        ((4 - sigma u : ℕ) : ℝ))
    (hw₀ : IsFractionalPacking
      (d8AugmentedDeletedGraph G (z₀ : A) a b
        (d8MissingLeft_ne_universal G hab z₀)
        (d8MissingRight_ne_universal G hab z₀)) w₀)
    (hunc₀ : fractionalUncoveredWeight
      (d8AugmentedDeletedGraph G (z₀ : A) a b
        (d8MissingLeft_ne_universal G hab z₀)
        (d8MissingRight_ne_universal G hab z₀)) w₀ ≤ 4)
    (hcard : 2 < Fintype.card A) :
    fractionalUncoveredWeight G
      (d8HallAverageWeight G z₀ hab w₀ P rho w) ≤ 4 := by
  have hU := sum_fractionalUncoveredWeight_d8HallDeleted_le
    G P sigma R hm hrho0 hrhoLe hsigma w hwTop hunc
  have hZ := sum_fractionalUncoveredWeight_d8CoherentStrippedWeight_le
    G z₀ hab P hreal hw₀ hunc₀
  have hcorr := three_mul_fractionalSize_d8HallCorrection
    G P hm hrho0 hrhoLe
  have hparts := card_nonUniversalVertices_add_card_universalVertices G
  have hpartsR : ((nonUniversalVertices G).card : ℝ) +
      ((universalVertices G).card : ℝ) = (Fintype.card A : ℝ) := by
    exact_mod_cast hparts
  have hsigmaSubtype :
      (∑ u : ↑(nonUniversalVertices G), (sigma u : ℝ)) =
        ∑ u ∈ nonUniversalVertices G, (sigma u : ℝ) := by
    exact (Finset.sum_subtype (nonUniversalVertices G)
      (fun _ ↦ Iff.rfl) (fun u ↦ (sigma u : ℝ))).symm
  have hnum :
      ((∑ u : ↑(nonUniversalVertices G),
          fractionalUncoveredWeight (d7DeletedGraph G (u : A)) (w u)) +
        (∑ z : ↑(universalVertices G),
          fractionalUncoveredWeight (d7DeletedGraph G (z : A))
            (d8CoherentStrippedWeight G z₀ hab w₀ z)) -
        3 * fractionalSize G (d8HallCorrection G P rho)) ≤
      (((Fintype.card A - 2 : ℕ) : ℝ) * 4) := by
    rw [hcorr]
    have hcard2 : 2 ≤ Fintype.card A := by omega
    rw [Nat.cast_sub hcard2, Nat.cast_ofNat]
    rw [hsigmaSubtype] at hU
    nlinarith
  rw [fractionalUncoveredWeight_d8HallAverageWeight
    G z₀ hab w₀ P rho w hcard]
  let d : ℝ := ((Fintype.card A - 2 : ℕ) : ℝ)
  have hd : 0 < d := by
    dsimp only [d]
    exact_mod_cast (Nat.sub_pos_of_lt hcard)
  calc
    d⁻¹ *
        ((∑ u : ↑(nonUniversalVertices G),
            fractionalUncoveredWeight (d7DeletedGraph G (u : A)) (w u)) +
          (∑ z : ↑(universalVertices G),
            fractionalUncoveredWeight (d7DeletedGraph G (z : A))
              (d8CoherentStrippedWeight G z₀ hab w₀ z)) -
          3 * fractionalSize G (d8HallCorrection G P rho)) ≤
      d⁻¹ * (d * 4) :=
        mul_le_mul_of_nonneg_left (by simpa only [d] using hnum)
          (inv_nonneg.mpr hd.le)
    _ = 4 := by field_simp [ne_of_gt hd]

/-! ### Edge-load feasibility of the Hall average -/

private lemma d8HallLiftedWeight_nonUniversal_le
    (G : SimpleGraph A) (P : D8SeparatedParameters G) {rho : ℝ}
    (sigma : A → ℕ) (R : D8HallRedistribution G P rho sigma)
    (w : ∀ u : ↑(nonUniversalVertices G),
      Finset (↑(d7DeletedFinset (u : A))) → ℝ)
    (hw : ∀ u : ↑(nonUniversalVertices G),
      IsCapacityPacking (d7DeletedGraph G (u : A))
        (d8HallDeletedCapacity G P rho sigma R u) (w u))
    (d v x : ↑(nonUniversalVertices G)) (hvx : v ≠ x)
    (he : s(v, x) ∈ (G.induce
      (↑(nonUniversalVertices G) : Set A)).edgeFinset) :
    fractionalEdgeLoad G (d7LiftedWeight (d : A) (w d))
        s((v : A), (x : A)) ≤
      if d = v ∨ d = x then 0 else 1 := by
  by_cases hd : d = v ∨ d = x
  · rw [if_pos hd]
    rcases hd with hdv | hdx
    · subst d
      exact le_of_eq (fractionalEdgeLoad_d7LiftedWeight_eq_zero_of_endpoint
        G (v : A) (x : A) (w v))
    · subst d
      simpa only [Sym2.eq_swap] using le_of_eq
        (fractionalEdgeLoad_d7LiftedWeight_eq_zero_of_endpoint
          G (x : A) (v : A) (w x))
  · rw [if_neg hd]
    have hvd : (v : A) ≠ (d : A) := by
      intro h
      exact hd (Or.inl (Subtype.ext h.symm))
    have hxd : (x : A) ≠ (d : A) := by
      intro h
      exact hd (Or.inr (Subtype.ext h.symm))
    rw [fractionalEdgeLoad_d7LiftedWeight_of_ne G (d : A)
      (v : A) (x : A) (w d) hvd hxd]
    have heDel : s(d7DeletedVertex (d : A) (v : A) hvd,
        d7DeletedVertex (d : A) (x : A) hxd) ∈
        (d7DeletedGraph G (d : A)).edgeFinset := by
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
      change G.Adj (v : A) (x : A)
      exact SimpleGraph.mem_edgeFinset.mp he
    calc
      fractionalEdgeLoad (d7DeletedGraph G (d : A)) (w d) _ ≤
          d8HallDeletedCapacity G P rho sigma R d _ := (hw d).2 _ heDel
      _ ≤ 1 := by
        rw [d8HallDeletedCapacity, if_pos heDel]
        exact sub_le_self 1 (d8HallDeduction_nonneg G P rho sigma R d _)

lemma sum_d8HallLiftedWeight_nonUniversal_le
    (G : SimpleGraph A) (P : D8SeparatedParameters G) {rho : ℝ}
    (sigma : A → ℕ) (R : D8HallRedistribution G P rho sigma)
    (w : ∀ u : ↑(nonUniversalVertices G),
      Finset (↑(d7DeletedFinset (u : A))) → ℝ)
    (hw : ∀ u : ↑(nonUniversalVertices G),
      IsCapacityPacking (d7DeletedGraph G (u : A))
        (d8HallDeletedCapacity G P rho sigma R u) (w u))
    (v x : ↑(nonUniversalVertices G)) (hvx : v ≠ x)
    (he : s(v, x) ∈ (G.induce
      (↑(nonUniversalVertices G) : Set A)).edgeFinset) :
    (∑ d : ↑(nonUniversalVertices G),
      fractionalEdgeLoad G (d7LiftedWeight (d : A) (w d))
        s((v : A), (x : A))) ≤
      ((nonUniversalVertices G).card : ℝ) - 2 := by
  calc
    _ ≤ ∑ d : ↑(nonUniversalVertices G),
        if d = v ∨ d = x then 0 else 1 := by
      apply Finset.sum_le_sum
      intro d _
      exact d8HallLiftedWeight_nonUniversal_le
        G P sigma R w hw d v x hvx he
    _ = ((nonUniversalVertices G).card : ℝ) - 2 := by
      rw [sum_ite_eq_zero_else_two v x hvx]
      simp only [Fintype.card_coe]
      ring

private lemma d8HallLiftedWeight_mixed_le
    (G : SimpleGraph A) (P : D8SeparatedParameters G) {rho : ℝ}
    (sigma : A → ℕ) (R : D8HallRedistribution G P rho sigma)
    (w : ∀ u : ↑(nonUniversalVertices G),
      Finset (↑(d7DeletedFinset (u : A))) → ℝ)
    (hw : ∀ u : ↑(nonUniversalVertices G),
      IsCapacityPacking (d7DeletedGraph G (u : A))
        (d8HallDeletedCapacity G P rho sigma R u) (w u))
    (d v : ↑(nonUniversalVertices G)) (z : ↑(universalVertices G)) :
    fractionalEdgeLoad G (d7LiftedWeight (d : A) (w d))
        s((v : A), (z : A)) ≤
      if d = v then 0 else
        1 - R.betaFlow d v / ((universalVertices G).card : ℝ) := by
  by_cases hd : d = v
  · subst d
    rw [if_pos rfl]
    exact le_of_eq (fractionalEdgeLoad_d7LiftedWeight_eq_zero_of_endpoint
      G (v : A) (z : A) (w v))
  · rw [if_neg hd]
    have hvd : (v : A) ≠ (d : A) := by
      intro h
      exact hd (Subtype.ext h.symm)
    have hzd : (z : A) ≠ (d : A) := by
      intro h
      exact nonUniversalVertex_not_mem_universalVertices G d.property
        (h ▸ z.property)
    rw [fractionalEdgeLoad_d7LiftedWeight_of_ne G (d : A)
      (v : A) (z : A) (w d) hvd hzd]
    let e : Sym2 (↑(d7DeletedFinset (d : A))) :=
      s(d7DeletedVertex (d : A) (v : A) hvd,
        d7DeletedVertex (d : A) (z : A) hzd)
    have he : e ∈ (d7DeletedGraph G (d : A)).edgeFinset := by
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
      change G.Adj (v : A) (z : A)
      exact (adj_of_mem_universalVertices G z.property (by
        intro h
        exact nonUniversalVertex_not_mem_universalVertices G v.property
          (h ▸ z.property))).symm
    calc
      fractionalEdgeLoad (d7DeletedGraph G (d : A)) (w d) e ≤
          d8HallDeletedCapacity G P rho sigma R d e := (hw d).2 e he
      _ = 1 - R.betaFlow d v /
          ((universalVertices G).card : ℝ) := by
        rw [d8HallDeletedCapacity, if_pos he]
        unfold d8HallDeduction
        simp only [e, Sym2.lift_mk]
        have hvNZ : (d7DeletedVertex (d : A) (v : A) hvd : A) ∉
            universalVertices G := by
          simpa using nonUniversalVertex_not_mem_universalVertices G v.property
        have hzZ : (d7DeletedVertex (d : A) (z : A) hzd : A) ∈
            universalVertices G := by simpa using z.property
        rw [dif_neg hvNZ, dif_pos hzZ]
        congr 2

lemma sum_d8HallLiftedWeight_mixed_le
    (G : SimpleGraph A) (P : D8SeparatedParameters G) {rho : ℝ}
    (sigma : A → ℕ) (R : D8HallRedistribution G P rho sigma)
    (w : ∀ u : ↑(nonUniversalVertices G),
      Finset (↑(d7DeletedFinset (u : A))) → ℝ)
    (hw : ∀ u : ↑(nonUniversalVertices G),
      IsCapacityPacking (d7DeletedGraph G (u : A))
        (d8HallDeletedCapacity G P rho sigma R u) (w u))
    (v : ↑(nonUniversalVertices G)) (z : ↑(universalVertices G)) :
    (∑ d : ↑(nonUniversalVertices G),
      fractionalEdgeLoad G (d7LiftedWeight (d : A) (w d))
        s((v : A), (z : A))) ≤
      ((nonUniversalVertices G).card : ℝ) - 1 -
        P.hallScale rho * P.betaIncident v := by
  have hmR : ((universalVertices G).card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_ne_zero.mpr ⟨( z : A), z.property⟩)
  calc
    _ ≤ ∑ d : ↑(nonUniversalVertices G),
        if d = v then 0 else
          1 - R.betaFlow d v /
            ((universalVertices G).card : ℝ) := by
      apply Finset.sum_le_sum
      intro d _
      exact d8HallLiftedWeight_mixed_le G P sigma R w hw d v z
    _ = ((nonUniversalVertices G).card : ℝ) - 1 -
          P.hallScale rho * P.betaIncident v := by
      have hpoint : ∀ d : ↑(nonUniversalVertices G),
          (if d = v then 0 else
            1 - R.betaFlow d v /
              ((universalVertices G).card : ℝ)) =
          (if d = v then 0 else 1) -
            R.betaFlow d v / ((universalVertices G).card : ℝ) := by
        intro d
        by_cases hd : d = v
        · subst d
          simp [R.diagonal_zero]
        · simp [hd]
      simp_rw [hpoint]
      rw [Finset.sum_sub_distrib, sum_ite_eq_zero_else,
        ← Finset.sum_div, R.beta_source_sum]
      unfold d8HallBetaSource D8SeparatedParameters.hallScale
      simp only [Fintype.card_coe]
      field_simp [hmR]

private lemma d8HallLiftedWeight_universal_le
    (G : SimpleGraph A) (P : D8SeparatedParameters G) {rho : ℝ}
    (sigma : A → ℕ) (R : D8HallRedistribution G P rho sigma)
    (w : ∀ u : ↑(nonUniversalVertices G),
      Finset (↑(d7DeletedFinset (u : A))) → ℝ)
    (hw : ∀ u : ↑(nonUniversalVertices G),
      IsCapacityPacking (d7DeletedGraph G (u : A))
        (d8HallDeletedCapacity G P rho sigma R u) (w u))
    (d : ↑(nonUniversalVertices G))
    (x y : ↑(universalVertices G)) (hxy : x ≠ y) :
    fractionalEdgeLoad G (d7LiftedWeight (d : A) (w d))
        s((x : A), (y : A)) ≤
      1 - R.alphaFlow d /
        (((universalVertices G).card.choose 2 : ℕ) : ℝ) := by
  have hxd : (x : A) ≠ (d : A) := by
    intro h
    exact nonUniversalVertex_not_mem_universalVertices G d.property
      (h ▸ x.property)
  have hyd : (y : A) ≠ (d : A) := by
    intro h
    exact nonUniversalVertex_not_mem_universalVertices G d.property
      (h ▸ y.property)
  rw [fractionalEdgeLoad_d7LiftedWeight_of_ne G (d : A)
    (x : A) (y : A) (w d) hxd hyd]
  let e : Sym2 (↑(d7DeletedFinset (d : A))) :=
    s(d7DeletedVertex (d : A) (x : A) hxd,
      d7DeletedVertex (d : A) (y : A) hyd)
  have he : e ∈ (d7DeletedGraph G (d : A)).edgeFinset := by
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    change G.Adj (x : A) (y : A)
    exact adj_of_mem_universalVertices G x.property
      (fun h ↦ hxy (Subtype.ext h))
  calc
    fractionalEdgeLoad (d7DeletedGraph G (d : A)) (w d) e ≤
        d8HallDeletedCapacity G P rho sigma R d e := (hw d).2 e he
    _ = 1 - R.alphaFlow d /
        (((universalVertices G).card.choose 2 : ℕ) : ℝ) := by
      rw [d8HallDeletedCapacity, if_pos he]
      unfold d8HallDeduction
      simp only [e, Sym2.lift_mk]
      have hxZ : (d7DeletedVertex (d : A) (x : A) hxd : A) ∈
          universalVertices G := by simpa using x.property
      have hyZ : (d7DeletedVertex (d : A) (y : A) hyd : A) ∈
          universalVertices G := by simpa using y.property
      rw [dif_pos hxZ, dif_pos hyZ]

lemma sum_d8HallLiftedWeight_universal_le
    (G : SimpleGraph A) (P : D8SeparatedParameters G) {rho : ℝ}
    (sigma : A → ℕ) (R : D8HallRedistribution G P rho sigma)
    (hm : 4 ≤ (universalVertices G).card)
    (w : ∀ u : ↑(nonUniversalVertices G),
      Finset (↑(d7DeletedFinset (u : A))) → ℝ)
    (hw : ∀ u : ↑(nonUniversalVertices G),
      IsCapacityPacking (d7DeletedGraph G (u : A))
        (d8HallDeletedCapacity G P rho sigma R u) (w u))
    (x y : ↑(universalVertices G)) (hxy : x ≠ y) :
    (∑ d : ↑(nonUniversalVertices G),
      fractionalEdgeLoad G (d7LiftedWeight (d : A) (w d))
        s((x : A), (y : A))) ≤
      ((nonUniversalVertices G).card : ℝ) -
        ∑ u : ↑(nonUniversalVertices G), P.alpha u := by
  have hchooseR :
      (((universalVertices G).card.choose 2 : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt
      (Nat.choose_pos (by omega : 2 ≤ (universalVertices G).card)))
  calc
    _ ≤ ∑ d : ↑(nonUniversalVertices G),
        (1 - R.alphaFlow d /
          (((universalVertices G).card.choose 2 : ℕ) : ℝ)) := by
      apply Finset.sum_le_sum
      intro d _
      exact d8HallLiftedWeight_universal_le G P sigma R w hw d x y hxy
    _ = ((nonUniversalVertices G).card : ℝ) -
          ∑ u : ↑(nonUniversalVertices G), P.alpha u := by
      rw [Finset.sum_sub_distrib]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe,
        nsmul_eq_mul, mul_one, ← Finset.sum_div, R.alpha_sum]
      unfold d8HallAlphaSource D8SeparatedParameters.alphaMass
      rw [Nat.cast_choose_two]
      have hmR : ((universalVertices G).card : ℝ) ≠ 0 := by positivity
      have hm1R : ((universalVertices G).card : ℝ) - 1 ≠ 0 := by
        have : (1 : ℝ) < ((universalVertices G).card : ℝ) := by
          exact_mod_cast (by omega : 1 < (universalVertices G).card)
        linarith
      field_simp [hmR, hm1R]

lemma d8HallCorrection_numerator_nonUniversal_le
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G)) {a b : A}
    (hab : Gᶜ.Adj a b)
    (w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ)
    (P : D8SeparatedParameters G)
    (hreal : P.RealizesCoherentRemovedFamily G z₀ hab w₀)
    (hw₀ : IsFractionalPacking
      (d8AugmentedDeletedGraph G (z₀ : A) a b
        (d8MissingLeft_ne_universal G hab z₀)
        (d8MissingRight_ne_universal G hab z₀)) w₀)
    {rho : ℝ} (hrho0 : 0 ≤ rho)
    (e : Sym2 (↑(nonUniversalVertices G)))
    (he : e ∈ (G.induce
      (↑(nonUniversalVertices G) : Set A)).edgeFinset) :
    (∑ z : ↑(universalVertices G),
        fractionalEdgeLoad G
          (d7LiftedWeight (z : A)
            (d8CoherentStrippedWeight G z₀ hab w₀ z))
          ((inducedEmbedding (nonUniversalVertices G)).sym2Map e)) +
        fractionalEdgeLoad G (d8HallCorrection G P rho)
          ((inducedEmbedding (nonUniversalVertices G)).sym2Map e) ≤
      ((universalVertices G).card : ℝ) := by
  have hshort := d8ShortcutCorrection_numerator_nonUniversal
    G z₀ hab w₀ P hreal e he
  have hhall := fractionalEdgeLoad_d8HallCorrection_nonUniversal
    G P rho e he
  have hshortcut := fractionalEdgeLoad_d8ShortcutCorrection_nonUniversal
    G P e he
  have hscale1 := P.hallScale_le_one hrho0
  have hbeta0 := P.beta_nonneg e he
  have hm0 : 0 ≤ ((universalVertices G).card : ℝ) := Nat.cast_nonneg _
  have hcorrLe :
      ((universalVertices G).card : ℝ) * P.hallScale rho * P.beta e ≤
        ((universalVertices G).card : ℝ) * P.beta e := by
    nlinarith [mul_nonneg hm0 hbeta0,
      mul_le_mul_of_nonneg_right hscale1 hbeta0]
  have hres : 0 ≤ ∑ z : ↑(universalVertices G),
      d8CoherentOldResidual G z₀ hab w₀ z
        ((d7NonUniversalDeletedEmbedding G z).sym2Map e) := by
    exact Finset.sum_nonneg fun z _ ↦
      d8CoherentOldResidual_nonneg G z₀ hab hw₀ z
        (d7NonUniversalDeletedEdge_mem G z e he)
  rw [hshortcut] at hshort
  rw [hhall]
  linarith

lemma d8HallCorrection_numerator_mixed_le
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G)) {a b : A}
    (hab : Gᶜ.Adj a b)
    (w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ)
    (P : D8SeparatedParameters G)
    (hreal : P.RealizesCoherentRemovedFamily G z₀ hab w₀)
    (hw₀ : IsFractionalPacking
      (d8AugmentedDeletedGraph G (z₀ : A) a b
        (d8MissingLeft_ne_universal G hab z₀)
        (d8MissingRight_ne_universal G hab z₀)) w₀)
    (hm : 4 ≤ (universalVertices G).card)
    {rho : ℝ} (hrho0 : 0 ≤ rho)
    (u : ↑(nonUniversalVertices G)) (y : ↑(universalVertices G)) :
    (∑ z : ↑(universalVertices G),
        fractionalEdgeLoad G
          (d7LiftedWeight (z : A)
            (d8CoherentStrippedWeight G z₀ hab w₀ z))
          s((u : A), (y : A))) +
        fractionalEdgeLoad G (d8HallCorrection G P rho)
          s((u : A), (y : A)) ≤
      ((universalVertices G).card : ℝ) - 1 +
        P.hallScale rho * P.betaIncident u := by
  have hshort := d8ShortcutCorrection_numerator_mixed
    G z₀ hab w₀ P hreal hm u y
  have hhall := fractionalEdgeLoad_d8HallCorrection_mixed G P rho u y
  have hshortcut := fractionalEdgeLoad_d8ShortcutCorrection_mixed G P hm u y
  have hrem : 0 ≤ ∑ z : ↑(universalVertices G),
      d8MixedOldResidual G z₀ hab w₀ u y z := by
    apply Finset.sum_nonneg
    intro z _
    unfold d8MixedOldResidual
    split
    · exact le_rfl
    · rename_i hzy
      have hyz : (y : A) ≠ (z : A) := by
        intro h
        exact hzy (Subtype.ext h.symm)
      exact d8CoherentOldResidual_nonneg G z₀ hab hw₀ z
        (d7MixedDeletedEdge_mem G z y hyz u)
  rw [hshortcut] at hshort
  rw [hhall]
  linarith

lemma d8HallCorrection_numerator_universal_le
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G)) {a b : A}
    (hab : Gᶜ.Adj a b)
    (w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ)
    (P : D8SeparatedParameters G)
    (hreal : P.RealizesCoherentRemovedFamily G z₀ hab w₀)
    (hw₀ : IsFractionalPacking
      (d8AugmentedDeletedGraph G (z₀ : A) a b
        (d8MissingLeft_ne_universal G hab z₀)
        (d8MissingRight_ne_universal G hab z₀)) w₀)
    (hm : 4 ≤ (universalVertices G).card)
    (rho : ℝ) (x y : ↑(universalVertices G)) (hxy : x ≠ y) :
    (∑ z : ↑(universalVertices G),
        fractionalEdgeLoad G
          (d7LiftedWeight (z : A)
            (d8CoherentStrippedWeight G z₀ hab w₀ z))
          s((x : A), (y : A))) +
        fractionalEdgeLoad G (d8HallCorrection G P rho)
          s((x : A), (y : A)) ≤
      ((universalVertices G).card : ℝ) - 2 +
        ∑ u : ↑(nonUniversalVertices G), P.alpha u := by
  have hshort := d8ShortcutCorrection_numerator_universal
    G z₀ hab w₀ P hreal hm x y hxy
  let e : Sym2 (↑(universalVertices G)) := s(x, y)
  have he : e ∈ (⊤ : SimpleGraph
      (↑(universalVertices G))).edgeFinset := by
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    exact hxy
  have hhall := fractionalEdgeLoad_d8HallCorrection_universal G P rho e he
  have hshortcut := fractionalEdgeLoad_d8ShortcutCorrection_universal_simplified
    G P hm e he
  have hrem : 0 ≤ ∑ z : ↑(universalVertices G),
      d8UniversalOldResidual G z₀ hab w₀ x y z := by
    apply Finset.sum_nonneg
    intro z _
    unfold d8UniversalOldResidual
    split
    · exact le_rfl
    · rename_i hz
      have hxz : (x : A) ≠ (z : A) := by
        intro h
        exact hz (Or.inl (Subtype.ext h.symm))
      have hyz : (y : A) ≠ (z : A) := by
        intro h
        exact hz (Or.inr (Subtype.ext h.symm))
      have hxyA : (x : A) ≠ (y : A) := fun h ↦ hxy (Subtype.ext h)
      exact d8CoherentOldResidual_nonneg G z₀ hab hw₀ z
        (d7UniversalDeletedEdge_mem G z x y hxz hyz hxyA)
  change fractionalEdgeLoad G (d8HallCorrection G P rho)
      s((x : A), (y : A)) =
        (∑ u : ↑(nonUniversalVertices G), P.alpha u) +
          (((universalVertices G).card : ℝ) - 2) * P.gamma at hhall
  change fractionalEdgeLoad G (d8ShortcutCorrection G P)
      s((x : A), (y : A)) =
        2 + (((universalVertices G).card : ℝ) - 2) * P.gamma at hshortcut
  rw [hshortcut] at hshort
  rw [hhall]
  linarith

private lemma d8HallAverageWeight_edgeLoad_le_one_of_numerator
    (G : SimpleGraph A)
    (z₀ : ↑(universalVertices G)) {a b : A} (hab : Gᶜ.Adj a b)
    (w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ)
    (P : D8SeparatedParameters G) (rho : ℝ)
    (w : ∀ u : ↑(nonUniversalVertices G),
      Finset (↑(d7DeletedFinset (u : A))) → ℝ)
    (hn : 2 < Fintype.card A) (e : Sym2 A)
    (hnum :
      (∑ u : ↑(nonUniversalVertices G),
          fractionalEdgeLoad G (d7LiftedWeight (u : A) (w u)) e) +
        (∑ z : ↑(universalVertices G),
          fractionalEdgeLoad G
            (d7LiftedWeight (z : A)
              (d8CoherentStrippedWeight G z₀ hab w₀ z)) e) +
        fractionalEdgeLoad G (d8HallCorrection G P rho) e ≤
          ((Fintype.card A - 2 : ℕ) : ℝ)) :
    fractionalEdgeLoad G
      (d8HallAverageWeight G z₀ hab w₀ P rho w) e ≤ 1 := by
  rw [fractionalEdgeLoad_d8HallAverageWeight]
  let d : ℝ := ((Fintype.card A - 2 : ℕ) : ℝ)
  have hd : 0 < d := by
    dsimp only [d]
    exact_mod_cast Nat.sub_pos_of_lt hn
  calc
    d⁻¹ *
        ((∑ u : ↑(nonUniversalVertices G),
            fractionalEdgeLoad G (d7LiftedWeight (u : A) (w u)) e) +
          (∑ z : ↑(universalVertices G),
            fractionalEdgeLoad G
              (d7LiftedWeight (z : A)
                (d8CoherentStrippedWeight G z₀ hab w₀ z)) e) +
          fractionalEdgeLoad G (d8HallCorrection G P rho) e) ≤
      d⁻¹ * d := mul_le_mul_of_nonneg_left
        (by simpa only [d] using hnum) (inv_nonneg.mpr hd.le)
    _ = 1 := by field_simp [ne_of_gt hd]

lemma d8HallAverageWeight_numerator_nonUniversal_le
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G)) {a b : A}
    (hab : Gᶜ.Adj a b)
    (w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ)
    (P : D8SeparatedParameters G)
    (hreal : P.RealizesCoherentRemovedFamily G z₀ hab w₀)
    (hw₀ : IsFractionalPacking
      (d8AugmentedDeletedGraph G (z₀ : A) a b
        (d8MissingLeft_ne_universal G hab z₀)
        (d8MissingRight_ne_universal G hab z₀)) w₀)
    {rho : ℝ} (hrho0 : 0 ≤ rho)
    (sigma : A → ℕ) (R : D8HallRedistribution G P rho sigma)
    (w : ∀ u : ↑(nonUniversalVertices G),
      Finset (↑(d7DeletedFinset (u : A))) → ℝ)
    (hw : ∀ u : ↑(nonUniversalVertices G),
      IsCapacityPacking (d7DeletedGraph G (u : A))
        (d8HallDeletedCapacity G P rho sigma R u) (w u))
    (v x : ↑(nonUniversalVertices G)) (hvx : v ≠ x)
    (he : s(v, x) ∈ (G.induce
      (↑(nonUniversalVertices G) : Set A)).edgeFinset) :
    (∑ u : ↑(nonUniversalVertices G),
        fractionalEdgeLoad G (d7LiftedWeight (u : A) (w u))
          s((v : A), (x : A))) +
      (∑ z : ↑(universalVertices G),
        fractionalEdgeLoad G
          (d7LiftedWeight (z : A)
            (d8CoherentStrippedWeight G z₀ hab w₀ z))
          s((v : A), (x : A))) +
      fractionalEdgeLoad G (d8HallCorrection G P rho)
        s((v : A), (x : A)) ≤
      ((Fintype.card A - 2 : ℕ) : ℝ) := by
  have hU := sum_d8HallLiftedWeight_nonUniversal_le
    G P sigma R w hw v x hvx he
  let e : Sym2 (↑(nonUniversalVertices G)) := s(v, x)
  have hZ := d8HallCorrection_numerator_nonUniversal_le
    G z₀ hab w₀ P hreal hw₀ hrho0 e (by simpa only [e] using he)
  change (∑ z : ↑(universalVertices G),
      fractionalEdgeLoad G
        (d7LiftedWeight (z : A)
          (d8CoherentStrippedWeight G z₀ hab w₀ z))
        s((v : A), (x : A))) +
      fractionalEdgeLoad G (d8HallCorrection G P rho)
        s((v : A), (x : A)) ≤
        ((universalVertices G).card : ℝ) at hZ
  have hparts := card_nonUniversalVertices_add_card_universalVertices G
  have hU2 : 2 ≤ (nonUniversalVertices G).card := by
    have hpair : ({v, x} : Finset (↑(nonUniversalVertices G))).card = 2 := by
      simp [hvx]
    have hle := Finset.card_le_card
      (Finset.subset_univ ({v, x} : Finset (↑(nonUniversalVertices G))))
    simpa only [hpair, Finset.card_univ, Fintype.card_coe] using hle
  have hA2 : 2 ≤ Fintype.card A := by omega
  have hpartsR : ((nonUniversalVertices G).card : ℝ) +
      ((universalVertices G).card : ℝ) = (Fintype.card A : ℝ) := by
    exact_mod_cast hparts
  rw [Nat.cast_sub hA2, Nat.cast_ofNat]
  linarith

lemma d8HallAverageWeight_numerator_mixed_le
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G)) {a b : A}
    (hab : Gᶜ.Adj a b)
    (w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ)
    (P : D8SeparatedParameters G)
    (hreal : P.RealizesCoherentRemovedFamily G z₀ hab w₀)
    (hw₀ : IsFractionalPacking
      (d8AugmentedDeletedGraph G (z₀ : A) a b
        (d8MissingLeft_ne_universal G hab z₀)
        (d8MissingRight_ne_universal G hab z₀)) w₀)
    (hm : 4 ≤ (universalVertices G).card)
    {rho : ℝ} (hrho0 : 0 ≤ rho)
    (sigma : A → ℕ) (R : D8HallRedistribution G P rho sigma)
    (w : ∀ u : ↑(nonUniversalVertices G),
      Finset (↑(d7DeletedFinset (u : A))) → ℝ)
    (hw : ∀ u : ↑(nonUniversalVertices G),
      IsCapacityPacking (d7DeletedGraph G (u : A))
        (d8HallDeletedCapacity G P rho sigma R u) (w u))
    (v : ↑(nonUniversalVertices G)) (z : ↑(universalVertices G)) :
    (∑ u : ↑(nonUniversalVertices G),
        fractionalEdgeLoad G (d7LiftedWeight (u : A) (w u))
          s((v : A), (z : A))) +
      (∑ y : ↑(universalVertices G),
        fractionalEdgeLoad G
          (d7LiftedWeight (y : A)
            (d8CoherentStrippedWeight G z₀ hab w₀ y))
          s((v : A), (z : A))) +
      fractionalEdgeLoad G (d8HallCorrection G P rho)
        s((v : A), (z : A)) ≤
      ((Fintype.card A - 2 : ℕ) : ℝ) := by
  have hU := sum_d8HallLiftedWeight_mixed_le
    G P sigma R w hw v z
  have hZ := d8HallCorrection_numerator_mixed_le
    G z₀ hab w₀ P hreal hw₀ hm hrho0 v z
  have hparts := card_nonUniversalVertices_add_card_universalVertices G
  have hA2 : 2 ≤ Fintype.card A := by omega
  have hpartsR : ((nonUniversalVertices G).card : ℝ) +
      ((universalVertices G).card : ℝ) = (Fintype.card A : ℝ) := by
    exact_mod_cast hparts
  rw [Nat.cast_sub hA2, Nat.cast_ofNat]
  linarith

lemma d8HallAverageWeight_numerator_universal_le
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G)) {a b : A}
    (hab : Gᶜ.Adj a b)
    (w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ)
    (P : D8SeparatedParameters G)
    (hreal : P.RealizesCoherentRemovedFamily G z₀ hab w₀)
    (hw₀ : IsFractionalPacking
      (d8AugmentedDeletedGraph G (z₀ : A) a b
        (d8MissingLeft_ne_universal G hab z₀)
        (d8MissingRight_ne_universal G hab z₀)) w₀)
    (hm : 4 ≤ (universalVertices G).card)
    (rho : ℝ) (sigma : A → ℕ) (R : D8HallRedistribution G P rho sigma)
    (w : ∀ u : ↑(nonUniversalVertices G),
      Finset (↑(d7DeletedFinset (u : A))) → ℝ)
    (hw : ∀ u : ↑(nonUniversalVertices G),
      IsCapacityPacking (d7DeletedGraph G (u : A))
        (d8HallDeletedCapacity G P rho sigma R u) (w u))
    (x y : ↑(universalVertices G)) (hxy : x ≠ y) :
    (∑ u : ↑(nonUniversalVertices G),
        fractionalEdgeLoad G (d7LiftedWeight (u : A) (w u))
          s((x : A), (y : A))) +
      (∑ z : ↑(universalVertices G),
        fractionalEdgeLoad G
          (d7LiftedWeight (z : A)
            (d8CoherentStrippedWeight G z₀ hab w₀ z))
          s((x : A), (y : A))) +
      fractionalEdgeLoad G (d8HallCorrection G P rho)
        s((x : A), (y : A)) ≤
      ((Fintype.card A - 2 : ℕ) : ℝ) := by
  have hU := sum_d8HallLiftedWeight_universal_le
    G P sigma R hm w hw x y hxy
  have hZ := d8HallCorrection_numerator_universal_le
    G z₀ hab w₀ P hreal hw₀ hm rho x y hxy
  have hparts := card_nonUniversalVertices_add_card_universalVertices G
  have hA2 : 2 ≤ Fintype.card A := by omega
  have hpartsR : ((nonUniversalVertices G).card : ℝ) +
      ((universalVertices G).card : ℝ) = (Fintype.card A : ℝ) := by
    exact_mod_cast hparts
  rw [Nat.cast_sub hA2, Nat.cast_ofNat]
  linarith

lemma d8HallAverageWeight_isFractionalPacking
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G)) {a b : A}
    (hab : Gᶜ.Adj a b)
    (w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ)
    (P : D8SeparatedParameters G)
    (hreal : P.RealizesCoherentRemovedFamily G z₀ hab w₀)
    (hw₀ : IsFractionalPacking
      (d8AugmentedDeletedGraph G (z₀ : A) a b
        (d8MissingLeft_ne_universal G hab z₀)
        (d8MissingRight_ne_universal G hab z₀)) w₀)
    (hm : 4 ≤ (universalVertices G).card)
    {rho : ℝ} (hrho0 : 0 ≤ rho)
    (hrhoLe : rho ≤ ((universalVertices G).card : ℝ) * P.betaMass)
    (sigma : A → ℕ) (R : D8HallRedistribution G P rho sigma)
    (w : ∀ u : ↑(nonUniversalVertices G),
      Finset (↑(d7DeletedFinset (u : A))) → ℝ)
    (hw : ∀ u : ↑(nonUniversalVertices G),
      IsCapacityPacking (d7DeletedGraph G (u : A))
        (d8HallDeletedCapacity G P rho sigma R u) (w u)) :
    IsFractionalPacking G
      (d8HallAverageWeight G z₀ hab w₀ P rho w) := by
  have hcard : 2 < Fintype.card A := by
    have hparts := card_nonUniversalVertices_add_card_universalVertices G
    omega
  have hwFractional : ∀ u : ↑(nonUniversalVertices G),
      IsFractionalPacking (d7DeletedGraph G (u : A)) (w u) := by
    intro u
    refine ⟨(hw u).1, ?_⟩
    intro e he
    calc
      fractionalEdgeLoad (d7DeletedGraph G (u : A)) (w u) e ≤
          d8HallDeletedCapacity G P rho sigma R u e := (hw u).2 e he
      _ ≤ 1 := by
        rw [d8HallDeletedCapacity, if_pos he]
        exact sub_le_self 1 (d8HallDeduction_nonneg G P rho sigma R u e)
  constructor
  · intro t ht
    unfold d8HallAverageWeight
    apply mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
    exact add_nonneg (add_nonneg
      (Finset.sum_nonneg fun u _ ↦ (hwFractional u).extendInduced.nonneg_on ht)
      (Finset.sum_nonneg fun z _ ↦
        (d8CoherentStrippedWeight_isFractionalPacking
          G z₀ hab hw₀ z).extendInduced.nonneg_on ht))
      (d8HallCorrection_nonneg G P hm hrhoLe t ht)
  · intro e he
    induction e using Sym2.inductionOn with
    | _ x y =>
      have hxy : x ≠ y := by
        have hnd := G.not_isDiag_of_mem_edgeFinset he
        simpa only [Sym2.mk_isDiag_iff] using hnd
      have nonUniversal_of_not_universal : ∀ {v : A},
          v ∉ universalVertices G → v ∈ nonUniversalVertices G := by
        intro v hv
        apply mem_nonUniversalVertices.mpr
        have hvne : Gᶜ.degree v ≠ 0 := by
          intro hz
          exact hv (mem_universalVertices.mpr hz)
        exact Nat.pos_of_ne_zero hvne
      apply d8HallAverageWeight_edgeLoad_le_one_of_numerator
        G z₀ hab w₀ P rho w hcard
      by_cases hxZ : x ∈ universalVertices G
      · let zx : ↑(universalVertices G) := ⟨x, hxZ⟩
        by_cases hyZ : y ∈ universalVertices G
        · let zy : ↑(universalVertices G) := ⟨y, hyZ⟩
          have hzxy : zx ≠ zy := fun h ↦ hxy (congrArg Subtype.val h)
          exact d8HallAverageWeight_numerator_universal_le
            G z₀ hab w₀ P hreal hw₀ hm rho sigma R w hw zx zy hzxy
        · let uy : ↑(nonUniversalVertices G) :=
            ⟨y, nonUniversal_of_not_universal hyZ⟩
          rw [show s(x, y) = s(y, x) from Sym2.eq_swap]
          exact d8HallAverageWeight_numerator_mixed_le
            G z₀ hab w₀ P hreal hw₀ hm hrho0 sigma R w hw uy zx
      · let ux : ↑(nonUniversalVertices G) :=
          ⟨x, nonUniversal_of_not_universal hxZ⟩
        by_cases hyZ : y ∈ universalVertices G
        · let zy : ↑(universalVertices G) := ⟨y, hyZ⟩
          exact d8HallAverageWeight_numerator_mixed_le
            G z₀ hab w₀ P hreal hw₀ hm hrho0 sigma R w hw ux zy
        · let uy : ↑(nonUniversalVertices G) :=
            ⟨y, nonUniversal_of_not_universal hyZ⟩
          have huxy : ux ≠ uy := fun h ↦ hxy (congrArg Subtype.val h)
          have heU : s(ux, uy) ∈ (G.induce
              (↑(nonUniversalVertices G) : Set A)).edgeFinset := by
            rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
            change G.Adj x y
            exact SimpleGraph.mem_edgeFinset.mp he
          exact d8HallAverageWeight_numerator_nonUniversal_le
            G z₀ hab w₀ P hreal hw₀ hrho0 sigma R w hw ux uy huxy heU

/-! ### The pointwise one-half bound in the Hall branch -/

lemma d8RemovedLoad_le_half_of_universal_endpoint
    (G : SimpleGraph A) (z : ↑(universalVertices G)) {a b : A}
    (hab : Gᶜ.Adj a b)
    {w : Finset (↑(d7DeletedFinset (A := A) (z : A))) → ℝ}
    (hwHalf : IsHalfBounded
      (d8AugmentedDeletedGraph G (z : A) a b
        (d8MissingLeft_ne_universal G hab z)
        (d8MissingRight_ne_universal G hab z)) w)
    (v : ↑(universalVertices G)) (hvz : (v : A) ≠ (z : A))
    (p : Sym2 (↑(d7DeletedFinset (A := A) (z : A))))
    (hvp : d7DeletedVertex (z : A) (v : A) hvz ∈ p) :
    d8RemovedLoad G (z : A) a b
      (d8MissingLeft_ne_universal G hab z)
      (d8MissingRight_ne_universal G hab z) w p ≤ 1 / 2 := by
  let xa := d7DeletedVertex (z : A) a
    (d8MissingLeft_ne_universal G hab z)
  let xb := d7DeletedVertex (z : A) b
    (d8MissingRight_ne_universal G hab z)
  let q := d7DeletedVertex (z : A) (v : A) hvz
  let H := d8AugmentedDeletedGraph G (z : A) a b
    (d8MissingLeft_ne_universal G hab z)
    (d8MissingRight_ne_universal G hab z)
  let T := (H.cliqueFinset 3).filter
    (fun t ↦ p ∈ t.sym2 ∧ s(xa, xb) ∈ t.sym2)
  have hxab : xa ≠ xb := by
    intro h
    exact hab.ne (congrArg Subtype.val h)
  have hxaq : xa ≠ q := by
    intro h
    exact d8MissingLeft_ne_universal G hab v (congrArg Subtype.val h)
  have hxbq : xb ≠ q := by
    intro h
    exact d8MissingRight_ne_universal G hab v (congrArg Subtype.val h)
  have hTsub : T ⊆ {{xa, xb, q}} := by
    intro t ht
    simp only [T, Finset.mem_filter] at ht
    simp only [Finset.mem_singleton]
    have htcard : t.card = 3 :=
      (SimpleGraph.mem_cliqueFinset_iff.mp ht.1).card_eq
    have hpair := Finset.mk_mem_sym2_iff.mp ht.2.2
    have hq : q ∈ t := Finset.mem_sym2_iff.mp ht.2.1 q hvp
    have hsub : ({xa, xb, q} : Finset _) ⊆ t := by
      intro r hr
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr
      rcases hr with rfl | rfl | rfl
      · exact hpair.1
      · exact hpair.2
      · exact hq
    have hthree : ({xa, xb, q} : Finset _).card = 3 := by
      exact Finset.card_eq_three.mpr
        ⟨xa, xb, q, hxab, hxaq, hxbq, rfl⟩
    exact (Finset.eq_of_subset_of_card_le hsub (by
      rw [htcard, hthree])).symm
  have hTcard : T.card ≤ 1 := by
    calc
      T.card ≤ ({{xa, xb, q}} : Finset (Finset _)).card :=
        Finset.card_le_card hTsub
      _ = 1 := Finset.card_singleton _
  unfold d8RemovedLoad fractionalEdgeLoad
  change (∑ t ∈ (H.cliqueFinset 3).filter (fun t ↦ p ∈ t.sym2),
      edgeTrianglesPart s(xa, xb) w t) ≤ 1 / 2
  rw [show (∑ t ∈ (H.cliqueFinset 3).filter (fun t ↦ p ∈ t.sym2),
      edgeTrianglesPart s(xa, xb) w t) = ∑ t ∈ T, w t by
    simp only [T, edgeTrianglesPart, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro t _
    by_cases hp : p ∈ t.sym2 <;>
      by_cases he : s(xa, xb) ∈ t.sym2 <;> simp [hp, he]]
  calc
    (∑ t ∈ T, w t) ≤ ∑ _t ∈ T, (1 / 2 : ℝ) := by
      apply Finset.sum_le_sum
      intro t ht
      exact hwHalf t (Finset.mem_filter.mp ht).1
    _ = (T.card : ℝ) * (1 / 2) := by
      simp only [Finset.sum_const, nsmul_eq_mul, Nat.cast_ofNat]
    _ ≤ 1 * (1 / 2) := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hTcard) (by norm_num)
    _ = 1 / 2 := by ring

lemma D8SeparatedParameters.alpha_le_half_of_realizes
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G)) {a b : A}
    (hab : Gᶜ.Adj a b)
    {w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ}
    (P : D8SeparatedParameters G)
    (hreal : P.RealizesCoherentRemovedFamily G z₀ hab w₀)
    (hm : 4 ≤ (universalVertices G).card)
    (hw₀Half : IsHalfBounded
      (d8AugmentedDeletedGraph G (z₀ : A) a b
        (d8MissingLeft_ne_universal G hab z₀)
        (d8MissingRight_ne_universal G hab z₀)) w₀)
    (u : ↑(nonUniversalVertices G)) : P.alpha u ≤ 1 / 2 := by
  let v := d7OtherUniversalFirst G z₀ hm
  have hvz : (v : A) ≠ (z₀ : A) := d8OtherUniversalFirst_val_ne G z₀ hm
  let p : Sym2 (↑(d7DeletedFinset (A := A) (z₀ : A))) :=
    s(d7NonUniversalDeletedEmbedding G z₀ u,
      d7DeletedVertex (z₀ : A) (v : A) hvz)
  have hvp : d7DeletedVertex (z₀ : A) (v : A) hvz ∈ p := by
    simp [p]
  rw [← hreal.alpha_eq z₀ v hvz u]
  exact d8RemovedLoad_le_half_of_universal_endpoint
    G z₀ hab (d8CoherentAugmentedWeight_halfBounded
      G z₀ hab hw₀Half z₀) v hvz p hvp

lemma D8SeparatedParameters.gamma_le_half_of_realizes
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G)) {a b : A}
    (hab : Gᶜ.Adj a b)
    {w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ}
    (P : D8SeparatedParameters G)
    (hreal : P.RealizesCoherentRemovedFamily G z₀ hab w₀)
    (hm : 4 ≤ (universalVertices G).card)
    (hw₀Half : IsHalfBounded
      (d8AugmentedDeletedGraph G (z₀ : A) a b
        (d8MissingLeft_ne_universal G hab z₀)
        (d8MissingRight_ne_universal G hab z₀)) w₀) :
    P.gamma ≤ 1 / 2 := by
  let x := d7OtherUniversalFirst G z₀ hm
  let y := d7OtherUniversalSecond G z₀ hm
  have hxz : (x : A) ≠ (z₀ : A) := d8OtherUniversalFirst_val_ne G z₀ hm
  have hyz : (y : A) ≠ (z₀ : A) := d8OtherUniversalSecond_val_ne G z₀ hm
  have hxy : (x : A) ≠ (y : A) := fun h ↦
    d7OtherUniversalFirst_ne_second G z₀ hm (Subtype.ext h)
  let p : Sym2 (↑(d7DeletedFinset (A := A) (z₀ : A))) :=
    s(d7DeletedVertex (z₀ : A) (x : A) hxz,
      d7DeletedVertex (z₀ : A) (y : A) hyz)
  have hxp : d7DeletedVertex (z₀ : A) (x : A) hxz ∈ p := by
    simp [p]
  rw [← hreal.gamma_eq z₀ x y hxz hyz hxy]
  exact d8RemovedLoad_le_half_of_universal_endpoint
    G z₀ hab (d8CoherentAugmentedWeight_halfBounded
      G z₀ hab hw₀Half z₀) x hxz p hxp

lemma d8HallUZZCorrection_apply_UUZ_eq_zero
    (G : SimpleGraph A) (P : D8SeparatedParameters G)
    (u v : ↑(nonUniversalVertices G))
    (z : ↑(universalVertices G)) :
    d8HallUZZCorrection G P {(z : A), (u : A), (v : A)} = 0 := by
  unfold d8HallUZZCorrection weightedAttachedEdgeWeight singleTriangleWeight
  apply Fintype.sum_eq_zero
  intro u'
  apply Fintype.sum_eq_zero
  intro f
  rw [if_neg]
  intro hEq
  have hfND : ¬(f : Sym2 (↑(universalVertices G))).IsDiag :=
    (⊤ : SimpleGraph (↑(universalVertices G))).not_isDiag_of_mem_edgeFinset
      f.property
  have hmapSub : (f : Sym2 (↑(universalVertices G))).toFinset.map
      (inducedEmbedding (universalVertices G)) ⊆
        ({(z : A), (u : A), (v : A)} : Finset A) := by
    intro x hx
    rw [hEq]
    simp only [attachedEdgeTriangle, Finset.mem_insert]
    exact Or.inr hx
  have hmapSingleton : (f : Sym2 (↑(universalVertices G))).toFinset.map
      (inducedEmbedding (universalVertices G)) ⊆ ({(z : A)} : Finset A) := by
    intro x hx
    have hxTarget := hmapSub hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxTarget ⊢
    rcases hxTarget with hxz | hxu | hxv
    · exact hxz
    · obtain ⟨x', hx', rfl⟩ := Finset.mem_map.mp hx
      apply (universalVertex_not_mem_nonUniversalVertices G x'.property).elim
      change (x' : A) = (u : A) at hxu
      rw [hxu]
      exact u.property
    · obtain ⟨x', hx', rfl⟩ := Finset.mem_map.mp hx
      apply (universalVertex_not_mem_nonUniversalVertices G x'.property).elim
      change (x' : A) = (v : A) at hxv
      rw [hxv]
      exact v.property
  have hcardMap : ((f : Sym2 (↑(universalVertices G))).toFinset.map
      (inducedEmbedding (universalVertices G))).card = 2 := by
    rw [Finset.card_map, Sym2.card_toFinset_of_not_isDiag _ hfND]
  have hcardLe := Finset.card_le_card hmapSingleton
  rw [hcardMap, Finset.card_singleton] at hcardLe
  omega

lemma d8HallZZZCorrection_apply_UUZ_eq_zero
    (G : SimpleGraph A) (P : D8SeparatedParameters G)
    (u v : ↑(nonUniversalVertices G))
    (z : ↑(universalVertices G)) :
    d8HallZZZCorrection G P {(z : A), (u : A), (v : A)} = 0 := by
  unfold d8HallZZZCorrection singleTriangleWeight
  apply Fintype.sum_eq_zero
  intro q
  rw [if_neg]
  intro hEq
  have huq : (u : A) ∈ (q : Finset A) := by
    rw [← hEq]
    simp
  have huZ := (Finset.mem_powersetCard.mp q.property).1 huq
  exact nonUniversalVertex_not_mem_universalVertices G u.property huZ

lemma d8HallCorrection_apply_UUZ
    (G : SimpleGraph A) (P : D8SeparatedParameters G) {rho : ℝ}
    (u v : ↑(nonUniversalVertices G)) (huv : u ≠ v)
    (z : ↑(universalVertices G))
    (he : s(u, v) ∈ (G.induce
      (↑(nonUniversalVertices G) : Set A)).edgeFinset) :
    d8HallCorrection G P rho {(z : A), (u : A), (v : A)} =
      P.hallScale rho * P.beta s(u, v) := by
  unfold d8HallCorrection d8HallUUZCorrection
  rw [d8UUZCorrection_apply G P u v huv z he,
    d8HallUZZCorrection_apply_UUZ_eq_zero G P u v z,
    d8HallZZZCorrection_apply_UUZ_eq_zero G P u v z]
  ring

lemma d8HallUZZCorrection_apply
    (G : SimpleGraph A) (P : D8SeparatedParameters G)
    (u : ↑(nonUniversalVertices G))
    (x y : ↑(universalVertices G)) (hxy : x ≠ y) :
    d8HallUZZCorrection G P {(u : A), (x : A), (y : A)} = P.alpha u := by
  let e : Sym2 (↑(universalVertices G)) := s(x, y)
  have he : e ∈ (⊤ : SimpleGraph
      (↑(universalVertices G))).edgeFinset := by
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    exact hxy
  have htriangle : attachedEdgeTriangle (universalVertices G) (u : A) e =
      ({(u : A), (x : A), (y : A)} : Finset A) := by
    simp only [attachedEdgeTriangle, e, Sym2.toFinset_mk_eq,
      Finset.map_insert, Finset.map_singleton, inducedEmbedding_apply]
  unfold d8HallUZZCorrection
  rw [Fintype.sum_eq_single u]
  · rw [← htriangle]
    exact weightedAttachedEdgeWeight_apply_d7
      (nonUniversalVertex_not_mem_universalVertices G u.property)
      (fun f hf ↦
        (⊤ : SimpleGraph (↑(universalVertices G))).not_isDiag_of_mem_edgeFinset hf)
      he
  · intro u' hu'
    unfold weightedAttachedEdgeWeight singleTriangleWeight
    apply Fintype.sum_eq_zero
    intro f
    rw [if_neg]
    intro hEq
    apply hu'
    apply Subtype.ext
    have humem : (u' : A) ∈ ({(u : A), (x : A), (y : A)} : Finset A) := by
      rw [hEq]
      simp [attachedEdgeTriangle]
    simp only [Finset.mem_insert, Finset.mem_singleton] at humem
    rcases humem with h | h | h
    · exact h
    · exact (nonUniversalVertex_not_mem_universalVertices G u'.property
        (h ▸ x.property)).elim
    · exact (nonUniversalVertex_not_mem_universalVertices G u'.property
        (h ▸ y.property)).elim

lemma d8HallZZZCorrection_apply_UZZ_eq_zero
    (G : SimpleGraph A) (P : D8SeparatedParameters G)
    (u : ↑(nonUniversalVertices G))
    (x y : ↑(universalVertices G)) :
    d8HallZZZCorrection G P {(u : A), (x : A), (y : A)} = 0 := by
  unfold d8HallZZZCorrection singleTriangleWeight
  apply Fintype.sum_eq_zero
  intro q
  rw [if_neg]
  intro hEq
  have huq : (u : A) ∈ (q : Finset A) := by
    rw [← hEq]
    simp
  have huZ := (Finset.mem_powersetCard.mp q.property).1 huq
  exact nonUniversalVertex_not_mem_universalVertices G u.property huZ

lemma d8HallCorrection_apply_UZZ
    (G : SimpleGraph A) (P : D8SeparatedParameters G) (rho : ℝ)
    (u : ↑(nonUniversalVertices G))
    (x y : ↑(universalVertices G)) (hxy : x ≠ y) :
    d8HallCorrection G P rho {(u : A), (x : A), (y : A)} = P.alpha u := by
  unfold d8HallCorrection d8HallUUZCorrection
  rw [d8UUZCorrection_apply_UZZ_eq_zero G P u x y,
    d8HallUZZCorrection_apply G P u x y hxy,
    d8HallZZZCorrection_apply_UZZ_eq_zero G P u x y]
  ring

lemma d8HallUZZCorrection_apply_ZZZ_eq_zero
    (G : SimpleGraph A) (P : D8SeparatedParameters G)
    (x y z : ↑(universalVertices G)) :
    d8HallUZZCorrection G P {(x : A), (y : A), (z : A)} = 0 := by
  unfold d8HallUZZCorrection weightedAttachedEdgeWeight singleTriangleWeight
  apply Fintype.sum_eq_zero
  intro u
  apply Fintype.sum_eq_zero
  intro e
  rw [if_neg]
  intro hEq
  have huTarget : (u : A) ∈
      ({(x : A), (y : A), (z : A)} : Finset A) := by
    rw [hEq]
    simp [attachedEdgeTriangle]
  simp only [Finset.mem_insert, Finset.mem_singleton] at huTarget
  rcases huTarget with h | h | h
  · exact (nonUniversalVertex_not_mem_universalVertices G u.property
      (h ▸ x.property)).elim
  · exact (nonUniversalVertex_not_mem_universalVertices G u.property
      (h ▸ y.property)).elim
  · exact (nonUniversalVertex_not_mem_universalVertices G u.property
      (h ▸ z.property)).elim

lemma d8HallZZZCorrection_apply
    (G : SimpleGraph A) (P : D8SeparatedParameters G)
    (x y z : ↑(universalVertices G))
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    d8HallZZZCorrection G P {(x : A), (y : A), (z : A)} = P.gamma := by
  have hxyA : (x : A) ≠ (y : A) := fun h ↦ hxy (Subtype.ext h)
  have hxzA : (x : A) ≠ (z : A) := fun h ↦ hxz (Subtype.ext h)
  have hyzA : (y : A) ≠ (z : A) := fun h ↦ hyz (Subtype.ext h)
  let q0 : Finset A := {(x : A), (y : A), (z : A)}
  have hqsub : q0 ⊆ universalVertices G := by
    intro a ha
    simp only [q0, Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl
    · exact x.property
    · exact y.property
    · exact z.property
  have hqcard : q0.card = 3 := by simp [q0, hxyA, hxzA, hyzA]
  let q : ↑((universalVertices G).powersetCard 3) :=
    ⟨q0, Finset.mem_powersetCard.mpr ⟨hqsub, hqcard⟩⟩
  unfold d8HallZZZCorrection singleTriangleWeight
  rw [Fintype.sum_eq_single q]
  · dsimp only [q, q0]
    rw [if_pos rfl]
  · intro q' hne
    rw [if_neg]
    intro hEq
    apply hne
    apply Subtype.ext
    exact hEq.symm

lemma d8HallCorrection_apply_ZZZ
    (G : SimpleGraph A) (P : D8SeparatedParameters G) (rho : ℝ)
    (x y z : ↑(universalVertices G))
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    d8HallCorrection G P rho {(x : A), (y : A), (z : A)} = P.gamma := by
  unfold d8HallCorrection d8HallUUZCorrection
  rw [d8UUZCorrection_apply_ZZZ_eq_zero G P x y z,
    d8HallUZZCorrection_apply_ZZZ_eq_zero G P x y z,
    d8HallZZZCorrection_apply G P x y z hxy hxz hyz]
  ring

lemma d8HallUZZCorrection_apply_UUU_eq_zero
    (G : SimpleGraph A) (P : D8SeparatedParameters G)
    (u v w : ↑(nonUniversalVertices G)) :
    d8HallUZZCorrection G P {(u : A), (v : A), (w : A)} = 0 := by
  unfold d8HallUZZCorrection
  apply Fintype.sum_eq_zero
  intro u'
  apply weightedAttachedEdgeWeight_eq_zero_of_not_exists_d8
  rintro ⟨e, he, hEq⟩
  obtain ⟨z, hz⟩ := Finset.nonempty_iff_ne_empty.mpr
    (Sym2.toFinset_ne_empty e)
  have hzMap : (z : A) ∈ ({(u : A), (v : A), (w : A)} : Finset A) := by
    rw [hEq]
    simp only [attachedEdgeTriangle, Finset.mem_insert]
    right
    exact Finset.mem_map.mpr ⟨z, hz, rfl⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hzMap
  rcases hzMap with h | h | h
  · exact (nonUniversalVertex_not_mem_universalVertices G u.property
      (by rw [← h]; exact z.property)).elim
  · exact (nonUniversalVertex_not_mem_universalVertices G v.property
      (by rw [← h]; exact z.property)).elim
  · exact (nonUniversalVertex_not_mem_universalVertices G w.property
      (by rw [← h]; exact z.property)).elim

lemma d8HallZZZCorrection_apply_UUU_eq_zero
    (G : SimpleGraph A) (P : D8SeparatedParameters G)
    (u v w : ↑(nonUniversalVertices G)) :
    d8HallZZZCorrection G P {(u : A), (v : A), (w : A)} = 0 := by
  unfold d8HallZZZCorrection singleTriangleWeight
  apply Fintype.sum_eq_zero
  intro q
  rw [if_neg]
  intro hEq
  have hqne : (q : Finset A) ≠ ∅ := by
    intro hzero
    have hcard := (Finset.mem_powersetCard.mp q.property).2
    rw [hzero, Finset.card_empty] at hcard
    omega
  obtain ⟨z, hzq⟩ := Finset.nonempty_iff_ne_empty.mpr hqne
  have hzTarget : z ∈ ({(u : A), (v : A), (w : A)} : Finset A) := by
    rw [hEq]
    exact hzq
  have hzZ := (Finset.mem_powersetCard.mp q.property).1 hzq
  simp only [Finset.mem_insert, Finset.mem_singleton] at hzTarget
  rcases hzTarget with h | h | h
  · exact (nonUniversalVertex_not_mem_universalVertices G u.property
      (h ▸ hzZ)).elim
  · exact (nonUniversalVertex_not_mem_universalVertices G v.property
      (h ▸ hzZ)).elim
  · exact (nonUniversalVertex_not_mem_universalVertices G w.property
      (h ▸ hzZ)).elim

lemma d8HallCorrection_apply_UUU_eq_zero
    (G : SimpleGraph A) (P : D8SeparatedParameters G) (rho : ℝ)
    (u v w : ↑(nonUniversalVertices G)) :
    d8HallCorrection G P rho {(u : A), (v : A), (w : A)} = 0 := by
  unfold d8HallCorrection d8HallUUZCorrection
  rw [d8UUZCorrection_apply_UUU_eq_zero G P u v w,
    d8HallUZZCorrection_apply_UUU_eq_zero G P u v w,
    d8HallZZZCorrection_apply_UUU_eq_zero G P u v w]
  ring

lemma d8HallAverageWeight_UUU_numerator_le
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G)) {a b : A}
    (hab : Gᶜ.Adj a b)
    {w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ}
    (P : D8SeparatedParameters G) (rho : ℝ)
    (w : ∀ u : ↑(nonUniversalVertices G),
      Finset (↑(d7DeletedFinset (u : A))) → ℝ)
    (hwTop : ∀ u : ↑(nonUniversalVertices G), IsHalfBounded
      (⊤ : SimpleGraph (↑(d7DeletedFinset (u : A)))) (w u))
    (hw₀Half : IsHalfBounded
      (d8AugmentedDeletedGraph G (z₀ : A) a b
        (d8MissingLeft_ne_universal G hab z₀)
        (d8MissingRight_ne_universal G hab z₀)) w₀)
    (u v x : ↑(nonUniversalVertices G))
    (huv : u ≠ v) (hux : u ≠ x) (hvx : v ≠ x)
    (ht : ({(u : A), (v : A), (x : A)} : Finset A) ∈
      G.cliqueFinset 3) :
    (∑ y : ↑(nonUniversalVertices G),
        d7LiftedWeight (y : A) (w y) {(u : A), (v : A), (x : A)}) +
      (∑ z : ↑(universalVertices G),
        d7LiftedWeight (z : A)
          (d8CoherentStrippedWeight G z₀ hab w₀ z)
          {(u : A), (v : A), (x : A)}) +
      d8HallCorrection G P rho {(u : A), (v : A), (x : A)} ≤
        (((Fintype.card A - 2 : ℕ) : ℝ)) / 2 := by
  have hU := sum_d7SmallNonUniversalDeleted_UUU_le G w hwTop
    u v x huv hux hvx ht
  have hZ : (∑ z : ↑(universalVertices G),
      d7LiftedWeight (z : A)
        (d8CoherentStrippedWeight G z₀ hab w₀ z)
        {(u : A), (v : A), (x : A)}) ≤
      ((universalVertices G).card : ℝ) * (1 / 2) := by
    calc
      _ ≤ ∑ _z : ↑(universalVertices G), (1 / 2 : ℝ) := by
        apply Finset.sum_le_sum
        intro z _
        exact d7LiftedWeight_le_half G z
          (d8CoherentStrippedWeight_halfBounded G z₀ hab hw₀Half z) ht
      _ = ((universalVertices G).card : ℝ) * (1 / 2) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe,
          nsmul_eq_mul]
  rw [d8HallCorrection_apply_UUU_eq_zero G P rho u v x, add_zero]
  have hparts := card_nonUniversalVertices_add_card_universalVertices G
  have hNU2 : 2 ≤ (nonUniversalVertices G).card := by
    have hpair : ({u, v} : Finset (↑(nonUniversalVertices G))).card = 2 := by
      simp [huv]
    have hle := Finset.card_le_card
      (Finset.subset_univ ({u, v} : Finset (↑(nonUniversalVertices G))))
    simpa only [hpair, Finset.card_univ, Fintype.card_coe] using hle
  have hpartsR : ((nonUniversalVertices G).card : ℝ) +
      ((universalVertices G).card : ℝ) = (Fintype.card A : ℝ) := by
    exact_mod_cast hparts
  rw [Nat.cast_sub (by omega : 2 ≤ Fintype.card A), Nat.cast_ofNat]
  linarith

lemma d8HallAverageWeight_UUZ_numerator_le
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G)) {a b : A}
    (hab : Gᶜ.Adj a b)
    {w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ}
    (P : D8SeparatedParameters G)
    (hreal : P.RealizesCoherentRemovedFamily G z₀ hab w₀)
    {rho : ℝ} (hrho0 : 0 ≤ rho)
    (hm : 4 ≤ (universalVertices G).card)
    (hw₀ : IsFractionalPacking
      (d8AugmentedDeletedGraph G (z₀ : A) a b
        (d8MissingLeft_ne_universal G hab z₀)
        (d8MissingRight_ne_universal G hab z₀)) w₀)
    (hw₀Half : IsHalfBounded
      (d8AugmentedDeletedGraph G (z₀ : A) a b
        (d8MissingLeft_ne_universal G hab z₀)
        (d8MissingRight_ne_universal G hab z₀)) w₀)
    (w : ∀ u : ↑(nonUniversalVertices G),
      Finset (↑(d7DeletedFinset (u : A))) → ℝ)
    (hwTop : ∀ u : ↑(nonUniversalVertices G), IsHalfBounded
      (⊤ : SimpleGraph (↑(d7DeletedFinset (u : A)))) (w u))
    (u v : ↑(nonUniversalVertices G)) (huv : u ≠ v)
    (z : ↑(universalVertices G))
    (he : s(u, v) ∈ (G.induce
      (↑(nonUniversalVertices G) : Set A)).edgeFinset)
    (ht : ({(z : A), (u : A), (v : A)} : Finset A) ∈
      G.cliqueFinset 3) :
    (∑ x : ↑(nonUniversalVertices G),
        d7LiftedWeight (x : A) (w x) {(z : A), (u : A), (v : A)}) +
      (∑ y : ↑(universalVertices G),
        d7LiftedWeight (y : A)
          (d8CoherentStrippedWeight G z₀ hab w₀ y)
          {(z : A), (u : A), (v : A)}) +
      d8HallCorrection G P rho {(z : A), (u : A), (v : A)} ≤
        (((Fintype.card A - 2 : ℕ) : ℝ)) / 2 := by
  have hU := sum_d7SmallNonUniversalDeleted_UUZ_le
    G w hwTop u v huv z ht
  have hZshort := d8ShortcutAverageWeight_UUZ_numerator_le
    G z₀ hab P hreal hm hw₀ hw₀Half u v huv z he ht
  rw [d8ShortcutCorrection_apply_UUZ G P u v huv z he] at hZshort
  rw [d8HallCorrection_apply_UUZ G P u v huv z he]
  have hscale := P.hallScale_le_one hrho0
  have hbeta := P.beta_nonneg s(u, v) he
  have hscaled : P.hallScale rho * P.beta s(u, v) ≤ P.beta s(u, v) := by
    calc
      P.hallScale rho * P.beta s(u, v) ≤ 1 * P.beta s(u, v) :=
        mul_le_mul_of_nonneg_right hscale hbeta
      _ = P.beta s(u, v) := one_mul _
  have hZ : (∑ y : ↑(universalVertices G),
      d7LiftedWeight (y : A)
        (d8CoherentStrippedWeight G z₀ hab w₀ y)
        {(z : A), (u : A), (v : A)}) +
      P.hallScale rho * P.beta s(u, v) ≤
        ((universalVertices G).card : ℝ) / 2 := by
    linarith
  have hparts := card_nonUniversalVertices_add_card_universalVertices G
  have hpartsR : ((nonUniversalVertices G).card : ℝ) +
      ((universalVertices G).card : ℝ) = (Fintype.card A : ℝ) := by
    exact_mod_cast hparts
  rw [Nat.cast_sub (by omega : 2 ≤ Fintype.card A), Nat.cast_ofNat]
  linarith

lemma d8HallAverageWeight_UZZ_numerator_le
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G)) {a b : A}
    (hab : Gᶜ.Adj a b)
    {w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ}
    (P : D8SeparatedParameters G)
    (hreal : P.RealizesCoherentRemovedFamily G z₀ hab w₀)
    (rho : ℝ) (hm : 4 ≤ (universalVertices G).card)
    (hw₀Half : IsHalfBounded
      (d8AugmentedDeletedGraph G (z₀ : A) a b
        (d8MissingLeft_ne_universal G hab z₀)
        (d8MissingRight_ne_universal G hab z₀)) w₀)
    (w : ∀ u : ↑(nonUniversalVertices G),
      Finset (↑(d7DeletedFinset (u : A))) → ℝ)
    (hwTop : ∀ u : ↑(nonUniversalVertices G), IsHalfBounded
      (⊤ : SimpleGraph (↑(d7DeletedFinset (u : A)))) (w u))
    (u : ↑(nonUniversalVertices G))
    (x y : ↑(universalVertices G)) (hxy : x ≠ y)
    (ht : ({(u : A), (x : A), (y : A)} : Finset A) ∈
      G.cliqueFinset 3) :
    (∑ v : ↑(nonUniversalVertices G),
        d7LiftedWeight (v : A) (w v) {(u : A), (x : A), (y : A)}) +
      (∑ z : ↑(universalVertices G),
        d7LiftedWeight (z : A)
          (d8CoherentStrippedWeight G z₀ hab w₀ z)
          {(u : A), (x : A), (y : A)}) +
      d8HallCorrection G P rho {(u : A), (x : A), (y : A)} ≤
        (((Fintype.card A - 2 : ℕ) : ℝ)) / 2 := by
  have hU := sum_d7SmallNonUniversalDeleted_UZZ_le G w hwTop u x y ht
  let f : ↑(universalVertices G) → ℝ := fun z ↦
    d7LiftedWeight (z : A)
      (d8CoherentStrippedWeight G z₀ hab w₀ z)
      {(u : A), (x : A), (y : A)}
  have hfx : f x ≤ 0 := by
    rw [show f x = 0 by
      exact d7LiftedWeight_eq_zero_of_mem G x _ (by simp)]
  have hfy : f y ≤ 0 := by
    rw [show f y = 0 by
      exact d7LiftedWeight_eq_zero_of_mem G y _ (by simp)]
  have hrest : ∀ z, z ≠ x → z ≠ y → f z ≤ 1 / 2 := by
    intro z _ _
    exact d7LiftedWeight_le_half G z
      (d8CoherentStrippedWeight_halfBounded G z₀ hab hw₀Half z) ht
  have hZ := sum_le_two_exception f x y hxy 0 0 (1 / 2) hfx hfy hrest
  simp only [f, Fintype.card_coe, zero_add] at hZ
  rw [d8HallCorrection_apply_UZZ G P rho u x y hxy]
  have halpha := P.alpha_le_half_of_realizes
    G z₀ hab hreal hm hw₀Half u
  have hparts := card_nonUniversalVertices_add_card_universalVertices G
  have hpartsR : ((nonUniversalVertices G).card : ℝ) +
      ((universalVertices G).card : ℝ) = (Fintype.card A : ℝ) := by
    exact_mod_cast hparts
  rw [Nat.cast_sub (by omega : 2 ≤ Fintype.card A), Nat.cast_ofNat]
  linarith

lemma d8HallAverageWeight_ZZZ_numerator_le
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G)) {a b : A}
    (hab : Gᶜ.Adj a b)
    {w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ}
    (P : D8SeparatedParameters G)
    (hreal : P.RealizesCoherentRemovedFamily G z₀ hab w₀)
    (rho : ℝ) (hm : 4 ≤ (universalVertices G).card)
    (hw₀Half : IsHalfBounded
      (d8AugmentedDeletedGraph G (z₀ : A) a b
        (d8MissingLeft_ne_universal G hab z₀)
        (d8MissingRight_ne_universal G hab z₀)) w₀)
    (w : ∀ u : ↑(nonUniversalVertices G),
      Finset (↑(d7DeletedFinset (u : A))) → ℝ)
    (hwTop : ∀ u : ↑(nonUniversalVertices G), IsHalfBounded
      (⊤ : SimpleGraph (↑(d7DeletedFinset (u : A)))) (w u))
    (x y z : ↑(universalVertices G))
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (ht : ({(x : A), (y : A), (z : A)} : Finset A) ∈
      G.cliqueFinset 3) :
    (∑ u : ↑(nonUniversalVertices G),
        d7LiftedWeight (u : A) (w u) {(x : A), (y : A), (z : A)}) +
      (∑ q : ↑(universalVertices G),
        d7LiftedWeight (q : A)
          (d8CoherentStrippedWeight G z₀ hab w₀ q)
          {(x : A), (y : A), (z : A)}) +
      d8HallCorrection G P rho {(x : A), (y : A), (z : A)} ≤
        (((Fintype.card A - 2 : ℕ) : ℝ)) / 2 := by
  have hU := sum_d7SmallNonUniversalDeleted_ZZZ_le G w hwTop x y z ht
  let f : ↑(universalVertices G) → ℝ := fun q ↦
    d7LiftedWeight (q : A)
      (d8CoherentStrippedWeight G z₀ hab w₀ q)
      {(x : A), (y : A), (z : A)}
  have hfx : f x ≤ 0 := by
    rw [show f x = 0 by
      exact d7LiftedWeight_eq_zero_of_mem G x _ (by simp)]
  have hfy : f y ≤ 0 := by
    rw [show f y = 0 by
      exact d7LiftedWeight_eq_zero_of_mem G y _ (by simp)]
  have hfz : f z ≤ 0 := by
    rw [show f z = 0 by
      exact d7LiftedWeight_eq_zero_of_mem G z _ (by simp)]
  have hrest : ∀ q, q ≠ x → q ≠ y → q ≠ z → f q ≤ 1 / 2 := by
    intro q _ _ _
    exact d7LiftedWeight_le_half G q
      (d8CoherentStrippedWeight_halfBounded G z₀ hab hw₀Half q) ht
  have hZ := sum_le_three_zero f x y z hxy hxz hyz hfx hfy hfz hrest
  simp only [f, Fintype.card_coe] at hZ
  rw [d8HallCorrection_apply_ZZZ G P rho x y z hxy hxz hyz]
  have hgamma := P.gamma_le_half_of_realizes
    G z₀ hab hreal hm hw₀Half
  have hparts := card_nonUniversalVertices_add_card_universalVertices G
  have hpartsR : ((nonUniversalVertices G).card : ℝ) +
      ((universalVertices G).card : ℝ) = (Fintype.card A : ℝ) := by
    exact_mod_cast hparts
  rw [Nat.cast_sub (by omega : 2 ≤ Fintype.card A), Nat.cast_ofNat]
  linarith

private lemma d8HallAverageWeight_numerator_le_of_mem_universal_left
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G)) {x y : A}
    (hxy : Gᶜ.Adj x y)
    {w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ}
    (P : D8SeparatedParameters G)
    (hreal : P.RealizesCoherentRemovedFamily G z₀ hxy w₀)
    {rho : ℝ} (hrho0 : 0 ≤ rho)
    (hm : 4 ≤ (universalVertices G).card)
    (hw₀ : IsFractionalPacking
      (d8AugmentedDeletedGraph G (z₀ : A) x y
        (d8MissingLeft_ne_universal G hxy z₀)
        (d8MissingRight_ne_universal G hxy z₀)) w₀)
    (hw₀Half : IsHalfBounded
      (d8AugmentedDeletedGraph G (z₀ : A) x y
        (d8MissingLeft_ne_universal G hxy z₀)
        (d8MissingRight_ne_universal G hxy z₀)) w₀)
    (w : ∀ u : ↑(nonUniversalVertices G),
      Finset (↑(d7DeletedFinset (u : A))) → ℝ)
    (hwTop : ∀ u : ↑(nonUniversalVertices G), IsHalfBounded
      (⊤ : SimpleGraph (↑(d7DeletedFinset (u : A)))) (w u))
    {a b c : A} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ht : ({a, b, c} : Finset A) ∈ G.cliqueFinset 3)
    (haZ : a ∈ universalVertices G) :
    (∑ u : ↑(nonUniversalVertices G),
        d7LiftedWeight (u : A) (w u) {a, b, c}) +
      (∑ z : ↑(universalVertices G),
        d7LiftedWeight (z : A)
          (d8CoherentStrippedWeight G z₀ hxy w₀ z) {a, b, c}) +
      d8HallCorrection G P rho {a, b, c} ≤
        (((Fintype.card A - 2 : ℕ) : ℝ)) / 2 := by
  have htri := SimpleGraph.mem_cliqueFinset_iff.mp ht
  have hadj := SimpleGraph.is3Clique_triple_iff.mp htri
  have nonUniversal_of_not_universal : ∀ {v : A},
      v ∉ universalVertices G → v ∈ nonUniversalVertices G := by
    intro v hv
    apply mem_nonUniversalVertices.mpr
    have hvne : Gᶜ.degree v ≠ 0 := by
      intro hz
      exact hv (mem_universalVertices.mpr hz)
    exact Nat.pos_of_ne_zero hvne
  let za : ↑(universalVertices G) := ⟨a, haZ⟩
  by_cases hbZ : b ∈ universalVertices G
  · let zb : ↑(universalVertices G) := ⟨b, hbZ⟩
    by_cases hcZ : c ∈ universalVertices G
    · let zc : ↑(universalVertices G) := ⟨c, hcZ⟩
      have hzab : za ≠ zb := fun h ↦ hab (congrArg Subtype.val h)
      have hzac : za ≠ zc := fun h ↦ hac (congrArg Subtype.val h)
      have hzbc : zb ≠ zc := fun h ↦ hbc (congrArg Subtype.val h)
      exact d8HallAverageWeight_ZZZ_numerator_le
        G z₀ hxy P hreal rho hm hw₀Half w hwTop
        za zb zc hzab hzac hzbc ht
    · let uc : ↑(nonUniversalVertices G) :=
        ⟨c, nonUniversal_of_not_universal hcZ⟩
      have hzab : za ≠ zb := fun h ↦ hab (congrArg Subtype.val h)
      have hset : ({(uc : A), (za : A), (zb : A)} : Finset A) =
          ({a, b, c} : Finset A) := by
        ext q
        simp only [uc, za, zb, Finset.mem_insert, Finset.mem_singleton]
        tauto
      have htri' : ({(uc : A), (za : A), (zb : A)} : Finset A) ∈
          G.cliqueFinset 3 := by rw [hset]; exact ht
      have hnum := d8HallAverageWeight_UZZ_numerator_le
        G z₀ hxy P hreal rho hm hw₀Half w hwTop uc za zb hzab htri'
      rwa [hset] at hnum
  · let ub : ↑(nonUniversalVertices G) :=
      ⟨b, nonUniversal_of_not_universal hbZ⟩
    by_cases hcZ : c ∈ universalVertices G
    · let zc : ↑(universalVertices G) := ⟨c, hcZ⟩
      have hzac : za ≠ zc := fun h ↦ hac (congrArg Subtype.val h)
      have hset : ({(ub : A), (za : A), (zc : A)} : Finset A) =
          ({a, b, c} : Finset A) := by
        ext q
        simp only [ub, za, zc, Finset.mem_insert, Finset.mem_singleton]
        tauto
      have htri' : ({(ub : A), (za : A), (zc : A)} : Finset A) ∈
          G.cliqueFinset 3 := by rw [hset]; exact ht
      have hnum := d8HallAverageWeight_UZZ_numerator_le
        G z₀ hxy P hreal rho hm hw₀Half w hwTop ub za zc hzac htri'
      rwa [hset] at hnum
    · let uc : ↑(nonUniversalVertices G) :=
        ⟨c, nonUniversal_of_not_universal hcZ⟩
      have hubc : ub ≠ uc := fun h ↦ hbc (congrArg Subtype.val h)
      have he : s(ub, uc) ∈ (G.induce
          (↑(nonUniversalVertices G) : Set A)).edgeFinset := by
        rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
        change G.Adj b c
        exact hadj.2.2
      exact d8HallAverageWeight_UUZ_numerator_le
        G z₀ hxy P hreal hrho0 hm hw₀ hw₀Half w hwTop
        ub uc hubc za he ht

private lemma d8HallAverageWeight_numerator_le_of_not_mem_universal_left
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G)) {x y : A}
    (hxy : Gᶜ.Adj x y)
    {w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ}
    (P : D8SeparatedParameters G)
    (hreal : P.RealizesCoherentRemovedFamily G z₀ hxy w₀)
    {rho : ℝ} (hrho0 : 0 ≤ rho)
    (hm : 4 ≤ (universalVertices G).card)
    (hw₀ : IsFractionalPacking
      (d8AugmentedDeletedGraph G (z₀ : A) x y
        (d8MissingLeft_ne_universal G hxy z₀)
        (d8MissingRight_ne_universal G hxy z₀)) w₀)
    (hw₀Half : IsHalfBounded
      (d8AugmentedDeletedGraph G (z₀ : A) x y
        (d8MissingLeft_ne_universal G hxy z₀)
        (d8MissingRight_ne_universal G hxy z₀)) w₀)
    (w : ∀ u : ↑(nonUniversalVertices G),
      Finset (↑(d7DeletedFinset (u : A))) → ℝ)
    (hwTop : ∀ u : ↑(nonUniversalVertices G), IsHalfBounded
      (⊤ : SimpleGraph (↑(d7DeletedFinset (u : A)))) (w u))
    {a b c : A} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ht : ({a, b, c} : Finset A) ∈ G.cliqueFinset 3)
    (haZ : a ∉ universalVertices G) :
    (∑ u : ↑(nonUniversalVertices G),
        d7LiftedWeight (u : A) (w u) {a, b, c}) +
      (∑ z : ↑(universalVertices G),
        d7LiftedWeight (z : A)
          (d8CoherentStrippedWeight G z₀ hxy w₀ z) {a, b, c}) +
      d8HallCorrection G P rho {a, b, c} ≤
        (((Fintype.card A - 2 : ℕ) : ℝ)) / 2 := by
  have htri := SimpleGraph.mem_cliqueFinset_iff.mp ht
  have hadj := SimpleGraph.is3Clique_triple_iff.mp htri
  have nonUniversal_of_not_universal : ∀ {v : A},
      v ∉ universalVertices G → v ∈ nonUniversalVertices G := by
    intro v hv
    apply mem_nonUniversalVertices.mpr
    have hvne : Gᶜ.degree v ≠ 0 := by
      intro hz
      exact hv (mem_universalVertices.mpr hz)
    exact Nat.pos_of_ne_zero hvne
  let ua : ↑(nonUniversalVertices G) :=
    ⟨a, nonUniversal_of_not_universal haZ⟩
  by_cases hbZ : b ∈ universalVertices G
  · let zb : ↑(universalVertices G) := ⟨b, hbZ⟩
    by_cases hcZ : c ∈ universalVertices G
    · let zc : ↑(universalVertices G) := ⟨c, hcZ⟩
      have hzbc : zb ≠ zc := fun h ↦ hbc (congrArg Subtype.val h)
      exact d8HallAverageWeight_UZZ_numerator_le
        G z₀ hxy P hreal rho hm hw₀Half w hwTop ua zb zc hzbc ht
    · let uc : ↑(nonUniversalVertices G) :=
        ⟨c, nonUniversal_of_not_universal hcZ⟩
      have huac : ua ≠ uc := fun h ↦ hac (congrArg Subtype.val h)
      have he : s(ua, uc) ∈ (G.induce
          (↑(nonUniversalVertices G) : Set A)).edgeFinset := by
        rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
        change G.Adj a c
        exact hadj.2.1
      have hset : ({(zb : A), (ua : A), (uc : A)} : Finset A) =
          ({a, b, c} : Finset A) := by
        ext q
        simp only [zb, ua, uc, Finset.mem_insert, Finset.mem_singleton]
        tauto
      have htri' : ({(zb : A), (ua : A), (uc : A)} : Finset A) ∈
          G.cliqueFinset 3 := by rw [hset]; exact ht
      have hnum := d8HallAverageWeight_UUZ_numerator_le
        G z₀ hxy P hreal hrho0 hm hw₀ hw₀Half w hwTop
        ua uc huac zb he htri'
      rwa [hset] at hnum
  · let ub : ↑(nonUniversalVertices G) :=
      ⟨b, nonUniversal_of_not_universal hbZ⟩
    by_cases hcZ : c ∈ universalVertices G
    · let zc : ↑(universalVertices G) := ⟨c, hcZ⟩
      have huab : ua ≠ ub := fun h ↦ hab (congrArg Subtype.val h)
      have he : s(ua, ub) ∈ (G.induce
          (↑(nonUniversalVertices G) : Set A)).edgeFinset := by
        rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
        change G.Adj a b
        exact hadj.1
      have hset : ({(zc : A), (ua : A), (ub : A)} : Finset A) =
          ({a, b, c} : Finset A) := by
        ext q
        simp only [zc, ua, ub, Finset.mem_insert, Finset.mem_singleton]
        tauto
      have htri' : ({(zc : A), (ua : A), (ub : A)} : Finset A) ∈
          G.cliqueFinset 3 := by rw [hset]; exact ht
      have hnum := d8HallAverageWeight_UUZ_numerator_le
        G z₀ hxy P hreal hrho0 hm hw₀ hw₀Half w hwTop
        ua ub huab zc he htri'
      rwa [hset] at hnum
    · let uc : ↑(nonUniversalVertices G) :=
        ⟨c, nonUniversal_of_not_universal hcZ⟩
      have huab : ua ≠ ub := fun h ↦ hab (congrArg Subtype.val h)
      have huac : ua ≠ uc := fun h ↦ hac (congrArg Subtype.val h)
      have hubc : ub ≠ uc := fun h ↦ hbc (congrArg Subtype.val h)
      exact d8HallAverageWeight_UUU_numerator_le
        G z₀ hxy P rho w hwTop hw₀Half ua ub uc huab huac hubc ht

lemma d8HallAverageWeight_halfBounded
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G)) {a b : A}
    (hab : Gᶜ.Adj a b)
    {w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ}
    (P : D8SeparatedParameters G)
    (hreal : P.RealizesCoherentRemovedFamily G z₀ hab w₀)
    {rho : ℝ} (hrho0 : 0 ≤ rho)
    (hm : 4 ≤ (universalVertices G).card)
    (hw₀ : IsFractionalPacking
      (d8AugmentedDeletedGraph G (z₀ : A) a b
        (d8MissingLeft_ne_universal G hab z₀)
        (d8MissingRight_ne_universal G hab z₀)) w₀)
    (hw₀Half : IsHalfBounded
      (d8AugmentedDeletedGraph G (z₀ : A) a b
        (d8MissingLeft_ne_universal G hab z₀)
        (d8MissingRight_ne_universal G hab z₀)) w₀)
    (w : ∀ u : ↑(nonUniversalVertices G),
      Finset (↑(d7DeletedFinset (u : A))) → ℝ)
    (hwTop : ∀ u : ↑(nonUniversalVertices G), IsHalfBounded
      (⊤ : SimpleGraph (↑(d7DeletedFinset (u : A)))) (w u)) :
    IsHalfBounded G (d8HallAverageWeight G z₀ hab w₀ P rho w) := by
  intro t ht
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Finset.card_eq_three.mp
    (SimpleGraph.mem_cliqueFinset_iff.mp ht).card_eq
  have finish :
      (∑ u : ↑(nonUniversalVertices G),
          d7LiftedWeight (u : A) (w u) {x, y, z}) +
        (∑ q : ↑(universalVertices G),
          d7LiftedWeight (q : A)
            (d8CoherentStrippedWeight G z₀ hab w₀ q) {x, y, z}) +
        d8HallCorrection G P rho {x, y, z} ≤
          (((Fintype.card A - 2 : ℕ) : ℝ)) / 2 →
      d8HallAverageWeight G z₀ hab w₀ P rho w {x, y, z} ≤ 1 / 2 := by
    intro hnum
    unfold d8HallAverageWeight
    let d : ℝ := ((Fintype.card A - 2 : ℕ) : ℝ)
    have hd : 0 < d := by
      dsimp only [d]
      have hparts := card_nonUniversalVertices_add_card_universalVertices G
      exact_mod_cast (Nat.sub_pos_of_lt (by omega : 2 < Fintype.card A))
    calc
      d⁻¹ * ((∑ u : ↑(nonUniversalVertices G),
            d7LiftedWeight (u : A) (w u) {x, y, z}) +
          (∑ q : ↑(universalVertices G),
            d7LiftedWeight (q : A)
              (d8CoherentStrippedWeight G z₀ hab w₀ q) {x, y, z}) +
          d8HallCorrection G P rho {x, y, z}) ≤ d⁻¹ * (d / 2) :=
        mul_le_mul_of_nonneg_left (by simpa only [d] using hnum)
          (inv_nonneg.mpr hd.le)
      _ = 1 / 2 := by field_simp [ne_of_gt hd]
  by_cases hxZ : x ∈ universalVertices G
  · apply finish
    exact d8HallAverageWeight_numerator_le_of_mem_universal_left
      G z₀ hab P hreal hrho0 hm hw₀ hw₀Half w hwTop
      hxy hxz hyz ht hxZ
  · apply finish
    exact d8HallAverageWeight_numerator_le_of_not_mem_universal_left
      G z₀ hab P hreal hrho0 hm hw₀ hw₀Half w hwTop
      hxy hxz hyz ht hxZ

/-- The Hall-adjusted average is a strong defect-four packing once the
weighted induction packings on all nonuniversal deletions have been
supplied. -/
lemma hasStrongFractionalPacking_d8HallAverageWeight
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G)) {a b : A}
    (hab : Gᶜ.Adj a b)
    {w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ}
    (P : D8SeparatedParameters G)
    (hreal : P.RealizesCoherentRemovedFamily G z₀ hab w₀)
    {rho : ℝ} (sigma : A → ℕ)
    (R : D8HallRedistribution G P rho sigma)
    (hm : 4 ≤ (universalVertices G).card)
    (hrho0 : 0 ≤ rho)
    (hrhoLe : rho ≤ ((universalVertices G).card : ℝ) * P.betaMass)
    (hsigma : ∀ u, sigma u ≤ 4)
    (hsigmaSum : 8 + rho ≤
      ∑ u ∈ nonUniversalVertices G, (sigma u : ℝ))
    (w : ∀ u : ↑(nonUniversalVertices G),
      Finset (↑(d7DeletedFinset (u : A))) → ℝ)
    (hw : ∀ u : ↑(nonUniversalVertices G), IsCapacityPacking
      (d7DeletedGraph G (u : A))
      (d8HallDeletedCapacity G P rho sigma R u) (w u))
    (hwTop : ∀ u : ↑(nonUniversalVertices G), IsCapacityPacking
      (⊤ : SimpleGraph (↑(d7DeletedFinset (u : A))))
      (d8HallDeletedCapacity G P rho sigma R u) (w u))
    (hunc : ∀ u : ↑(nonUniversalVertices G), capacityUncoveredWeight
      (⊤ : SimpleGraph (↑(d7DeletedFinset (u : A))))
      (d8HallDeletedCapacity G P rho sigma R u) (w u) ≤
        ((4 - sigma u : ℕ) : ℝ))
    (hwTopHalf : ∀ u : ↑(nonUniversalVertices G), IsHalfBounded
      (⊤ : SimpleGraph (↑(d7DeletedFinset (u : A)))) (w u))
    (hw₀ : IsFractionalPacking
      (d8AugmentedDeletedGraph G (z₀ : A) a b
        (d8MissingLeft_ne_universal G hab z₀)
        (d8MissingRight_ne_universal G hab z₀)) w₀)
    (hw₀Half : IsHalfBounded
      (d8AugmentedDeletedGraph G (z₀ : A) a b
        (d8MissingLeft_ne_universal G hab z₀)
        (d8MissingRight_ne_universal G hab z₀)) w₀)
    (hunc₀ : fractionalUncoveredWeight
      (d8AugmentedDeletedGraph G (z₀ : A) a b
        (d8MissingLeft_ne_universal G hab z₀)
        (d8MissingRight_ne_universal G hab z₀)) w₀ ≤ 4)
    (hcard : 2 < Fintype.card A) :
    HasStrongFractionalPacking G 4 := by
  exact ⟨d8HallAverageWeight G z₀ hab w₀ P rho w,
    d8HallAverageWeight_isFractionalPacking
      G z₀ hab w₀ P hreal hw₀ hm hrho0 hrhoLe sigma R w hw,
    fractionalUncoveredWeight_d8HallAverageWeight_le_four
      G z₀ hab P hreal sigma R hm hrho0 hrhoLe hsigma hsigmaSum
        w hwTop hunc hw₀ hunc₀ hcard,
    d8HallAverageWeight_halfBounded
      G z₀ hab P hreal hrho0 hm hw₀ hw₀Half w hwTopHalf⟩

private lemma exists_compl_adj_of_missingEdgeCount_eq_d8 {n : ℕ}
    (G : SimpleGraph A) (hexact : missingEdgeCount G = n) (hn : 0 < n) :
    ∃ a b : A, Gᶜ.Adj a b := by
  have hpos : 0 < Gᶜ.edgeFinset.card := by
    rw [show Gᶜ.edgeFinset.card = missingEdgeCount G from rfl, hexact]
    exact hn
  obtain ⟨e, he⟩ := Finset.card_pos.mp hpos
  induction e using Sym2.inductionOn with
  | _ a b =>
      refine ⟨a, b, ?_⟩
      simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using he

/-- Complete case D8.  The shortcut inequality and its strict complement
exhaust all possibilities; in the latter branch Claim 5.8 supplies the
Hall redistribution and weighted induction supplies every deleted packing. -/
theorem d8_case {n : ℕ}
    (hcard : Fintype.card A = n) (hn : 14 ≤ n)
    (G : SimpleGraph A) (hexact : missingEdgeCount G = n)
    (hm : 4 ≤ (universalVertices G).card)
    (hnoD5 : ∀ u : A, 3 * Gᶜ.degree u ≤ n + 4)
    (hstrong : AlmostCompleteStrongAt (n - 1)) :
    HasStrongFractionalPacking G 4 := by
  obtain ⟨z, hz⟩ := Finset.card_pos.mp
    (show 0 < (universalVertices G).card by omega)
  let z₀ : ↑(universalVertices G) := ⟨z, hz⟩
  obtain ⟨a, b, hab⟩ :=
    exists_compl_adj_of_missingEdgeCount_eq_d8 G hexact (by omega)
  obtain ⟨w₀, P, hw₀, hw₀Half, hunc₀, hsymm, _hwStrip,
      _hwStripHalf, _hidentity, _hresidual, hbeta, halpha, hgamma⟩ :=
    exists_d8SeparatedParameters_and_strippedWeight
      hcard hn G hexact z₀
        (d8MissingLeft_ne_universal G hab z₀)
        (d8MissingRight_ne_universal G hab z₀) hab hm hstrong
  have hreal : P.RealizesCoherentRemovedFamily G z₀ hab w₀ :=
    P.realizesCoherentRemovedFamily_of_eq_extracted
      G z₀ hab w₀ hm hsymm hbeta halpha hgamma
  by_cases hshortcut :
      (Fintype.card A : ℝ) + 4 - 3 * P.betaMass ≤
        3 * ((universalVertices G).card : ℝ)
  · exact hasStrongFractionalPacking_d8ShortcutAverageWeight
      G z₀ hab P hreal (hcard ▸ hn) hm hshortcut hw₀ hw₀Half hunc₀
  · have hfail : 3 * ((universalVertices G).card : ℝ) <
        (n : ℝ) + 4 - 3 * P.betaMass := by
      have hstrict : 3 * ((universalVertices G).card : ℝ) <
          (Fintype.card A : ℝ) + 4 - 3 * P.betaMass :=
        lt_of_not_ge hshortcut
      rwa [hcard] at hstrict
    obtain ⟨rho, sigma, R, hrho0, _hrhoSix, hrhoLe,
        hsigma, _hsupport, hsigmaSum⟩ :=
      exists_d8HallRedistribution
        hcard hn G hexact hm hnoD5 P hfail
    have hsigmaFour : ∀ u, sigma u ≤ 4 := by
      intro u
      exact (hsigma u).trans (Nat.min_le_left _ _)
    have hweights : ∀ u : ↑(nonUniversalVertices G),
        ∃ w : Finset (↑(d7DeletedFinset (u : A))) → ℝ,
          IsCapacityPacking (d7DeletedGraph G (u : A))
              (d8HallDeletedCapacity G P rho sigma R u) w ∧
          IsCapacityPacking (⊤ : SimpleGraph
              (↑(d7DeletedFinset (u : A))))
              (d8HallDeletedCapacity G P rho sigma R u) w ∧
          capacityUncoveredWeight (⊤ : SimpleGraph
              (↑(d7DeletedFinset (u : A))))
              (d8HallDeletedCapacity G P rho sigma R u) w ≤
                ((4 - sigma u : ℕ) : ℝ) ∧
          IsHalfBounded (⊤ : SimpleGraph
              (↑(d7DeletedFinset (u : A)))) w := by
      intro u
      exact exists_d8HallSupportedWeightedPacking
        hcard hn G hexact P sigma hsigma R hm hrho0 hrhoLe hstrong u
    choose w hw hwTop hunc hwTopHalf using hweights
    exact hasStrongFractionalPacking_d8HallAverageWeight
      G z₀ hab P hreal sigma R hm hrho0 hrhoLe hsigmaFour hsigmaSum
        w hw hwTop hunc hwTopHalf hw₀ hw₀Half hunc₀ (by omega)

end

end Erdos76
