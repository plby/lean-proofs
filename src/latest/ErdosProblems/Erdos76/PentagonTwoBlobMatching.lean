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
# Proposition 7.2(b): two blobs with a deleted matching

Let `A` and `B` be disjoint, let `f : A ↪ B`, and delete the cross pairs
`a -- f a`.  Appendix A of Gruslys--Letzter assigns weight according to the
number of common neighbours of the internal pair of a cross triangle.  We
split that weight into three constant families: pairs inside `A`, pairs of
matched vertices inside `B`, and pairs containing the (possible) unmatched
vertex of `B`.
-/

open Finset
open scoped BigOperators

namespace Erdos76

noncomputable section

attribute [local instance] Classical.propDecidable

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Cross triangles with two vertices in `A`.  The attachment `z : B` must
avoid the two forbidden partners of the vertices in the internal pair. -/
def embeddingAABFamily (A B : Finset α) (f : A ↪ B) :
    Finset (Finset α) :=
  (Finset.univ : Finset B).biUnion fun z ↦
    ((A.powersetCard 2).filter fun p ↦
      ∀ a : A, a.1 ∈ p → z ≠ f a).image (insert z.1)

/-- Cross triangles with two matched vertices in `B`. -/
def embeddingABBMatchedFamily (A B : Finset α) (f : A ↪ B) :
    Finset (Finset α) :=
  (Finset.univ : Finset A).biUnion fun a ↦
    ((B.powersetCard 2).filter fun p ↦
      (f a).1 ∉ p ∧ p ⊆ embeddingRangeFinset A B f).image (insert a.1)

/-- Cross triangles whose internal `B`-pair contains a vertex outside the
range of the matching embedding. -/
def embeddingABBUnmatchedFamily (A B : Finset α) (f : A ↪ B) :
    Finset (Finset α) :=
  (Finset.univ : Finset A).biUnion fun a ↦
    ((B.powersetCard 2).filter fun p ↦
      (f a).1 ∉ p ∧ ¬p ⊆ embeddingRangeFinset A B f).image (insert a.1)

lemma mem_embeddingAABFamily_iff
    {A B : Finset α} {f : A ↪ B} {t : Finset α} :
    t ∈ embeddingAABFamily A B f ↔
      ∃ z : B, ∃ p ∈ A.powersetCard 2,
        (∀ a : A, a.1 ∈ p → z ≠ f a) ∧ t = insert z.1 p := by
  classical
  simp only [embeddingAABFamily, mem_biUnion, mem_univ, true_and,
    mem_image, mem_filter]
  aesop

lemma mem_embeddingABBMatchedFamily_iff
    {A B : Finset α} {f : A ↪ B} {t : Finset α} :
    t ∈ embeddingABBMatchedFamily A B f ↔
      ∃ a : A, ∃ p ∈ B.powersetCard 2,
        (f a).1 ∉ p ∧ p ⊆ embeddingRangeFinset A B f ∧
          t = insert a.1 p := by
  classical
  simp only [embeddingABBMatchedFamily, mem_biUnion, mem_univ, true_and,
    mem_image, mem_filter]
  aesop

lemma mem_embeddingABBUnmatchedFamily_iff
    {A B : Finset α} {f : A ↪ B} {t : Finset α} :
    t ∈ embeddingABBUnmatchedFamily A B f ↔
      ∃ a : A, ∃ p ∈ B.powersetCard 2,
        (f a).1 ∉ p ∧ ¬p ⊆ embeddingRangeFinset A B f ∧
          t = insert a.1 p := by
  classical
  simp only [embeddingABBUnmatchedFamily, mem_biUnion, mem_univ, true_and,
    mem_image, mem_filter]
  aesop

lemma embeddingAABFamily_subset_twoOneTriangleFamily
    (A B : Finset α) (f : A ↪ B) :
    embeddingAABFamily A B f ⊆ twoOneTriangleFamily A B := by
  classical
  intro t ht
  obtain ⟨z, p, hp, _havoid, rfl⟩ := mem_embeddingAABFamily_iff.mp ht
  exact mem_twoOneTriangleFamily_iff.mpr ⟨z.1, z.2, p, hp, rfl⟩

lemma embeddingABBMatchedFamily_subset_twoOneTriangleFamily
    (A B : Finset α) (f : A ↪ B) :
    embeddingABBMatchedFamily A B f ⊆ twoOneTriangleFamily B A := by
  classical
  intro t ht
  obtain ⟨a, p, hp, _havoid, _hrange, rfl⟩ :=
    mem_embeddingABBMatchedFamily_iff.mp ht
  exact mem_twoOneTriangleFamily_iff.mpr ⟨a.1, a.2, p, hp, rfl⟩

lemma embeddingABBUnmatchedFamily_subset_twoOneTriangleFamily
    (A B : Finset α) (f : A ↪ B) :
    embeddingABBUnmatchedFamily A B f ⊆ twoOneTriangleFamily B A := by
  classical
  intro t ht
  obtain ⟨a, p, hp, _havoid, _hrange, rfl⟩ :=
    mem_embeddingABBUnmatchedFamily_iff.mp ht
  exact mem_twoOneTriangleFamily_iff.mpr ⟨a.1, a.2, p, hp, rfl⟩

lemma completeExceptEmbeddingMatching_internal_adj_left
    {A B : Finset α} (hAB : Disjoint A B) (f : A ↪ B)
    {x y : α} (hx : x ∈ A) (hy : y ∈ A) (hxy : x ≠ y) :
    (completeExceptEmbeddingMatching A B f).Adj x y := by
  classical
  rw [completeExceptEmbeddingMatching, SimpleGraph.deleteEdges_adj]
  refine ⟨by simpa using hxy, ?_⟩
  intro hmem
  obtain ⟨a, _ha, haeq⟩ := mem_image.mp hmem
  have hxmem : x ∈ s(a.1, (f a).1).toFinset := by
    have : x ∈ s(x, y).toFinset := by simp [hxy]
    exact (congrArg (fun e : Sym2 α ↦ x ∈ e.toFinset) haeq).mpr this
  have hxcases : x = a.1 ∨ x = (f a).1 := by
    simpa [Sym2.toFinset_mk_eq] using hxmem
  rcases hxcases with hxa | hxfa
  · have hymem : y ∈ s(a.1, (f a).1).toFinset := by
      have : y ∈ s(x, y).toFinset := by simp [hxy]
      exact (congrArg (fun e : Sym2 α ↦ y ∈ e.toFinset) haeq).mpr this
    have hycases : y = a.1 ∨ y = (f a).1 := by
      simpa [Sym2.toFinset_mk_eq] using hymem
    rcases hycases with hya | hyfa
    · exact hxy (hxa.trans hya.symm)
    · exact Finset.disjoint_left.mp hAB hy (hyfa ▸ (f a).2)
  · exact Finset.disjoint_left.mp hAB hx (hxfa ▸ (f a).2)

lemma completeExceptEmbeddingMatching_internal_adj_right
    {A B : Finset α} (hAB : Disjoint A B) (f : A ↪ B)
    {x y : α} (hx : x ∈ B) (hy : y ∈ B) (hxy : x ≠ y) :
    (completeExceptEmbeddingMatching A B f).Adj x y := by
  classical
  rw [completeExceptEmbeddingMatching, SimpleGraph.deleteEdges_adj]
  refine ⟨by simpa using hxy, ?_⟩
  intro hmem
  obtain ⟨a, _ha, haeq⟩ := mem_image.mp hmem
  have hxmem : x ∈ s(a.1, (f a).1).toFinset := by
    have : x ∈ s(x, y).toFinset := by simp [hxy]
    exact (congrArg (fun e : Sym2 α ↦ x ∈ e.toFinset) haeq).mpr this
  have hxcases : x = a.1 ∨ x = (f a).1 := by
    simpa [Sym2.toFinset_mk_eq] using hxmem
  rcases hxcases with hxa | hxfa
  · exact Finset.disjoint_left.mp hAB (hxa ▸ a.2) hx
  · have hymem : y ∈ s(a.1, (f a).1).toFinset := by
      have : y ∈ s(x, y).toFinset := by simp [hxy]
      exact (congrArg (fun e : Sym2 α ↦ y ∈ e.toFinset) haeq).mpr this
    have hycases : y = a.1 ∨ y = (f a).1 := by
      simpa [Sym2.toFinset_mk_eq] using hymem
    rcases hycases with hya | hyfa
    · exact Finset.disjoint_left.mp hAB (hya ▸ a.2) hy
    · apply hxy
      calc
        x = (f a).1 := hxfa
        _ = y := hyfa.symm

lemma embeddingAABFamily_isNClique
    {A B : Finset α} (hAB : Disjoint A B) (f : A ↪ B) :
    ∀ t ∈ embeddingAABFamily A B f,
      (completeExceptEmbeddingMatching A B f).IsNClique 3 t := by
  classical
  intro t ht
  obtain ⟨z, p, hp, havoid, rfl⟩ := mem_embeddingAABFamily_iff.mp ht
  rcases mem_powersetCard.mp hp with ⟨hpA, hpcard⟩
  obtain ⟨x, y, hxy, rfl⟩ := card_eq_two.mp hpcard
  have hxA : x ∈ A := hpA (by simp)
  have hyA : y ∈ A := hpA (by simp)
  let ax : A := ⟨x, hxA⟩
  let ay : A := ⟨y, hyA⟩
  have hzx : z ≠ f ax := havoid ax (by simp [ax])
  have hzy : z ≠ f ay := havoid ay (by simp [ay])
  have hzA : z.1 ∉ A := fun hzA ↦ Finset.disjoint_left.mp hAB hzA z.2
  have hzx' : z.1 ≠ x := fun h ↦ hzA (h ▸ hxA)
  have hzy' : z.1 ≠ y := fun h ↦ hzA (h ▸ hyA)
  rw [SimpleGraph.isNClique_iff]
  refine ⟨?_, by simp [hxy, hzx', hzy']⟩
  rw [coe_insert, SimpleGraph.isClique_insert]
  constructor
  · rw [coe_insert, coe_singleton]
    exact Set.pairwise_pair.mpr fun _ ↦
      ⟨completeExceptEmbeddingMatching_internal_adj_left hAB f hxA hyA hxy,
        completeExceptEmbeddingMatching_internal_adj_left hAB f hyA hxA hxy.symm⟩
  · intro u hu hzu
    have huCases : u = x ∨ u = y := by simpa using hu
    rcases huCases with rfl | rfl
    · exact (completeExceptEmbeddingMatching_cross_adj hAB f ax z).2 hzx |>.symm
    · exact (completeExceptEmbeddingMatching_cross_adj hAB f ay z).2 hzy |>.symm

private lemma embeddingABBFamily_isNClique_of_mem
    {A B : Finset α} (hAB : Disjoint A B) (f : A ↪ B)
    (a : A) {p : Finset α} (hp : p ∈ B.powersetCard 2)
    (havoid : (f a).1 ∉ p) :
    (completeExceptEmbeddingMatching A B f).IsNClique 3 (insert a.1 p) := by
  classical
  rcases mem_powersetCard.mp hp with ⟨hpB, hpcard⟩
  obtain ⟨x, y, hxy, rfl⟩ := card_eq_two.mp hpcard
  have hxB : x ∈ B := hpB (by simp)
  have hyB : y ∈ B := hpB (by simp)
  have hafx : (f a).1 ≠ x := by simpa [hxy] using fun h ↦ havoid (by simp [h])
  have hafy : (f a).1 ≠ y := by simpa [hxy] using fun h ↦ havoid (by simp [h])
  let bx : B := ⟨x, hxB⟩
  let byy : B := ⟨y, hyB⟩
  have hax : bx ≠ f a := fun h ↦ hafx (Subtype.ext_iff.mp h).symm
  have hay : byy ≠ f a := fun h ↦ hafy (Subtype.ext_iff.mp h).symm
  have haB : a.1 ∉ B := fun haB ↦ Finset.disjoint_left.mp hAB a.2 haB
  have hax' : a.1 ≠ x := fun h ↦ haB (h ▸ hxB)
  have hay' : a.1 ≠ y := fun h ↦ haB (h ▸ hyB)
  rw [SimpleGraph.isNClique_iff]
  refine ⟨?_, by simp [hxy, hax', hay']⟩
  rw [coe_insert, SimpleGraph.isClique_insert]
  constructor
  · rw [coe_insert, coe_singleton]
    exact Set.pairwise_pair.mpr fun _ ↦
      ⟨completeExceptEmbeddingMatching_internal_adj_right hAB f hxB hyB hxy,
        completeExceptEmbeddingMatching_internal_adj_right hAB f hyB hxB hxy.symm⟩
  · intro u hu hau
    have huCases : u = x ∨ u = y := by simpa using hu
    rcases huCases with rfl | rfl
    · exact (completeExceptEmbeddingMatching_cross_adj hAB f a bx).2 hax
    · exact (completeExceptEmbeddingMatching_cross_adj hAB f a byy).2 hay

lemma embeddingABBMatchedFamily_isNClique
    {A B : Finset α} (hAB : Disjoint A B) (f : A ↪ B) :
    ∀ t ∈ embeddingABBMatchedFamily A B f,
      (completeExceptEmbeddingMatching A B f).IsNClique 3 t := by
  classical
  intro t ht
  obtain ⟨a, p, hp, havoid, _hrange, rfl⟩ :=
    mem_embeddingABBMatchedFamily_iff.mp ht
  exact embeddingABBFamily_isNClique_of_mem hAB f a hp havoid

lemma embeddingABBUnmatchedFamily_isNClique
    {A B : Finset α} (hAB : Disjoint A B) (f : A ↪ B) :
    ∀ t ∈ embeddingABBUnmatchedFamily A B f,
      (completeExceptEmbeddingMatching A B f).IsNClique 3 t := by
  classical
  intro t ht
  obtain ⟨a, p, hp, havoid, _hrange, rfl⟩ :=
    mem_embeddingABBUnmatchedFamily_iff.mp ht
  exact embeddingABBFamily_isNClique_of_mem hAB f a hp havoid

/-! ## Exact loads on internal pairs -/

/-- The two matching partners in `B` of a pair contained in `A`. -/
def embeddingPairRange {A B : Finset α} (f : A ↪ B)
    (p : Finset α) (hp : p ⊆ A) : Finset B :=
  p.attach.image fun x ↦ f ⟨x.1, hp x.2⟩

lemma mem_embeddingPairRange_iff
    {A B : Finset α} (f : A ↪ B) (p : Finset α) (hp : p ⊆ A)
    (z : B) :
    z ∈ embeddingPairRange f p hp ↔
      ∃ a : A, a.1 ∈ p ∧ z = f a := by
  classical
  constructor
  · intro hz
    obtain ⟨x, hx, hzx⟩ := mem_image.mp hz
    exact ⟨⟨x.1, hp x.2⟩, x.2, hzx.symm⟩
  · rintro ⟨a, ha, rfl⟩
    apply mem_image.mpr
    refine ⟨⟨a.1, ha⟩, mem_attach _ _, ?_⟩
    exact congrArg f (Subtype.ext rfl)

lemma card_embeddingPairRange
    {A B : Finset α} (f : A ↪ B) (p : Finset α) (hp : p ⊆ A) :
    (embeddingPairRange f p hp).card = p.card := by
  classical
  rw [embeddingPairRange]
  calc
    (p.attach.image fun x ↦ f ⟨x.1, hp x.2⟩).card = p.attach.card := by
      apply card_image_of_injOn
      intro x _ y _ hxy
      have hsub : (⟨x.1, hp x.2⟩ : A) = ⟨y.1, hp y.2⟩ := f.injective hxy
      exact Subtype.ext (congrArg (fun a : A ↦ a.1) hsub)
    _ = p.card := card_attach

lemma avoid_embeddingPairRange_iff
    {A B : Finset α} (f : A ↪ B) (p : Finset α) (hp : p ⊆ A)
    (z : B) :
    z ∈ (Finset.univ : Finset B) \ embeddingPairRange f p hp ↔
      ∀ a : A, a.1 ∈ p → z ≠ f a := by
  classical
  rw [mem_sdiff]
  simp only [mem_univ, true_and]
  constructor
  · intro hz a ha hza
    exact hz ((mem_embeddingPairRange_iff f p hp z).2 ⟨a, ha, hza⟩)
  · intro havoid hz
    obtain ⟨a, ha, hza⟩ := (mem_embeddingPairRange_iff f p hp z).1 hz
    exact havoid a ha hza

lemma card_avoid_embeddingPairRange
    {A B : Finset α} (f : A ↪ B) (p : Finset α) (hp : p ⊆ A) :
    ((Finset.univ : Finset B) \ embeddingPairRange f p hp).card =
      B.card - p.card := by
  classical
  rw [card_sdiff_of_subset (subset_univ _), card_embeddingPairRange]
  simp

lemma filter_embeddingAABFamily_of_edge_subset_left
    {A B : Finset α} (hAB : Disjoint A B) (f : A ↪ B)
    (e : Sym2 α) (hecard : e.toFinset.card = 2)
    (heA : e.toFinset ⊆ A) :
    (embeddingAABFamily A B f).filter (fun t ↦ e ∈ t.sym2) =
      ((Finset.univ : Finset B) \ embeddingPairRange f e.toFinset heA).image
        (fun z ↦ insert z.1 e.toFinset) := by
  classical
  ext t
  constructor
  · intro ht
    rcases mem_filter.mp ht with ⟨htF, het⟩
    have htTwo : t ∈ twoOneTriangleFamily A B :=
      embeddingAABFamily_subset_twoOneTriangleFamily A B f htF
    have htFiltered : t ∈
        (twoOneTriangleFamily A B).filter (fun u ↦ e ∈ u.sym2) :=
      mem_filter.mpr ⟨htTwo, het⟩
    rw [filter_twoOne_of_edge_subset_base hAB e hecard heA] at htFiltered
    obtain ⟨z, hzB, hzt⟩ := mem_image.mp htFiltered
    let zz : B := ⟨z, hzB⟩
    obtain ⟨z', p, hp, havoid, htEq⟩ := mem_embeddingAABFamily_iff.mp htF
    have hz'T : z'.1 ∈ t := by rw [htEq]; simp
    have hz'Cases : z'.1 = z ∨ z'.1 ∈ e.toFinset := by
      rw [← hzt] at hz'T
      exact mem_insert.mp hz'T
    have hz'z : z'.1 = z := hz'Cases.resolve_right fun hz'e ↦
      Finset.disjoint_left.mp hAB (heA hz'e) z'.2
    have hzz : z' = zz := Subtype.ext hz'z
    subst z'
    have hpEq : p = e.toFinset := by
      have htEq' : insert z p = insert z e.toFinset := htEq.symm.trans hzt.symm
      have hzP : z ∉ p := fun hzP ↦
        Finset.disjoint_left.mp hAB
          ((mem_powersetCard.mp hp).1 hzP) hzB
      have hzE : z ∉ e.toFinset := fun hzE ↦
        Finset.disjoint_left.mp hAB (heA hzE) hzB
      simpa [hzP, hzE] using congrArg (fun u : Finset α ↦ u.erase z) htEq'
    subst p
    exact mem_image.mpr
      ⟨zz, (avoid_embeddingPairRange_iff f e.toFinset heA zz).2 havoid,
        by simpa [zz] using hzt⟩
  · intro ht
    obtain ⟨z, hzAvoid, rfl⟩ := mem_image.mp ht
    apply mem_filter.mpr
    refine ⟨mem_embeddingAABFamily_iff.mpr
      ⟨z, e.toFinset, mem_powersetCard.mpr ⟨heA, hecard⟩,
        (avoid_embeddingPairRange_iff f e.toFinset heA z).1 hzAvoid, rfl⟩, ?_⟩
    exact mem_sym2_iff.mpr fun x hx ↦ mem_insert_of_mem (by simpa using hx)

lemma card_filter_embeddingAABFamily_of_edge_subset_left
    {A B : Finset α} (hAB : Disjoint A B) (f : A ↪ B)
    (e : Sym2 α) (hecard : e.toFinset.card = 2)
    (heA : e.toFinset ⊆ A) :
    ((embeddingAABFamily A B f).filter fun t ↦ e ∈ t.sym2).card =
      B.card - 2 := by
  classical
  rw [filter_embeddingAABFamily_of_edge_subset_left hAB f e hecard heA]
  calc
    (((Finset.univ : Finset B) \ embeddingPairRange f e.toFinset heA).image
        (fun z ↦ insert z.1 e.toFinset)).card =
        ((Finset.univ : Finset B) \ embeddingPairRange f e.toFinset heA).card := by
      apply card_image_of_injOn
      intro z _ w _ hzw
      have hzE : z.1 ∉ e.toFinset := fun hzE ↦
        Finset.disjoint_left.mp hAB (heA hzE) z.2
      have hwE : w.1 ∉ e.toFinset := fun hwE ↦
        Finset.disjoint_left.mp hAB (heA hwE) w.2
      change insert z.1 e.toFinset = insert w.1 e.toFinset at hzw
      have hzmem : z.1 ∈ insert w.1 e.toFinset := by
        rw [← hzw]
        exact mem_insert_self _ _
      rcases mem_insert.mp hzmem with h | h
      · exact Subtype.ext h
      · exact (hzE h).elim
    _ = B.card - e.toFinset.card := card_avoid_embeddingPairRange f _ heA
    _ = B.card - 2 := by rw [hecard]

/-- Matching indices whose partners lie in a prescribed set of `B`. -/
def embeddingPairPreimage {A B : Finset α} (f : A ↪ B)
    (p : Finset α) : Finset A :=
  (Finset.univ : Finset A).filter fun a ↦ (f a).1 ∈ p

lemma card_embeddingPairPreimage
    {A B : Finset α} (f : A ↪ B) (p : Finset α) :
    (embeddingPairPreimage f p).card =
      (p ∩ embeddingRangeFinset A B f).card := by
  classical
  apply Finset.card_bij (fun a _ha ↦ (f a).1)
  · intro a ha
    have hfa : (f a).1 ∈ p := (mem_filter.mp ha).2
    exact mem_inter.mpr ⟨hfa, mem_embeddingRangeFinset A B f a⟩
  · intro a ha b hb hab
    exact f.injective (Subtype.ext hab)
  · intro z hz
    rcases mem_inter.mp hz with ⟨hzp, hzrange⟩
    obtain ⟨a, _ha, hfa⟩ := mem_image.mp hzrange
    refine ⟨a, mem_filter.mpr ⟨mem_univ _, ?_⟩, hfa⟩
    simpa [hfa] using hzp

lemma card_avoid_embeddingPairPreimage
    {A B : Finset α} (f : A ↪ B) (p : Finset α) :
    ((Finset.univ : Finset A) \ embeddingPairPreimage f p).card =
      A.card - (p ∩ embeddingRangeFinset A B f).card := by
  classical
  rw [card_sdiff_of_subset (subset_univ _), card_embeddingPairPreimage]
  simp

lemma filter_embeddingABBMatchedFamily_of_edge_subset_right
    {A B : Finset α} (hAB : Disjoint A B) (f : A ↪ B)
    (e : Sym2 α) (hecard : e.toFinset.card = 2)
    (heB : e.toFinset ⊆ B)
    (heRange : e.toFinset ⊆ embeddingRangeFinset A B f) :
    (embeddingABBMatchedFamily A B f).filter (fun t ↦ e ∈ t.sym2) =
      ((Finset.univ : Finset A) \ embeddingPairPreimage f e.toFinset).image
        (fun a ↦ insert a.1 e.toFinset) := by
  classical
  ext t
  constructor
  · intro ht
    rcases mem_filter.mp ht with ⟨htF, het⟩
    have htTwo : t ∈ twoOneTriangleFamily B A :=
      embeddingABBMatchedFamily_subset_twoOneTriangleFamily A B f htF
    have htFiltered : t ∈
        (twoOneTriangleFamily B A).filter (fun u ↦ e ∈ u.sym2) :=
      mem_filter.mpr ⟨htTwo, het⟩
    rw [filter_twoOne_of_edge_subset_base hAB.symm e hecard heB] at htFiltered
    obtain ⟨a, haA, hat⟩ := mem_image.mp htFiltered
    let aa : A := ⟨a, haA⟩
    obtain ⟨a', p, hp, havoid, _hrange, htEq⟩ :=
      mem_embeddingABBMatchedFamily_iff.mp htF
    have ha'T : a'.1 ∈ t := by rw [htEq]; simp
    have ha'Cases : a'.1 = a ∨ a'.1 ∈ e.toFinset := by
      rw [← hat] at ha'T
      exact mem_insert.mp ha'T
    have ha'a : a'.1 = a := ha'Cases.resolve_right fun ha'e ↦
      Finset.disjoint_left.mp hAB a'.2 (heB ha'e)
    have haa : a' = aa := Subtype.ext ha'a
    subst a'
    have hpEq : p = e.toFinset := by
      have htEq' : insert a p = insert a e.toFinset := htEq.symm.trans hat.symm
      have haP : a ∉ p := fun haP ↦
        Finset.disjoint_left.mp hAB haA ((mem_powersetCard.mp hp).1 haP)
      have haE : a ∉ e.toFinset := fun haE ↦
        Finset.disjoint_left.mp hAB haA (heB haE)
      simpa [haP, haE] using congrArg (fun u : Finset α ↦ u.erase a) htEq'
    subst p
    have haaAvoid : aa ∈ (Finset.univ : Finset A) \
        embeddingPairPreimage f e.toFinset := by
      exact mem_sdiff.mpr ⟨mem_univ _, fun hpre ↦
        havoid (mem_filter.mp hpre).2⟩
    exact mem_image.mpr ⟨aa, haaAvoid, by simpa [aa] using hat⟩
  · intro ht
    obtain ⟨a, haAvoid, rfl⟩ := mem_image.mp ht
    have hfa : (f a).1 ∉ e.toFinset := by
      simpa [embeddingPairPreimage] using haAvoid
    apply mem_filter.mpr
    refine ⟨mem_embeddingABBMatchedFamily_iff.mpr
      ⟨a, e.toFinset, mem_powersetCard.mpr ⟨heB, hecard⟩,
        hfa, heRange, rfl⟩, ?_⟩
    exact mem_sym2_iff.mpr fun x hx ↦ mem_insert_of_mem (by simpa using hx)

lemma card_filter_embeddingABBMatchedFamily_of_edge_subset_right
    {A B : Finset α} (hAB : Disjoint A B) (f : A ↪ B)
    (e : Sym2 α) (hecard : e.toFinset.card = 2)
    (heB : e.toFinset ⊆ B)
    (heRange : e.toFinset ⊆ embeddingRangeFinset A B f) :
    ((embeddingABBMatchedFamily A B f).filter fun t ↦ e ∈ t.sym2).card =
      A.card - 2 := by
  classical
  rw [filter_embeddingABBMatchedFamily_of_edge_subset_right
    hAB f e hecard heB heRange]
  calc
    (((Finset.univ : Finset A) \ embeddingPairPreimage f e.toFinset).image
        (fun a ↦ insert a.1 e.toFinset)).card =
        ((Finset.univ : Finset A) \ embeddingPairPreimage f e.toFinset).card := by
      apply card_image_of_injOn
      intro a _ b _ hab
      have haE : a.1 ∉ e.toFinset := fun haE ↦
        Finset.disjoint_left.mp hAB a.2 (heB haE)
      change insert a.1 e.toFinset = insert b.1 e.toFinset at hab
      have hamem : a.1 ∈ insert b.1 e.toFinset := by
        rw [← hab]
        exact mem_insert_self _ _
      rcases mem_insert.mp hamem with h | h
      · exact Subtype.ext h
      · exact (haE h).elim
    _ = A.card - (e.toFinset ∩ embeddingRangeFinset A B f).card :=
      card_avoid_embeddingPairPreimage f _
    _ = A.card - 2 := by
      rw [inter_eq_left.mpr heRange, hecard]

lemma filter_embeddingABBUnmatchedFamily_of_edge_subset_right
    {A B : Finset α} (hAB : Disjoint A B) (f : A ↪ B)
    (e : Sym2 α) (hecard : e.toFinset.card = 2)
    (heB : e.toFinset ⊆ B)
    (heRange : ¬e.toFinset ⊆ embeddingRangeFinset A B f) :
    (embeddingABBUnmatchedFamily A B f).filter (fun t ↦ e ∈ t.sym2) =
      ((Finset.univ : Finset A) \ embeddingPairPreimage f e.toFinset).image
        (fun a ↦ insert a.1 e.toFinset) := by
  classical
  ext t
  constructor
  · intro ht
    rcases mem_filter.mp ht with ⟨htF, het⟩
    have htTwo : t ∈ twoOneTriangleFamily B A :=
      embeddingABBUnmatchedFamily_subset_twoOneTriangleFamily A B f htF
    have htFiltered : t ∈
        (twoOneTriangleFamily B A).filter (fun u ↦ e ∈ u.sym2) :=
      mem_filter.mpr ⟨htTwo, het⟩
    rw [filter_twoOne_of_edge_subset_base hAB.symm e hecard heB] at htFiltered
    obtain ⟨a, haA, hat⟩ := mem_image.mp htFiltered
    let aa : A := ⟨a, haA⟩
    obtain ⟨a', p, hp, havoid, _hrange, htEq⟩ :=
      mem_embeddingABBUnmatchedFamily_iff.mp htF
    have ha'T : a'.1 ∈ t := by rw [htEq]; simp
    have ha'Cases : a'.1 = a ∨ a'.1 ∈ e.toFinset := by
      rw [← hat] at ha'T
      exact mem_insert.mp ha'T
    have ha'a : a'.1 = a := ha'Cases.resolve_right fun ha'e ↦
      Finset.disjoint_left.mp hAB a'.2 (heB ha'e)
    have haa : a' = aa := Subtype.ext ha'a
    subst a'
    have hpEq : p = e.toFinset := by
      have htEq' : insert a p = insert a e.toFinset := htEq.symm.trans hat.symm
      have haP : a ∉ p := fun haP ↦
        Finset.disjoint_left.mp hAB haA ((mem_powersetCard.mp hp).1 haP)
      have haE : a ∉ e.toFinset := fun haE ↦
        Finset.disjoint_left.mp hAB haA (heB haE)
      simpa [haP, haE] using congrArg (fun u : Finset α ↦ u.erase a) htEq'
    subst p
    have haaAvoid : aa ∈ (Finset.univ : Finset A) \
        embeddingPairPreimage f e.toFinset := by
      exact mem_sdiff.mpr ⟨mem_univ _, fun hpre ↦
        havoid (mem_filter.mp hpre).2⟩
    exact mem_image.mpr ⟨aa, haaAvoid, by simpa [aa] using hat⟩
  · intro ht
    obtain ⟨a, haAvoid, rfl⟩ := mem_image.mp ht
    have hfa : (f a).1 ∉ e.toFinset := by
      simpa [embeddingPairPreimage] using haAvoid
    apply mem_filter.mpr
    refine ⟨mem_embeddingABBUnmatchedFamily_iff.mpr
      ⟨a, e.toFinset, mem_powersetCard.mpr ⟨heB, hecard⟩,
        hfa, heRange, rfl⟩, ?_⟩
    exact mem_sym2_iff.mpr fun x hx ↦ mem_insert_of_mem (by simpa using hx)

lemma card_filter_embeddingABBUnmatchedFamily_of_edge_subset_right
    {A B : Finset α} (hAB : Disjoint A B) (f : A ↪ B)
    (e : Sym2 α) (hecard : e.toFinset.card = 2)
    (heB : e.toFinset ⊆ B)
    (heRange : ¬e.toFinset ⊆ embeddingRangeFinset A B f) :
    ((embeddingABBUnmatchedFamily A B f).filter fun t ↦ e ∈ t.sym2).card =
      A.card - (e.toFinset ∩ embeddingRangeFinset A B f).card := by
  classical
  rw [filter_embeddingABBUnmatchedFamily_of_edge_subset_right
    hAB f e hecard heB heRange]
  calc
    (((Finset.univ : Finset A) \ embeddingPairPreimage f e.toFinset).image
        (fun a ↦ insert a.1 e.toFinset)).card =
        ((Finset.univ : Finset A) \ embeddingPairPreimage f e.toFinset).card := by
      apply card_image_of_injOn
      intro a _ b _ hab
      have haE : a.1 ∉ e.toFinset := fun haE ↦
        Finset.disjoint_left.mp hAB a.2 (heB haE)
      change insert a.1 e.toFinset = insert b.1 e.toFinset at hab
      have hamem : a.1 ∈ insert b.1 e.toFinset := by
        rw [← hab]
        exact mem_insert_self _ _
      rcases mem_insert.mp hamem with h | h
      · exact Subtype.ext h
      · exact (haE h).elim
    _ = A.card - (e.toFinset ∩ embeddingRangeFinset A B f).card :=
      card_avoid_embeddingPairPreimage f _

lemma card_inter_embeddingRange_eq_one_of_pair_not_subset
    {A B : Finset α} (f : A ↪ B)
    (hBle : B.card ≤ A.card + 1)
    (p : Finset α) (hpB : p ⊆ B) (hpcard : p.card = 2)
    (hpRange : ¬p ⊆ embeddingRangeFinset A B f) :
    (p ∩ embeddingRangeFinset A B f).card = 1 := by
  classical
  have hdiffNonempty : (p \ embeddingRangeFinset A B f).Nonempty := by
    obtain ⟨x, hxp, hxnot⟩ :
        ∃ x ∈ p, x ∉ embeddingRangeFinset A B f := by
      simpa [Finset.subset_iff] using hpRange
    exact ⟨x, mem_sdiff.mpr ⟨hxp, hxnot⟩⟩
  have hdiffSub : p \ embeddingRangeFinset A B f ⊆
      B \ embeddingRangeFinset A B f := by
    intro x hx
    exact mem_sdiff.mpr ⟨hpB (mem_sdiff.mp hx).1, (mem_sdiff.mp hx).2⟩
  have hdiffLe : (p \ embeddingRangeFinset A B f).card ≤ 1 :=
    (card_le_card hdiffSub).trans
      (card_unmatched_embeddingRange_le_one hBle f)
  have hdiffCard : (p \ embeddingRangeFinset A B f).card = 1 := by
    have : 0 < (p \ embeddingRangeFinset A B f).card := card_pos.mpr hdiffNonempty
    omega
  have hsplit :
      (p ∩ embeddingRangeFinset A B f).card +
          (p \ embeddingRangeFinset A B f).card = p.card :=
    card_inter_add_card_sdiff p (embeddingRangeFinset A B f)
  omega

/-- The Appendix A weight for Proposition 7.2(b). -/
def proposition72bWeight (A B : Finset α) (f : A ↪ B) :
    Finset α → ℝ :=
  addTriangleWeight
    (constantTriangleFamilyWeight (embeddingAABFamily A B f)
      (2 * (B.card - 2)))
    (addTriangleWeight
      (constantTriangleFamilyWeight (embeddingABBMatchedFamily A B f)
        (2 * (A.card - 2)))
      (constantTriangleFamilyWeight (embeddingABBUnmatchedFamily A B f)
        (2 * (A.card - 1))))

private lemma card_filter_family_eq_zero_of_subset_twoOne_attachment
    {A B : Finset α} {F : Finset (Finset α)} (hAB : Disjoint A B)
    (hF : F ⊆ twoOneTriangleFamily A B)
    (e : Sym2 α) (hecard : e.toFinset.card = 2)
    (heB : e.toFinset ⊆ B) :
    (F.filter fun t ↦ e ∈ t.sym2).card = 0 := by
  classical
  rw [card_eq_zero]
  apply eq_empty_iff_forall_notMem.mpr
  intro t ht
  have htBig : t ∈
      (twoOneTriangleFamily A B).filter (fun u ↦ e ∈ u.sym2) :=
    mem_filter.mpr ⟨hF (mem_filter.mp ht).1, (mem_filter.mp ht).2⟩
  have hzero := card_filter_twoOne_eq_zero_of_edge_subset_attachment
    hAB e hecard heB
  have hempty :
      (twoOneTriangleFamily A B).filter (fun u ↦ e ∈ u.sym2) = ∅ :=
    card_eq_zero.mp hzero
  rw [hempty] at htBig
  simp at htBig

private lemma constant_family_load_eq_half_of_card_sub_two
    {G : SimpleGraph α} {F : Finset (Finset α)} {n : ℕ}
    (hn : 3 ≤ n) (htri : ∀ t ∈ F, G.IsNClique 3 t)
    {e : Sym2 α} (hcard : (F.filter fun t ↦ e ∈ t.sym2).card = n - 2) :
    fractionalEdgeLoad G (constantTriangleFamilyWeight F (2 * (n - 2))) e =
      1 / 2 := by
  rw [fractionalEdgeLoad_constantTriangleFamilyWeight htri, hcard]
  have hn2N : 0 < n - 2 := by omega
  have hn2 : (0 : ℝ) < ((n - 2 : ℕ) : ℝ) := by exact_mod_cast hn2N
  push_cast only [Nat.cast_mul, Nat.cast_ofNat]
  field_simp

private lemma constant_family_load_eq_half_of_card_sub_one
    {G : SimpleGraph α} {F : Finset (Finset α)} {n : ℕ}
    (hn : 2 ≤ n) (htri : ∀ t ∈ F, G.IsNClique 3 t)
    {e : Sym2 α} (hcard : (F.filter fun t ↦ e ∈ t.sym2).card = n - 1) :
    fractionalEdgeLoad G (constantTriangleFamilyWeight F (2 * (n - 1))) e =
      1 / 2 := by
  rw [fractionalEdgeLoad_constantTriangleFamilyWeight htri, hcard]
  have hn1N : 0 < n - 1 := by omega
  have hn1 : (0 : ℝ) < ((n - 1 : ℕ) : ℝ) := by exact_mod_cast hn1N
  push_cast only [Nat.cast_mul, Nat.cast_ofNat]
  field_simp

private lemma constant_family_load_eq_zero_of_card_zero
    {G : SimpleGraph α} {F : Finset (Finset α)} {d : ℕ}
    (htri : ∀ t ∈ F, G.IsNClique 3 t)
    {e : Sym2 α} (hcard : (F.filter fun t ↦ e ∈ t.sym2).card = 0) :
    fractionalEdgeLoad G (constantTriangleFamilyWeight F d) e = 0 := by
  rw [fractionalEdgeLoad_constantTriangleFamilyWeight htri, hcard]
  simp

lemma fractionalEdgeLoad_proposition72bWeight_of_subset_left
    {A B : Finset α} (hAB : Disjoint A B) (f : A ↪ B)
    (hAcard : 3 ≤ A.card) (hAleB : A.card ≤ B.card)
    {e : Sym2 α} (hecard : e.toFinset.card = 2)
    (heA : e.toFinset ⊆ A) :
    fractionalEdgeLoad (completeExceptEmbeddingMatching A B f)
      (proposition72bWeight A B f) e = 1 / 2 := by
  classical
  let G := completeExceptEmbeddingMatching A B f
  let FA := embeddingAABFamily A B f
  let FM := embeddingABBMatchedFamily A B f
  let FU := embeddingABBUnmatchedFamily A B f
  have hBcard : 3 ≤ B.card := hAcard.trans hAleB
  have htriA : ∀ t ∈ FA, G.IsNClique 3 t :=
    embeddingAABFamily_isNClique hAB f
  have htriM : ∀ t ∈ FM, G.IsNClique 3 t :=
    embeddingABBMatchedFamily_isNClique hAB f
  have htriU : ∀ t ∈ FU, G.IsNClique 3 t :=
    embeddingABBUnmatchedFamily_isNClique hAB f
  have hcardA : (FA.filter fun t ↦ e ∈ t.sym2).card = B.card - 2 := by
    simpa only [FA] using
      card_filter_embeddingAABFamily_of_edge_subset_left hAB f e hecard heA
  have hcardM : (FM.filter fun t ↦ e ∈ t.sym2).card = 0 := by
    apply card_filter_family_eq_zero_of_subset_twoOne_attachment
      hAB.symm (embeddingABBMatchedFamily_subset_twoOneTriangleFamily A B f)
      e hecard heA
  have hcardU : (FU.filter fun t ↦ e ∈ t.sym2).card = 0 := by
    apply card_filter_family_eq_zero_of_subset_twoOne_attachment
      hAB.symm (embeddingABBUnmatchedFamily_subset_twoOneTriangleFamily A B f)
      e hecard heA
  rw [proposition72bWeight,
    show addTriangleWeight _ _ = (fun t ↦ _ + _) by rfl,
    fractionalEdgeLoad_add,
    show addTriangleWeight _ _ = (fun t ↦ _ + _) by rfl,
    fractionalEdgeLoad_add]
  have hloadA := constant_family_load_eq_half_of_card_sub_two
    hBcard htriA hcardA
  have hloadM := constant_family_load_eq_zero_of_card_zero
    (d := 2 * (A.card - 2)) htriM hcardM
  have hloadU := constant_family_load_eq_zero_of_card_zero
    (d := 2 * (A.card - 1)) htriU hcardU
  change fractionalEdgeLoad G
        (constantTriangleFamilyWeight FA (2 * (B.card - 2))) e +
      (fractionalEdgeLoad G
          (constantTriangleFamilyWeight FM (2 * (A.card - 2))) e +
        fractionalEdgeLoad G
          (constantTriangleFamilyWeight FU (2 * (A.card - 1))) e) = 1 / 2
  rw [hloadA, hloadM, hloadU]
  norm_num

lemma fractionalEdgeLoad_proposition72bWeight_of_subset_right
    {A B : Finset α} (hAB : Disjoint A B) (f : A ↪ B)
    (hAcard : 3 ≤ A.card) (hBle : B.card ≤ A.card + 1)
    {e : Sym2 α} (hecard : e.toFinset.card = 2)
    (heB : e.toFinset ⊆ B) :
    fractionalEdgeLoad (completeExceptEmbeddingMatching A B f)
      (proposition72bWeight A B f) e = 1 / 2 := by
  classical
  let G := completeExceptEmbeddingMatching A B f
  let FA := embeddingAABFamily A B f
  let FM := embeddingABBMatchedFamily A B f
  let FU := embeddingABBUnmatchedFamily A B f
  have htriA : ∀ t ∈ FA, G.IsNClique 3 t :=
    embeddingAABFamily_isNClique hAB f
  have htriM : ∀ t ∈ FM, G.IsNClique 3 t :=
    embeddingABBMatchedFamily_isNClique hAB f
  have htriU : ∀ t ∈ FU, G.IsNClique 3 t :=
    embeddingABBUnmatchedFamily_isNClique hAB f
  have hcardA : (FA.filter fun t ↦ e ∈ t.sym2).card = 0 := by
    apply card_filter_family_eq_zero_of_subset_twoOne_attachment hAB
      (embeddingAABFamily_subset_twoOneTriangleFamily A B f) e hecard heB
  by_cases heRange : e.toFinset ⊆ embeddingRangeFinset A B f
  · have hcardM : (FM.filter fun t ↦ e ∈ t.sym2).card = A.card - 2 := by
      simpa only [FM] using
        card_filter_embeddingABBMatchedFamily_of_edge_subset_right
          hAB f e hecard heB heRange
    have hcardU : (FU.filter fun t ↦ e ∈ t.sym2).card = 0 := by
      rw [card_eq_zero]
      apply eq_empty_iff_forall_notMem.mpr
      intro t ht
      have hpEq : ∀ a' : A, ∀ p' ∈ B.powersetCard 2,
          (f a').1 ∉ p' → ¬p' ⊆ embeddingRangeFinset A B f →
          t = insert a'.1 p' → p' = e.toFinset := by
        intro a' p' hp' _hav' _hnr' ht'
        have htTwo : t ∈ twoOneTriangleFamily B A :=
          embeddingABBUnmatchedFamily_subset_twoOneTriangleFamily A B f
            (mem_filter.mp ht).1
        have htBig : t ∈ (twoOneTriangleFamily B A).filter
            (fun u ↦ e ∈ u.sym2) :=
          mem_filter.mpr ⟨htTwo, (mem_filter.mp ht).2⟩
        rw [filter_twoOne_of_edge_subset_base hAB.symm e hecard heB] at htBig
        obtain ⟨a, ha, hat⟩ := mem_image.mp htBig
        have haT : a'.1 ∈ t := by rw [ht']; simp
        have haa : a'.1 = a := (by
          rcases (by rw [← hat] at haT; exact mem_insert.mp haT) with h | h
          · exact h
          · exact (Finset.disjoint_left.mp hAB a'.2 (heB h)).elim)
        subst a
        have haP : a'.1 ∉ p' := fun h ↦
          Finset.disjoint_left.mp hAB a'.2 ((mem_powersetCard.mp hp').1 h)
        have haE : a'.1 ∉ e.toFinset := fun h ↦
          Finset.disjoint_left.mp hAB a'.2 (heB h)
        simpa [haP, haE] using congrArg (fun u : Finset α ↦ u.erase a'.1)
          (ht'.symm.trans hat.symm)
      obtain ⟨a', p', hp', hav', hpNot, ht'⟩ :=
        mem_embeddingABBUnmatchedFamily_iff.mp (mem_filter.mp ht).1
      exact hpNot ((hpEq a' p' hp' hav' hpNot ht') ▸ heRange)
    rw [proposition72bWeight,
      show addTriangleWeight _ _ = (fun t ↦ _ + _) by rfl,
      fractionalEdgeLoad_add,
      show addTriangleWeight _ _ = (fun t ↦ _ + _) by rfl,
      fractionalEdgeLoad_add]
    have hloadA := constant_family_load_eq_zero_of_card_zero
      (d := 2 * (B.card - 2)) htriA hcardA
    have hloadM := constant_family_load_eq_half_of_card_sub_two
      hAcard htriM hcardM
    have hloadU := constant_family_load_eq_zero_of_card_zero
      (d := 2 * (A.card - 1)) htriU hcardU
    change fractionalEdgeLoad G
          (constantTriangleFamilyWeight FA (2 * (B.card - 2))) e +
        (fractionalEdgeLoad G
            (constantTriangleFamilyWeight FM (2 * (A.card - 2))) e +
          fractionalEdgeLoad G
            (constantTriangleFamilyWeight FU (2 * (A.card - 1))) e) = 1 / 2
    rw [hloadA, hloadM, hloadU]
    norm_num

  · have hinter :
        (e.toFinset ∩ embeddingRangeFinset A B f).card = 1 :=
      card_inter_embeddingRange_eq_one_of_pair_not_subset
        f hBle e.toFinset heB hecard heRange
    have hcardM : (FM.filter fun t ↦ e ∈ t.sym2).card = 0 := by
      rw [card_eq_zero]
      apply eq_empty_iff_forall_notMem.mpr
      intro t ht
      have htTwo : t ∈ twoOneTriangleFamily B A :=
        embeddingABBMatchedFamily_subset_twoOneTriangleFamily A B f
          (mem_filter.mp ht).1
      have htBig : t ∈ (twoOneTriangleFamily B A).filter
          (fun u ↦ e ∈ u.sym2) :=
        mem_filter.mpr ⟨htTwo, (mem_filter.mp ht).2⟩
      rw [filter_twoOne_of_edge_subset_base hAB.symm e hecard heB] at htBig
      obtain ⟨a, ha, hat⟩ := mem_image.mp htBig
      obtain ⟨a', p', hp', _hav', hrange', ht'⟩ :=
        mem_embeddingABBMatchedFamily_iff.mp (mem_filter.mp ht).1
      have haT : a'.1 ∈ t := by rw [ht']; simp
      have haa : a'.1 = a := (by
        rcases (by rw [← hat] at haT; exact mem_insert.mp haT) with h | h
        · exact h
        · exact (Finset.disjoint_left.mp hAB a'.2 (heB h)).elim)
      subst a
      have haP : a'.1 ∉ p' := fun h ↦
        Finset.disjoint_left.mp hAB a'.2 ((mem_powersetCard.mp hp').1 h)
      have haE : a'.1 ∉ e.toFinset := fun h ↦
        Finset.disjoint_left.mp hAB a'.2 (heB h)
      have hpEq : p' = e.toFinset := by
        simpa [haP, haE] using congrArg (fun u : Finset α ↦ u.erase a'.1)
          (ht'.symm.trans hat.symm)
      exact heRange (hpEq ▸ hrange')
    have hcardU : (FU.filter fun t ↦ e ∈ t.sym2).card = A.card - 1 := by
      rw [show (FU.filter fun t ↦ e ∈ t.sym2).card =
          A.card - (e.toFinset ∩ embeddingRangeFinset A B f).card by
        simpa only [FU] using
          card_filter_embeddingABBUnmatchedFamily_of_edge_subset_right
            hAB f e hecard heB heRange]
      rw [hinter]
    rw [proposition72bWeight,
      show addTriangleWeight _ _ = (fun t ↦ _ + _) by rfl,
      fractionalEdgeLoad_add,
      show addTriangleWeight _ _ = (fun t ↦ _ + _) by rfl,
      fractionalEdgeLoad_add]
    have hloadA := constant_family_load_eq_zero_of_card_zero
      (d := 2 * (B.card - 2)) htriA hcardA
    have hloadM := constant_family_load_eq_zero_of_card_zero
      (d := 2 * (A.card - 2)) htriM hcardM
    have hloadU := constant_family_load_eq_half_of_card_sub_one
      (by omega : 2 ≤ A.card) htriU hcardU
    change fractionalEdgeLoad G
          (constantTriangleFamilyWeight FA (2 * (B.card - 2))) e +
        (fractionalEdgeLoad G
            (constantTriangleFamilyWeight FM (2 * (A.card - 2))) e +
          fractionalEdgeLoad G
            (constantTriangleFamilyWeight FU (2 * (A.card - 1))) e) = 1 / 2
    rw [hloadA, hloadM, hloadU]
    norm_num

/-! ## Exact loads on surviving cross pairs -/

def embeddingAABCrossPairs {A B : Finset α} (f : A ↪ B)
    (a : A) (b : B) : Finset (Finset α) :=
  (A.powersetCard 2).filter fun p ↦
    a.1 ∈ p ∧ ∀ x : A, x.1 ∈ p → b ≠ f x

def embeddingAABOtherCandidates {A B : Finset α} (f : A ↪ B)
    (a : A) (b : B) : Finset A :=
  ((Finset.univ : Finset A).erase a).filter fun x ↦ b ≠ f x

lemma embeddingAABCrossPairs_eq_image
    {A B : Finset α} (f : A ↪ B) (a : A) (b : B)
    (hba : b ≠ f a) :
    embeddingAABCrossPairs f a b =
      (embeddingAABOtherCandidates f a b).image
        (fun x ↦ {a.1, x.1}) := by
  classical
  ext p
  constructor
  · intro hp
    rcases mem_filter.mp hp with ⟨hpPow, haP, havoid⟩
    rcases mem_powersetCard.mp hpPow with ⟨hpA, hpCard⟩
    have heraseCard : (p.erase a.1).card = 1 := by
      rw [card_erase_of_mem haP, hpCard]
    obtain ⟨x, hxErase⟩ := card_eq_one.mp heraseCard
    have hxP : x ∈ p := by
      have : x ∈ p.erase a.1 := by simp [hxErase]
      exact (mem_erase.mp this).2
    have hxA : x ∈ A := hpA hxP
    let xx : A := ⟨x, hxA⟩
    have hxa : xx ≠ a := by
      intro h
      have : x = a.1 := Subtype.ext_iff.mp h
      subst x
      simpa using (mem_erase.mp (by simp [hxErase] : a.1 ∈ p.erase a.1)).1
    have hpEq : p = {a.1, x} := by
      rw [← insert_erase haP, hxErase]
    have hxxCand : xx ∈ embeddingAABOtherCandidates f a b := by
      apply mem_filter.mpr
      refine ⟨mem_erase.mpr ⟨hxa, mem_univ _⟩, ?_⟩
      exact havoid xx hxP
    exact mem_image.mpr ⟨xx, hxxCand, by simpa [xx, hpEq]⟩
  · intro hp
    obtain ⟨x, hxCand, rfl⟩ := mem_image.mp hp
    rcases mem_filter.mp hxCand with ⟨hxaUniv, hbx⟩
    have hxa : x ≠ a := (mem_erase.mp hxaUniv).1
    have haxVal : a.1 ≠ x.1 := fun h ↦ hxa (Subtype.ext h.symm)
    apply mem_filter.mpr
    refine ⟨mem_powersetCard.mpr ⟨?_, by simp [haxVal]⟩,
      mem_insert_self _ _, ?_⟩
    · intro y hy
      rcases mem_insert.mp hy with h | h
      · simpa [h] using a.2
      · have hyx : y = x.1 := by simpa using h
        simpa [hyx] using x.2
    · intro y hy
      have hyCases : y = a ∨ y = x := by
        have : y.1 = a.1 ∨ y.1 = x.1 := by simpa using hy
        rcases this with h | h
        · exact Or.inl (Subtype.ext h)
        · exact Or.inr (Subtype.ext h)
      rcases hyCases with rfl | rfl
      · exact hba
      · exact hbx

lemma card_embeddingAABOtherCandidates
    {A B : Finset α} (f : A ↪ B) (a : A) (b : B)
    (hba : b ≠ f a) :
    (embeddingAABOtherCandidates f a b).card =
      if b.1 ∈ embeddingRangeFinset A B f then A.card - 2
      else A.card - 1 := by
  classical
  by_cases hbRange : b.1 ∈ embeddingRangeFinset A B f
  · rw [if_pos hbRange]
    obtain ⟨c, _hc, hfc⟩ := mem_image.mp hbRange
    have hfcb : f c = b := Subtype.ext hfc
    have hca : c ≠ a := by
      intro h
      apply hba
      simpa [h] using hfcb.symm
    have hset : embeddingAABOtherCandidates f a b =
        ((Finset.univ : Finset A).erase a).erase c := by
      ext x
      simp only [embeddingAABOtherCandidates, mem_filter, mem_erase, mem_univ,
        and_true]
      constructor
      · rintro ⟨hxa, hbx⟩
        refine ⟨?_, hxa⟩
        intro hxc
        apply hbx
        subst x
        exact hfcb.symm
      · rintro ⟨hxc, hxa⟩
        refine ⟨hxa, ?_⟩
        intro hbx
        apply hxc
        apply f.injective
        exact hbx.symm.trans hfcb.symm
    rw [hset, card_erase_of_mem (by simp [hca]), card_erase_of_mem (by simp)]
    rw [card_univ, Fintype.card_coe]
    omega
  · rw [if_neg hbRange]
    have hset : embeddingAABOtherCandidates f a b =
        (Finset.univ : Finset A).erase a := by
      ext x
      simp only [embeddingAABOtherCandidates, mem_filter]
      constructor
      · exact And.left
      · intro hx
        refine ⟨hx, ?_⟩
        intro hbx
        apply hbRange
        have : b = f x := hbx
        simpa [this] using mem_embeddingRangeFinset A B f x
    rw [hset, card_erase_of_mem (mem_univ _)]
    simp

lemma card_embeddingAABCrossPairs
    {A B : Finset α} (f : A ↪ B) (a : A) (b : B)
    (hba : b ≠ f a) :
    (embeddingAABCrossPairs f a b).card =
      if b.1 ∈ embeddingRangeFinset A B f then A.card - 2
      else A.card - 1 := by
  classical
  rw [embeddingAABCrossPairs_eq_image f a b hba]
  rw [card_image_of_injOn]
  · exact card_embeddingAABOtherCandidates f a b hba
  · intro x hx y hy hxy
    have hxa : x ≠ a := (mem_erase.mp (mem_filter.mp hx).1).1
    have hya : y ≠ a := (mem_erase.mp (mem_filter.mp hy).1).1
    change ({a.1, x.1} : Finset α) = {a.1, y.1} at hxy
    have hxmem : x.1 ∈ ({a.1, y.1} : Finset α) := by
      rw [← hxy]
      simp
    rcases mem_insert.mp hxmem with h | h
    · exact (hxa (Subtype.ext h)).elim
    · exact Subtype.ext (by simpa using h)

lemma filter_embeddingAABFamily_cross
    {A B : Finset α} (hAB : Disjoint A B) (f : A ↪ B)
    (a : A) (b : B) :
    (embeddingAABFamily A B f).filter
        (fun t ↦ s(a.1, b.1) ∈ t.sym2) =
      (embeddingAABCrossPairs f a b).image (insert b.1) := by
  classical
  have hab : a.1 ≠ b.1 := fun h ↦
    Finset.disjoint_left.mp hAB a.2 (h ▸ b.2)
  ext t
  constructor
  · intro ht
    rcases mem_filter.mp ht with ⟨htF, het⟩
    obtain ⟨z, p, hp, havoid, htEq⟩ := mem_embeddingAABFamily_iff.mp htF
    have hbT : b.1 ∈ t :=
      (mem_sym2_iff.mp het) b.1 (by simp [hab])
    have hzEq : z.1 = b.1 := by
      rw [htEq] at hbT
      rcases mem_insert.mp hbT with h | h
      · exact h.symm
      · exact (Finset.disjoint_left.mp hAB
          ((mem_powersetCard.mp hp).1 h) b.2).elim
    have hz : z = b := Subtype.ext hzEq
    subst z
    have haT : a.1 ∈ t :=
      (mem_sym2_iff.mp het) a.1 (by simp [hab])
    have haP : a.1 ∈ p := by
      rw [htEq] at haT
      rcases mem_insert.mp haT with h | h
      · exact (hab h).elim
      · exact h
    exact mem_image.mpr
      ⟨p, mem_filter.mpr ⟨hp, haP, havoid⟩, htEq.symm⟩
  · intro ht
    obtain ⟨p, hp, rfl⟩ := mem_image.mp ht
    rcases mem_filter.mp hp with ⟨hpPow, haP, havoid⟩
    apply mem_filter.mpr
    refine ⟨mem_embeddingAABFamily_iff.mpr
      ⟨b, p, hpPow, havoid, rfl⟩, ?_⟩
    apply mem_sym2_iff.mpr
    intro x hx
    have hxCases : x = a.1 ∨ x = b.1 := by
      simpa [hab] using hx
    rcases hxCases with rfl | rfl
    · exact mem_insert_of_mem haP
    · exact mem_insert_self _ _

lemma card_filter_embeddingAABFamily_cross
    {A B : Finset α} (hAB : Disjoint A B) (f : A ↪ B)
    (a : A) (b : B) (hba : b ≠ f a) :
    ((embeddingAABFamily A B f).filter
      (fun t ↦ s(a.1, b.1) ∈ t.sym2)).card =
        if b.1 ∈ embeddingRangeFinset A B f then A.card - 2
        else A.card - 1 := by
  classical
  rw [filter_embeddingAABFamily_cross hAB f a b]
  rw [card_image_of_injOn]
  · exact card_embeddingAABCrossPairs f a b hba
  · intro p hp q hq hpq
    have hbP : b.1 ∉ p := fun h ↦
      Finset.disjoint_left.mp hAB ((mem_powersetCard.mp (mem_filter.mp hp).1).1 h) b.2
    have hbQ : b.1 ∉ q := fun h ↦
      Finset.disjoint_left.mp hAB ((mem_powersetCard.mp (mem_filter.mp hq).1).1 h) b.2
    simpa [hbP, hbQ] using congrArg (fun u : Finset α ↦ u.erase b.1) hpq

def embeddingABBAllCrossPairs {A B : Finset α} (f : A ↪ B)
    (a : A) (b : B) : Finset (Finset α) :=
  (B.powersetCard 2).filter fun p ↦ b.1 ∈ p ∧ (f a).1 ∉ p

def embeddingABBOtherCandidates {A B : Finset α} (f : A ↪ B)
    (a : A) (b : B) : Finset B :=
  (((Finset.univ : Finset B).erase b).erase (f a))

def embeddingABBCrossPairsMatched {A B : Finset α} (f : A ↪ B)
    (a : A) (b : B) : Finset (Finset α) :=
  (embeddingABBAllCrossPairs f a b).filter fun p ↦
    p ⊆ embeddingRangeFinset A B f

def embeddingABBCrossPairsUnmatched {A B : Finset α} (f : A ↪ B)
    (a : A) (b : B) : Finset (Finset α) :=
  (embeddingABBAllCrossPairs f a b).filter fun p ↦
    ¬p ⊆ embeddingRangeFinset A B f

lemma embeddingABBAllCrossPairs_eq_image
    {A B : Finset α} (f : A ↪ B) (a : A) (b : B)
    (hba : b ≠ f a) :
    embeddingABBAllCrossPairs f a b =
      (embeddingABBOtherCandidates f a b).image
        (fun z ↦ {b.1, z.1}) := by
  classical
  ext p
  constructor
  · intro hp
    rcases mem_filter.mp hp with ⟨hpPow, hbP, hfaP⟩
    rcases mem_powersetCard.mp hpPow with ⟨hpB, hpCard⟩
    have heraseCard : (p.erase b.1).card = 1 := by
      rw [card_erase_of_mem hbP, hpCard]
    obtain ⟨z, hzErase⟩ := card_eq_one.mp heraseCard
    have hzP : z ∈ p := by
      have : z ∈ p.erase b.1 := by simp [hzErase]
      exact (mem_erase.mp this).2
    have hzB : z ∈ B := hpB hzP
    let zz : B := ⟨z, hzB⟩
    have hzb : zz ≠ b := by
      intro h
      have : z = b.1 := Subtype.ext_iff.mp h
      subst z
      simpa using (mem_erase.mp (by simp [hzErase] : b.1 ∈ p.erase b.1)).1
    have hzfa : zz ≠ f a := by
      intro h
      have hval : z = (f a).1 := congrArg Subtype.val h
      exact hfaP (hval ▸ hzP)
    have hpEq : p = {b.1, z} := by
      rw [← insert_erase hbP, hzErase]
    have hzzCand : zz ∈ embeddingABBOtherCandidates f a b := by
      exact mem_erase.mpr ⟨hzfa, mem_erase.mpr ⟨hzb, mem_univ _⟩⟩
    exact mem_image.mpr ⟨zz, hzzCand, by simpa [zz, hpEq]⟩
  · intro hp
    obtain ⟨z, hzCand, rfl⟩ := mem_image.mp hp
    have hzfa : z ≠ f a := (mem_erase.mp hzCand).1
    have hzb : z ≠ b := (mem_erase.mp (mem_erase.mp hzCand).2).1
    have hbzVal : b.1 ≠ z.1 := fun h ↦ hzb (Subtype.ext h.symm)
    apply mem_filter.mpr
    refine ⟨mem_powersetCard.mpr ⟨?_, by simp [hbzVal]⟩,
      mem_insert_self _ _, ?_⟩
    · intro x hx
      have hxCases : x = b.1 ∨ x = z.1 := by simpa using hx
      rcases hxCases with rfl | rfl
      · exact b.2
      · exact z.2
    · intro hfaMem
      have hcases : (f a).1 = b.1 ∨ (f a).1 = z.1 := by
        simpa using hfaMem
      rcases hcases with h | h
      · exact hba (Subtype.ext h.symm)
      · exact hzfa (Subtype.ext h.symm)

lemma embeddingABBCrossPairsMatched_eq_image
    {A B : Finset α} (f : A ↪ B) (a : A) (b : B)
    (hba : b ≠ f a) :
    embeddingABBCrossPairsMatched f a b =
      ((embeddingABBOtherCandidates f a b).filter fun z ↦
        b.1 ∈ embeddingRangeFinset A B f ∧
          z.1 ∈ embeddingRangeFinset A B f).image
        (fun z ↦ {b.1, z.1}) := by
  classical
  rw [embeddingABBCrossPairsMatched, embeddingABBAllCrossPairs_eq_image f a b hba]
  ext p
  constructor
  · intro hp
    rcases mem_filter.mp hp with ⟨hpImage, hpRange⟩
    obtain ⟨z, hzCand, rfl⟩ := mem_image.mp hpImage
    have hbRange : b.1 ∈ embeddingRangeFinset A B f := hpRange (by simp)
    have hzRange : z.1 ∈ embeddingRangeFinset A B f := hpRange (by simp)
    exact mem_image.mpr ⟨z, mem_filter.mpr ⟨hzCand, hbRange, hzRange⟩, rfl⟩
  · intro hp
    obtain ⟨z, hz, rfl⟩ := mem_image.mp hp
    rcases mem_filter.mp hz with ⟨hzCand, hbRange, hzRange⟩
    exact mem_filter.mpr
      ⟨mem_image.mpr ⟨z, hzCand, rfl⟩, by
        intro x hx
        have hxCases : x = b.1 ∨ x = z.1 := by simpa using hx
        rcases hxCases with rfl | rfl
        · exact hbRange
        · exact hzRange⟩

lemma embeddingABBCrossPairsUnmatched_eq_image
    {A B : Finset α} (f : A ↪ B) (a : A) (b : B)
    (hba : b ≠ f a) :
    embeddingABBCrossPairsUnmatched f a b =
      ((embeddingABBOtherCandidates f a b).filter fun z ↦
        ¬(b.1 ∈ embeddingRangeFinset A B f ∧
          z.1 ∈ embeddingRangeFinset A B f)).image
        (fun z ↦ {b.1, z.1}) := by
  classical
  rw [embeddingABBCrossPairsUnmatched, embeddingABBAllCrossPairs_eq_image f a b hba]
  ext p
  constructor
  · intro hp
    rcases mem_filter.mp hp with ⟨hpImage, hpNot⟩
    obtain ⟨z, hzCand, rfl⟩ := mem_image.mp hpImage
    have hnot : ¬(b.1 ∈ embeddingRangeFinset A B f ∧
        z.1 ∈ embeddingRangeFinset A B f) := by
      intro h
      apply hpNot
      intro x hx
      have hxCases : x = b.1 ∨ x = z.1 := by simpa using hx
      rcases hxCases with rfl | rfl
      · exact h.1
      · exact h.2
    exact mem_image.mpr ⟨z, mem_filter.mpr ⟨hzCand, hnot⟩, rfl⟩
  · intro hp
    obtain ⟨z, hz, rfl⟩ := mem_image.mp hp
    rcases mem_filter.mp hz with ⟨hzCand, hnot⟩
    exact mem_filter.mpr
      ⟨mem_image.mpr ⟨z, hzCand, rfl⟩, by
        intro hpRange
        exact hnot ⟨hpRange (by simp), hpRange (by simp)⟩⟩

def embeddingRangeSubtypeFinset {A B : Finset α} (f : A ↪ B) : Finset B :=
  (Finset.univ : Finset A).image f

lemma mem_embeddingRangeSubtypeFinset_iff
    {A B : Finset α} (f : A ↪ B) (b : B) :
    b ∈ embeddingRangeSubtypeFinset f ↔
      b.1 ∈ embeddingRangeFinset A B f := by
  classical
  simp [embeddingRangeSubtypeFinset, embeddingRangeFinset]

lemma card_embeddingRangeSubtypeFinset
    {A B : Finset α} (f : A ↪ B) :
    (embeddingRangeSubtypeFinset f).card = A.card := by
  classical
  rw [embeddingRangeSubtypeFinset, card_image_of_injOn]
  · simp
  · intro x _ y _ h
    exact f.injective h

lemma card_embeddingABBCrossPairsMatched
    {A B : Finset α} (f : A ↪ B) (a : A) (b : B)
    (hba : b ≠ f a) :
    (embeddingABBCrossPairsMatched f a b).card =
      if b.1 ∈ embeddingRangeFinset A B f then A.card - 2 else 0 := by
  classical
  rw [embeddingABBCrossPairsMatched_eq_image f a b hba,
    card_image_of_injOn]
  · by_cases hbRange : b.1 ∈ embeddingRangeFinset A B f
    · rw [if_pos hbRange]
      have hfilter :
          (embeddingABBOtherCandidates f a b).filter (fun z ↦
              b.1 ∈ embeddingRangeFinset A B f ∧
                z.1 ∈ embeddingRangeFinset A B f) =
            ((embeddingRangeSubtypeFinset f).erase b).erase (f a) := by
        ext z
        simp only [mem_filter, embeddingABBOtherCandidates, mem_erase]
        rw [mem_embeddingRangeSubtypeFinset_iff]
        simp [hbRange, and_assoc]
      rw [hfilter, card_erase_of_mem, card_erase_of_mem,
        card_embeddingRangeSubtypeFinset]
      · omega
      · exact (mem_embeddingRangeSubtypeFinset_iff f b).2 hbRange
      · have hfaRange := mem_embeddingRangeFinset A B f a
        exact mem_erase.mpr
          ⟨hba.symm, (mem_embeddingRangeSubtypeFinset_iff f (f a)).2 hfaRange⟩
    · rw [if_neg hbRange, card_eq_zero]
      apply eq_empty_iff_forall_notMem.mpr
      intro z hz
      exact hbRange (mem_filter.mp hz).2.1
  · intro z hz w hw hzw
    have hzb : z ≠ b := (mem_erase.mp (mem_erase.mp (mem_filter.mp hz).1).2).1
    change ({b.1, z.1} : Finset α) = {b.1, w.1} at hzw
    have hzmem : z.1 ∈ ({b.1, w.1} : Finset α) := by
      rw [← hzw]
      simp
    rcases mem_insert.mp hzmem with h | h
    · exact (hzb (Subtype.ext h)).elim
    · exact Subtype.ext (by simpa using h)

lemma card_embeddingABBCrossPairsUnmatched
    {A B : Finset α} (f : A ↪ B) (a : A) (b : B)
    (hba : b ≠ f a) (hBle : B.card ≤ A.card + 1) :
    (embeddingABBCrossPairsUnmatched f a b).card =
      if b.1 ∈ embeddingRangeFinset A B f then B.card - A.card
      else A.card - 1 := by
  classical
  rw [embeddingABBCrossPairsUnmatched_eq_image f a b hba,
    card_image_of_injOn]
  · by_cases hbRange : b.1 ∈ embeddingRangeFinset A B f
    · rw [if_pos hbRange]
      have hfilter :
          (embeddingABBOtherCandidates f a b).filter (fun z ↦
              ¬(b.1 ∈ embeddingRangeFinset A B f ∧
                z.1 ∈ embeddingRangeFinset A B f)) =
            (Finset.univ : Finset B) \ embeddingRangeSubtypeFinset f := by
        ext z
        simp only [mem_filter, embeddingABBOtherCandidates, mem_erase,
          mem_sdiff, mem_univ, true_and]
        rw [mem_embeddingRangeSubtypeFinset_iff]
        constructor
        · rintro ⟨_hzbase, hnot⟩
          exact fun hzRange ↦ hnot ⟨hbRange, hzRange⟩
        · intro hzNot
          refine ⟨⟨?_, ?_, trivial⟩, ?_⟩
          · intro hzfa
            apply hzNot
            simpa [hzfa] using mem_embeddingRangeFinset A B f a
          · intro hzb
            apply hzNot
            simpa [hzb] using hbRange
          · exact fun h ↦ hzNot h.2
      rw [hfilter, card_sdiff_of_subset (subset_univ _),
        card_embeddingRangeSubtypeFinset]
      simp
    · rw [if_neg hbRange]
      have hfilter :
          (embeddingABBOtherCandidates f a b).filter (fun z ↦
              ¬(b.1 ∈ embeddingRangeFinset A B f ∧
                z.1 ∈ embeddingRangeFinset A B f)) =
            embeddingABBOtherCandidates f a b := by
        apply filter_true_of_mem
        intro z hz
        exact fun h ↦ hbRange h.1
      have hAleB : A.card ≤ B.card := by
        rw [← card_embeddingRangeFinset A B f]
        exact card_le_card (embeddingRangeFinset_subset A B f)
      have hbDiff : b.1 ∈ B \ embeddingRangeFinset A B f :=
        mem_sdiff.mpr ⟨b.2, hbRange⟩
      have hdiffPos : 0 < (B \ embeddingRangeFinset A B f).card :=
        card_pos.mpr ⟨b.1, hbDiff⟩
      have hBcard : B.card = A.card + 1 := by
        rw [card_sdiff_of_subset (embeddingRangeFinset_subset A B f),
          card_embeddingRangeFinset] at hdiffPos
        omega
      rw [hfilter, embeddingABBOtherCandidates,
        card_erase_of_mem, card_erase_of_mem, card_univ, Fintype.card_coe]
      · omega
      · exact mem_univ _
      · exact mem_erase.mpr ⟨hba.symm, mem_univ _⟩
  · intro z hz w hw hzw
    have hzb : z ≠ b := (mem_erase.mp (mem_erase.mp (mem_filter.mp hz).1).2).1
    change ({b.1, z.1} : Finset α) = {b.1, w.1} at hzw
    have hzmem : z.1 ∈ ({b.1, w.1} : Finset α) := by
      rw [← hzw]
      simp
    rcases mem_insert.mp hzmem with h | h
    · exact (hzb (Subtype.ext h)).elim
    · exact Subtype.ext (by simpa using h)

lemma filter_embeddingABBMatchedFamily_cross
    {A B : Finset α} (hAB : Disjoint A B) (f : A ↪ B)
    (a : A) (b : B) :
    (embeddingABBMatchedFamily A B f).filter
        (fun t ↦ s(a.1, b.1) ∈ t.sym2) =
      (embeddingABBCrossPairsMatched f a b).image (insert a.1) := by
  classical
  have hab : a.1 ≠ b.1 := fun h ↦
    Finset.disjoint_left.mp hAB a.2 (h ▸ b.2)
  ext t
  constructor
  · intro ht
    rcases mem_filter.mp ht with ⟨htF, het⟩
    obtain ⟨a', p, hp, havoid, hpRange, htEq⟩ :=
      mem_embeddingABBMatchedFamily_iff.mp htF
    have haT : a.1 ∈ t :=
      (mem_sym2_iff.mp het) a.1 (by simp [hab])
    have haEq : a'.1 = a.1 := by
      rw [htEq] at haT
      rcases mem_insert.mp haT with h | h
      · exact h.symm
      · exact (Finset.disjoint_left.mp hAB a.2
          ((mem_powersetCard.mp hp).1 h)).elim
    have haa : a' = a := Subtype.ext haEq
    subst a'
    have hbT : b.1 ∈ t :=
      (mem_sym2_iff.mp het) b.1 (by simp [hab])
    have hbP : b.1 ∈ p := by
      rw [htEq] at hbT
      rcases mem_insert.mp hbT with h | h
      · exact (hab h.symm).elim
      · exact h
    exact mem_image.mpr
      ⟨p, mem_filter.mpr
        ⟨mem_filter.mpr ⟨hp, hbP, havoid⟩, hpRange⟩, htEq.symm⟩
  · intro ht
    obtain ⟨p, hp, rfl⟩ := mem_image.mp ht
    rcases mem_filter.mp hp with ⟨hpAll, hpRange⟩
    rcases mem_filter.mp hpAll with ⟨hpPow, hbP, havoid⟩
    apply mem_filter.mpr
    refine ⟨mem_embeddingABBMatchedFamily_iff.mpr
      ⟨a, p, hpPow, havoid, hpRange, rfl⟩, ?_⟩
    apply mem_sym2_iff.mpr
    intro x hx
    have hxCases : x = a.1 ∨ x = b.1 := by simpa [hab] using hx
    rcases hxCases with rfl | rfl
    · exact mem_insert_self _ _
    · exact mem_insert_of_mem hbP

lemma filter_embeddingABBUnmatchedFamily_cross
    {A B : Finset α} (hAB : Disjoint A B) (f : A ↪ B)
    (a : A) (b : B) :
    (embeddingABBUnmatchedFamily A B f).filter
        (fun t ↦ s(a.1, b.1) ∈ t.sym2) =
      (embeddingABBCrossPairsUnmatched f a b).image (insert a.1) := by
  classical
  have hab : a.1 ≠ b.1 := fun h ↦
    Finset.disjoint_left.mp hAB a.2 (h ▸ b.2)
  ext t
  constructor
  · intro ht
    rcases mem_filter.mp ht with ⟨htF, het⟩
    obtain ⟨a', p, hp, havoid, hpRange, htEq⟩ :=
      mem_embeddingABBUnmatchedFamily_iff.mp htF
    have haT : a.1 ∈ t :=
      (mem_sym2_iff.mp het) a.1 (by simp [hab])
    have haEq : a'.1 = a.1 := by
      rw [htEq] at haT
      rcases mem_insert.mp haT with h | h
      · exact h.symm
      · exact (Finset.disjoint_left.mp hAB a.2
          ((mem_powersetCard.mp hp).1 h)).elim
    have haa : a' = a := Subtype.ext haEq
    subst a'
    have hbT : b.1 ∈ t :=
      (mem_sym2_iff.mp het) b.1 (by simp [hab])
    have hbP : b.1 ∈ p := by
      rw [htEq] at hbT
      rcases mem_insert.mp hbT with h | h
      · exact (hab h.symm).elim
      · exact h
    exact mem_image.mpr
      ⟨p, mem_filter.mpr
        ⟨mem_filter.mpr ⟨hp, hbP, havoid⟩, hpRange⟩, htEq.symm⟩
  · intro ht
    obtain ⟨p, hp, rfl⟩ := mem_image.mp ht
    rcases mem_filter.mp hp with ⟨hpAll, hpRange⟩
    rcases mem_filter.mp hpAll with ⟨hpPow, hbP, havoid⟩
    apply mem_filter.mpr
    refine ⟨mem_embeddingABBUnmatchedFamily_iff.mpr
      ⟨a, p, hpPow, havoid, hpRange, rfl⟩, ?_⟩
    apply mem_sym2_iff.mpr
    intro x hx
    have hxCases : x = a.1 ∨ x = b.1 := by simpa [hab] using hx
    rcases hxCases with rfl | rfl
    · exact mem_insert_self _ _
    · exact mem_insert_of_mem hbP

lemma card_filter_embeddingABBMatchedFamily_cross
    {A B : Finset α} (hAB : Disjoint A B) (f : A ↪ B)
    (a : A) (b : B) (hba : b ≠ f a) :
    ((embeddingABBMatchedFamily A B f).filter
      (fun t ↦ s(a.1, b.1) ∈ t.sym2)).card =
        if b.1 ∈ embeddingRangeFinset A B f then A.card - 2 else 0 := by
  classical
  rw [filter_embeddingABBMatchedFamily_cross hAB f a b,
    card_image_of_injOn]
  · exact card_embeddingABBCrossPairsMatched f a b hba
  · intro p hp q hq hpq
    have haP : a.1 ∉ p := fun h ↦
      Finset.disjoint_left.mp hAB a.2
        ((mem_powersetCard.mp (mem_filter.mp (mem_filter.mp hp).1).1).1 h)
    have haQ : a.1 ∉ q := fun h ↦
      Finset.disjoint_left.mp hAB a.2
        ((mem_powersetCard.mp (mem_filter.mp (mem_filter.mp hq).1).1).1 h)
    simpa [haP, haQ] using congrArg (fun u : Finset α ↦ u.erase a.1) hpq

lemma card_filter_embeddingABBUnmatchedFamily_cross
    {A B : Finset α} (hAB : Disjoint A B) (f : A ↪ B)
    (a : A) (b : B) (hba : b ≠ f a) (hBle : B.card ≤ A.card + 1) :
    ((embeddingABBUnmatchedFamily A B f).filter
      (fun t ↦ s(a.1, b.1) ∈ t.sym2)).card =
        if b.1 ∈ embeddingRangeFinset A B f then B.card - A.card
        else A.card - 1 := by
  classical
  rw [filter_embeddingABBUnmatchedFamily_cross hAB f a b,
    card_image_of_injOn]
  · exact card_embeddingABBCrossPairsUnmatched f a b hba hBle
  · intro p hp q hq hpq
    have haP : a.1 ∉ p := fun h ↦
      Finset.disjoint_left.mp hAB a.2
        ((mem_powersetCard.mp (mem_filter.mp (mem_filter.mp hp).1).1).1 h)
    have haQ : a.1 ∉ q := fun h ↦
      Finset.disjoint_left.mp hAB a.2
        ((mem_powersetCard.mp (mem_filter.mp (mem_filter.mp hq).1).1).1 h)
    simpa [haP, haQ] using congrArg (fun u : Finset α ↦ u.erase a.1) hpq

private lemma proposition72b_cross_matched_arithmetic
    {a b : ℕ} (ha : 3 ≤ a) (hab : a ≤ b) (hba : b ≤ a + 1) :
    ((a - 2 : ℕ) : ℝ) * (((2 * (b - 2) : ℕ) : ℝ))⁻¹ +
        ((a - 2 : ℕ) : ℝ) * (((2 * (a - 2) : ℕ) : ℝ))⁻¹ +
        ((b - a : ℕ) : ℝ) * (((2 * (a - 1) : ℕ) : ℝ))⁻¹ = 1 := by
  have hcases : b = a ∨ b = a + 1 := by omega
  rcases hcases with hb | hb
  · subst b
    have ha2 : (0 : ℝ) < ((a - 2 : ℕ) : ℝ) := by
      exact_mod_cast (show 0 < a - 2 by omega)
    rw [show a - a = 0 by omega]
    norm_num [Nat.cast_mul]
    field_simp [ne_of_gt ha2]
    norm_num
  · subst b
    have ha2 : (0 : ℝ) < ((a - 2 : ℕ) : ℝ) := by
      exact_mod_cast (show 0 < a - 2 by omega)
    have ha1 : (0 : ℝ) < ((a - 1 : ℕ) : ℝ) := by
      exact_mod_cast (show 0 < a - 1 by omega)
    rw [show a + 1 - 2 = a - 1 by omega, show a + 1 - a = 1 by omega]
    norm_num [Nat.cast_mul]
    field_simp [ne_of_gt ha2, ne_of_gt ha1]
    norm_num [Nat.cast_sub (by omega : 2 ≤ a), Nat.cast_sub (by omega : 1 ≤ a)]
    ring

private lemma proposition72b_cross_unmatched_arithmetic
    {a b : ℕ} (ha : 3 ≤ a) (hab : a ≤ b) (hba : b ≤ a + 1)
    (hneq : b ≠ a) :
    ((a - 1 : ℕ) : ℝ) * (((2 * (b - 2) : ℕ) : ℝ))⁻¹ +
        ((a - 1 : ℕ) : ℝ) * (((2 * (a - 1) : ℕ) : ℝ))⁻¹ = 1 := by
  have hb : b = a + 1 := by omega
  subst b
  rw [show a + 1 - 2 = a - 1 by omega]
  have ha1 : (0 : ℝ) < ((a - 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < a - 1 by omega)
  norm_num [Nat.cast_mul]
  field_simp [ne_of_gt ha1]
  norm_num

lemma fractionalEdgeLoad_proposition72bWeight_cross
    {A B : Finset α} (hAB : Disjoint A B) (f : A ↪ B)
    (hAcard : 3 ≤ A.card) (hAleB : A.card ≤ B.card)
    (hBle : B.card ≤ A.card + 1)
    (a : A) (b : B) (hba : b ≠ f a) :
    fractionalEdgeLoad (completeExceptEmbeddingMatching A B f)
      (proposition72bWeight A B f) s(a.1, b.1) = 1 := by
  classical
  let G := completeExceptEmbeddingMatching A B f
  let FA := embeddingAABFamily A B f
  let FM := embeddingABBMatchedFamily A B f
  let FU := embeddingABBUnmatchedFamily A B f
  have htriA : ∀ t ∈ FA, G.IsNClique 3 t :=
    embeddingAABFamily_isNClique hAB f
  have htriM : ∀ t ∈ FM, G.IsNClique 3 t :=
    embeddingABBMatchedFamily_isNClique hAB f
  have htriU : ∀ t ∈ FU, G.IsNClique 3 t :=
    embeddingABBUnmatchedFamily_isNClique hAB f
  have hcardA := card_filter_embeddingAABFamily_cross hAB f a b hba
  have hcardM := card_filter_embeddingABBMatchedFamily_cross hAB f a b hba
  have hcardU := card_filter_embeddingABBUnmatchedFamily_cross
    hAB f a b hba hBle
  rw [proposition72bWeight,
    show addTriangleWeight _ _ = (fun t ↦ _ + _) by rfl,
    fractionalEdgeLoad_add,
    show addTriangleWeight _ _ = (fun t ↦ _ + _) by rfl,
    fractionalEdgeLoad_add,
    fractionalEdgeLoad_constantTriangleFamilyWeight htriA,
    fractionalEdgeLoad_constantTriangleFamilyWeight htriM,
    fractionalEdgeLoad_constantTriangleFamilyWeight htriU]
  by_cases hbRange : b.1 ∈ embeddingRangeFinset A B f
  · rw [if_pos hbRange] at hcardA hcardM hcardU
    rw [hcardA, hcardM, hcardU]
    simpa only [add_assoc] using
      proposition72b_cross_matched_arithmetic hAcard hAleB hBle
  · rw [if_neg hbRange] at hcardA hcardM hcardU
    rw [hcardA, hcardM, hcardU]
    have hneq : B.card ≠ A.card := by
      intro hEq
      have hRangeEq : embeddingRangeFinset A B f = B := by
        apply eq_of_subset_of_card_le (embeddingRangeFinset_subset A B f)
        rw [card_embeddingRangeFinset, hEq]
      apply hbRange
      rw [hRangeEq]
      exact b.2
    simpa only [Nat.cast_zero, zero_mul, zero_add, add_zero, add_assoc] using
      proposition72b_cross_unmatched_arithmetic hAcard hAleB hBle hneq

lemma proposition72bWeight_eq_zero_of_not_subset_union
    {A B t : Finset α} (hAB : Disjoint A B) (f : A ↪ B)
    (ht : ¬t ⊆ A ∪ B) :
    proposition72bWeight A B f t = 0 := by
  classical
  have hAAB : t ∉ embeddingAABFamily A B f := by
    intro htF
    have htBig := embeddingAABFamily_subset_twoOneTriangleFamily A B f htF
    exact ht ((mem_powersetCard.mp
      (twoOneTriangleFamily_subset_powersetCard_union hAB htBig)).1)
  have hABBM : t ∉ embeddingABBMatchedFamily A B f := by
    intro htF
    have htBig := embeddingABBMatchedFamily_subset_twoOneTriangleFamily A B f htF
    have htBA := (mem_powersetCard.mp
      (twoOneTriangleFamily_subset_powersetCard_union hAB.symm htBig)).1
    exact ht (by simpa [union_comm] using htBA)
  have hABBU : t ∉ embeddingABBUnmatchedFamily A B f := by
    intro htF
    have htBig := embeddingABBUnmatchedFamily_subset_twoOneTriangleFamily A B f htF
    have htBA := (mem_powersetCard.mp
      (twoOneTriangleFamily_subset_powersetCard_union hAB.symm htBig)).1
    exact ht (by simpa [union_comm] using htBA)
  simp [proposition72bWeight, addTriangleWeight,
    constantTriangleFamilyWeight, hAAB, hABBM, hABBU]

lemma fractionalEdgeLoad_proposition72bWeight_eq_zero_of_not_subset_union
    {G : SimpleGraph α} {A B : Finset α} (hAB : Disjoint A B) (f : A ↪ B)
    {e : Sym2 α} (he : ¬e.toFinset ⊆ A ∪ B) :
    fractionalEdgeLoad G (proposition72bWeight A B f) e = 0 := by
  classical
  unfold fractionalEdgeLoad
  apply sum_eq_zero
  intro t ht
  apply proposition72bWeight_eq_zero_of_not_subset_union hAB f
  intro htUnion
  apply he
  induction e using Sym2.inductionOn with
  | hf u v =>
      have huv := Finset.mk_mem_sym2_iff.mp (mem_filter.mp ht).2
      intro x hx
      rw [Sym2.toFinset_mk_eq] at hx
      rcases mem_insert.mp hx with rfl | hx
      · exact htUnion huv.1
      · have hxv : x = v := by simpa using hx
        exact hxv ▸ htUnion huv.2

theorem isFractionalPacking_proposition72bWeight
    {A B : Finset α} (hAB : Disjoint A B) (f : A ↪ B)
    (hAcard : 3 ≤ A.card) (hAleB : A.card ≤ B.card)
    (hBle : B.card ≤ A.card + 1) :
    IsFractionalPacking (completeExceptEmbeddingMatching A B f)
      (proposition72bWeight A B f) := by
  classical
  let G := completeExceptEmbeddingMatching A B f
  constructor
  · intro t ht
    simp only [proposition72bWeight, addTriangleWeight,
      constantTriangleFamilyWeight]
    split <;> split <;> split <;> positivity
  · intro e heG
    have hecard : e.toFinset.card = 2 :=
      SimpleGraph.card_toFinset_mem_edgeFinset ⟨e, heG⟩
    by_cases heUnion : e.toFinset ⊆ A ∪ B
    · induction e using Sym2.inductionOn with
      | hf x y =>
          have hxyG : G.Adj x y := by
            simpa [G, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
              using heG
          have hxy : x ≠ y := hxyG.ne
          have hxUnion : x ∈ A ∨ x ∈ B := by
            have hx := heUnion (show x ∈ s(x, y).toFinset by simp)
            simpa using hx
          have hyUnion : y ∈ A ∨ y ∈ B := by
            have hy := heUnion (show y ∈ s(x, y).toFinset by simp)
            simpa using hy
          rcases hxUnion with hxA | hxB <;>
            rcases hyUnion with hyA | hyB
          · have heA : s(x, y).toFinset ⊆ A := by
              intro z hz
              simp only [Sym2.toFinset_mk_eq, mem_insert, mem_singleton] at hz
              rcases hz with rfl | rfl
              · exact hxA
              · exact hyA
            rw [fractionalEdgeLoad_proposition72bWeight_of_subset_left
              hAB f hAcard hAleB hecard heA]
            norm_num
          · let a : A := ⟨x, hxA⟩
            let b : B := ⟨y, hyB⟩
            have hba : b ≠ f a :=
              (completeExceptEmbeddingMatching_cross_adj hAB f a b).mp hxyG
            rw [fractionalEdgeLoad_proposition72bWeight_cross
              hAB f hAcard hAleB hBle a b hba]
          · let a : A := ⟨y, hyA⟩
            let b : B := ⟨x, hxB⟩
            have hba : b ≠ f a :=
              (completeExceptEmbeddingMatching_cross_adj hAB f a b).mp hxyG.symm
            simpa [a, b, Sym2.eq_swap] using
              (fractionalEdgeLoad_proposition72bWeight_cross
                hAB f hAcard hAleB hBle a b hba).le
          · have heB : s(x, y).toFinset ⊆ B := by
              intro z hz
              simp only [Sym2.toFinset_mk_eq, mem_insert, mem_singleton] at hz
              rcases hz with rfl | rfl
              · exact hxB
              · exact hyB
            rw [fractionalEdgeLoad_proposition72bWeight_of_subset_right
              hAB f hAcard hBle hecard heB]
            norm_num
    · rw [fractionalEdgeLoad_proposition72bWeight_eq_zero_of_not_subset_union
        hAB f heUnion]
      norm_num

lemma twoOneTriangleFamily_mem_internalCrossTriangles_of_sides
    {G : SimpleGraph α} {A B : Finset α} {s : Set α} {t : Finset α}
    (hBase : ∀ x ∈ A, x ∈ s) (hAttachment : ∀ z ∈ B, z ∉ s)
    (ht : t ∈ twoOneTriangleFamily A B) (htri : G.IsNClique 3 t) :
    t ∈ internalCrossTriangles G s := by
  classical
  obtain ⟨z, hzB, p, hp, rfl⟩ := mem_twoOneTriangleFamily_iff.mp ht
  rcases mem_powersetCard.mp hp with ⟨hpA, hpcard⟩
  obtain ⟨x, y, hxy, rfl⟩ := card_eq_two.mp hpcard
  have hxA : x ∈ A := hpA (by simp)
  have hyA : y ∈ A := hpA (by simp)
  have hzs : z ∉ s := hAttachment z hzB
  have hxs : x ∈ s := hBase x hxA
  have hys : y ∈ s := hBase y hyA
  have hzx : z ≠ x := fun h ↦ hzs (h ▸ hxs)
  have hzy : z ≠ y := fun h ↦ hzs (h ▸ hys)
  rw [SimpleGraph.isNClique_iff] at htri
  rcases htri with ⟨hclique, _hcard⟩
  have hxyG : G.Adj x y := hclique (by simp) (by simp) hxy
  have hzxG : G.Adj z x := hclique (by simp) (by simp) hzx
  have hzyG : G.Adj z y := hclique (by simp) (by simp) hzy
  exact insert_mem_internalCrossTriangles_of_opposite hxyG
    (by simp [hxs, hys]) (by simp [hzs, hxs]) hzxG hzyG

lemma isFractionalInternalCrossPacking_proposition72bWeight
    {A B : Finset α} (hAB : Disjoint A B) (f : A ↪ B)
    (hAcard : 3 ≤ A.card) (hAleB : A.card ≤ B.card)
    (hBle : B.card ≤ A.card + 1) :
    IsFractionalInternalCrossPacking
      (completeExceptEmbeddingMatching A B f) (A : Set α)
      (proposition72bWeight A B f) := by
  classical
  let G := completeExceptEmbeddingMatching A B f
  refine ⟨isFractionalPacking_proposition72bWeight
    hAB f hAcard hAleB hBle, ?_⟩
  intro t htCross
  have htriA : ∀ u ∈ embeddingAABFamily A B f, G.IsNClique 3 u :=
    embeddingAABFamily_isNClique hAB f
  have htriM : ∀ u ∈ embeddingABBMatchedFamily A B f, G.IsNClique 3 u :=
    embeddingABBMatchedFamily_isNClique hAB f
  have htriU : ∀ u ∈ embeddingABBUnmatchedFamily A B f, G.IsNClique 3 u :=
    embeddingABBUnmatchedFamily_isNClique hAB f
  have htA : t ∉ embeddingAABFamily A B f := by
    intro ht
    apply htCross
    apply twoOneTriangleFamily_mem_internalCrossTriangles_of_sides
      (s := (A : Set α)) (fun x hx ↦ hx)
      (fun z hz hzA ↦ Finset.disjoint_left.mp hAB hzA hz)
      (embeddingAABFamily_subset_twoOneTriangleFamily A B f ht)
      (htriA t ht)
  have htM : t ∉ embeddingABBMatchedFamily A B f := by
    intro ht
    apply htCross
    have ht' := twoOneTriangleFamily_mem_internalCrossTriangles_of_sides
      (G := G) (s := (A : Set α)ᶜ)
      (fun x hx ↦ by
        exact fun hxA ↦ Finset.disjoint_left.mp hAB hxA hx)
      (fun z hz ↦ by simp [hz])
      (embeddingABBMatchedFamily_subset_twoOneTriangleFamily A B f ht)
      (htriM t ht)
    simpa only [internalCrossTriangles_set_compl] using ht'
  have htU : t ∉ embeddingABBUnmatchedFamily A B f := by
    intro ht
    apply htCross
    have ht' := twoOneTriangleFamily_mem_internalCrossTriangles_of_sides
      (G := G) (s := (A : Set α)ᶜ)
      (fun x hx ↦ by
        exact fun hxA ↦ Finset.disjoint_left.mp hAB hxA hx)
      (fun z hz ↦ by simp [hz])
      (embeddingABBUnmatchedFamily_subset_twoOneTriangleFamily A B f ht)
      (htriU t ht)
    simpa only [internalCrossTriangles_set_compl] using ht'
  simp [proposition72bWeight, addTriangleWeight,
    constantTriangleFamilyWeight, htA, htM, htU]

private lemma card_filter_edgeFinset_subset_eq_choose_of_isClique
    {G : SimpleGraph α} {A : Finset α} (hA : G.IsClique (A : Set α)) :
    (G.edgeFinset.filter fun e ↦ e.toFinset ⊆ A).card = A.card.choose 2 := by
  rw [G.card_filter_edgeFinset_toFinset_subset A]
  have htop : G.induce (↑A : Set α) = ⊤ := G.induce_eq_top.mpr hA
  calc
    #(G.induce (↑A : Set α)).edgeFinset =
        Nat.card (G.induce (↑A : Set α)).edgeSet := by
          rw [Nat.card_eq_fintype_card, SimpleGraph.card_edgeSet]
    _ = Nat.card (⊤ : SimpleGraph A).edgeSet :=
      congrArg (fun H : SimpleGraph A ↦ Nat.card H.edgeSet) htop
    _ = #((⊤ : SimpleGraph A).edgeFinset) := by
      rw [Nat.card_eq_fintype_card, SimpleGraph.card_edgeSet]
    _ = (Fintype.card A).choose 2 :=
      SimpleGraph.card_edgeFinset_top_eq_card_choose_two
    _ = A.card.choose 2 := by simp

theorem fractionalSize_proposition72bWeight
    {A B : Finset α} (hAB : Disjoint A B) (f : A ↪ B)
    (hAcard : 3 ≤ A.card) (hAleB : A.card ≤ B.card)
    (hBle : B.card ≤ A.card + 1) :
    fractionalSize (completeExceptEmbeddingMatching A B f)
      (proposition72bWeight A B f) =
        (((A.card.choose 2 + B.card.choose 2 : ℕ) : ℝ)) / 2 := by
  classical
  let G := completeExceptEmbeddingMatching A B f
  let w := proposition72bWeight A B f
  let EA := G.edgeFinset.filter fun e ↦ e.toFinset ⊆ A
  let EB := G.edgeFinset.filter fun e ↦ e.toFinset ⊆ B
  let EI := internalEdgeFinset G (A : Set α)
  have hAclique : G.IsClique (A : Set α) := by
    intro x hx y hy hxy
    exact completeExceptEmbeddingMatching_internal_adj_left hAB f hx hy hxy
  have hBclique : G.IsClique (B : Set α) := by
    intro x hx y hy hxy
    exact completeExceptEmbeddingMatching_internal_adj_right hAB f hx hy hxy
  have hEAcard : EA.card = A.card.choose 2 := by
    simpa only [EA] using
      card_filter_edgeFinset_subset_eq_choose_of_isClique hAclique
  have hEBcard : EB.card = B.card.choose 2 := by
    simpa only [EB] using
      card_filter_edgeFinset_subset_eq_choose_of_isClique hBclique
  have hdis : Disjoint EA EB := by
    rw [Finset.disjoint_left]
    intro e heA heB
    have heG : e ∈ G.edgeFinset := (mem_filter.mp heA).1
    have hecard : e.toFinset.card = 2 :=
      SimpleGraph.card_toFinset_mem_edgeFinset ⟨e, heG⟩
    have hnonempty : e.toFinset.Nonempty := card_pos.mp (by omega)
    obtain ⟨x, hx⟩ := hnonempty
    exact Finset.disjoint_left.mp hAB
      ((mem_filter.mp heA).2 hx) ((mem_filter.mp heB).2 hx)
  have hsub : EA ∪ EB ⊆ EI := by
    intro e he
    rcases mem_union.mp he with heA | heB
    · rcases mem_filter.mp heA with ⟨heG, heA⟩
      exact mem_filter.mpr ⟨heG,
        (sameSide_iff_subset_side_or_compl (A : Set α) e).mpr
          (Or.inl (by simpa using heA))⟩
    · rcases mem_filter.mp heB with ⟨heG, heB⟩
      apply mem_filter.mpr
      refine ⟨heG,
        (sameSide_iff_subset_side_or_compl (A : Set α) e).mpr (Or.inr ?_)⟩
      intro x hx
      simp only [Set.mem_toFinset, Set.mem_compl_iff]
      intro hxA
      exact Finset.disjoint_left.mp hAB hxA (heB hx)
  have hsumSupport :
      (∑ e ∈ EI, fractionalEdgeLoad G w e) =
        ∑ e ∈ EA ∪ EB, fractionalEdgeLoad G w e := by
    symm
    apply sum_subset hsub
    intro e heI heNot
    have heG : e ∈ G.edgeFinset := (mem_filter.mp heI).1
    have hnotA : ¬e.toFinset ⊆ A := by
      intro heA
      exact heNot (mem_union_left EB (mem_filter.mpr ⟨heG, heA⟩))
    have hnotB : ¬e.toFinset ⊆ B := by
      intro heB
      exact heNot (mem_union_right EA (mem_filter.mpr ⟨heG, heB⟩))
    apply fractionalEdgeLoad_proposition72bWeight_eq_zero_of_not_subset_union
      hAB f
    intro heUnion
    rcases (sameSide_iff_subset_side_or_compl (A : Set α) e).mp
      (mem_filter.mp heI).2 with heA | heAc
    · exact hnotA (by simpa using heA)
    · apply hnotB
      intro x hx
      have hxUnion := heUnion hx
      have hxNotA : x ∉ A := by simpa using heAc hx
      rcases mem_union.mp hxUnion with hxA | hxB
      · exact (hxNotA hxA).elim
      · exact hxB
  have hsumA :
      (∑ e ∈ EA, fractionalEdgeLoad G w e) = (EA.card : ℝ) / 2 := by
    calc
      (∑ e ∈ EA, fractionalEdgeLoad G w e) = ∑ _e ∈ EA, (1 / 2 : ℝ) := by
        apply sum_congr rfl
        intro e he
        have heG : e ∈ G.edgeFinset := (mem_filter.mp he).1
        have hecard : e.toFinset.card = 2 :=
          SimpleGraph.card_toFinset_mem_edgeFinset ⟨e, heG⟩
        exact fractionalEdgeLoad_proposition72bWeight_of_subset_left
          hAB f hAcard hAleB hecard (mem_filter.mp he).2
      _ = (EA.card : ℝ) / 2 := by simp [div_eq_mul_inv]
  have hsumB :
      (∑ e ∈ EB, fractionalEdgeLoad G w e) = (EB.card : ℝ) / 2 := by
    calc
      (∑ e ∈ EB, fractionalEdgeLoad G w e) = ∑ _e ∈ EB, (1 / 2 : ℝ) := by
        apply sum_congr rfl
        intro e he
        have heG : e ∈ G.edgeFinset := (mem_filter.mp he).1
        have hecard : e.toFinset.card = 2 :=
          SimpleGraph.card_toFinset_mem_edgeFinset ⟨e, heG⟩
        exact fractionalEdgeLoad_proposition72bWeight_of_subset_right
          hAB f hAcard hBle hecard (mem_filter.mp he).2
      _ = (EB.card : ℝ) / 2 := by simp [div_eq_mul_inv]
  have hcross := isFractionalInternalCrossPacking_proposition72bWeight
    hAB f hAcard hAleB hBle
  calc
    fractionalSize G w = ∑ e ∈ EI, fractionalEdgeLoad G w e := by
      simpa only [G, w, EI] using
        (sum_internalEdge_fractionalEdgeLoad_eq_fractionalSize hcross).symm
    _ = ∑ e ∈ EA ∪ EB, fractionalEdgeLoad G w e := hsumSupport
    _ = (∑ e ∈ EA, fractionalEdgeLoad G w e) +
        ∑ e ∈ EB, fractionalEdgeLoad G w e := sum_union hdis
    _ = (EA.card : ℝ) / 2 + (EB.card : ℝ) / 2 := by rw [hsumA, hsumB]
    _ = (((A.card.choose 2 + B.card.choose 2 : ℕ) : ℝ)) / 2 := by
      rw [hEAcard, hEBcard]
      push_cast
      ring

/-- Proposition 7.2(b) for two complete blobs whose cross graph is complete
apart from a matching saturating the smaller blob.  The explicit Appendix A
weight is a feasible cross-triangle packing and has exactly half the total
number of internal pairs. -/
theorem proposition72b_completeTwoBlobPacking
    {A B : Finset α} (hAB : Disjoint A B) (f : A ↪ B)
    (hAcard : 3 ≤ A.card) (hAleB : A.card ≤ B.card)
    (hBle : B.card ≤ A.card + 1) :
    IsFractionalInternalCrossPacking
        (completeExceptEmbeddingMatching A B f) (A : Set α)
        (proposition72bWeight A B f) ∧
      fractionalSize (completeExceptEmbeddingMatching A B f)
        (proposition72bWeight A B f) =
          (((A.card.choose 2 + B.card.choose 2 : ℕ) : ℝ)) / 2 :=
  ⟨isFractionalInternalCrossPacking_proposition72bWeight
      hAB f hAcard hAleB hBle,
    fractionalSize_proposition72bWeight hAB f hAcard hAleB hBle⟩

private lemma insert_attachment_isNClique
    {G : SimpleGraph α} {e : Sym2 α} (heG : e ∈ G.edgeFinset)
    (z : α) (hz : ∀ x ∈ e.toFinset, G.Adj z x) :
    G.IsNClique 3 (insert z e.toFinset) := by
  classical
  induction e using Sym2.inductionOn with
  | hf x y =>
      have hxyG : G.Adj x y := by
        simpa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using heG
      have hzx : G.Adj z x := hz x (by simp [hxyG.ne])
      have hzy : G.Adj z y := hz y (by simp [hxyG.ne])
      simpa [Sym2.toFinset_mk_eq] using
        (SimpleGraph.is3Clique_triple_iff.mpr ⟨hzx, hzy, hxyG⟩)

private lemma embeddingAABFamily_incident_isNClique
    {G : SimpleGraph α} {A B : Finset α} (hAB : Disjoint A B)
    (f : A ↪ B)
    (hcross : ∀ a : A, ∀ b : B, G.Adj a.1 b.1 ↔ b ≠ f a)
    {e : Sym2 α} (heG : e ∈ G.edgeFinset)
    (hecard : e.toFinset.card = 2) (heA : e.toFinset ⊆ A) :
    ∀ t ∈ embeddingAABFamily A B f, e ∈ t.sym2 → G.IsNClique 3 t := by
  classical
  intro t htF het
  have ht : t ∈ (embeddingAABFamily A B f).filter
      (fun u ↦ e ∈ u.sym2) := mem_filter.mpr ⟨htF, het⟩
  rw [filter_embeddingAABFamily_of_edge_subset_left
    hAB f e hecard heA] at ht
  obtain ⟨z, hzAvoid, rfl⟩ := mem_image.mp ht
  apply insert_attachment_isNClique heG z.1
  intro x hx
  let a : A := ⟨x, heA hx⟩
  have havoid : z ≠ f a :=
    (avoid_embeddingPairRange_iff f e.toFinset heA z).1 hzAvoid a hx
  exact (hcross a z).2 havoid |>.symm

private lemma embeddingABBFamily_incident_isNClique_of_filter_image
    {G : SimpleGraph α} {A B : Finset α} (f : A ↪ B)
    (hcross : ∀ a : A, ∀ b : B, G.Adj a.1 b.1 ↔ b ≠ f a)
    {F : Finset (Finset α)} {e : Sym2 α}
    (heG : e ∈ G.edgeFinset) (heB : e.toFinset ⊆ B)
    (hfilter : F.filter (fun t ↦ e ∈ t.sym2) =
      ((Finset.univ : Finset A) \ embeddingPairPreimage f e.toFinset).image
        (fun a ↦ insert a.1 e.toFinset)) :
    ∀ t ∈ F, e ∈ t.sym2 → G.IsNClique 3 t := by
  classical
  intro t htF het
  have ht : t ∈ F.filter (fun u ↦ e ∈ u.sym2) :=
    mem_filter.mpr ⟨htF, het⟩
  rw [hfilter] at ht
  obtain ⟨a, haAvoid, rfl⟩ := mem_image.mp ht
  have hfa : (f a).1 ∉ e.toFinset := by
    simpa [embeddingPairPreimage] using haAvoid
  apply insert_attachment_isNClique heG a.1
  intro x hx
  let b : B := ⟨x, heB hx⟩
  have hbfa : b ≠ f a := by
    intro hEq
    apply hfa
    have hxEq : x = (f a).1 := congrArg Subtype.val hEq
    simpa [hxEq] using hx
  exact (hcross a b).2 hbfa

lemma fractionalEdgeLoad_zeroExtend_proposition72bWeight_of_subset_left
    {G : SimpleGraph α} {A B : Finset α} (hAB : Disjoint A B)
    (f : A ↪ B)
    (hcross : ∀ a : A, ∀ b : B, G.Adj a.1 b.1 ↔ b ≠ f a)
    (hAcard : 3 ≤ A.card) (hAleB : A.card ≤ B.card)
    {e : Sym2 α} (heG : e ∈ G.edgeFinset) (heA : e.toFinset ⊆ A) :
    fractionalEdgeLoad G
      (zeroExtendTriangleWeight G (proposition72bWeight A B f)) e = 1 / 2 := by
  classical
  let FA := embeddingAABFamily A B f
  let FM := embeddingABBMatchedFamily A B f
  let FU := embeddingABBUnmatchedFamily A B f
  have hBcard : 3 ≤ B.card := hAcard.trans hAleB
  have hecard : e.toFinset.card = 2 :=
    SimpleGraph.card_toFinset_mem_edgeFinset ⟨e, heG⟩
  have hcardA : (FA.filter fun t ↦ e ∈ t.sym2).card = B.card - 2 := by
    simpa only [FA] using
      card_filter_embeddingAABFamily_of_edge_subset_left hAB f e hecard heA
  have hcardM : (FM.filter fun t ↦ e ∈ t.sym2).card = 0 := by
    apply card_filter_family_eq_zero_of_subset_twoOne_attachment
      hAB.symm (embeddingABBMatchedFamily_subset_twoOneTriangleFamily A B f)
      e hecard heA
  have hcardU : (FU.filter fun t ↦ e ∈ t.sym2).card = 0 := by
    apply card_filter_family_eq_zero_of_subset_twoOne_attachment
      hAB.symm (embeddingABBUnmatchedFamily_subset_twoOneTriangleFamily A B f)
      e hecard heA
  have htriA : ∀ t ∈ FA, e ∈ t.sym2 → G.IsNClique 3 t := by
    simpa only [FA] using embeddingAABFamily_incident_isNClique
      hAB f hcross heG hecard heA
  have htriM : ∀ t ∈ FM, e ∈ t.sym2 → G.IsNClique 3 t := by
    intro t htF het
    have ht : t ∈ FM.filter (fun u ↦ e ∈ u.sym2) :=
      mem_filter.mpr ⟨htF, het⟩
    rw [card_eq_zero.mp hcardM] at ht
    simp at ht
  have htriU : ∀ t ∈ FU, e ∈ t.sym2 → G.IsNClique 3 t := by
    intro t htF het
    have ht : t ∈ FU.filter (fun u ↦ e ∈ u.sym2) :=
      mem_filter.mpr ⟨htF, het⟩
    rw [card_eq_zero.mp hcardU] at ht
    simp at ht
  rw [fractionalEdgeLoad_zeroExtend (G := G) le_rfl,
    proposition72bWeight,
    show addTriangleWeight _ _ = (fun t ↦ _ + _) by rfl,
    fractionalEdgeLoad_add,
    show addTriangleWeight _ _ = (fun t ↦ _ + _) by rfl,
    fractionalEdgeLoad_add,
    fractionalEdgeLoad_constantTriangleFamilyWeight_of_incident htriA,
    fractionalEdgeLoad_constantTriangleFamilyWeight_of_incident htriM,
    fractionalEdgeLoad_constantTriangleFamilyWeight_of_incident htriU,
    hcardA, hcardM, hcardU]
  have hpos : (0 : ℝ) < ((B.card - 2 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < B.card - 2 by omega)
  norm_num [Nat.cast_mul]
  field_simp [ne_of_gt hpos]

lemma fractionalEdgeLoad_zeroExtend_proposition72bWeight_of_subset_right
    {G : SimpleGraph α} {A B : Finset α} (hAB : Disjoint A B)
    (f : A ↪ B)
    (hcross : ∀ a : A, ∀ b : B, G.Adj a.1 b.1 ↔ b ≠ f a)
    (hAcard : 3 ≤ A.card) (hBle : B.card ≤ A.card + 1)
    {e : Sym2 α} (heG : e ∈ G.edgeFinset) (heB : e.toFinset ⊆ B) :
    fractionalEdgeLoad G
      (zeroExtendTriangleWeight G (proposition72bWeight A B f)) e = 1 / 2 := by
  classical
  let FA := embeddingAABFamily A B f
  let FM := embeddingABBMatchedFamily A B f
  let FU := embeddingABBUnmatchedFamily A B f
  have hecard : e.toFinset.card = 2 :=
    SimpleGraph.card_toFinset_mem_edgeFinset ⟨e, heG⟩
  have hcardA : (FA.filter fun t ↦ e ∈ t.sym2).card = 0 := by
    apply card_filter_family_eq_zero_of_subset_twoOne_attachment hAB
      (embeddingAABFamily_subset_twoOneTriangleFamily A B f) e hecard heB
  have htriA : ∀ t ∈ FA, e ∈ t.sym2 → G.IsNClique 3 t := by
    intro t htF het
    have ht : t ∈ FA.filter (fun u ↦ e ∈ u.sym2) :=
      mem_filter.mpr ⟨htF, het⟩
    rw [card_eq_zero.mp hcardA] at ht
    simp at ht
  by_cases heRange : e.toFinset ⊆ embeddingRangeFinset A B f
  · have hcardM : (FM.filter fun t ↦ e ∈ t.sym2).card = A.card - 2 := by
      simpa only [FM] using
        card_filter_embeddingABBMatchedFamily_of_edge_subset_right
          hAB f e hecard heB heRange
    have hcardU : (FU.filter fun t ↦ e ∈ t.sym2).card = 0 := by
      rw [card_eq_zero]
      apply eq_empty_iff_forall_notMem.mpr
      intro t ht
      have htTwo : t ∈ twoOneTriangleFamily B A :=
        embeddingABBUnmatchedFamily_subset_twoOneTriangleFamily A B f
          (mem_filter.mp ht).1
      have htBig : t ∈ (twoOneTriangleFamily B A).filter
          (fun u ↦ e ∈ u.sym2) :=
        mem_filter.mpr ⟨htTwo, (mem_filter.mp ht).2⟩
      rw [filter_twoOne_of_edge_subset_base hAB.symm e hecard heB] at htBig
      obtain ⟨a, ha, hat⟩ := mem_image.mp htBig
      obtain ⟨a', p', hp', hav', hpNot, ht'⟩ :=
        mem_embeddingABBUnmatchedFamily_iff.mp (mem_filter.mp ht).1
      have haT : a'.1 ∈ t := by rw [ht']; simp
      have haa : a'.1 = a := by
        rcases (by rw [← hat] at haT; exact mem_insert.mp haT) with h | h
        · exact h
        · exact (Finset.disjoint_left.mp hAB a'.2 (heB h)).elim
      subst a
      have haP : a'.1 ∉ p' := fun h ↦
        Finset.disjoint_left.mp hAB a'.2 ((mem_powersetCard.mp hp').1 h)
      have haE : a'.1 ∉ e.toFinset := fun h ↦
        Finset.disjoint_left.mp hAB a'.2 (heB h)
      have hpEq : p' = e.toFinset := by
        simpa [haP, haE] using congrArg (fun u : Finset α ↦ u.erase a'.1)
          (ht'.symm.trans hat.symm)
      exact hpNot (hpEq ▸ heRange)
    have htriM : ∀ t ∈ FM, e ∈ t.sym2 → G.IsNClique 3 t := by
      apply embeddingABBFamily_incident_isNClique_of_filter_image
        f hcross heG heB
      simpa only [FM] using
        filter_embeddingABBMatchedFamily_of_edge_subset_right
          hAB f e hecard heB heRange
    have htriU : ∀ t ∈ FU, e ∈ t.sym2 → G.IsNClique 3 t := by
      intro t htF het
      have ht : t ∈ FU.filter (fun u ↦ e ∈ u.sym2) :=
        mem_filter.mpr ⟨htF, het⟩
      rw [card_eq_zero.mp hcardU] at ht
      simp at ht
    rw [fractionalEdgeLoad_zeroExtend (G := G) le_rfl,
      proposition72bWeight,
      show addTriangleWeight _ _ = (fun t ↦ _ + _) by rfl,
      fractionalEdgeLoad_add,
      show addTriangleWeight _ _ = (fun t ↦ _ + _) by rfl,
      fractionalEdgeLoad_add,
      fractionalEdgeLoad_constantTriangleFamilyWeight_of_incident htriA,
      fractionalEdgeLoad_constantTriangleFamilyWeight_of_incident htriM,
      fractionalEdgeLoad_constantTriangleFamilyWeight_of_incident htriU,
      hcardA, hcardM, hcardU]
    have hpos : (0 : ℝ) < ((A.card - 2 : ℕ) : ℝ) := by
      exact_mod_cast (show 0 < A.card - 2 by omega)
    norm_num [Nat.cast_mul]
    field_simp [ne_of_gt hpos]
  · have hinter :
        (e.toFinset ∩ embeddingRangeFinset A B f).card = 1 :=
      card_inter_embeddingRange_eq_one_of_pair_not_subset
        f hBle e.toFinset heB hecard heRange
    have hcardM : (FM.filter fun t ↦ e ∈ t.sym2).card = 0 := by
      rw [card_eq_zero]
      apply eq_empty_iff_forall_notMem.mpr
      intro t ht
      have htTwo : t ∈ twoOneTriangleFamily B A :=
        embeddingABBMatchedFamily_subset_twoOneTriangleFamily A B f
          (mem_filter.mp ht).1
      have htBig : t ∈ (twoOneTriangleFamily B A).filter
          (fun u ↦ e ∈ u.sym2) :=
        mem_filter.mpr ⟨htTwo, (mem_filter.mp ht).2⟩
      rw [filter_twoOne_of_edge_subset_base hAB.symm e hecard heB] at htBig
      obtain ⟨a, ha, hat⟩ := mem_image.mp htBig
      obtain ⟨a', p', hp', _hav', hrange', ht'⟩ :=
        mem_embeddingABBMatchedFamily_iff.mp (mem_filter.mp ht).1
      have haT : a'.1 ∈ t := by rw [ht']; simp
      have haa : a'.1 = a := by
        rcases (by rw [← hat] at haT; exact mem_insert.mp haT) with h | h
        · exact h
        · exact (Finset.disjoint_left.mp hAB a'.2 (heB h)).elim
      subst a
      have haP : a'.1 ∉ p' := fun h ↦
        Finset.disjoint_left.mp hAB a'.2 ((mem_powersetCard.mp hp').1 h)
      have haE : a'.1 ∉ e.toFinset := fun h ↦
        Finset.disjoint_left.mp hAB a'.2 (heB h)
      have hpEq : p' = e.toFinset := by
        simpa [haP, haE] using congrArg (fun u : Finset α ↦ u.erase a'.1)
          (ht'.symm.trans hat.symm)
      exact heRange (hpEq ▸ hrange')
    have hcardU : (FU.filter fun t ↦ e ∈ t.sym2).card = A.card - 1 := by
      rw [show (FU.filter fun t ↦ e ∈ t.sym2).card =
          A.card - (e.toFinset ∩ embeddingRangeFinset A B f).card by
        simpa only [FU] using
          card_filter_embeddingABBUnmatchedFamily_of_edge_subset_right
            hAB f e hecard heB heRange]
      rw [hinter]
    have htriM : ∀ t ∈ FM, e ∈ t.sym2 → G.IsNClique 3 t := by
      intro t htF het
      have ht : t ∈ FM.filter (fun u ↦ e ∈ u.sym2) :=
        mem_filter.mpr ⟨htF, het⟩
      rw [card_eq_zero.mp hcardM] at ht
      simp at ht
    have htriU : ∀ t ∈ FU, e ∈ t.sym2 → G.IsNClique 3 t := by
      apply embeddingABBFamily_incident_isNClique_of_filter_image
        f hcross heG heB
      simpa only [FU] using
        filter_embeddingABBUnmatchedFamily_of_edge_subset_right
          hAB f e hecard heB heRange
    rw [fractionalEdgeLoad_zeroExtend (G := G) le_rfl,
      proposition72bWeight,
      show addTriangleWeight _ _ = (fun t ↦ _ + _) by rfl,
      fractionalEdgeLoad_add,
      show addTriangleWeight _ _ = (fun t ↦ _ + _) by rfl,
      fractionalEdgeLoad_add,
      fractionalEdgeLoad_constantTriangleFamilyWeight_of_incident htriA,
      fractionalEdgeLoad_constantTriangleFamilyWeight_of_incident htriM,
      fractionalEdgeLoad_constantTriangleFamilyWeight_of_incident htriU,
      hcardA, hcardM, hcardU]
    have hpos : (0 : ℝ) < ((A.card - 1 : ℕ) : ℝ) := by
      exact_mod_cast (show 0 < A.card - 1 by omega)
    norm_num [Nat.cast_mul]
    field_simp [ne_of_gt hpos]

lemma le_completeExceptEmbeddingMatching_of_cross
    {G : SimpleGraph α} {A B : Finset α} (f : A ↪ B)
    (hcross : ∀ a : A, ∀ b : B, G.Adj a.1 b.1 ↔ b ≠ f a) :
    G ≤ completeExceptEmbeddingMatching A B f := by
  classical
  intro x y hxy
  rw [completeExceptEmbeddingMatching, SimpleGraph.deleteEdges_adj]
  refine ⟨by simpa using hxy.ne, ?_⟩
  intro hmem
  obtain ⟨a, _ha, haeq⟩ := mem_image.mp hmem
  have hxyEdge : s(x, y) ∈ G.edgeSet := by
    simpa [SimpleGraph.mem_edgeSet] using hxy
  have hmatchEdge : s(a.1, (f a).1) ∈ G.edgeSet := by
    rw [haeq]
    exact hxyEdge
  have hmatchAdj : G.Adj a.1 (f a).1 := by
    simpa [SimpleGraph.mem_edgeSet] using hmatchEdge
  exact (hcross a (f a)).mp hmatchAdj rfl

/-- Proposition 7.2(b) with arbitrary colours inside the two blobs.  The
cross graph is complete apart from the matching represented by `f`; after
restricting the explicit complete-blob weight to actual graph triangles,
every actual internal edge still has load exactly one half. -/
theorem proposition72b_twoBlobPacking
    {G : SimpleGraph α} {A B : Finset α} (hAB : Disjoint A B)
    (f : A ↪ B)
    (hcross : ∀ a : A, ∀ b : B, G.Adj a.1 b.1 ↔ b ≠ f a)
    (hAcard : 3 ≤ A.card) (hAleB : A.card ≤ B.card)
    (hBle : B.card ≤ A.card + 1) :
    IsFractionalPacking G
        (zeroExtendTriangleWeight G (proposition72bWeight A B f)) ∧
      (∀ e ∈ G.edgeFinset, e.toFinset ⊆ A →
        fractionalEdgeLoad G
          (zeroExtendTriangleWeight G (proposition72bWeight A B f)) e = 1 / 2) ∧
      (∀ e ∈ G.edgeFinset, e.toFinset ⊆ B →
        fractionalEdgeLoad G
          (zeroExtendTriangleWeight G (proposition72bWeight A B f)) e = 1 / 2) := by
  classical
  have hGK : G ≤ completeExceptEmbeddingMatching A B f :=
    le_completeExceptEmbeddingMatching_of_cross f hcross
  have hcomplete := proposition72b_completeTwoBlobPacking
    hAB f hAcard hAleB hBle
  refine ⟨hcomplete.1.1.restrictToSubgraph hGK, ?_, ?_⟩
  · intro e heG heA
    exact fractionalEdgeLoad_zeroExtend_proposition72bWeight_of_subset_left
      hAB f hcross hAcard hAleB heG heA
  · intro e heG heB
    exact fractionalEdgeLoad_zeroExtend_proposition72bWeight_of_subset_right
      hAB f hcross hAcard hBle heG heB

lemma isFractionalInternalCrossPacking_zeroExtend_proposition72bWeight
    {G : SimpleGraph α} {A B : Finset α} (hAB : Disjoint A B)
    (f : A ↪ B)
    (hcross : ∀ a : A, ∀ b : B, G.Adj a.1 b.1 ↔ b ≠ f a)
    (hAcard : 3 ≤ A.card) (hAleB : A.card ≤ B.card)
    (hBle : B.card ≤ A.card + 1) :
    IsFractionalInternalCrossPacking G (A : Set α)
      (zeroExtendTriangleWeight G (proposition72bWeight A B f)) := by
  classical
  refine ⟨(proposition72b_twoBlobPacking
    hAB f hcross hAcard hAleB hBle).1, ?_⟩
  intro t htCross
  by_cases htG : t ∈ G.cliqueFinset 3
  · rw [zeroExtendTriangleWeight_of_mem htG]
    have htri : G.IsNClique 3 t :=
      SimpleGraph.mem_cliqueFinset_iff.mp htG
    have htA : t ∉ embeddingAABFamily A B f := by
      intro ht
      apply htCross
      apply twoOneTriangleFamily_mem_internalCrossTriangles_of_sides
        (s := (A : Set α)) (fun x hx ↦ hx)
        (fun z hz hzA ↦ Finset.disjoint_left.mp hAB hzA hz)
        (embeddingAABFamily_subset_twoOneTriangleFamily A B f ht) htri
    have htM : t ∉ embeddingABBMatchedFamily A B f := by
      intro ht
      apply htCross
      have ht' := twoOneTriangleFamily_mem_internalCrossTriangles_of_sides
        (G := G) (s := (A : Set α)ᶜ)
        (fun x hx ↦ by
          exact fun hxA ↦ Finset.disjoint_left.mp hAB hxA hx)
        (fun z hz ↦ by simp [hz])
        (embeddingABBMatchedFamily_subset_twoOneTriangleFamily A B f ht) htri
      simpa only [internalCrossTriangles_set_compl] using ht'
    have htU : t ∉ embeddingABBUnmatchedFamily A B f := by
      intro ht
      apply htCross
      have ht' := twoOneTriangleFamily_mem_internalCrossTriangles_of_sides
        (G := G) (s := (A : Set α)ᶜ)
        (fun x hx ↦ by
          exact fun hxA ↦ Finset.disjoint_left.mp hAB hxA hx)
        (fun z hz ↦ by simp [hz])
        (embeddingABBUnmatchedFamily_subset_twoOneTriangleFamily A B f ht) htri
      simpa only [internalCrossTriangles_set_compl] using ht'
    simp [proposition72bWeight, addTriangleWeight,
      constantTriangleFamilyWeight, htA, htM, htU]
  · exact zeroExtendTriangleWeight_of_not_mem htG

theorem fractionalSize_zeroExtend_proposition72bWeight
    {G : SimpleGraph α} {A B : Finset α} (hAB : Disjoint A B)
    (f : A ↪ B)
    (hcross : ∀ a : A, ∀ b : B, G.Adj a.1 b.1 ↔ b ≠ f a)
    (hAcard : 3 ≤ A.card) (hAleB : A.card ≤ B.card)
    (hBle : B.card ≤ A.card + 1) :
    fractionalSize G
        (zeroExtendTriangleWeight G (proposition72bWeight A B f)) =
      ((sideEdgeFinset G A).card : ℝ) / 2 +
        ((sideEdgeFinset G B).card : ℝ) / 2 := by
  classical
  let w := zeroExtendTriangleWeight G (proposition72bWeight A B f)
  let EA := sideEdgeFinset G A
  let EB := sideEdgeFinset G B
  let EI := internalEdgeFinset G (A : Set α)
  have hdis : Disjoint EA EB := by
    rw [Finset.disjoint_left]
    intro e heA heB
    have heG : e ∈ G.edgeFinset := (mem_filter.mp heA).1
    have hecard : e.toFinset.card = 2 :=
      SimpleGraph.card_toFinset_mem_edgeFinset ⟨e, heG⟩
    have hnonempty : e.toFinset.Nonempty := card_pos.mp (by omega)
    obtain ⟨x, hx⟩ := hnonempty
    exact Finset.disjoint_left.mp hAB
      ((mem_filter.mp heA).2 hx) ((mem_filter.mp heB).2 hx)
  have hsub : EA ∪ EB ⊆ EI := by
    intro e he
    rcases mem_union.mp he with heA | heB
    · rcases mem_filter.mp heA with ⟨heG, heA⟩
      exact mem_filter.mpr ⟨heG,
        (sameSide_iff_subset_side_or_compl (A : Set α) e).mpr
          (Or.inl (by simpa using heA))⟩
    · rcases mem_filter.mp heB with ⟨heG, heB⟩
      apply mem_filter.mpr
      refine ⟨heG,
        (sameSide_iff_subset_side_or_compl (A : Set α) e).mpr (Or.inr ?_)⟩
      intro x hx
      simp only [Set.mem_toFinset, Set.mem_compl_iff]
      intro hxA
      exact Finset.disjoint_left.mp hAB hxA (heB hx)
  have hsumSupport :
      (∑ e ∈ EI, fractionalEdgeLoad G w e) =
        ∑ e ∈ EA ∪ EB, fractionalEdgeLoad G w e := by
    symm
    apply sum_subset hsub
    intro e heI heNot
    have heG : e ∈ G.edgeFinset := (mem_filter.mp heI).1
    have hnotA : ¬e.toFinset ⊆ A := by
      intro heA
      exact heNot (mem_union_left EB (mem_filter.mpr ⟨heG, heA⟩))
    have hnotB : ¬e.toFinset ⊆ B := by
      intro heB
      exact heNot (mem_union_right EA (mem_filter.mpr ⟨heG, heB⟩))
    unfold w
    rw [fractionalEdgeLoad_zeroExtend (G := G) le_rfl]
    apply fractionalEdgeLoad_proposition72bWeight_eq_zero_of_not_subset_union
      hAB f
    intro heUnion
    rcases (sameSide_iff_subset_side_or_compl (A : Set α) e).mp
      (mem_filter.mp heI).2 with heA | heAc
    · exact hnotA (by simpa using heA)
    · apply hnotB
      intro x hx
      have hxUnion := heUnion hx
      have hxNotA : x ∉ A := by simpa using heAc hx
      rcases mem_union.mp hxUnion with hxA | hxB
      · exact (hxNotA hxA).elim
      · exact hxB
  have hsumA :
      (∑ e ∈ EA, fractionalEdgeLoad G w e) = (EA.card : ℝ) / 2 := by
    calc
      (∑ e ∈ EA, fractionalEdgeLoad G w e) = ∑ _e ∈ EA, (1 / 2 : ℝ) := by
        apply sum_congr rfl
        intro e he
        exact fractionalEdgeLoad_zeroExtend_proposition72bWeight_of_subset_left
          hAB f hcross hAcard hAleB (mem_filter.mp he).1 (mem_filter.mp he).2
      _ = (EA.card : ℝ) / 2 := by simp [div_eq_mul_inv]
  have hsumB :
      (∑ e ∈ EB, fractionalEdgeLoad G w e) = (EB.card : ℝ) / 2 := by
    calc
      (∑ e ∈ EB, fractionalEdgeLoad G w e) = ∑ _e ∈ EB, (1 / 2 : ℝ) := by
        apply sum_congr rfl
        intro e he
        exact fractionalEdgeLoad_zeroExtend_proposition72bWeight_of_subset_right
          hAB f hcross hAcard hBle (mem_filter.mp he).1 (mem_filter.mp he).2
      _ = (EB.card : ℝ) / 2 := by simp [div_eq_mul_inv]
  have hpacking :=
    isFractionalInternalCrossPacking_zeroExtend_proposition72bWeight
      hAB f hcross hAcard hAleB hBle
  calc
    fractionalSize G w = ∑ e ∈ EI, fractionalEdgeLoad G w e := by
      simpa only [w, EI] using
        (sum_internalEdge_fractionalEdgeLoad_eq_fractionalSize hpacking).symm
    _ = ∑ e ∈ EA ∪ EB, fractionalEdgeLoad G w e := hsumSupport
    _ = (∑ e ∈ EA, fractionalEdgeLoad G w e) +
        ∑ e ∈ EB, fractionalEdgeLoad G w e := sum_union hdis
    _ = (EA.card : ℝ) / 2 + (EB.card : ℝ) / 2 := by rw [hsumA, hsumB]
    _ = ((sideEdgeFinset G A).card : ℝ) / 2 +
        ((sideEdgeFinset G B).card : ℝ) / 2 := by rfl

/-- Exact arbitrary-internal-colour form of Proposition 7.2(b). -/
theorem proposition72b_twoBlobPacking_exact
    {G : SimpleGraph α} {A B : Finset α} (hAB : Disjoint A B)
    (f : A ↪ B)
    (hcross : ∀ a : A, ∀ b : B, G.Adj a.1 b.1 ↔ b ≠ f a)
    (hAcard : 3 ≤ A.card) (hAleB : A.card ≤ B.card)
    (hBle : B.card ≤ A.card + 1) :
    IsFractionalInternalCrossPacking G (A : Set α)
        (zeroExtendTriangleWeight G (proposition72bWeight A B f)) ∧
      fractionalSize G
          (zeroExtendTriangleWeight G (proposition72bWeight A B f)) =
        ((sideEdgeFinset G A).card : ℝ) / 2 +
          ((sideEdgeFinset G B).card : ℝ) / 2 :=
  ⟨isFractionalInternalCrossPacking_zeroExtend_proposition72bWeight
      hAB f hcross hAcard hAleB hBle,
    fractionalSize_zeroExtend_proposition72bWeight
      hAB f hcross hAcard hAleB hBle⟩

end

end Erdos76
