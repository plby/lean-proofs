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
import ErdosProblems.Erdos76.WeightedHypergraph
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

/-! The three-uniform hypergraph of monochromatic triangles. -/

open Finset

namespace Erdos76

noncomputable section

attribute [local instance] Classical.propDecidable

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- The three graph edges supported by a triangle candidate. -/
def triangleEdgeSet (t : Finset A) : Finset (Finset A) :=
  t.powersetCard 2

@[simp] lemma card_triangleEdgeSet {t : Finset A} (ht : t.card = 3) :
    (triangleEdgeSet t).card = 3 := by
  simp [triangleEdgeSet, card_powersetCard, ht]

lemma triangleEdgeSet_subset_univ_edges (t : Finset A) :
    triangleEdgeSet t ⊆ (Finset.univ : Finset A).powersetCard 2 := by
  apply powersetCard_mono
  exact subset_univ t

/-- An index for a monochromatic triangle in the colouring represented by
`G`. -/
abbrev MonoTriangle (G : SimpleGraph A) :=
  {t : Finset A // t ∈ monochromaticTriangles G}

/-- Graph edges are represented by two-element vertex finsets.  The active
vertex set therefore has cardinality `choose |A| 2`, while the edge indices
are exactly the monochromatic triangles. -/
def monochromaticTriangleHypergraph (G : SimpleGraph A) :
    FiniteHypergraph (Finset A) (MonoTriangle G) where
  vertexSet := (Finset.univ : Finset A).powersetCard 2
  support t := triangleEdgeSet t.1
  support_subset_vertexSet t := triangleEdgeSet_subset_univ_edges t.1

lemma monochromaticTriangleHypergraph_isUniform (G : SimpleGraph A) :
    (monochromaticTriangleHypergraph G).IsUniform 3 := by
  intro t
  apply card_triangleEdgeSet
  rcases (mem_monochromaticTriangles.mp t.2) with ht | ht
  · exact ht.card_eq
  · exact ht.card_eq

@[simp] lemma card_monochromaticTriangleHypergraph_vertexSet (G : SimpleGraph A) :
    (monochromaticTriangleHypergraph G).vertexSet.card = (Fintype.card A).choose 2 := by
  simp [monochromaticTriangleHypergraph, card_powersetCard]

lemma inter_card_le_one_of_disjoint_triangleEdgeSet {s t : Finset A}
    (hd : Disjoint (triangleEdgeSet s) (triangleEdgeSet t)) : #(s ∩ t) ≤ 1 := by
  by_contra h
  have htwo : 2 ≤ #(s ∩ t) := by omega
  obtain ⟨p, hp⟩ := powersetCard_nonempty.mpr htwo
  have hpdata := mem_powersetCard.mp hp
  have hps : p ∈ triangleEdgeSet s := by
    rw [triangleEdgeSet, mem_powersetCard]
    exact ⟨hpdata.1.trans inter_subset_left, hpdata.2⟩
  have hpt : p ∈ triangleEdgeSet t := by
    rw [triangleEdgeSet, mem_powersetCard]
    exact ⟨hpdata.1.trans inter_subset_right, hpdata.2⟩
  exact (Finset.disjoint_left.mp hd hps) hpt

/-- Forget the subtype proofs in a matching of the monochromatic-triangle
hypergraph. -/
def matchingTriangles {G : SimpleGraph A} (M : Finset (MonoTriangle G)) :
    Finset (Finset A) :=
  M.image Subtype.val

@[simp] lemma card_matchingTriangles {G : SimpleGraph A}
    (M : Finset (MonoTriangle G)) : (matchingTriangles M).card = M.card := by
  exact card_image_of_injective M Subtype.val_injective

lemma matchingTriangles_subset {G : SimpleGraph A} (M : Finset (MonoTriangle G)) :
    matchingTriangles M ⊆ monochromaticTriangles G := by
  intro t ht
  obtain ⟨s, hsM, rfl⟩ := mem_image.mp ht
  exact s.2

lemma matchingTriangles_edgeDisjoint {G : SimpleGraph A}
    {M : Finset (MonoTriangle G)}
    (hM : (monochromaticTriangleHypergraph G).IsMatching M) :
    EdgeDisjoint (matchingTriangles M) := by
  intro s hs t ht hst
  obtain ⟨s', hs'M, rfl⟩ := mem_image.mp hs
  obtain ⟨t', ht'M, rfl⟩ := mem_image.mp ht
  have hs't' : s' ≠ t' := fun h ↦ hst (congr_arg Subtype.val h)
  have hdis : Disjoint (triangleEdgeSet s'.1) (triangleEdgeSet t'.1) :=
    hM (by simpa using hs'M) (by simpa using ht'M) hs't'
  exact inter_card_le_one_of_disjoint_triangleEdgeSet hdis

lemma matchingTriangles_isMonochromaticPacking {G : SimpleGraph A}
    {M : Finset (MonoTriangle G)}
    (hM : (monochromaticTriangleHypergraph G).IsMatching M) :
    IsMonochromaticPacking G (matchingTriangles M) :=
  ⟨matchingTriangles_subset M, matchingTriangles_edgeDisjoint hM⟩

lemma matching_card_le_monoPackingNumber {G : SimpleGraph A}
    {M : Finset (MonoTriangle G)}
    (hM : (monochromaticTriangleHypergraph G).IsMatching M) :
    M.card ≤ monoPackingNumber G := by
  rw [← card_matchingTriangles M]
  exact card_le_monoPackingNumber (matchingTriangles_isMonochromaticPacking hM)

end

end Erdos76
