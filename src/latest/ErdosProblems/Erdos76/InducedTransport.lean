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

/-!
# Extending fractional packings from induced subgraphs

A triangle weight on the graph induced by a finite set `S` is extended to the
ambient graph by assigning weight zero to every triangle not contained in
`S`.  The construction preserves total weight and the load on each induced
edge.  In particular, a feasible fractional packing of the induced graph is a
feasible fractional packing of the ambient graph.

The embedding of the subtype is kept explicit throughout.  This avoids
depending on definitional equality between the predicates `x ∈ S` and
`x ∈ (↑S : Set α)`; the small comparison lemmas below use subtype extensionality
and proof irrelevance at that boundary.
-/

open Finset
open scoped BigOperators

namespace Erdos76

noncomputable section

attribute [local instance] Classical.propDecidable

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The canonical inclusion of a finite subtype into its ambient type. -/
def inducedEmbedding (S : Finset α) : S ↪ α :=
  Function.Embedding.subtype (fun x : α ↦ x ∈ S)

@[simp] lemma inducedEmbedding_apply (S : Finset α) (x : S) :
    inducedEmbedding S x = x := rfl

/-- The two syntactically different subtype inclusions used by `Finset` and
`SimpleGraph.induce` agree.  The proof does not rely on their proof fields
being definitionally equal. -/
lemma inducedEmbedding_eq_setEmbedding (S : Finset α) :
    inducedEmbedding S =
      Function.Embedding.subtype (fun x : α ↦ x ∈ (S : Set α)) := by
  ext x
  rfl

/-- Restrict an ambient finset known to lie in `S` to the subtype `S`. -/
def restrictToInduced (S : Finset α) (t : Finset α)
    (ht : t ⊆ S) : Finset S :=
  t.subtype (· ∈ S)

/-- Restriction is inverse to the subtype inclusion.  `Subtype.ext` is used
explicitly here: the membership proofs in the two subtype values need not be
definitionally identical. -/
lemma restrictToInduced_map (S : Finset α) (t : Finset S) :
    restrictToInduced S (t.map (inducedEmbedding S))
        (fun _ hx ↦ Finset.property_of_mem_map_subtype t hx) = t := by
  ext x
  constructor
  · intro hx
    have hx' : (x : α) ∈ t.map (inducedEmbedding S) := by
      exact Finset.mem_subtype.mp hx
    obtain ⟨y, hy, hyx⟩ := Finset.mem_map.mp hx'
    have : y = x := Subtype.ext hyx
    simpa only [this] using hy
  · intro hx
    apply Finset.mem_subtype.mpr
    exact Finset.mem_map.mpr ⟨x, hx, rfl⟩

/-- Extend a weight on the induced vertex type by zero outside `S`. -/
def extendInducedWeight (S : Finset α) (w : Finset S → ℝ) : Finset α → ℝ :=
  fun t ↦ if ht : t ⊆ S then w (restrictToInduced S t ht) else 0

@[simp]
lemma extendInducedWeight_map (S : Finset α) (w : Finset S → ℝ)
    (t : Finset S) :
    extendInducedWeight S w (t.map (inducedEmbedding S)) = w t := by
  classical
  rw [extendInducedWeight, dif_pos]
  · rw [restrictToInduced_map]
  · exact fun x hx ↦ Finset.property_of_mem_map_subtype t hx

lemma extendInducedWeight_eq_zero {S : Finset α} {w : Finset S → ℝ}
    {t : Finset α} (ht : ¬t ⊆ S) :
    extendInducedWeight S w t = 0 := by
  simp [extendInducedWeight, ht]

private lemma inducedClique_map_iff (G : SimpleGraph α) (S : Finset α)
    (t : Finset S) (n : ℕ) :
    (G.induce (S : Set α)).IsNClique n t ↔
      G.IsNClique n (t.map (inducedEmbedding S)) := by
  rw [inducedEmbedding_eq_setEmbedding]
  exact SimpleGraph.isNClique_induce_iff (G := G) (S : Set α) t n

private lemma edge_mem_map_iff (S : Finset α) (p : Sym2 S)
    (t : Finset S) :
    (inducedEmbedding S).sym2Map p ∈ (t.map (inducedEmbedding S)).sym2 ↔
      p ∈ t.sym2 := by
  rw [Finset.sym2_map]
  constructor
  · intro hp
    obtain ⟨q, hq, hqp⟩ := Finset.mem_map.mp hp
    have : q = p := (inducedEmbedding S).sym2Map.injective hqp
    simpa only [this] using hq
  · intro hp
    exact Finset.mem_map.mpr ⟨p, hp, rfl⟩

/-- Extension by zero preserves total fractional triangle weight. -/
lemma fractionalSize_extendInducedWeight (G : SimpleGraph α) (S : Finset α)
    (w : Finset S → ℝ) :
    fractionalSize G (extendInducedWeight S w) =
      fractionalSize (G.induce (S : Set α)) w := by
  classical
  letI : DecidableRel G.Adj := Classical.decRel _
  letI : DecidableRel (G.induce (S : Set α)).Adj := Classical.decRel _
  unfold fractionalSize
  symm
  apply Finset.sum_bij_ne_zero
    (fun t _ _ ↦ t.map (inducedEmbedding S))
  · intro t ht hwt
    apply SimpleGraph.mem_cliqueFinset_iff.mpr
    exact (inducedClique_map_iff G S t 3).mp
      (SimpleGraph.mem_cliqueFinset_iff.mp ht)
  · intro t₁ ht₁ hw₁ t₂ ht₂ hw₂ heq
    exact Finset.map_injective (inducedEmbedding S) heq
  · intro t ht hne
    have hsub : t ⊆ S := by
      by_contra h
      simp only [extendInducedWeight, dif_neg h] at hne
      exact hne rfl
    let u : Finset S := restrictToInduced S t hsub
    have humap : u.map (inducedEmbedding S) = t := by
      simpa only [u, restrictToInduced, inducedEmbedding] using
        (Finset.subtype_map_of_mem hsub)
    have huclique : u ∈ (G.induce (S : Set α)).cliqueFinset 3 := by
      apply SimpleGraph.mem_cliqueFinset_iff.mpr
      rw [inducedClique_map_iff, humap]
      exact SimpleGraph.mem_cliqueFinset_iff.mp ht
    have hwu : w u ≠ 0 := by
      simpa only [← humap, extendInducedWeight_map] using hne
    exact ⟨u, huclique, hwu, humap⟩
  · intro t ht hwt
    exact (extendInducedWeight_map S w t).symm

/-- Extension by zero preserves the load on each edge of the induced graph. -/
lemma fractionalEdgeLoad_extendInducedWeight (G : SimpleGraph α) (S : Finset α)
    (w : Finset S → ℝ) (p : Sym2 S) :
    fractionalEdgeLoad G (extendInducedWeight S w)
        ((inducedEmbedding S).sym2Map p) =
      fractionalEdgeLoad (G.induce (S : Set α)) w p := by
  classical
  letI : DecidableRel G.Adj := Classical.decRel _
  letI : DecidableRel (G.induce (S : Set α)).Adj := Classical.decRel _
  unfold fractionalEdgeLoad
  symm
  apply Finset.sum_bij_ne_zero
    (fun t _ _ ↦ t.map (inducedEmbedding S))
  · intro t ht hwt
    simp only [Finset.mem_filter] at ht ⊢
    exact ⟨SimpleGraph.mem_cliqueFinset_iff.mpr
        ((inducedClique_map_iff G S t 3).mp
          (SimpleGraph.mem_cliqueFinset_iff.mp ht.1)),
      (edge_mem_map_iff S p t).mpr ht.2⟩
  · intro t₁ ht₁ hw₁ t₂ ht₂ hw₂ heq
    exact Finset.map_injective (inducedEmbedding S) heq
  · intro t ht hne
    simp only [Finset.mem_filter] at ht
    have hsub : t ⊆ S := by
      by_contra h
      simp only [extendInducedWeight, dif_neg h] at hne
      exact hne rfl
    let u : Finset S := restrictToInduced S t hsub
    have humap : u.map (inducedEmbedding S) = t := by
      simpa only [u, restrictToInduced, inducedEmbedding] using
        (Finset.subtype_map_of_mem hsub)
    have huclique : u ∈ (G.induce (S : Set α)).cliqueFinset 3 := by
      apply SimpleGraph.mem_cliqueFinset_iff.mpr
      rw [inducedClique_map_iff, humap]
      exact SimpleGraph.mem_cliqueFinset_iff.mp ht.1
    have hp : p ∈ u.sym2 := by
      apply (edge_mem_map_iff S p u).mp
      simpa only [humap] using ht.2
    have hwu : w u ≠ 0 := by
      simpa only [← humap, extendInducedWeight_map] using hne
    exact ⟨u, Finset.mem_filter.mpr ⟨huclique, hp⟩, hwu, humap⟩
  · intro t ht hwt
    exact (extendInducedWeight_map S w t).symm

private lemma edgeLoad_extendInducedWeight_eq_zero_of_not_subset
    (G : SimpleGraph α) (S : Finset α) (w : Finset S → ℝ)
    (a b : α) (ha : a ∉ S) :
    fractionalEdgeLoad G (extendInducedWeight S w) s(a, b) = 0 := by
  classical
  letI : DecidableRel G.Adj := Classical.decRel _
  unfold fractionalEdgeLoad
  apply Finset.sum_eq_zero
  intro t ht
  simp only [Finset.mem_filter] at ht
  rw [extendInducedWeight, dif_neg]
  intro hsub
  exact ha (hsub (Finset.mk_mem_sym2_iff.mp ht.2).1)

/-- A feasible fractional packing of an induced subgraph remains feasible
after extension by zero to the ambient graph. -/
lemma IsFractionalPacking.extendInduced {G : SimpleGraph α} {S : Finset α}
    {w : Finset S → ℝ} (hw : IsFractionalPacking (G.induce (S : Set α)) w) :
    IsFractionalPacking G (extendInducedWeight S w) := by
  classical
  letI : DecidableRel G.Adj := Classical.decRel _
  letI : DecidableRel (G.induce (S : Set α)).Adj := Classical.decRel _
  constructor
  · intro t ht
    by_cases hsub : t ⊆ S
    · let u : Finset S := restrictToInduced S t hsub
      have humap : u.map (inducedEmbedding S) = t := by
        simpa only [u, restrictToInduced, inducedEmbedding] using
          (Finset.subtype_map_of_mem hsub)
      rw [extendInducedWeight, dif_pos hsub]
      apply hw.1 u
      apply SimpleGraph.mem_cliqueFinset_iff.mpr
      rw [inducedClique_map_iff, humap]
      exact SimpleGraph.mem_cliqueFinset_iff.mp ht
    · simp [extendInducedWeight, hsub]
  · intro p hp
    induction p using Sym2.inductionOn with
    | hf a b =>
      by_cases ha : a ∈ S
      · by_cases hb : b ∈ S
        · let aS : S := ⟨a, ha⟩
          let bS : S := ⟨b, hb⟩
          let q : Sym2 S := s(aS, bS)
          have hmap : (inducedEmbedding S).sym2Map q = s(a, b) := by
            rfl
          have hab : G.Adj a b := by
            simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using hp
          have hq : q ∈ (G.induce (S : Set α)).edgeFinset := by
            apply SimpleGraph.mem_edgeFinset.mpr
            change (G.induce (S : Set α)).Adj aS bS
            exact hab
          rw [← hmap, fractionalEdgeLoad_extendInducedWeight]
          exact hw.2 q hq
        · have hz := edgeLoad_extendInducedWeight_eq_zero_of_not_subset
              G S w b a hb
          rw [show s(a, b) = s(b, a) from Sym2.sound (Sym2.Rel.swap a b)]
          rw [hz]
          norm_num
      · rw [edgeLoad_extendInducedWeight_eq_zero_of_not_subset G S w a b ha]
        norm_num

/-- Taking complements commutes with taking an induced subgraph. -/
lemma compl_induce (G : SimpleGraph α) (S : Finset α) :
    Gᶜ.induce (S : Set α) = (G.induce (S : Set α))ᶜ := by
  ext x y
  simp [SimpleGraph.compl_adj]

/-- Blue weights, naturally given on the complement of the induced red
graph, extend to a packing of the ambient complement. -/
lemma IsFractionalPacking.extendInduced_compl {G : SimpleGraph α}
    {S : Finset α} {w : Finset S → ℝ}
    (hw : IsFractionalPacking (G.induce (S : Set α))ᶜ w) :
    IsFractionalPacking Gᶜ (extendInducedWeight S w) := by
  apply IsFractionalPacking.extendInduced (G := Gᶜ) (S := S)
  rwa [compl_induce]

/-- The covered-edge normalization is preserved by zero extension. -/
lemma fractionalCoveredSize_extendInducedWeight
    (G : SimpleGraph α) (S : Finset α) (w : Finset S → ℝ) :
    fractionalCoveredSize G (extendInducedWeight S w) =
      fractionalCoveredSize (G.induce (S : Set α)) w := by
  simp only [fractionalCoveredSize, fractionalSize_extendInducedWeight]

/-- Package the red and blue extensions used in local averaging. -/
lemma extendInduced_pair {G : SimpleGraph α} {S : Finset α}
    {wR wB : Finset S → ℝ}
    (hR : IsFractionalPacking (G.induce (S : Set α)) wR)
    (hB : IsFractionalPacking (G.induce (S : Set α))ᶜ wB) :
    IsFractionalPacking G (extendInducedWeight S wR) ∧
      IsFractionalPacking Gᶜ (extendInducedWeight S wB) ∧
      fractionalCoveredSize G (extendInducedWeight S wR) +
          fractionalCoveredSize Gᶜ (extendInducedWeight S wB) =
        fractionalCoveredSize (G.induce (S : Set α)) wR +
          fractionalCoveredSize (G.induce (S : Set α))ᶜ wB := by
  refine ⟨hR.extendInduced, hB.extendInduced_compl, ?_⟩
  rw [fractionalCoveredSize_extendInducedWeight]
  rw [fractionalCoveredSize_extendInducedWeight, compl_induce]

end

end Erdos76
