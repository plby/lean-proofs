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
import ErdosProblems.Erdos76.AlmostBipartitePartSize
import ErdosProblems.Erdos76.FractionalStabilityInduction
import Mathlib.Tactic

/-!
# The almost-bipartite one-vertex extension

This module formalizes Lemma 2.7 of Gruslys--Letzter.  It is downstream of
the companion almost-complete decomposition theorem and of the
matching-avoidance form of Proposition 4.2.
-/

open Finset
open scoped BigOperators

namespace Erdos76

noncomputable section

attribute [local instance] Classical.propDecidable

/-- The old side `s`, embedded into `Fin (n+1)`, together with the newly
adjoined final vertex. -/
def insertLastPart {n : ℕ} (s : Set (Fin n)) : Set (Fin (n + 1)) :=
  insert (Fin.last n) (Fin.castSucc '' s)

@[simp] lemma castSucc_mem_insertLastPart {n : ℕ} (s : Set (Fin n))
    (i : Fin n) : i.castSucc ∈ insertLastPart s ↔ i ∈ s := by
  simp [insertLastPart, Fin.castSucc_ne_last, Fin.castSucc_inj]

@[simp] lemma last_mem_insertLastPart {n : ℕ} (s : Set (Fin n)) :
    Fin.last n ∈ insertLastPart s := by
  simp [insertLastPart]

@[simp] lemma ncard_insertLastPart {n : ℕ} (s : Set (Fin n)) :
    (insertLastPart s).ncard = s.ncard + 1 := by
  rw [insertLastPart, Set.ncard_insert_of_notMem]
  · exact congrArg (fun q : ℕ ↦ q + 1)
      (Set.ncard_image_of_injective s (Fin.castSucc_injective n))
  · rintro ⟨i, _hi, hi⟩
    exact Fin.castSucc_ne_last i hi

@[simp] lemma ncard_compl_insertLastPart {n : ℕ} (s : Set (Fin n)) :
    (insertLastPart s)ᶜ.ncard = sᶜ.ncard := by
  have hold : s.ncard + sᶜ.ncard = n := by
    rw [Set.ncard_add_ncard_compl]
    simp
  have hnew : (insertLastPart s).ncard + (insertLastPart s)ᶜ.ncard = n + 1 := by
    rw [Set.ncard_add_ncard_compl]
    simp
  rw [ncard_insertLastPart] at hnew
  omega

/-- Blue neighbours of the new final vertex which lie in the old side `s`. -/
def newBlueNeighbors {n : ℕ} (G : SimpleGraph (Fin (n + 1)))
    (s : Set (Fin n)) : Finset (Fin n) :=
  univ.filter fun i ↦ i ∈ s ∧ G.Adj i.castSucc (Fin.last n)

@[simp] lemma mem_newBlueNeighbors {n : ℕ}
    (G : SimpleGraph (Fin (n + 1))) (s : Set (Fin n)) (i : Fin n) :
    i ∈ newBlueNeighbors G s ↔
      i ∈ s ∧ G.Adj i.castSucc (Fin.last n) := by
  simp [newBlueNeighbors]

private lemma last_red_adj_of_mem_side_sdiff_newBlue {n : ℕ}
    (G : SimpleGraph (Fin (n + 1))) (s : Set (Fin n))
    {v : Fin n} (hv : v ∈ s.toFinset \ newBlueNeighbors G s) :
    Gᶜ.Adj (Fin.last n) v.castSucc := by
  have hvData := mem_sdiff.mp hv
  rw [SimpleGraph.compl_adj]
  refine ⟨(Fin.castSucc_ne_last v).symm, ?_⟩
  intro hadj
  exact hvData.2 ((mem_newBlueNeighbors G s v).mpr
    ⟨by simpa using hvData.1, hadj.symm⟩)

private def lastEdgeEmbedding (n : ℕ) : Fin n ↪ Sym2 (Fin (n + 1)) where
  toFun i := s(i.castSucc, Fin.last n)
  inj' := by
    intro i j hij
    change s(i.castSucc, Fin.last n) =
      s(j.castSucc, Fin.last n) at hij
    have hi : i.castSucc ∈ s(i.castSucc, Fin.last n) := by simp
    rw [hij] at hi
    simp only [Sym2.mem_iff] at hi
    rcases hi with hi | hi
    · exact (Fin.castSuccEmb).injective hi
    · exact (Fin.castSucc_ne_last i hi).elim

private def oldInternalEdges {n : ℕ} (H : SimpleGraph (Fin n))
    (s : Set (Fin n)) : Finset (Sym2 (Fin (n + 1))) :=
  (internalEdgeFinset H s).map Fin.castSuccEmb.sym2Map

private def newInternalEdges {n : ℕ} (G : SimpleGraph (Fin (n + 1)))
    (s : Set (Fin n)) : Finset (Sym2 (Fin (n + 1))) :=
  (newBlueNeighbors G s).map (lastEdgeEmbedding n)

private lemma oldInternalEdges_disjoint_newInternalEdges {n : ℕ}
    (H : SimpleGraph (Fin n)) (G : SimpleGraph (Fin (n + 1)))
    (s : Set (Fin n)) :
    Disjoint (oldInternalEdges H s) (newInternalEdges G s) := by
  rw [Finset.disjoint_left]
  intro e heOld heNew
  rcases mem_map.mp heOld with ⟨p, _hp, rfl⟩
  rcases mem_map.mp heNew with ⟨i, _hi, hpi⟩
  change s(i.castSucc, Fin.last n) = Fin.castSuccEmb.sym2Map p at hpi
  have hlast : Fin.last n ∈
      Fin.castSuccEmb.sym2Map p := by
    rw [← hpi]
    simp
  change Fin.last n ∈ Sym2.map Fin.castSucc p at hlast
  induction p using Sym2.inductionOn with
  | hf a b =>
      simp only [Sym2.map_mk, Sym2.mem_iff] at hlast
      rcases hlast with hlast | hlast
      · exact Fin.castSucc_ne_last a hlast.symm
      · exact Fin.castSucc_ne_last b hlast.symm

private lemma last_not_mem_castSym2Map {n : ℕ} (p : Sym2 (Fin n)) :
    Fin.last n ∉ Fin.castSuccEmb.sym2Map p := by
  change Fin.last n ∉ Sym2.map Fin.castSucc p
  induction p using Sym2.inductionOn with
  | hf a b =>
      simp only [Sym2.map_mk, Sym2.mem_iff, not_or]
      exact ⟨(Fin.castSucc_ne_last a).symm,
        (Fin.castSucc_ne_last b).symm⟩

@[simp] private lemma mem_oldInternalEdges_cast_cast {n : ℕ}
    (H : SimpleGraph (Fin n)) (s : Set (Fin n)) (a b : Fin n) :
    s(a.castSucc, b.castSucc) ∈ oldInternalEdges H s ↔
      s(a, b) ∈ internalEdgeFinset H s := by
  constructor
  · intro hmem
    rcases mem_map.mp hmem with ⟨p, hp, hpeq⟩
    have hpeq' : Fin.castSuccEmb.sym2Map p =
        Fin.castSuccEmb.sym2Map s(a, b) := by
      simpa [Sym2.map_mk] using hpeq
    have : p = s(a, b) := Fin.castSuccEmb.sym2Map.injective hpeq'
    simpa [this] using hp
  · intro hp
    refine mem_map.mpr ⟨s(a, b), hp, ?_⟩
    simp [Sym2.map_mk]

@[simp] private lemma not_mem_oldInternalEdges_last_left {n : ℕ}
    (H : SimpleGraph (Fin n)) (s : Set (Fin n)) (b : Fin n) :
    s(Fin.last n, b.castSucc) ∉ oldInternalEdges H s := by
  intro hmem
  rcases mem_map.mp hmem with ⟨p, _hp, hpeq⟩
  apply last_not_mem_castSym2Map p
  rw [hpeq]
  simp

@[simp] private lemma not_mem_oldInternalEdges_last_right {n : ℕ}
    (H : SimpleGraph (Fin n)) (s : Set (Fin n)) (a : Fin n) :
    s(a.castSucc, Fin.last n) ∉ oldInternalEdges H s := by
  intro hmem
  rcases mem_map.mp hmem with ⟨p, _hp, hpeq⟩
  apply last_not_mem_castSym2Map p
  rw [hpeq]
  simp

@[simp] private lemma not_mem_oldInternalEdges_last_last {n : ℕ}
    (H : SimpleGraph (Fin n)) (s : Set (Fin n)) :
    s(Fin.last n, Fin.last n) ∉ oldInternalEdges H s := by
  intro hmem
  rcases mem_map.mp hmem with ⟨p, _hp, hpeq⟩
  apply last_not_mem_castSym2Map p
  rw [hpeq]
  simp

@[simp] private lemma mem_newInternalEdges_cast_last {n : ℕ}
    (G : SimpleGraph (Fin (n + 1))) (s : Set (Fin n)) (a : Fin n) :
    s(a.castSucc, Fin.last n) ∈ newInternalEdges G s ↔
      a ∈ newBlueNeighbors G s := by
  constructor
  · intro hmem
    rcases mem_map.mp hmem with ⟨i, hi, hieq⟩
    change s(i.castSucc, Fin.last n) =
      s(a.castSucc, Fin.last n) at hieq
    have hia : i = a := (lastEdgeEmbedding n).injective hieq
    simpa [hia] using hi
  · intro ha
    exact mem_map.mpr ⟨a, ha, rfl⟩

@[simp] private lemma mem_newInternalEdges_last_cast {n : ℕ}
    (G : SimpleGraph (Fin (n + 1))) (s : Set (Fin n)) (b : Fin n) :
    s(Fin.last n, b.castSucc) ∈ newInternalEdges G s ↔
      b ∈ newBlueNeighbors G s := by
  rw [show s(Fin.last n, b.castSucc) =
      s(b.castSucc, Fin.last n) from Sym2.eq_swap]
  exact mem_newInternalEdges_cast_last G s b

@[simp] private lemma not_mem_newInternalEdges_cast_cast {n : ℕ}
    (G : SimpleGraph (Fin (n + 1))) (s : Set (Fin n)) (a b : Fin n) :
    s(a.castSucc, b.castSucc) ∉ newInternalEdges G s := by
  intro hmem
  rcases mem_map.mp hmem with ⟨i, _hi, hieq⟩
  have hlast : Fin.last n ∈ s(a.castSucc, b.castSucc) := by
    rw [← hieq]
    change Fin.last n ∈ s(i.castSucc, Fin.last n)
    simp
  simp only [Sym2.mem_iff] at hlast
  rcases hlast with hlast | hlast
  · exact Fin.castSucc_ne_last a hlast.symm
  · exact Fin.castSucc_ne_last b hlast.symm

@[simp] private lemma not_mem_newInternalEdges_last_last {n : ℕ}
    (G : SimpleGraph (Fin (n + 1))) (s : Set (Fin n)) :
    s(Fin.last n, Fin.last n) ∉ newInternalEdges G s := by
  intro hmem
  rcases mem_map.mp hmem with ⟨i, _hi, hieq⟩
  have hi : i.castSucc ∈ s(Fin.last n, Fin.last n) := by
    rw [← hieq]
    change i.castSucc ∈ s(i.castSucc, Fin.last n)
    simp
  simp only [Sym2.mem_iff] at hi
  rcases hi with hi | hi
  · exact Fin.castSucc_ne_last i hi
  · exact Fin.castSucc_ne_last i hi

private lemma internalEdgeFinset_insertLastPart {n : ℕ}
    (H : SimpleGraph (Fin n)) (G : SimpleGraph (Fin (n + 1)))
    (hHG : IsInitialVertexExtension H G) (s : Set (Fin n)) :
    internalEdgeFinset G (insertLastPart s) =
      oldInternalEdges H s ∪ newInternalEdges G s := by
  ext e
  induction e using Sym2.inductionOn with
  | hf a b =>
      induction a using Fin.lastCases with
      | last =>
          induction b using Fin.lastCases with
          | last =>
              simp [internalEdgeFinset, SimpleGraph.mem_edgeFinset,
                SimpleGraph.mem_edgeSet]
          | cast b =>
              simp [internalEdgeFinset, SimpleGraph.mem_edgeFinset,
                SimpleGraph.mem_edgeSet, SimpleGraph.adj_comm, sameSide_mk,
                and_comm]
      | cast a =>
          induction b using Fin.lastCases with
          | last =>
              simp [internalEdgeFinset, SimpleGraph.mem_edgeFinset,
                SimpleGraph.mem_edgeSet, sameSide_mk, and_comm]
          | cast b =>
              simp [internalEdgeFinset, SimpleGraph.mem_edgeFinset,
                SimpleGraph.mem_edgeSet, sameSide_mk, hHG a b]

/-- Exact same-side edge count after placing the new final vertex into the
side `s`: the old internal edges plus its blue neighbours in that side. -/
theorem card_internalEdgeFinset_insertLastPart {n : ℕ}
    (H : SimpleGraph (Fin n)) (G : SimpleGraph (Fin (n + 1)))
    (hHG : IsInitialVertexExtension H G) (s : Set (Fin n)) :
    (internalEdgeFinset G (insertLastPart s)).card =
      (internalEdgeFinset H s).card + (newBlueNeighbors G s).card := by
  rw [internalEdgeFinset_insertLastPart H G hHG s,
    card_union_of_disjoint
      (oldInternalEdges_disjoint_newInternalEdges H G s),
    oldInternalEdges, newInternalEdges, card_map, card_map]

/-- The two possible placements of the new vertex add respectively the blue
neighbours on the two old sides. -/
theorem exists_extension_partition_of_neighbor_bound {n : ℕ}
    (H : SimpleGraph (Fin n)) (G : SimpleGraph (Fin (n + 1)))
    (hHG : IsInitialVertexExtension H G) (s : Set (Fin n))
    {q : ℕ}
    (hbound : (internalEdgeFinset H s).card +
      min (newBlueNeighbors G s).card
        (newBlueNeighbors G sᶜ).card ≤ q) :
    PartitionCloseToBipartite G q := by
  by_cases hle : (newBlueNeighbors G s).card ≤
      (newBlueNeighbors G sᶜ).card
  · refine ⟨insertLastPart s, ?_⟩
    rw [card_internalEdgeFinset_insertLastPart H G hHG s]
    simpa [min_eq_left hle] using hbound
  · refine ⟨insertLastPart sᶜ, ?_⟩
    rw [card_internalEdgeFinset_insertLastPart H G hHG sᶜ]
    have hinter : internalEdgeFinset H sᶜ = internalEdgeFinset H s := by
      ext e
      induction e using Sym2.inductionOn with
      | hf a b =>
          simp only [internalEdgeFinset, mem_filter,
            SimpleGraph.mem_edgeFinset, sameSide_mk, Set.mem_compl_iff]
          tauto
    rw [hinter]
    simpa [min_eq_right (Nat.le_of_not_ge hle)] using hbound

/-! ## The two numerical steps in Claim 4.6 -/

/-- If the new blue matching and the old internal blue edges almost fill the
smaller part, the old-side decompositions already beat the stability
threshold.  This is Claim 4.6's contradiction, written without the auxiliary
half-integral variable `x`. -/
lemma claim46_old_partition_contradiction
    (n a b k m : ℕ) (hn : 22 ≤ n) (hab : a + b = n)
    (hba : b ≤ a) (hk : k ≤ n / 8) (hpart : k + 4 ≤ b)
    (hlarge : b ≤ m + k + 3) :
    (n : ℝ) * ((n : ℝ) + 1) / 4 <
      ((a.choose 2 + b.choose 2 : ℕ) : ℝ) + 2 * k + 3 * m := by
  have h8k : 8 * k ≤ n := by omega
  have hnR : (22 : ℝ) ≤ n := by exact_mod_cast hn
  have habR : (a : ℝ) + b = n := by exact_mod_cast hab
  have hbaR : (b : ℝ) ≤ a := by exact_mod_cast hba
  have h8kR : (8 : ℝ) * k ≤ n := by exact_mod_cast h8k
  have hpartR : (k : ℝ) + 4 ≤ b := by exact_mod_cast hpart
  have hlargeR : (b : ℝ) ≤ m + k + 3 := by exact_mod_cast hlarge
  rw [Nat.cast_add, Nat.cast_choose_two, Nat.cast_choose_two]
  nlinarith [sq_nonneg ((a : ℝ) - b),
    sq_nonneg ((n : ℝ) - 2 * b - 3)]

/-- The internal-pair count of any bipartition of `n+1` vertices is at least
`(n+1)(n-1)/4`. -/
lemma augmented_internal_pairs_lower_bound
    (n a b : ℕ) (hab : a + b = n + 1) :
    (n + 1 : ℝ) * ((n : ℝ) - 1) / 4 ≤
      ((a.choose 2 + b.choose 2 : ℕ) : ℝ) := by
  have habR : (a : ℝ) + b = n + 1 := by exact_mod_cast hab
  rw [Nat.cast_add, Nat.cast_choose_two, Nat.cast_choose_two]
  nlinarith [sq_nonneg ((a : ℝ) - b)]

/-- The final arithmetic in Lemma 2.7: an augmented-side residual packing
and `k+m` blue cross triangles force the desired `1/8` bound. -/
lemma claim46_final_neighbor_bound
    (n a b k m : ℕ) (hab : a + b = n + 1)
    (hupper :
      ((a.choose 2 + b.choose 2 : ℕ) : ℝ) + 2 * (k + m) ≤
        (n : ℝ) * ((n : ℝ) + 1) / 4) :
    k + m ≤ (n + 1) / 8 := by
  have hlower := augmented_internal_pairs_lower_bound n a b hab
  simp only [Nat.cast_add] at hlower hupper
  have hreal : (8 : ℝ) * ((k + m : ℕ) : ℝ) ≤ n + 1 := by
    simp only [Nat.cast_add]
    nlinarith
  have hnat : 8 * (k + m) ≤ n + 1 := by exact_mod_cast hreal
  omega

/-! ## Transporting old-vertex packings into the extension -/

private def oldVertexFinset (n : ℕ) : Finset (Fin (n + 1)) :=
  univ.erase (Fin.last n)

private def oldVertexEquiv (n : ℕ) : Fin n ≃ oldVertexFinset n :=
  Equiv.ofBijective
    (fun i : Fin n ↦
      (⟨i.castSucc, by simp [oldVertexFinset, Fin.castSucc_ne_last]⟩ :
        oldVertexFinset n))
    ⟨fun _ _ h ↦ Fin.castSuccEmb.injective (congrArg Subtype.val h), by
      rintro ⟨v, hv⟩
      induction v using Fin.lastCases with
      | last => simp [oldVertexFinset] at hv
      | cast i =>
          refine ⟨i, ?_⟩
          apply Subtype.ext
          rfl⟩

@[simp] private lemma oldVertexEquiv_coe (n : ℕ) (i : Fin n) :
    ((oldVertexEquiv n i : oldVertexFinset n) : Fin (n + 1)) = i.castSucc :=
  rfl

private lemma map_oldVertexEquiv_eq_induce {n : ℕ}
    (H : SimpleGraph (Fin n)) (G : SimpleGraph (Fin (n + 1)))
    (hHG : IsInitialVertexExtension H G) :
    H.map (oldVertexEquiv n).toEmbedding =
      G.induce (oldVertexFinset n : Set (Fin (n + 1))) := by
  ext x y
  have hx : ((oldVertexEquiv n).symm x).castSucc =
      (x : Fin (n + 1)) := by
    have hx' := congrArg Subtype.val
      ((oldVertexEquiv n).apply_symm_apply x)
    change ((oldVertexEquiv n).symm x).castSucc = x.val at hx'
    exact hx'
  have hy : ((oldVertexEquiv n).symm y).castSucc =
      (y : Fin (n + 1)) := by
    have hy' := congrArg Subtype.val
      ((oldVertexEquiv n).apply_symm_apply y)
    change ((oldVertexEquiv n).symm y).castSucc = y.val at hy'
    exact hy'
  rw [← SimpleGraph.comap_symm H (oldVertexEquiv n)]
  change H.Adj ((oldVertexEquiv n).symm x)
      ((oldVertexEquiv n).symm y) ↔ G.Adj x.val y.val
  rw [hHG, hx, hy]

/-- Extend a weight on the old `Fin n` vertices by zero to the final point of
`Fin (n+1)`. -/
def liftOldWeight {n : ℕ} (w : Finset (Fin n) → ℝ) :
    Finset (Fin (n + 1)) → ℝ :=
  extendInducedWeight (oldVertexFinset n)
    (relabelWeight (oldVertexEquiv n) w)

lemma IsFractionalPacking.liftOld {n : ℕ}
    {H : SimpleGraph (Fin n)} {G : SimpleGraph (Fin (n + 1))}
    (hHG : IsInitialVertexExtension H G) {w : Finset (Fin n) → ℝ}
    (hw : IsFractionalPacking H w) :
    IsFractionalPacking G (liftOldWeight w) := by
  have hw' := hw.relabel (oldVertexEquiv n)
  rw [map_oldVertexEquiv_eq_induce H G hHG] at hw'
  exact hw'.extendInduced

lemma fractionalCoveredSize_liftOld {n : ℕ}
    (H : SimpleGraph (Fin n)) (G : SimpleGraph (Fin (n + 1)))
    (hHG : IsInitialVertexExtension H G) (w : Finset (Fin n) → ℝ) :
    fractionalCoveredSize G (liftOldWeight w) =
      fractionalCoveredSize H w := by
  rw [liftOldWeight, fractionalCoveredSize_extendInducedWeight,
    ← map_oldVertexEquiv_eq_induce H G hHG,
    fractionalCoveredSize_relabel]

private lemma initialVertexExtension_compl {n : ℕ}
    {H : SimpleGraph (Fin n)} {G : SimpleGraph (Fin (n + 1))}
    (hHG : IsInitialVertexExtension H G) :
    IsInitialVertexExtension Hᶜ Gᶜ := by
  intro a b
  simp only [SimpleGraph.compl_adj]
  rw [hHG]
  constructor
  · rintro ⟨hab, hnadj⟩
    exact ⟨fun hcast ↦ hab (Fin.castSuccEmb.injective hcast), hnadj⟩
  · rintro ⟨hcast, hnadj⟩
    exact ⟨fun hab ↦ hcast (congrArg Fin.castSucc hab), hnadj⟩

lemma IsFractionalPacking.liftOld_compl {n : ℕ}
    {H : SimpleGraph (Fin n)} {G : SimpleGraph (Fin (n + 1))}
    (hHG : IsInitialVertexExtension H G) {w : Finset (Fin n) → ℝ}
    (hw : IsFractionalPacking Hᶜ w) :
    IsFractionalPacking Gᶜ (liftOldWeight w) :=
  hw.liftOld (initialVertexExtension_compl hHG)

lemma fractionalCoveredSize_liftOld_compl {n : ℕ}
    (H : SimpleGraph (Fin n)) (G : SimpleGraph (Fin (n + 1)))
    (hHG : IsInitialVertexExtension H G) (w : Finset (Fin n) → ℝ) :
    fractionalCoveredSize Gᶜ (liftOldWeight w) =
      fractionalCoveredSize Hᶜ w :=
  fractionalCoveredSize_liftOld Hᶜ Gᶜ
    (initialVertexExtension_compl hHG) w

/-! ## Maximum blue matchings across the two new-neighbour sets -/

/-- An oriented matching from `B₁` to `B₂` consisting of blue edges of
the old graph.  The orientation makes the two sets of saturated vertices
literal images of the two coordinate projections. -/
def IsBluePairMatching {n : ℕ} (H : SimpleGraph (Fin n))
    (B₁ B₂ : Finset (Fin n)) (M : Finset (Fin n × Fin n)) : Prop :=
  (∀ p ∈ M, p.1 ∈ B₁ ∧ p.2 ∈ B₂ ∧ H.Adj p.1 p.2) ∧
    (M : Set (Fin n × Fin n)).Pairwise fun p q ↦
      p.1 ≠ q.1 ∧ p.2 ≠ q.2

private def bluePairMatchings {n : ℕ} (H : SimpleGraph (Fin n))
    (B₁ B₂ : Finset (Fin n)) : Finset (Finset (Fin n × Fin n)) :=
  univ.filter (IsBluePairMatching H B₁ B₂)

@[simp] private lemma mem_bluePairMatchings {n : ℕ}
    (H : SimpleGraph (Fin n)) (B₁ B₂ : Finset (Fin n))
    (M : Finset (Fin n × Fin n)) :
    M ∈ bluePairMatchings H B₁ B₂ ↔
      IsBluePairMatching H B₁ B₂ M := by
  simp [bluePairMatchings]

private lemma empty_isBluePairMatching {n : ℕ} (H : SimpleGraph (Fin n))
    (B₁ B₂ : Finset (Fin n)) :
    IsBluePairMatching H B₁ B₂ ∅ := by
  simp [IsBluePairMatching]

/-- A maximum blue matching across two specified vertex sets exists by
finite maximization. -/
theorem exists_maximum_bluePairMatching {n : ℕ}
    (H : SimpleGraph (Fin n)) (B₁ B₂ : Finset (Fin n)) :
    ∃ M : Finset (Fin n × Fin n),
      IsBluePairMatching H B₁ B₂ M ∧
        ∀ N : Finset (Fin n × Fin n),
          IsBluePairMatching H B₁ B₂ N → N.card ≤ M.card := by
  obtain ⟨M, hM, hmax⟩ := Finset.exists_max_image
    (bluePairMatchings H B₁ B₂) Finset.card
    ⟨∅, mem_bluePairMatchings H B₁ B₂ ∅ |>.mpr
      (empty_isBluePairMatching H B₁ B₂)⟩
  exact ⟨M, (mem_bluePairMatchings H B₁ B₂ M).mp hM,
    fun N hN ↦ hmax N
      ((mem_bluePairMatchings H B₁ B₂ N).mpr hN)⟩

def blueMatchingLeftVertices {n : ℕ} (M : Finset (Fin n × Fin n)) :
    Finset (Fin n) := M.image Prod.fst

def blueMatchingRightVertices {n : ℕ} (M : Finset (Fin n × Fin n)) :
    Finset (Fin n) := M.image Prod.snd

/-- The blue neighbours on the first side not saturated by an oriented
matching. -/
def unsaturatedBlueLeft {n : ℕ} (B : Finset (Fin n))
    (M : Finset (Fin n × Fin n)) : Finset (Fin n) :=
  B \ blueMatchingLeftVertices M

/-- The blue neighbours on the second side not saturated by an oriented
matching. -/
def unsaturatedBlueRight {n : ℕ} (B : Finset (Fin n))
    (M : Finset (Fin n × Fin n)) : Finset (Fin n) :=
  B \ blueMatchingRightVertices M

lemma IsBluePairMatching.left_injective {n : ℕ}
    {H : SimpleGraph (Fin n)} {B₁ B₂ : Finset (Fin n)}
    {M : Finset (Fin n × Fin n)}
    (hM : IsBluePairMatching H B₁ B₂ M) :
    Set.InjOn Prod.fst (M : Set (Fin n × Fin n)) := by
  intro p hp q hq hpq
  by_contra hpne
  exact (hM.2 hp hq hpne).1 hpq

lemma IsBluePairMatching.right_injective {n : ℕ}
    {H : SimpleGraph (Fin n)} {B₁ B₂ : Finset (Fin n)}
    {M : Finset (Fin n × Fin n)}
    (hM : IsBluePairMatching H B₁ B₂ M) :
    Set.InjOn Prod.snd (M : Set (Fin n × Fin n)) := by
  intro p hp q hq hpq
  by_contra hpne
  exact (hM.2 hp hq hpne).2 hpq

lemma IsBluePairMatching.card_leftVertices {n : ℕ}
    {H : SimpleGraph (Fin n)} {B₁ B₂ : Finset (Fin n)}
    {M : Finset (Fin n × Fin n)}
    (hM : IsBluePairMatching H B₁ B₂ M) :
    (blueMatchingLeftVertices M).card = M.card := by
  exact Finset.card_image_iff.mpr hM.left_injective

lemma IsBluePairMatching.card_rightVertices {n : ℕ}
    {H : SimpleGraph (Fin n)} {B₁ B₂ : Finset (Fin n)}
    {M : Finset (Fin n × Fin n)}
    (hM : IsBluePairMatching H B₁ B₂ M) :
    (blueMatchingRightVertices M).card = M.card := by
  exact Finset.card_image_iff.mpr hM.right_injective

lemma IsBluePairMatching.leftVertices_subset {n : ℕ}
    {H : SimpleGraph (Fin n)} {B₁ B₂ : Finset (Fin n)}
    {M : Finset (Fin n × Fin n)}
    (hM : IsBluePairMatching H B₁ B₂ M) :
    blueMatchingLeftVertices M ⊆ B₁ := by
  rintro x hx
  rcases mem_image.mp hx with ⟨p, hp, rfl⟩
  exact (hM.1 p hp).1

lemma IsBluePairMatching.rightVertices_subset {n : ℕ}
    {H : SimpleGraph (Fin n)} {B₁ B₂ : Finset (Fin n)}
    {M : Finset (Fin n × Fin n)}
    (hM : IsBluePairMatching H B₁ B₂ M) :
    blueMatchingRightVertices M ⊆ B₂ := by
  rintro x hx
  rcases mem_image.mp hx with ⟨p, hp, rfl⟩
  exact (hM.1 p hp).2.1

lemma IsBluePairMatching.card_unsaturatedBlueLeft {n : ℕ}
    {H : SimpleGraph (Fin n)} {B₁ B₂ : Finset (Fin n)}
    {M : Finset (Fin n × Fin n)}
    (hM : IsBluePairMatching H B₁ B₂ M) :
    (unsaturatedBlueLeft B₁ M).card = B₁.card - M.card := by
  rw [unsaturatedBlueLeft, card_sdiff_of_subset hM.leftVertices_subset,
    hM.card_leftVertices]

lemma IsBluePairMatching.card_unsaturatedBlueRight {n : ℕ}
    {H : SimpleGraph (Fin n)} {B₁ B₂ : Finset (Fin n)}
    {M : Finset (Fin n × Fin n)}
    (hM : IsBluePairMatching H B₁ B₂ M) :
    (unsaturatedBlueRight B₂ M).card = B₂.card - M.card := by
  rw [unsaturatedBlueRight, card_sdiff_of_subset hM.rightVertices_subset,
    hM.card_rightVertices]

private lemma exists_unsaturated_left {n : ℕ}
    {H : SimpleGraph (Fin n)} {B₁ B₂ : Finset (Fin n)}
    {M : Finset (Fin n × Fin n)}
    (hM : IsBluePairMatching H B₁ B₂ M)
    (hlt : M.card < B₁.card) :
    ∃ a ∈ B₁, a ∉ blueMatchingLeftVertices M := by
  by_contra hnone
  push_neg at hnone
  have hsub : B₁ ⊆ blueMatchingLeftVertices M := fun a ha ↦ hnone a ha
  have := card_le_card hsub
  rw [hM.card_leftVertices] at this
  omega

private lemma exists_unsaturated_right {n : ℕ}
    {H : SimpleGraph (Fin n)} {B₁ B₂ : Finset (Fin n)}
    {M : Finset (Fin n × Fin n)}
    (hM : IsBluePairMatching H B₁ B₂ M)
    (hlt : M.card < B₂.card) :
    ∃ b ∈ B₂, b ∉ blueMatchingRightVertices M := by
  by_contra hnone
  push_neg at hnone
  have hsub : B₂ ⊆ blueMatchingRightVertices M := fun b hb ↦ hnone b hb
  have := card_le_card hsub
  rw [hM.card_rightVertices] at this
  omega

private lemma maximum_bluePairMatching_nonadjacent_unsaturated {n : ℕ}
    {H : SimpleGraph (Fin n)} {B₁ B₂ : Finset (Fin n)}
    {M : Finset (Fin n × Fin n)}
    (hM : IsBluePairMatching H B₁ B₂ M)
    (hmax : ∀ N : Finset (Fin n × Fin n),
      IsBluePairMatching H B₁ B₂ N → N.card ≤ M.card)
    {a b : Fin n} (haB : a ∈ B₁) (hbB : b ∈ B₂)
    (ha : a ∉ blueMatchingLeftVertices M)
    (hb : b ∉ blueMatchingRightVertices M) :
    ¬ H.Adj a b := by
  intro hab
  have hpnot : (a, b) ∉ M := by
    intro hp
    exact ha (mem_image.mpr ⟨(a, b), hp, rfl⟩)
  have hins : IsBluePairMatching H B₁ B₂ (insert (a, b) M) := by
    constructor
    · intro p hp
      rcases mem_insert.mp hp with rfl | hp
      · exact ⟨haB, hbB, hab⟩
      · exact hM.1 p hp
    · intro p hp q hq hpq
      rcases mem_insert.mp hp with rfl | hp
      · rcases mem_insert.mp hq with rfl | hq
        · exact (hpq rfl).elim
        · exact ⟨fun h ↦ ha (mem_image.mpr ⟨q, hq, h.symm⟩),
            fun h ↦ hb (mem_image.mpr ⟨q, hq, h.symm⟩)⟩
      · rcases mem_insert.mp hq with rfl | hq
        · exact ⟨fun h ↦ ha (mem_image.mpr ⟨p, hp, h⟩),
            fun h ↦ hb (mem_image.mpr ⟨p, hp, h⟩)⟩
        · exact hM.2 hp hq hpq
  have := hmax (insert (a, b) M) hins
  rw [card_insert_of_notMem hpnot] at this
  omega

private lemma maximum_bluePairMatching_compl_adj_unsaturated {n : ℕ}
    {H : SimpleGraph (Fin n)} {B₁ B₂ : Finset (Fin n)}
    {M : Finset (Fin n × Fin n)}
    (hM : IsBluePairMatching H B₁ B₂ M)
    (hmax : ∀ N : Finset (Fin n × Fin n),
      IsBluePairMatching H B₁ B₂ N → N.card ≤ M.card)
    (hdis : Disjoint B₁ B₂)
    {a b : Fin n} (ha : a ∈ unsaturatedBlueLeft B₁ M)
    (hb : b ∈ unsaturatedBlueRight B₂ M) : Hᶜ.Adj a b := by
  have haData := mem_sdiff.mp ha
  have hbData := mem_sdiff.mp hb
  rw [SimpleGraph.compl_adj]
  refine ⟨?_, maximum_bluePairMatching_nonadjacent_unsaturated hM hmax
    haData.1 hbData.1 haData.2 hbData.2⟩
  intro hab
  subst b
  exact Finset.disjoint_left.mp hdis haData.1 hbData.1

/-! ## Forgetting the orientation of the blue matching -/

/-- The unordered old edges underlying an oriented blue matching. -/
def bluePairMatchingEdges {n : ℕ} (M : Finset (Fin n × Fin n)) :
    Finset (Sym2 (Fin n)) :=
  M.image fun p ↦ s(p.1, p.2)

lemma IsBluePairMatching.edgeMap_injective {n : ℕ}
    {H : SimpleGraph (Fin n)} {s₁ : Set (Fin n)}
    {B₁ B₂ : Finset (Fin n)} {M : Finset (Fin n × Fin n)}
    (hM : IsBluePairMatching H B₁ B₂ M)
    (hB₁ : B₁ ⊆ s₁.toFinset) (hB₂ : B₂ ⊆ s₁ᶜ.toFinset) :
    Set.InjOn (fun p : Fin n × Fin n ↦ s(p.1, p.2)) M := by
  intro p hp q hq hpq
  rcases Sym2.eq_iff.mp hpq with ⟨hp₁, hp₂⟩ | ⟨hp₁, hp₂⟩
  · exact Prod.ext hp₁ hp₂
  · have hpSide : p.1 ∈ s₁ := by
      simpa using hB₁ (hM.1 p hp).1
    have hqNotSide : q.2 ∉ s₁ := by
      simpa using hB₂ (hM.1 q hq).2.1
    exact (hqNotSide (hp₁ ▸ hpSide)).elim

lemma IsBluePairMatching.card_bluePairMatchingEdges {n : ℕ}
    {H : SimpleGraph (Fin n)} {s₁ : Set (Fin n)}
    {B₁ B₂ : Finset (Fin n)} {M : Finset (Fin n × Fin n)}
    (hM : IsBluePairMatching H B₁ B₂ M)
    (hB₁ : B₁ ⊆ s₁.toFinset) (hB₂ : B₂ ⊆ s₁ᶜ.toFinset) :
    (bluePairMatchingEdges M).card = M.card := by
  exact Finset.card_image_iff.mpr (hM.edgeMap_injective hB₁ hB₂)

lemma IsBluePairMatching.bluePairMatchingEdges_subset_edgeFinset {n : ℕ}
    {H : SimpleGraph (Fin n)} {B₁ B₂ : Finset (Fin n)}
    {M : Finset (Fin n × Fin n)}
    (hM : IsBluePairMatching H B₁ B₂ M) :
    bluePairMatchingEdges M ⊆ H.edgeFinset := by
  intro e he
  obtain ⟨p, hp, rfl⟩ := mem_image.mp he
  exact SimpleGraph.mem_edgeFinset.mpr (hM.1 p hp).2.2

lemma IsBluePairMatching.isCrossMatching_bluePairMatchingEdges {n : ℕ}
    {H : SimpleGraph (Fin n)} {s₁ : Set (Fin n)}
    {B₁ B₂ : Finset (Fin n)} {M : Finset (Fin n × Fin n)}
    (hM : IsBluePairMatching H B₁ B₂ M)
    (hB₁ : B₁ ⊆ s₁.toFinset) (hB₂ : B₂ ⊆ s₁ᶜ.toFinset) :
    IsCrossMatching s₁ (bluePairMatchingEdges M) := by
  constructor
  · intro e he
    obtain ⟨p, hp, rfl⟩ := mem_image.mp he
    rw [sameSide_mk]
    have hpSide : p.1 ∈ s₁ := by
      simpa using hB₁ (hM.1 p hp).1
    have hpNotSide : p.2 ∉ s₁ := by
      simpa using hB₂ (hM.1 p hp).2.1
    intro hsame
    exact hpNotSide (hsame.mp hpSide)
  · intro e he f hf hef
    obtain ⟨p, hp, rfl⟩ := mem_image.mp he
    obtain ⟨q, hq, rfl⟩ := mem_image.mp hf
    have hpq : p ≠ q := by
      intro hpq
      subst q
      exact hef rfl
    have hcoords := hM.2 hp hq hpq
    have hp₁Side : p.1 ∈ s₁ := by
      simpa using hB₁ (hM.1 p hp).1
    have hq₁Side : q.1 ∈ s₁ := by
      simpa using hB₁ (hM.1 q hq).1
    have hp₂NotSide : p.2 ∉ s₁ := by
      simpa using hB₂ (hM.1 p hp).2.1
    have hq₂NotSide : q.2 ∉ s₁ := by
      simpa using hB₂ (hM.1 q hq).2.1
    change Disjoint s(p.1, p.2).toFinset s(q.1, q.2).toFinset
    rw [Finset.disjoint_left]
    intro x hxp hxq
    have hxp' : x ∈ s(p.1, p.2) := by simpa using hxp
    have hxq' : x ∈ s(q.1, q.2) := by simpa using hxq
    simp only [Sym2.mem_iff] at hxp' hxq'
    rcases hxp' with hxp | hxp <;> rcases hxq' with hxq | hxq
    · exact hcoords.1 (hxp.symm.trans hxq)
    · exact hq₂NotSide (hxq ▸ hxp ▸ hp₁Side)
    · exact hp₂NotSide (hxp ▸ hxq ▸ hq₁Side)
    · exact hcoords.2 (hxp.symm.trans hxq)

/-! ## The integral blue packing in the one-vertex extension -/

/-- Embed an old triangle family into the first `n` vertices. -/
def liftOldTriangles {n : ℕ} (P : Finset (Finset (Fin n))) :
    Finset (Finset (Fin (n + 1))) :=
  P.map (Finset.mapEmbedding Fin.castSuccEmb).toEmbedding

/-- Attach the new final vertex to every edge of an oriented matching. -/
def attachedLastBlueTriangles {n : ℕ} (M : Finset (Fin n × Fin n)) :
    Finset (Finset (Fin (n + 1))) :=
  M.image fun p ↦
    ({p.1.castSucc, p.2.castSucc, Fin.last n} : Finset (Fin (n + 1)))

/-- The old cross packing together with the matching triangles through the
new vertex. -/
def extensionBlueTriangles {n : ℕ} (P : Finset (Finset (Fin n)))
    (M : Finset (Fin n × Fin n)) : Finset (Finset (Fin (n + 1))) :=
  liftOldTriangles P ∪ attachedLastBlueTriangles M

@[simp] lemma card_liftOldTriangles {n : ℕ}
    (P : Finset (Finset (Fin n))) :
    (liftOldTriangles P).card = P.card := by
  simp [liftOldTriangles]

lemma IsBluePairMatching.attachedTriangleMap_injective {n : ℕ}
    {H : SimpleGraph (Fin n)} {s₁ : Set (Fin n)}
    {B₁ B₂ : Finset (Fin n)} {M : Finset (Fin n × Fin n)}
    (hM : IsBluePairMatching H B₁ B₂ M)
    (hB₁ : B₁ ⊆ s₁.toFinset) (hB₂ : B₂ ⊆ s₁ᶜ.toFinset) :
    Set.InjOn
      (fun p : Fin n × Fin n ↦
        ({p.1.castSucc, p.2.castSucc, Fin.last n} :
          Finset (Fin (n + 1)))) M := by
  intro p hp q hq hpq
  change
    ({p.1.castSucc, p.2.castSucc, Fin.last n} : Finset (Fin (n + 1))) =
      ({q.1.castSucc, q.2.castSucc, Fin.last n} : Finset (Fin (n + 1)))
    at hpq
  have hp₁Side : p.1 ∈ s₁ := by
    simpa using hB₁ (hM.1 p hp).1
  have hp₂NotSide : p.2 ∉ s₁ := by
    simpa using hB₂ (hM.1 p hp).2.1
  have hq₁Side : q.1 ∈ s₁ := by
    simpa using hB₁ (hM.1 q hq).1
  have hq₂NotSide : q.2 ∉ s₁ := by
    simpa using hB₂ (hM.1 q hq).2.1
  have hp₁mem : p.1.castSucc ∈
      ({q.1.castSucc, q.2.castSucc, Fin.last n} :
        Finset (Fin (n + 1))) := by
    have hp₁self : p.1.castSucc ∈
        ({p.1.castSucc, p.2.castSucc, Fin.last n} :
          Finset (Fin (n + 1))) := by simp
    rw [hpq] at hp₁self
    exact hp₁self
  have hp₁q₁ : p.1 = q.1 := by
    simp only [mem_insert, mem_singleton] at hp₁mem
    rcases hp₁mem with h | h | h
    · exact Fin.castSuccEmb.injective h
    · exact (hq₂NotSide (Fin.castSuccEmb.injective h ▸ hp₁Side)).elim
    · exact (Fin.castSucc_ne_last p.1 h).elim
  have hp₂mem : p.2.castSucc ∈
      ({q.1.castSucc, q.2.castSucc, Fin.last n} :
        Finset (Fin (n + 1))) := by
    have hp₂self : p.2.castSucc ∈
        ({p.1.castSucc, p.2.castSucc, Fin.last n} :
          Finset (Fin (n + 1))) := by simp
    rw [hpq] at hp₂self
    exact hp₂self
  have hp₂q₂ : p.2 = q.2 := by
    simp only [mem_insert, mem_singleton] at hp₂mem
    rcases hp₂mem with h | h | h
    · exact (hp₂NotSide (Fin.castSuccEmb.injective h ▸ hq₁Side)).elim
    · exact Fin.castSuccEmb.injective h
    · exact (Fin.castSucc_ne_last p.2 h).elim
  exact Prod.ext hp₁q₁ hp₂q₂

lemma IsBluePairMatching.card_attachedLastBlueTriangles {n : ℕ}
    {H : SimpleGraph (Fin n)} {s₁ : Set (Fin n)}
    {B₁ B₂ : Finset (Fin n)} {M : Finset (Fin n × Fin n)}
    (hM : IsBluePairMatching H B₁ B₂ M)
    (hB₁ : B₁ ⊆ s₁.toFinset) (hB₂ : B₂ ⊆ s₁ᶜ.toFinset) :
    (attachedLastBlueTriangles M).card = M.card := by
  exact Finset.card_image_iff.mpr
    (IsBluePairMatching.attachedTriangleMap_injective hM hB₁ hB₂)

lemma IsBluePairMatching.attachedLastBlueTriangles_edgeDisjoint {n : ℕ}
    {H : SimpleGraph (Fin n)} {s₁ : Set (Fin n)}
    {B₁ B₂ : Finset (Fin n)} {M : Finset (Fin n × Fin n)}
    (hM : IsBluePairMatching H B₁ B₂ M)
    (hB₁ : B₁ ⊆ s₁.toFinset) (hB₂ : B₂ ⊆ s₁ᶜ.toFinset) :
    EdgeDisjoint (attachedLastBlueTriangles M) := by
  intro t ht u hu htu
  obtain ⟨p, hp, rfl⟩ := mem_image.mp ht
  obtain ⟨q, hq, rfl⟩ := mem_image.mp hu
  have hpq : p ≠ q := by
    intro hpq
    subst q
    exact htu rfl
  have hcoords := hM.2 hp hq hpq
  have hp₁Side : p.1 ∈ s₁ := by
    simpa using hB₁ (hM.1 p hp).1
  have hq₁Side : q.1 ∈ s₁ := by
    simpa using hB₁ (hM.1 q hq).1
  have hp₂NotSide : p.2 ∉ s₁ := by
    simpa using hB₂ (hM.1 p hp).2.1
  have hq₂NotSide : q.2 ∉ s₁ := by
    simpa using hB₂ (hM.1 q hq).2.1
  rw [card_le_one]
  intro x hx y hy
  have hxP := (mem_inter.mp hx).1
  have hxQ := (mem_inter.mp hx).2
  have hyP := (mem_inter.mp hy).1
  have hyQ := (mem_inter.mp hy).2
  simp only [mem_insert, mem_singleton] at hxP hxQ hyP hyQ
  have classify (z : Fin (n + 1))
      (hzP : z = p.1.castSucc ∨ z = p.2.castSucc ∨ z = Fin.last n)
      (hzQ : z = q.1.castSucc ∨ z = q.2.castSucc ∨ z = Fin.last n) :
      z = Fin.last n := by
    rcases hzP with hzP | hzP | hzP <;>
      rcases hzQ with hzQ | hzQ | hzQ
    · exact (hcoords.1 (Fin.castSuccEmb.injective (hzP.symm.trans hzQ))).elim
    · exact (hq₂NotSide
        (Fin.castSuccEmb.injective (hzP.symm.trans hzQ) ▸ hp₁Side)).elim
    · exact (Fin.castSucc_ne_last p.1 (hzP.symm.trans hzQ)).elim
    · exact (hp₂NotSide
        (Fin.castSuccEmb.injective (hzP.symm.trans hzQ) ▸ hq₁Side)).elim
    · exact (hcoords.2 (Fin.castSuccEmb.injective (hzP.symm.trans hzQ))).elim
    · exact (Fin.castSucc_ne_last p.2 (hzP.symm.trans hzQ)).elim
    · exact (Fin.castSucc_ne_last q.1 (hzQ.symm.trans hzP)).elim
    · exact (Fin.castSucc_ne_last q.2 (hzQ.symm.trans hzP)).elim
    · exact hzP
  exact (classify x hxP hxQ).trans (classify y hyP hyQ).symm

lemma attachedLastBlueTriangles_are_triangles {n : ℕ}
    {H : SimpleGraph (Fin n)} {G : SimpleGraph (Fin (n + 1))}
    (hHG : IsInitialVertexExtension H G) {s₁ : Set (Fin n)}
    {B₁ B₂ : Finset (Fin n)} {M : Finset (Fin n × Fin n)}
    (hM : IsBluePairMatching H B₁ B₂ M)
    (hB₁ : B₁ ⊆ newBlueNeighbors G s₁)
    (hB₂ : B₂ ⊆ newBlueNeighbors G s₁ᶜ) :
    ∀ t ∈ attachedLastBlueTriangles M, G.IsNClique 3 t := by
  intro t ht
  obtain ⟨p, hp, rfl⟩ := mem_image.mp ht
  apply SimpleGraph.is3Clique_triple_iff.mpr
  have hfirst := (hM.1 p hp).1
  have hsecond := (hM.1 p hp).2.1
  have hp₁new := (mem_newBlueNeighbors G s₁ p.1).mp (hB₁ hfirst)
  have hp₂new := (mem_newBlueNeighbors G s₁ᶜ p.2).mp (hB₂ hsecond)
  exact ⟨(hHG p.1 p.2).mp (hM.1 p hp).2.2,
    hp₁new.2, hp₂new.2⟩

lemma liftOldTriangles_are_triangles {n : ℕ}
    {H : SimpleGraph (Fin n)} {G : SimpleGraph (Fin (n + 1))}
    (hHG : IsInitialVertexExtension H G)
    {P : Finset (Finset (Fin n))}
    (hP : ∀ t ∈ P, H.IsNClique 3 t) :
    ∀ t ∈ liftOldTriangles P, G.IsNClique 3 t := by
  intro t ht
  obtain ⟨u, hu, rfl⟩ := mem_map.mp ht
  have hmaple : H.map Fin.castSuccEmb ≤ G :=
    (SimpleGraph.map_le_iff_le_comap Fin.castSuccEmb H G).mpr
      (fun a b hab ↦ (hHG a b).mp hab)
  exact (hP u hu).map.mono hmaple

lemma liftOldTriangles_edgeDisjoint {n : ℕ}
    {P : Finset (Finset (Fin n))} (hP : EdgeDisjoint P) :
    EdgeDisjoint (liftOldTriangles P) := by
  intro t ht u hu htu
  obtain ⟨a, ha, rfl⟩ := mem_map.mp ht
  obtain ⟨b, hb, rfl⟩ := mem_map.mp hu
  have hab : a ≠ b := by
    intro hab
    subst b
    exact htu rfl
  change #(a.map Fin.castSuccEmb ∩ b.map Fin.castSuccEmb) ≤ 1
  rw [← Finset.map_inter]
  simpa using hP ha hb hab

private lemma liftOldTriangles_cross_attached_edgeDisjoint {n : ℕ}
    {H : SimpleGraph (Fin n)}
    {B₁ B₂ : Finset (Fin n)} {M : Finset (Fin n × Fin n)}
    (hM : IsBluePairMatching H B₁ B₂ M)
    {P : Finset (Finset (Fin n))}
    (hP : ∀ t ∈ P,
      (H.deleteEdges (bluePairMatchingEdges M : Set (Sym2 (Fin n)))).IsNClique 3 t) :
    ∀ t ∈ liftOldTriangles P, ∀ u ∈ attachedLastBlueTriangles M,
      (t ∩ u).card ≤ 1 := by
  intro t ht u hu
  obtain ⟨a, ha, rfl⟩ := mem_map.mp ht
  obtain ⟨p, hp, rfl⟩ := mem_image.mp hu
  rw [card_le_one]
  intro x hx y hy
  have hxOld := (mem_inter.mp hx).1
  have hxNew := (mem_inter.mp hx).2
  have hyOld := (mem_inter.mp hy).1
  have hyNew := (mem_inter.mp hy).2
  simp only [mem_insert, mem_singleton] at hxNew hyNew
  have hxNotLast : x ≠ Fin.last n := by
    intro h
    subst x
    rcases mem_map.mp hxOld with ⟨z, _hz, hlast⟩
    exact Fin.castSucc_ne_last z hlast
  have hyNotLast : y ≠ Fin.last n := by
    intro h
    subst y
    rcases mem_map.mp hyOld with ⟨z, _hz, hlast⟩
    exact Fin.castSucc_ne_last z hlast
  rcases hxNew with hx₁ | hx₂ | hxLast
  · rcases hyNew with hy₁ | hy₂ | hyLast
    · exact hx₁.trans hy₁.symm
    · exfalso
      have hp₁a : p.1 ∈ a := by
        simpa [hx₁] using hxOld
      have hp₂a : p.2 ∈ a := by
        simpa [hy₂] using hyOld
      have hadj := (hP a ha).isClique hp₁a hp₂a (hM.1 p hp).2.2.ne
      have hnot : s(p.1, p.2) ∉
          (bluePairMatchingEdges M : Set (Sym2 (Fin n))) := by
        have hadjData : H.Adj p.1 p.2 ∧
            s(p.1, p.2) ∉
              (bluePairMatchingEdges M : Set (Sym2 (Fin n))) := by
          simpa only [SimpleGraph.deleteEdges_adj] using hadj
        exact hadjData.2
      have hmem : s(p.1, p.2) ∈ bluePairMatchingEdges M :=
        mem_image.mpr ⟨p, hp, rfl⟩
      exact hnot hmem
    · exact (hyNotLast hyLast).elim
  · rcases hyNew with hy₁ | hy₂ | hyLast
    · exfalso
      have hp₂a : p.2 ∈ a := by
        simpa [hx₂] using hxOld
      have hp₁a : p.1 ∈ a := by
        simpa [hy₁] using hyOld
      have hadj := (hP a ha).isClique hp₂a hp₁a (hM.1 p hp).2.2.ne.symm
      have hnot : s(p.1, p.2) ∉
          (bluePairMatchingEdges M : Set (Sym2 (Fin n))) := by
        rw [show s(p.1, p.2) = s(p.2, p.1) from Sym2.eq_swap]
        have hadjData : H.Adj p.2 p.1 ∧
            s(p.2, p.1) ∉
              (bluePairMatchingEdges M : Set (Sym2 (Fin n))) := by
          simpa only [SimpleGraph.deleteEdges_adj] using hadj
        exact hadjData.2
      have hmem : s(p.1, p.2) ∈ bluePairMatchingEdges M :=
        mem_image.mpr ⟨p, hp, rfl⟩
      exact hnot hmem
    · exact hx₂.trans hy₂.symm
    · exact (hyNotLast hyLast).elim
  · exact (hxNotLast hxLast).elim

/-- Exact finite certificate for the blue family used in Claim 4.6. -/
theorem extensionBlueTriangles_certificate {n : ℕ}
    {H : SimpleGraph (Fin n)} {G : SimpleGraph (Fin (n + 1))}
    (hHG : IsInitialVertexExtension H G) (s₁ : Set (Fin n))
    (B₁ B₂ : Finset (Fin n)) (M : Finset (Fin n × Fin n))
    (hM : IsBluePairMatching H B₁ B₂ M)
    (hB₁ : B₁ ⊆ newBlueNeighbors G s₁)
    (hB₂ : B₂ ⊆ newBlueNeighbors G s₁ᶜ)
    (P : Finset (Finset (Fin n)))
    (hP : IsInternalEdgeCoveringCrossPacking
      (H.deleteEdges (bluePairMatchingEdges M : Set (Sym2 (Fin n)))) s₁ P) :
    (∀ t ∈ extensionBlueTriangles P M, G.IsNClique 3 t) ∧
      EdgeDisjoint (extensionBlueTriangles P M) ∧
      (extensionBlueTriangles P M).card = P.card + M.card := by
  have hB₁side : B₁ ⊆ s₁.toFinset := by
    intro v hv
    simpa using ((mem_newBlueNeighbors G s₁ v).mp (hB₁ hv)).1
  have hB₂side : B₂ ⊆ s₁ᶜ.toFinset := by
    intro v hv
    simpa using ((mem_newBlueNeighbors G s₁ᶜ v).mp (hB₂ hv)).1
  have hOldTri : ∀ t ∈ liftOldTriangles P, G.IsNClique 3 t :=
    liftOldTriangles_are_triangles hHG fun t ht ↦
      (hP.1 t ht).mono (by
        intro a b hab
        have habData : H.Adj a b ∧ s(a, b) ∉
            (bluePairMatchingEdges M : Set (Sym2 (Fin n))) := by
          simpa only [SimpleGraph.deleteEdges_adj] using hab
        exact habData.1)
  have hNewTri : ∀ t ∈ attachedLastBlueTriangles M, G.IsNClique 3 t :=
    attachedLastBlueTriangles_are_triangles hHG hM hB₁ hB₂
  have hOldEd : EdgeDisjoint (liftOldTriangles P) :=
    liftOldTriangles_edgeDisjoint hP.2.1
  have hNewEd : EdgeDisjoint (attachedLastBlueTriangles M) :=
    IsBluePairMatching.attachedLastBlueTriangles_edgeDisjoint
      hM hB₁side hB₂side
  have hCross := liftOldTriangles_cross_attached_edgeDisjoint hM hP.1
  have hdisj : Disjoint (liftOldTriangles P) (attachedLastBlueTriangles M) := by
    rw [Finset.disjoint_left]
    intro t htOld htNew
    have hinter := hCross t htOld t htNew
    have hcard := (hOldTri t htOld).card_eq
    simpa [hcard] using hinter
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    rcases mem_union.mp ht with ht | ht
    · exact hOldTri t ht
    · exact hNewTri t ht
  · intro t ht u hu htu
    rcases mem_union.mp ht with htOld | htNew <;>
      rcases mem_union.mp hu with huOld | huNew
    · exact hOldEd htOld huOld htu
    · exact hCross t htOld u huNew
    · simpa [inter_comm] using hCross u huOld t htNew
    · exact hNewEd htNew huNew htu
  · rw [extensionBlueTriangles, card_union_of_disjoint hdisj,
      card_liftOldTriangles,
      hM.card_attachedLastBlueTriangles hB₁side hB₂side]

/-! ## Claim 4.6: the first packing contradiction -/

/-- The matching triangles through the new vertex and the cross packing of
the old internal blue edges cannot almost fill the smaller old part.  This is
the first, contradiction-based half of Claim 4.6. -/
lemma claim46_matching_add_internal_le_part_sub_four
    (hAC : AlmostCompleteFractionalDecomposition)
    (hcross : AlmostBipartiteIntegralCrossPackingAvoiding)
    {n : ℕ} (hn : 22 ≤ n)
    (H : SimpleGraph (Fin n)) (G : SimpleGraph (Fin (n + 1)))
    (hHG : IsInitialVertexExtension H G)
    (hH : FractionalCoveredSizeAtMost H
      ((n : ℝ) * ((n : ℝ) - 1) / 4))
    (hG : FractionalCoveredSizeAtMost G
      ((n : ℝ) * ((n : ℝ) + 1) / 4))
    (s₁ : Set (Fin n))
    (hk : (internalEdgeFinset H s₁).card ≤ n / 8)
    (hsize₁ : (internalEdgeFinset H s₁).card + 4 ≤ s₁.ncard)
    (hsize₂ : (internalEdgeFinset H s₁).card + 4 ≤ s₁ᶜ.ncard)
    (hseven₁ : 7 ≤ s₁.ncard) (hseven₂ : 7 ≤ s₁ᶜ.ncard)
    (hsmall : s₁ᶜ.ncard ≤ s₁.ncard)
    (M : Finset (Fin n × Fin n))
    (hM : IsBluePairMatching H (newBlueNeighbors G s₁)
      (newBlueNeighbors G s₁ᶜ) M) :
    M.card + (internalEdgeFinset H s₁).card ≤ s₁ᶜ.ncard - 4 := by
  let E := bluePairMatchingEdges M
  have hB₁side : newBlueNeighbors G s₁ ⊆ s₁.toFinset := by
    intro v hv
    simpa using ((mem_newBlueNeighbors G s₁ v).mp hv).1
  have hB₂side : newBlueNeighbors G s₁ᶜ ⊆ s₁ᶜ.toFinset := by
    intro v hv
    simpa using ((mem_newBlueNeighbors G s₁ᶜ v).mp hv).1
  have hEMatch : IsCrossMatching s₁ E := by
    exact hM.isCrossMatching_bluePairMatchingEdges hB₁side hB₂side
  obtain ⟨P, hP⟩ := hcross n hn H s₁ E hEMatch hk hH
  have hInternal : internalEdgeFinset (H.deleteEdges (E : Set (Sym2 (Fin n)))) s₁ =
      internalEdgeFinset H s₁ :=
    internalEdgeFinset_deleteEdges_of_cross H s₁ E hEMatch.1
  have hPcard : P.card = (internalEdgeFinset H s₁).card := by
    rw [hP.2.2.2.2, hInternal]
  have hBlueCert := extensionBlueTriangles_certificate hHG s₁
    (newBlueNeighbors G s₁) (newBlueNeighbors G s₁ᶜ) M hM
    (fun _ h ↦ h) (fun _ h ↦ h) P (by simpa [E] using hP)
  let wBlue : Finset (Fin (n + 1)) → ℝ :=
    integralPackingWeight (extensionBlueTriangles P M)
  have hwBlue : IsFractionalPacking G wBlue :=
    isFractionalPacking_integralPackingWeight hBlueCert.2.1
  have hBlueSize : fractionalCoveredSize G wBlue =
      3 * ((internalEdgeFinset H s₁).card + M.card : ℕ) := by
    dsimp only [wBlue]
    rw [fractionalCoveredSize,
      fractionalSize_integralPackingWeight hBlueCert.1,
      hBlueCert.2.2, hPcard]
  obtain ⟨wRed, hwRed, hRedSize⟩ :=
    hasResidualInternalDecompositions_of_almostComplete hAC H s₁
      hsize₁ hsize₂ hseven₁ hseven₂
  let wRed' : Finset (Fin (n + 1)) → ℝ := liftOldWeight wRed
  have hwRed' : IsFractionalPacking Gᶜ wRed' := by
    exact hwRed.liftOld_compl hHG
  have hRedSize' :
      ((s₁.ncard.choose 2 + s₁ᶜ.ncard.choose 2 : ℕ) : ℝ) -
          ((internalEdgeFinset H s₁).card : ℝ) ≤
        fractionalCoveredSize Gᶜ wRed' := by
    dsimp only [wRed']
    rw [fractionalCoveredSize_liftOld_compl H G hHG]
    exact hRedSize
  have hPack := hG wBlue wRed' hwBlue hwRed'
  have hsum : s₁.ncard + s₁ᶜ.ncard = n := by
    rw [Set.ncard_add_ncard_compl]
    simp
  by_contra hbound
  have halmost : s₁ᶜ.ncard ≤
      M.card + (internalEdgeFinset H s₁).card + 3 := by
    omega
  have hstrict := claim46_old_partition_contradiction n s₁.ncard s₁ᶜ.ncard
    (internalEdgeFinset H s₁).card M.card hn hsum hsmall hk hsize₂ halmost
  rw [twoColorCoveredSize, hBlueSize] at hPack
  push_cast at hPack hRedSize' hstrict
  linarith

/-- Once an augmented bipartition has `k+m` internal blue edges, the blue
integral packing of the same cardinality and the two residual red
decompositions give the final numerical bound in Claim 4.6. -/
private lemma claim46_final_of_augmented_partition
    (hAC : AlmostCompleteFractionalDecomposition)
    {n k m : ℕ} (G : SimpleGraph (Fin (n + 1)))
    (hG : FractionalCoveredSizeAtMost G
      ((n : ℝ) * ((n : ℝ) + 1) / 4))
    (t : Set (Fin (n + 1)))
    (hInternal : (internalEdgeFinset G t).card = k + m)
    (hsize₁ : k + m + 4 ≤ t.ncard)
    (hsize₂ : k + m + 4 ≤ tᶜ.ncard)
    (hseven₁ : 7 ≤ t.ncard) (hseven₂ : 7 ≤ tᶜ.ncard)
    (Q : Finset (Finset (Fin (n + 1))))
    (hQTri : ∀ u ∈ Q, G.IsNClique 3 u)
    (hQEd : EdgeDisjoint Q) (hQcard : Q.card = k + m) :
    k + m ≤ (n + 1) / 8 := by
  let wBlue : Finset (Fin (n + 1)) → ℝ := integralPackingWeight Q
  have hwBlue : IsFractionalPacking G wBlue :=
    isFractionalPacking_integralPackingWeight hQEd
  have hBlueSize : fractionalCoveredSize G wBlue = 3 * (k + m : ℕ) := by
    dsimp only [wBlue]
    rw [fractionalCoveredSize,
      fractionalSize_integralPackingWeight hQTri, hQcard]
  obtain ⟨wRed, hwRed, hRedSize⟩ :=
    hasResidualInternalDecompositions_of_almostComplete hAC G t
      (by rw [hInternal]; exact hsize₁)
      (by rw [hInternal]; exact hsize₂) hseven₁ hseven₂
  have hPack := hG wBlue wRed hwBlue hwRed
  have hsum : t.ncard + tᶜ.ncard = n + 1 := by
    rw [Set.ncard_add_ncard_compl]
    simp
  have hPairUpper :
      (((t.ncard.choose 2 + tᶜ.ncard.choose 2 : ℕ) : ℝ) +
          2 * (k + m) ≤ (n : ℝ) * ((n : ℝ) + 1) / 4) := by
    rw [twoColorCoveredSize, hBlueSize] at hPack
    rw [hInternal] at hRedSize
    push_cast at hPack hRedSize ⊢
    linarith
  exact claim46_final_neighbor_bound n t.ncard tᶜ.ncard k m hsum hPairUpper

/-- The full numerical conclusion of Claim 4.6, conditional only on the
saturating matching conclusion of Claim 4.5. -/
lemma claim46_final_neighbor_bound_of_saturating_matching
    (hAC : AlmostCompleteFractionalDecomposition)
    (hcross : AlmostBipartiteIntegralCrossPackingAvoiding)
    {n : ℕ} (hn : 22 ≤ n)
    (H : SimpleGraph (Fin n)) (G : SimpleGraph (Fin (n + 1)))
    (hHG : IsInitialVertexExtension H G)
    (hH : FractionalCoveredSizeAtMost H
      ((n : ℝ) * ((n : ℝ) - 1) / 4))
    (hG : FractionalCoveredSizeAtMost G
      ((n : ℝ) * ((n : ℝ) + 1) / 4))
    (s₁ : Set (Fin n))
    (hk : (internalEdgeFinset H s₁).card ≤ n / 8)
    (hsize₁ : (internalEdgeFinset H s₁).card + 4 ≤ s₁.ncard)
    (hsize₂ : (internalEdgeFinset H s₁).card + 4 ≤ s₁ᶜ.ncard)
    (hseven₁ : 7 ≤ s₁.ncard) (hseven₂ : 7 ≤ s₁ᶜ.ncard)
    (M : Finset (Fin n × Fin n))
    (hM : IsBluePairMatching H (newBlueNeighbors G s₁)
      (newBlueNeighbors G s₁ᶜ) M)
    (hMsat : M.card = min (newBlueNeighbors G s₁).card
      (newBlueNeighbors G s₁ᶜ).card) :
    (internalEdgeFinset H s₁).card +
        min (newBlueNeighbors G s₁).card
          (newBlueNeighbors G s₁ᶜ).card ≤ (n + 1) / 8 := by
  let k := (internalEdgeFinset H s₁).card
  let E := bluePairMatchingEdges M
  have hB₁side : newBlueNeighbors G s₁ ⊆ s₁.toFinset := by
    intro v hv
    simpa using ((mem_newBlueNeighbors G s₁ v).mp hv).1
  have hB₂side : newBlueNeighbors G s₁ᶜ ⊆ s₁ᶜ.toFinset := by
    intro v hv
    simpa using ((mem_newBlueNeighbors G s₁ᶜ v).mp hv).1
  have hEMatch : IsCrossMatching s₁ E :=
    hM.isCrossMatching_bluePairMatchingEdges hB₁side hB₂side
  obtain ⟨P, hP⟩ := hcross n hn H s₁ E hEMatch hk hH
  have hInternalOld :
      internalEdgeFinset (H.deleteEdges (E : Set (Sym2 (Fin n)))) s₁ =
        internalEdgeFinset H s₁ :=
    internalEdgeFinset_deleteEdges_of_cross H s₁ E hEMatch.1
  have hPcard : P.card = k := by
    dsimp only [k]
    rw [hP.2.2.2.2, hInternalOld]
  have hBlueCert := extensionBlueTriangles_certificate hHG s₁
    (newBlueNeighbors G s₁) (newBlueNeighbors G s₁ᶜ) M hM
    (fun _ h ↦ h) (fun _ h ↦ h) P (by simpa [E] using hP)
  have hsumOld : s₁.ncard + s₁ᶜ.ncard = n := by
    rw [Set.ncard_add_ncard_compl]
    simp
  by_cases hparts : s₁ᶜ.ncard ≤ s₁.ncard
  · have hfirst := claim46_matching_add_internal_le_part_sub_four
      hAC hcross hn H G hHG hH hG s₁ hk hsize₁ hsize₂ hseven₁ hseven₂
      hparts M hM
    by_cases hneighbors : (newBlueNeighbors G s₁).card ≤
        (newBlueNeighbors G s₁ᶜ).card
    · have hm : M.card = (newBlueNeighbors G s₁).card := by
        simpa [min_eq_left hneighbors] using hMsat
      have hInternalNew :
          (internalEdgeFinset G (insertLastPart s₁)).card = k + M.card := by
        rw [card_internalEdgeFinset_insertLastPart H G hHG s₁]
        simpa [k, hm]
      have hsmallBound : k + M.card + 4 ≤ s₁ᶜ.ncard := by
        dsimp only [k] at hfirst ⊢
        omega
      have hfinal := claim46_final_of_augmented_partition hAC G hG
        (insertLastPart s₁) hInternalNew
        (by simp only [ncard_insertLastPart]; omega)
        (by simpa using hsmallBound)
        (by simp only [ncard_insertLastPart]; omega) (by simpa using hseven₂)
        (extensionBlueTriangles P M) hBlueCert.1 hBlueCert.2.1
        (by rw [hBlueCert.2.2, hPcard])
      simpa [k, hMsat, add_comm] using hfinal
    · have hneighbors' : (newBlueNeighbors G s₁ᶜ).card ≤
          (newBlueNeighbors G s₁).card := Nat.le_of_not_ge hneighbors
      have hm : M.card = (newBlueNeighbors G s₁ᶜ).card := by
        simpa [min_eq_right hneighbors'] using hMsat
      have hInternalCompl : internalEdgeFinset H s₁ᶜ =
          internalEdgeFinset H s₁ := by
        ext e
        induction e using Sym2.inductionOn with
        | hf a b =>
            simp only [internalEdgeFinset, mem_filter, sameSide_mk,
              Set.mem_compl_iff]
            tauto
      have hInternalNew :
          (internalEdgeFinset G (insertLastPart s₁ᶜ)).card = k + M.card := by
        rw [card_internalEdgeFinset_insertLastPart H G hHG s₁ᶜ,
          hInternalCompl]
        simpa [k, hm]
      have hsmallBound : k + M.card + 4 ≤ s₁ᶜ.ncard := by
        dsimp only [k] at hfirst ⊢
        omega
      have hfinal := claim46_final_of_augmented_partition hAC G hG
        (insertLastPart s₁ᶜ) hInternalNew
        (by simp only [ncard_insertLastPart]; omega)
        (by simpa using hsmallBound.trans hparts)
        (by simp only [ncard_insertLastPart]; omega) (by simpa using hseven₁)
        (extensionBlueTriangles P M) hBlueCert.1 hBlueCert.2.1
        (by rw [hBlueCert.2.2, hPcard])
      simpa [k, hMsat, add_comm] using hfinal
  · have hparts' : s₁.ncard ≤ s₁ᶜ.ncard := Nat.le_of_not_ge hparts
    have hInternalCompl : internalEdgeFinset H s₁ᶜ =
        internalEdgeFinset H s₁ := by
      ext e
      induction e using Sym2.inductionOn with
      | hf a b =>
          simp only [internalEdgeFinset, mem_filter, sameSide_mk,
            Set.mem_compl_iff]
          tauto
    have hkCompl : (internalEdgeFinset H s₁ᶜ).card ≤ n / 8 := by
      rwa [hInternalCompl]
    have hMswap : IsBluePairMatching H (newBlueNeighbors G s₁ᶜ)
        (newBlueNeighbors G (s₁ᶜ)ᶜ) (M.image Prod.swap) := by
      constructor
      · intro p hp
        obtain ⟨q, hq, rfl⟩ := mem_image.mp hp
        have hqData := hM.1 q hq
        exact ⟨hqData.2.1, by simpa using hqData.1, hqData.2.2.symm⟩
      · intro p hp q hq hpq
        obtain ⟨p', hp', rfl⟩ := mem_image.mp hp
        obtain ⟨q', hq', rfl⟩ := mem_image.mp hq
        have hpq' : p' ≠ q' := by
          intro h
          subst q'
          exact hpq rfl
        exact ⟨(hM.2 hp' hq' hpq').2, (hM.2 hp' hq' hpq').1⟩
    have hswapCard : (M.image Prod.swap).card = M.card := by
      rw [card_image_iff.mpr]
      intro p _ q _ h
      exact Prod.swap_injective h
    have hfirst := claim46_matching_add_internal_le_part_sub_four
      hAC hcross hn H G hHG hH hG s₁ᶜ hkCompl
      (by simpa [hInternalCompl] using hsize₂)
      (by simpa [hInternalCompl] using hsize₁)
      hseven₂ (by simpa using hseven₁) (by simpa using hparts')
      (M.image Prod.swap) (by simpa using hMswap)
    have hfirst' : k + M.card + 4 ≤ s₁.ncard := by
      have hfirst₀ : M.card + k ≤ s₁.ncard - 4 := by
        simpa [hswapCard, hInternalCompl, k] using hfirst
      omega
    by_cases hneighbors : (newBlueNeighbors G s₁).card ≤
        (newBlueNeighbors G s₁ᶜ).card
    · have hm : M.card = (newBlueNeighbors G s₁).card := by
        simpa [min_eq_left hneighbors] using hMsat
      have hInternalNew :
          (internalEdgeFinset G (insertLastPart s₁)).card = k + M.card := by
        rw [card_internalEdgeFinset_insertLastPart H G hHG s₁]
        simpa [k, hm]
      have hfinal := claim46_final_of_augmented_partition hAC G hG
        (insertLastPart s₁) hInternalNew
        (by simp only [ncard_insertLastPart]; omega)
        (by simpa using hfirst'.trans hparts')
        (by simp only [ncard_insertLastPart]; omega) (by simpa using hseven₂)
        (extensionBlueTriangles P M) hBlueCert.1 hBlueCert.2.1
        (by rw [hBlueCert.2.2, hPcard])
      simpa [k, hMsat, add_comm] using hfinal
    · have hneighbors' : (newBlueNeighbors G s₁ᶜ).card ≤
          (newBlueNeighbors G s₁).card := Nat.le_of_not_ge hneighbors
      have hm : M.card = (newBlueNeighbors G s₁ᶜ).card := by
        simpa [min_eq_right hneighbors'] using hMsat
      have hInternalNew :
          (internalEdgeFinset G (insertLastPart s₁ᶜ)).card = k + M.card := by
        rw [card_internalEdgeFinset_insertLastPart H G hHG s₁ᶜ,
          hInternalCompl]
        simpa [k, hm]
      have hfinal := claim46_final_of_augmented_partition hAC G hG
        (insertLastPart s₁ᶜ) hInternalNew
        (by simp only [ncard_insertLastPart]; omega)
        (by simpa using hfirst')
        (by simp only [ncard_insertLastPart]; omega) (by simpa using hseven₁)
        (extensionBlueTriangles P M) hBlueCert.1 hBlueCert.2.1
        (by rw [hBlueCert.2.2, hPcard])
      simpa [k, hMsat, add_comm] using hfinal

/-! ## A deletion-and-residual assembly lemma

Claim 4.5 uses an integral family of red triangles and decomposes the red
graphs induced by the two old parts after deleting the internal edges used
by that family.  The next lemmas package the elementary load calculation:
zero-extend the residual packing from the graph with *all* triangle edges
deleted, then add the integral triangle weight.  Deleting the additional
cross edges is harmless for the two induced residual graphs and makes the
edge-load disjointness literal. -/

/-- All unordered pairs occurring in a finite family of vertex sets. -/
def familyPairFinset {α : Type*} [DecidableEq α]
    (P : Finset (Finset α)) : Finset (Sym2 α) :=
  P.biUnion fun t ↦ t.sym2

@[simp] lemma mem_familyPairFinset {α : Type*} [DecidableEq α]
    {P : Finset (Finset α)} {e : Sym2 α} :
    e ∈ familyPairFinset P ↔ ∃ t ∈ P, e ∈ t.sym2 := by
  simp [familyPairFinset]

private lemma fractionalEdgeLoad_integralPackingWeight_eq_zero
    {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) (P : Finset (Finset α)) {e : Sym2 α}
    (he : e ∉ familyPairFinset P) :
    fractionalEdgeLoad G (integralPackingWeight P) e = 0 := by
  unfold fractionalEdgeLoad integralPackingWeight
  apply sum_eq_zero
  intro t ht
  have hte := (mem_filter.mp ht).2
  rw [if_neg]
  intro htP
  exact he (mem_familyPairFinset.mpr ⟨t, htP, hte⟩)

/-- Add an integral triangle packing to an ambient residual packing whose
load is zero on every pair used by the integral family.  This is the exact
packing-splice used in Claim 4.5; the residual decompositions below will
provide the zero-load property by deleting their internal base edges. -/
lemma isFractionalPacking_add_integral_of_zero_load
    {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) (P : Finset (Finset α))
    (hP : EdgeDisjoint P)
    (w : Finset α → ℝ)
    (hw : IsFractionalPacking G w)
    (hzero : ∀ e ∈ G.edgeFinset, e ∈ familyPairFinset P →
      fractionalEdgeLoad G w e = 0) :
    IsFractionalPacking G
      (addTriangleWeight (integralPackingWeight P) w) := by
  have hInt := isFractionalPacking_integralPackingWeight (G := G) hP
  constructor
  · intro t ht
    exact add_nonneg (hInt.nonneg_on ht) (hw.nonneg_on ht)
  · intro e heG
    change fractionalEdgeLoad G
      (fun t ↦ integralPackingWeight P t + w t) e ≤ 1
    rw [fractionalEdgeLoad_add]
    by_cases heD : e ∈ familyPairFinset P
    · rw [hzero e heG heD, add_zero]
      exact hInt.edgeLoad_le_one heG
    · rw [fractionalEdgeLoad_integralPackingWeight_eq_zero G P heD,
        zero_add]
      exact hw.edgeLoad_le_one heG

/-- Exact covered-size identity for the preceding packing splice. -/
lemma fractionalCoveredSize_add_integral
    {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) (P : Finset (Finset α))
    (hPtri : ∀ t ∈ P, G.IsNClique 3 t)
    (w : Finset α → ℝ) :
    fractionalCoveredSize G
      (addTriangleWeight (integralPackingWeight P) w) =
      3 * (P.card : ℝ) + fractionalCoveredSize G w := by
  simp only [fractionalCoveredSize]
  rw [fractionalSize_addTriangleWeight,
    fractionalSize_integralPackingWeight hPtri]
  rw [mul_add]

private lemma fractionalSize_zeroExtend_mono
    {α : Type*} [Fintype α] [DecidableEq α]
    {H G : SimpleGraph α} (hHG : H ≤ G) (w : Finset α → ℝ) :
    fractionalSize G (zeroExtendTriangleWeight H w) =
      fractionalSize H w := by
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
      intro t htG htH
      exact zeroExtendTriangleWeight_of_not_mem htH
    _ = ∑ t ∈ sH, w t := by
      apply sum_congr rfl
      intro t ht
      exact zeroExtendTriangleWeight_of_mem ht

private lemma IsFractionalPacking.zeroExtendToSupergraph
    {α : Type*} [Fintype α] [DecidableEq α]
    {H K : SimpleGraph α} (hHK : H ≤ K) {w : Finset α → ℝ}
    (hw : IsFractionalPacking H w) :
    IsFractionalPacking K (zeroExtendTriangleWeight H w) := by
  constructor
  · exact zeroExtendTriangleWeight_nonneg hHK hw
  · intro e he
    rw [fractionalEdgeLoad_zeroExtend hHK]
    by_cases heH : e ∈ H.edgeFinset
    · exact hw.edgeLoad_le_one heH
    · have heND : ¬ e.IsDiag := K.not_isDiag_of_mem_edgeFinset he
      rw [fractionalEdgeLoad_eq_zero_of_not_edge H w heND heH]
      norm_num

private lemma IsFractionalDecomposition.relabelForExtension
    {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    {G : SimpleGraph α} {w : Finset α → ℝ}
    (hw : IsFractionalDecomposition G w) (e : α ≃ β) :
    IsFractionalDecomposition (G.map e.toEmbedding) (relabelWeight e w) := by
  refine ⟨hw.isPacking.relabel e, ?_⟩
  intro p hp
  have hp' : p ∈ (G.map e.toEmbedding).edgeSet := by
    simpa only [SimpleGraph.mem_edgeFinset] using hp
  rw [SimpleGraph.edgeSet_map e.toEmbedding G] at hp'
  obtain ⟨q, hq, rfl⟩ := hp'
  rw [fractionalEdgeLoad_relabel]
  apply hw.edgeLoad_eq_one
  simpa only [SimpleGraph.mem_edgeFinset] using hq

private lemma almostCompleteFractionalDecomposition_fintype_forExtension
    (hAC : AlmostCompleteFractionalDecomposition)
    {β : Type*} [Fintype β] [DecidableEq β]
    (G : SimpleGraph β) (hcard : 7 ≤ Fintype.card β)
    (hmissing : missingEdgeCount G ≤ Fintype.card β - 4) :
    ∃ w : Finset β → ℝ, IsFractionalDecomposition G w := by
  let e : β ≃ Fin (Fintype.card β) := Fintype.equivFinOfCardEq rfl
  let H : SimpleGraph (Fin (Fintype.card β)) := G.map e.toEmbedding
  letI : DecidableRel H.Adj := Classical.decRel _
  have hmissH : missingEdgeCount H ≤ Fintype.card β - 4 := by
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
      _ ≤ Fintype.card β - 4 := hmissing
  obtain ⟨w, hw⟩ := hAC (Fintype.card β) hcard H hmissH
  let u : Finset β → ℝ := relabelWeight e.symm w
  have hmap : H.map e.symm.toEmbedding = G := by
    dsimp only [H]
    rw [SimpleGraph.map_map]
    simpa using G.map_id
  refine ⟨u, ?_⟩
  simpa only [u, hmap] using hw.relabelForExtension e.symm

private lemma card_edgeFinset_add_missing_forExtension
    {α : Type*} [Fintype α] [DecidableEq α] (G : SimpleGraph α) :
    G.edgeFinset.card + missingEdgeCount G =
      (Fintype.card α).choose 2 := by
  have hdisj : Disjoint G.edgeFinset Gᶜ.edgeFinset := by
    rw [Finset.disjoint_left]
    intro e heG heGc
    induction e using Sym2.inductionOn with
    | hf a b =>
        have hab : G.Adj a b := by
          simpa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using heG
        have hnab : ¬ G.Adj a b := by
          have hc : Gᶜ.Adj a b := by
            simpa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using heGc
          exact hc.2
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

private lemma natCard_edgeSet_add_missing_forExtension
    {α : Type*} [Fintype α] [DecidableEq α] (G : SimpleGraph α) :
    Nat.card G.edgeSet + missingEdgeCount G =
      (Fintype.card α).choose 2 := by
  have h := card_edgeFinset_add_missing_forExtension G
  have hedge : G.edgeFinset.card = Nat.card G.edgeSet := by
    rw [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card]
  rw [hedge] at h
  exact h

private lemma missingEdgeCount_compl_induce_forExtension
    {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) (S : Finset α) :
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

private lemma missingEdgeCount_mono_le_add_edgeSet_card_sub
    {α : Type*} [Fintype α] [DecidableEq α]
    {H K : SimpleGraph α} (hHK : H ≤ K) :
    missingEdgeCount H ≤ missingEdgeCount K +
      (Nat.card K.edgeSet - Nat.card H.edgeSet) := by
  have hsub : H.edgeFinset ⊆ K.edgeFinset :=
    by
      intro e he
      induction e using Sym2.inductionOn with
      | hf a b =>
          exact SimpleGraph.mem_edgeFinset.mpr
            (hHK (SimpleGraph.mem_edgeFinset.mp he))
  have hHsum := card_edgeFinset_add_missing_forExtension H
  have hKsum := card_edgeFinset_add_missing_forExtension K
  have hHcard : H.edgeFinset.card = Nat.card H.edgeSet := by
    rw [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card]
  have hKcard : K.edgeFinset.card = Nat.card K.edgeSet := by
    rw [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card]
  rw [hHcard] at hHsum
  rw [hKcard] at hKsum
  omega

private lemma map_induced_edges_lost_to_deleteEdges_subset
    {α : Type*} [Fintype α] [DecidableEq α]
    (R : SimpleGraph α) (S : Finset α) (D : Finset (Sym2 α)) :
    ((R.induce (S : Set α)).edgeFinset \
        ((R.deleteEdges (D : Set (Sym2 α))).induce
          (S : Set α)).edgeFinset).map
            (inducedEmbedding S).sym2Map ⊆ D := by
  intro p hp
  obtain ⟨q, hq, rfl⟩ := mem_map.mp hp
  rcases mem_sdiff.mp hq with ⟨hqK, hqH⟩
  induction q using Sym2.inductionOn with
  | hf a b =>
      have habR : R.Adj a.1 b.1 := by
        simpa using SimpleGraph.mem_edgeFinset.mp hqK
      have habNot : ¬ (R.deleteEdges (D : Set (Sym2 α))).Adj a.1 b.1 := by
        intro hab
        apply hqH
        exact SimpleGraph.mem_edgeFinset.mpr hab
      have habD : s(a.1, b.1) ∈ D := by
        by_contra habD
        exact habNot (SimpleGraph.deleteEdges_adj.mpr
          ⟨habR, by simpa using habD⟩)
      simpa [inducedEmbedding] using habD

private lemma induce_deleteEdges_le
    {α : Type*} [Fintype α] [DecidableEq α]
    (R : SimpleGraph α) (S : Finset α) (D : Finset (Sym2 α)) :
    (R.deleteEdges (D : Set (Sym2 α))).induce (S : Set α) ≤
      R.induce (S : Set α) := by
  intro a b hab
  exact (SimpleGraph.deleteEdges_adj.mp hab).1

private lemma card_induced_edges_lost_to_deleteEdges_le
    {α : Type*} [Fintype α] [DecidableEq α]
    (R : SimpleGraph α) (S : Finset α) (D : Finset (Sym2 α)) :
    Nat.card (R.induce (S : Set α)).edgeSet -
      Nat.card ((R.deleteEdges (D : Set (Sym2 α))).induce
        (S : Set α)).edgeSet ≤ D.card := by
  let E := (R.induce (S : Set α)).edgeFinset \
    ((R.deleteEdges (D : Set (Sym2 α))).induce (S : Set α)).edgeFinset
  have hsub :
      ((R.deleteEdges (D : Set (Sym2 α))).induce
        (S : Set α)).edgeFinset ⊆ (R.induce (S : Set α)).edgeFinset := by
    intro e he
    induction e using Sym2.inductionOn with
    | hf a b =>
        exact SimpleGraph.mem_edgeFinset.mpr
          ((induce_deleteEdges_le R S D) (SimpleGraph.mem_edgeFinset.mp he))
  have hEcardEq : E.card = (R.induce (S : Set α)).edgeFinset.card -
      ((R.deleteEdges (D : Set (Sym2 α))).induce
        (S : Set α)).edgeFinset.card := by
    dsimp only [E]
    rw [card_sdiff_of_subset hsub]
  have hmapcard : (E.map (inducedEmbedding S).sym2Map).card = E.card :=
    card_map (inducedEmbedding S).sym2Map
  have hEle : E.card ≤ D.card := by
    rw [← hmapcard]
    exact card_le_card (map_induced_edges_lost_to_deleteEdges_subset R S D)
  have hKcard : (R.induce (S : Set α)).edgeFinset.card =
      Nat.card (R.induce (S : Set α)).edgeSet := by
    rw [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card]
  have hHcard : ((R.deleteEdges (D : Set (Sym2 α))).induce
      (S : Set α)).edgeFinset.card =
      Nat.card ((R.deleteEdges (D : Set (Sym2 α))).induce
        (S : Set α)).edgeSet := by
    rw [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card]
  rw [hKcard, hHcard] at hEcardEq
  omega

/-- Deleting `D` before restricting to a finite induced side creates at
most `D.card` additional missing edges on that side. -/
private lemma missingEdgeCount_induce_deleteEdges_le
    {α : Type*} [Fintype α] [DecidableEq α]
    (R : SimpleGraph α) (S : Finset α) (D : Finset (Sym2 α)) :
    missingEdgeCount
        ((R.deleteEdges (D : Set (Sym2 α))).induce (S : Set α)) ≤
      missingEdgeCount (R.induce (S : Set α)) + D.card := by
  have hmono :
      missingEdgeCount
          ((R.deleteEdges (D : Set (Sym2 α))).induce (S : Set α)) ≤
        missingEdgeCount (R.induce (S : Set α)) +
          (Nat.card (R.induce (S : Set α)).edgeSet -
            Nat.card ((R.deleteEdges (D : Set (Sym2 α))).induce
              (S : Set α)).edgeSet) :=
    missingEdgeCount_mono_le_add_edgeSet_card_sub
      (induce_deleteEdges_le R S D)
  have hcard := card_induced_edges_lost_to_deleteEdges_le R S D
  omega

/-- Only deleted edges whose two endpoints lie in `S` can increase the
missing-edge count of the graph induced by `S`. -/
private lemma map_induced_edges_lost_to_deleteEdges_subset_inter_side
    {α : Type*} [Fintype α] [DecidableEq α]
    (R : SimpleGraph α) (S : Finset α) (D : Finset (Sym2 α)) :
    ((R.induce (S : Set α)).edgeFinset \
        ((R.deleteEdges (D : Set (Sym2 α))).induce
          (S : Set α)).edgeFinset).map
            (inducedEmbedding S).sym2Map ⊆
      D ∩ sideEdgeFinset R S := by
  intro e he
  have heD := map_induced_edges_lost_to_deleteEdges_subset R S D he
  obtain ⟨q, hq, rfl⟩ := mem_map.mp he
  rcases mem_sdiff.mp hq with ⟨hqR, _hqDeleted⟩
  refine mem_inter.mpr ⟨heD, ?_⟩
  induction q using Sym2.inductionOn with
  | hf a b =>
      apply mem_filter.mpr
      constructor
      · simpa [inducedEmbedding] using
          SimpleGraph.mem_edgeFinset.mp hqR
      · intro v hv
        have hv' : v ∈ s(a.1, b.1) := by
          simpa [inducedEmbedding] using hv
        simp only [Sym2.mem_iff] at hv'
        rcases hv' with rfl | rfl
        · exact a.2
        · exact b.2

private lemma card_induced_edges_lost_to_deleteEdges_le_inter_side
    {α : Type*} [Fintype α] [DecidableEq α]
    (R : SimpleGraph α) (S : Finset α) (D : Finset (Sym2 α)) :
    Nat.card (R.induce (S : Set α)).edgeSet -
      Nat.card ((R.deleteEdges (D : Set (Sym2 α))).induce
        (S : Set α)).edgeSet ≤ (D ∩ sideEdgeFinset R S).card := by
  let E := (R.induce (S : Set α)).edgeFinset \
    ((R.deleteEdges (D : Set (Sym2 α))).induce (S : Set α)).edgeFinset
  have hsub :
      ((R.deleteEdges (D : Set (Sym2 α))).induce
        (S : Set α)).edgeFinset ⊆ (R.induce (S : Set α)).edgeFinset := by
    intro e he
    induction e using Sym2.inductionOn with
    | hf a b =>
        exact SimpleGraph.mem_edgeFinset.mpr
          ((induce_deleteEdges_le R S D)
            (SimpleGraph.mem_edgeFinset.mp he))
  have hEcard : E.card = (R.induce (S : Set α)).edgeFinset.card -
      ((R.deleteEdges (D : Set (Sym2 α))).induce
        (S : Set α)).edgeFinset.card := by
    dsimp only [E]
    rw [card_sdiff_of_subset hsub]
  have hmapcard : (E.map (inducedEmbedding S).sym2Map).card = E.card :=
    card_map (inducedEmbedding S).sym2Map
  have hle : E.card ≤ (D ∩ sideEdgeFinset R S).card := by
    rw [← hmapcard]
    exact card_le_card
      (map_induced_edges_lost_to_deleteEdges_subset_inter_side R S D)
  have hKcard : (R.induce (S : Set α)).edgeFinset.card =
      Nat.card (R.induce (S : Set α)).edgeSet := by
    rw [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card]
  have hHcard : ((R.deleteEdges (D : Set (Sym2 α))).induce
      (S : Set α)).edgeFinset.card =
      Nat.card ((R.deleteEdges (D : Set (Sym2 α))).induce
        (S : Set α)).edgeSet := by
    rw [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card]
  rw [hKcard, hHcard] at hEcard
  omega

private lemma missingEdgeCount_induce_deleteEdges_le_inter_side
    {α : Type*} [Fintype α] [DecidableEq α]
    (R : SimpleGraph α) (S : Finset α) (D : Finset (Sym2 α)) :
    missingEdgeCount
        ((R.deleteEdges (D : Set (Sym2 α))).induce (S : Set α)) ≤
      missingEdgeCount (R.induce (S : Set α)) +
        (D ∩ sideEdgeFinset R S).card := by
  have hmono := missingEdgeCount_mono_le_add_edgeSet_card_sub
    (induce_deleteEdges_le R S D)
  have hcard :=
    card_induced_edges_lost_to_deleteEdges_le_inter_side R S D
  omega

/-! ## The arithmetic contradiction in Claim 4.5 -/

/-- The internal-pair count of a bipartition of `n` vertices. -/
private lemma old_internal_pairs_lower_bound
    (n a b : ℕ) (hab : a + b = n) :
    (n : ℝ) * ((n : ℝ) - 2) / 4 ≤
      ((a.choose 2 + b.choose 2 : ℕ) : ℝ) := by
  have habR : (a : ℝ) + b = n := by exact_mod_cast hab
  rw [Nat.cast_add, Nat.cast_choose_two, Nat.cast_choose_two]
  nlinarith [sq_nonneg ((a : ℝ) - b)]

/-- The slightly asymmetric estimate used in the truncated branch of
Claim 4.5.  Its quarter-unit parity loss is exactly the square
`(a-b-1)^2`. -/
private lemma old_internal_pairs_add_smaller_lower_bound
    (n a b : ℕ) (hab : a + b = n) :
    ((n : ℝ) * (n : ℝ) - 1) / 4 ≤
      ((a.choose 2 + b.choose 2 : ℕ) : ℝ) + b := by
  have habR : (a : ℝ) + b = n := by exact_mod_cast hab
  rw [Nat.cast_add, Nat.cast_choose_two, Nat.cast_choose_two]
  nlinarith [sq_nonneg ((a : ℝ) - b - 1)]

/-- Pure numerical endpoint of Claim 4.5.  The first alternative is the
untruncated second red packing; the second says it was truncated at the
almost-complete admissibility cap. -/
lemma claim45_numerical_contradiction
    (n a b k k₁ k₂ m p₁ p₂ : ℕ)
    (hn : 22 ≤ n) (hab : a + b = n) (hk : k₁ + k₂ = k)
    (hp₁ : (a : ℝ) - m - 3 - 2 * k₁ ≤ 2 * p₁)
    (hp₂ :
      (b : ℝ) - m - 2 - 2 * k₂ ≤ 2 * p₂ ∨
        (p₂ : ℝ) = b - k₂ - 4)
    (hupper :
      ((a.choose 2 + b.choose 2 : ℕ) : ℝ) + 2 * k + 3 * m +
          2 * (p₁ + p₂) ≤
        (n : ℝ) * ((n : ℝ) + 1) / 4) : False := by
  have hkR : (k₁ : ℝ) + k₂ = k := by exact_mod_cast hk
  have hnR : (22 : ℝ) ≤ n := by exact_mod_cast hn
  have habR : (a : ℝ) + b = n := by exact_mod_cast hab
  rcases hp₂ with hp₂ | hp₂
  · have hpairs := old_internal_pairs_lower_bound n a b hab
    push_cast at hp₁ hp₂ hpairs hupper
    nlinarith
  · have hpairs := old_internal_pairs_add_smaller_lower_bound n a b hab
    push_cast at hp₁ hp₂ hpairs hupper
    nlinarith

/-! ## Lifting the red matchings to the one-vertex extension -/

private lemma claim45_first_cap_arithmetic
    (n a b k p : ℕ) (hn : 22 ≤ n) (hab : a + b = n)
    (hba : b ≤ a) (hk : k ≤ n / 8) (hp : 2 * p ≤ a - 1) :
    p + k ≤ a - 4 := by
  omega

private def oldRedHom {n : ℕ}
    (H : SimpleGraph (Fin n)) (G : SimpleGraph (Fin (n + 1)))
    (hHG : IsInitialVertexExtension H G) : Hᶜ →g Gᶜ where
  toFun := Fin.castSucc
  map_rel' := by
    intro a b hab
    have hab' : a ≠ b ∧ ¬ H.Adj a b := by
      simpa [SimpleGraph.compl_adj] using hab
    have hne : a.castSucc ≠ b.castSucc :=
      fun h ↦ hab'.1 (Fin.castSuccEmb.injective h)
    have hnot : ¬ G.Adj a.castSucc b.castSucc := by
      simpa [hHG a b] using hab'.2
    simpa [SimpleGraph.compl_adj] using And.intro hne hnot

private def liftOldRedMatching {n : ℕ}
    (H : SimpleGraph (Fin n)) (G : SimpleGraph (Fin (n + 1)))
    (hHG : IsInitialVertexExtension H G) (M : Hᶜ.Subgraph) :
    Gᶜ.Subgraph :=
  M.map (oldRedHom H G hHG)

private lemma liftOldRedMatching_isMatching {n : ℕ}
    (H : SimpleGraph (Fin n)) (G : SimpleGraph (Fin (n + 1)))
    (hHG : IsInitialVertexExtension H G) {M : Hᶜ.Subgraph}
    (hM : M.IsMatching) :
    (liftOldRedMatching H G hHG M).IsMatching := by
  exact hM.map (oldRedHom H G hHG) Fin.castSuccEmb.injective

private lemma liftOldRedMatching_verts {n : ℕ}
    (H : SimpleGraph (Fin n)) (G : SimpleGraph (Fin (n + 1)))
    (hHG : IsInitialVertexExtension H G) (M : Hᶜ.Subgraph) :
    (liftOldRedMatching H G hHG M).verts = Fin.castSucc '' M.verts := by
  exact SimpleGraph.Subgraph.map_verts _ _

private lemma liftOldRedMatching_edgeCard {n : ℕ}
    (H : SimpleGraph (Fin n)) (G : SimpleGraph (Fin (n + 1)))
    (hHG : IsInitialVertexExtension H G) {M : Hᶜ.Subgraph}
    (hM : M.IsMatching) :
    Fintype.card (liftOldRedMatching H G hHG M).edgeSet =
      Fintype.card M.edgeSet := by
  have hML := liftOldRedMatching_isMatching H G hHG hM
  have hverts :
      (liftOldRedMatching H G hHG M).verts.toFinset.card =
        M.verts.toFinset.card := by
    rw [liftOldRedMatching_verts H G hHG M]
    simpa [Set.ncard_eq_toFinset_card'] using
      (Set.ncard_image_of_injective M.verts Fin.castSuccEmb.injective)
  have hleft :=
    SimpleGraph.Subgraph.IsMatching.card_verts_eq_two_mul_card_edgeFinset_GL hML
  have hright :=
    SimpleGraph.Subgraph.IsMatching.card_verts_eq_two_mul_card_edgeFinset_GL hM
  omega

private lemma last_not_mem_liftOldRedMatching_verts {n : ℕ}
    (H : SimpleGraph (Fin n)) (G : SimpleGraph (Fin (n + 1)))
    (hHG : IsInitialVertexExtension H G) (M : Hᶜ.Subgraph) :
    Fin.last n ∉ (liftOldRedMatching H G hHG M).verts := by
  rw [liftOldRedMatching_verts H G hHG M]
  rintro ⟨v, _hv, hv⟩
  exact Fin.castSucc_ne_last v hv

/-- The endpoint-cover matching construction, lifted to the red graph of
the one-vertex extension and attached to a prescribed red common
neighbour.  The last inequality is the parity-sharp matching estimate. -/
private lemma exists_lifted_attachedRedMatching
    {n : ℕ} (H : SimpleGraph (Fin n)) (G : SimpleGraph (Fin (n + 1)))
    (hHG : IsInitialVertexExtension H G)
    (X D : Finset (Fin n)) (z : Fin (n + 1))
    (hstar : ∀ v ∈ (X \ D) \
        chosenEndpointCover (edgesInsideOutside H X D),
      Gᶜ.Adj z v.castSucc) :
    ∃ M : Gᶜ.Subgraph,
      let P := attachedMatchingTriangles M z
      M.IsMatching ∧
        M.verts ⊆ Fin.castSucc ''
          ((((X \ D) \
            chosenEndpointCover (edgesInsideOutside H X D) :
              Finset (Fin n))) : Set (Fin n)) ∧
        (∀ t ∈ P, Gᶜ.IsNClique 3 t) ∧ EdgeDisjoint P ∧
        P.card = Fintype.card M.edgeSet ∧
        ((X \ D) \
            chosenEndpointCover (edgesInsideOutside H X D)).card ≤
          2 * P.card + 1 := by
  let C := chosenEndpointCover (edgesInsideOutside H X D)
  obtain ⟨M₀, hM₀, hM₀verts, hM₀card⟩ :=
    exists_matching_in_compl_remainder_edgeCount H X D
  let M := liftOldRedMatching H G hHG M₀
  have hM : M.IsMatching := liftOldRedMatching_isMatching H G hHG hM₀
  have hMverts : M.verts ⊆ Fin.castSucc ''
      (((((X \ D) \ C : Finset (Fin n))) : Set (Fin n))) := by
    rw [liftOldRedMatching_verts H G hHG M₀]
    rintro _ ⟨v, hv, rfl⟩
    exact ⟨v, hM₀verts hv, rfl⟩
  have hz : z ∉ M.verts := by
    intro hz
    rcases hMverts hz with ⟨v, hv, rfl⟩
    exact (Gᶜ.loopless.irrefl _
      (hstar v (by simpa [C] using hv))).elim
  have hstarM : ∀ v ∈ M.verts, Gᶜ.Adj z v := by
    intro v hv
    rcases hMverts hv with ⟨u, hu, rfl⟩
    exact hstar u (by simpa [C] using hu)
  have hcert := attachedMatchingTriangles_certificate hM hz hstarM
  refine ⟨M, hM, ?_, hcert.1, hcert.2.1, hcert.2.2, ?_⟩
  · simpa [M, C] using hMverts
  · rw [hcert.2.2, liftOldRedMatching_edgeCard H G hHG hM₀]
    simpa [C] using hM₀card

/-- Cross-family edge-disjointness for two stars on disjoint matching
bases.  If the attachment vertices differ, it is enough that at least one
of them is not used by the opposite matching. -/
private lemma attachedMatchingTriangles_cross_inter_card_le_one
    {α : Type*} [Fintype α] [DecidableEq α]
    {G : SimpleGraph α} {M N : G.Subgraph} {z w : α}
    (hMN : Disjoint M.verts N.verts)
    (hzM : z ∉ M.verts) (hwN : w ∉ N.verts)
    (hattach : z = w ∨ z ∉ N.verts ∨ w ∉ M.verts) :
    ∀ t ∈ attachedMatchingTriangles M z,
      ∀ u ∈ attachedMatchingTriangles N w, (t ∩ u).card ≤ 1 := by
  intro t ht u hu
  obtain ⟨e, _he, rfl⟩ := mem_image.mp ht
  obtain ⟨f, _hf, rfl⟩ := mem_image.mp hu
  rw [card_le_one]
  intro x hx y hy
  have classifyM : ∀ q : M.edgeSet, ∀ a,
      a ∈ insert z q.1.toFinset → a = z ∨ a ∈ M.verts := by
    intro q a ha
    rcases mem_insert.mp ha with rfl | ha
    · exact Or.inl rfl
    · exact Or.inr (M.mem_verts_of_mem_edge q.property (by simpa using ha))
  have classifyN : ∀ q : N.edgeSet, ∀ a,
      a ∈ insert w q.1.toFinset → a = w ∨ a ∈ N.verts := by
    intro q a ha
    rcases mem_insert.mp ha with rfl | ha
    · exact Or.inl rfl
    · exact Or.inr (N.mem_verts_of_mem_edge q.property (by simpa using ha))
  have hxM := classifyM e x (mem_inter.mp hx).1
  have hxN := classifyN f x (mem_inter.mp hx).2
  have hyM := classifyM e y (mem_inter.mp hy).1
  have hyN := classifyN f y (mem_inter.mp hy).2
  have hbase : ∀ a, a ∈ M.verts → a ∈ N.verts → False := by
    intro a haM haN
    exact Set.disjoint_left.mp hMN haM haN
  rcases hattach with rfl | hzN | hwM
  · have element_eq : ∀ a,
        (a = z ∨ a ∈ M.verts) → (a = z ∨ a ∈ N.verts) → a = z := by
      intro a haM haN
      rcases haM with haM | haM
      · exact haM
      · rcases haN with haN | haN
        · subst a
          exact (hzM haM).elim
        · exact (hbase _ haM haN).elim
    exact (element_eq x hxM hxN).trans (element_eq y hyM hyN).symm
  · have element_eq : ∀ a,
        (a = z ∨ a ∈ M.verts) → (a = w ∨ a ∈ N.verts) → a = w := by
      intro a haM haN
      rcases haN with haN | haN
      · exact haN
      · rcases haM with haM | haM
        · subst a
          exact (hzN haN).elim
        · exact (hbase _ haM haN).elim
    have hxw : x = w := element_eq x hxM hxN
    have hyw : y = w := element_eq y hyM hyN
    exact hxw.trans hyw.symm
  · have element_eq : ∀ a,
        (a = z ∨ a ∈ M.verts) → (a = w ∨ a ∈ N.verts) → a = z := by
      intro a haM haN
      rcases haM with haM | haM
      · exact haM
      · rcases haN with haN | haN
        · subst a
          exact (hwM haM).elim
        · exact (hbase _ haM haN).elim
    have hxz : x = z := element_eq x hxM hxN
    have hyz : y = z := element_eq y hyM hyN
    exact hxz.trans hyz.symm

private def liftOldSet {n : ℕ} (s : Set (Fin n)) : Set (Fin (n + 1)) :=
  Fin.castSucc '' s

@[simp] private lemma castSucc_mem_liftOldSet {n : ℕ}
    (s : Set (Fin n)) (v : Fin n) :
    v.castSucc ∈ liftOldSet s ↔ v ∈ s := by
  constructor
  · rintro ⟨u, hu, huv⟩
    exact (Fin.castSuccEmb.injective huv).symm ▸ hu
  · exact fun hv ↦ ⟨v, hv, rfl⟩

private lemma last_not_mem_liftOldSet {n : ℕ} (s : Set (Fin n)) :
    Fin.last n ∉ liftOldSet s := by
  rintro ⟨v, _hv, hv⟩
  exact Fin.castSucc_ne_last v hv

private lemma liftOldSet_disjoint_compl {n : ℕ} (s : Set (Fin n)) :
    Disjoint (liftOldSet s) (liftOldSet sᶜ) := by
  rw [Set.disjoint_left]
  intro v hvS hvT
  rcases hvS with ⟨a, ha, rfl⟩
  have haT : a ∈ sᶜ := (castSucc_mem_liftOldSet sᶜ a).mp hvT
  exact haT ha

private lemma liftOldSet_toFinset {n : ℕ} (s : Set (Fin n)) :
    liftOldSet (s.toFinset : Set (Fin n)) = liftOldSet s := by
  ext v
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u, by simpa using hu, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u, by simpa using hu, rfl⟩

private lemma liftOldSet_toFinset_eq_map {n : ℕ} (s : Set (Fin n)) :
    (liftOldSet s).toFinset = s.toFinset.map Fin.castSuccEmb := by
  ext v
  induction v using Fin.lastCases with
  | last => simp [last_not_mem_liftOldSet]
  | cast v => simp [castSucc_mem_liftOldSet]

@[simp] private lemma card_liftOldSet_toFinset {n : ℕ}
    (s : Set (Fin n)) : (liftOldSet s).toFinset.card = s.ncard := by
  rw [liftOldSet_toFinset_eq_map, card_map]
  exact (Set.ncard_eq_toFinset_card' s).symm

private lemma sideEdgeFinset_liftOldSet_eq_map {n : ℕ}
    (H : SimpleGraph (Fin n)) (G : SimpleGraph (Fin (n + 1)))
    (hHG : IsInitialVertexExtension H G) (s : Set (Fin n)) :
    sideEdgeFinset G (liftOldSet s).toFinset =
      (sideEdgeFinset H s.toFinset).map Fin.castSuccEmb.sym2Map := by
  rw [liftOldSet_toFinset_eq_map]
  ext e
  induction e using Sym2.inductionOn with
  | hf a b =>
      induction a using Fin.lastCases with
      | last =>
          constructor
          · intro he
            have hsub := (mem_filter.mp he).2
            have hlast : Fin.last n ∈ s.toFinset.map Fin.castSuccEmb :=
              hsub (by simp)
            rcases mem_map.mp hlast with ⟨u, _hu, hueq⟩
            exact (Fin.castSucc_ne_last u hueq).elim
          · intro he
            rcases mem_map.mp he with ⟨q, _hq, hqeq⟩
            exact (last_not_mem_castSym2Map q (by rw [hqeq]; simp)).elim
      | cast a =>
          induction b using Fin.lastCases with
          | last =>
              constructor
              · intro he
                have hsub := (mem_filter.mp he).2
                have hlast : Fin.last n ∈ s.toFinset.map Fin.castSuccEmb :=
                  hsub (by simp)
                rcases mem_map.mp hlast with ⟨u, _hu, hueq⟩
                exact (Fin.castSucc_ne_last u hueq).elim
              · intro he
                rcases mem_map.mp he with ⟨q, _hq, hqeq⟩
                exact (last_not_mem_castSym2Map q (by rw [hqeq]; simp)).elim
          | cast b =>
              constructor
              · intro he
                rcases mem_filter.mp he with ⟨habG, hsub⟩
                apply mem_map.mpr
                refine ⟨s(a, b), ?_, by simp⟩
                apply mem_filter.mpr
                have habG' : G.Adj a.castSucc b.castSucc := by
                  simpa [SimpleGraph.mem_edgeFinset,
                    SimpleGraph.mem_edgeSet] using habG
                refine ⟨SimpleGraph.mem_edgeFinset.mpr
                  ((hHG a b).mpr habG'), ?_⟩
                intro v hv
                have hvab : v = a ∨ v = b := by simpa using hv
                rcases hvab with hva | hvb
                · have haMap : a.castSucc ∈
                      s.toFinset.map Fin.castSuccEmb := hsub (by simp)
                  rcases mem_map.mp haMap with ⟨u, hu, hua⟩
                  have hua' : u = a := Fin.castSuccEmb.injective hua
                  simpa [hva, hua'] using hu
                · have hbMap : b.castSucc ∈
                      s.toFinset.map Fin.castSuccEmb := hsub (by simp)
                  rcases mem_map.mp hbMap with ⟨u, hu, hub⟩
                  have hub' : u = b := Fin.castSuccEmb.injective hub
                  simpa [hvb, hub'] using hu
              · intro he
                rcases mem_map.mp he with ⟨q, hq, hqeq⟩
                have hqeq' : q = s(a, b) := by
                  apply Fin.castSuccEmb.sym2Map.injective
                  simpa using hqeq
                subst q
                rcases mem_filter.mp hq with ⟨habH, hsub⟩
                apply mem_filter.mpr
                have habH' : H.Adj a b := by
                  simpa [SimpleGraph.mem_edgeFinset,
                    SimpleGraph.mem_edgeSet] using habH
                refine ⟨SimpleGraph.mem_edgeFinset.mpr
                  ((hHG a b).mp habH'), ?_⟩
                intro v hv
                have hvab : v = a.castSucc ∨ v = b.castSucc := by
                  simpa using hv
                rcases hvab with hva | hvb
                · rw [hva]
                  exact mem_map.mpr ⟨a, hsub (by simp), rfl⟩
                · rw [hvb]
                  exact mem_map.mpr ⟨b, hsub (by simp), rfl⟩

private lemma card_sideEdgeFinset_liftOldSet {n : ℕ}
    (H : SimpleGraph (Fin n)) (G : SimpleGraph (Fin (n + 1)))
    (hHG : IsInitialVertexExtension H G) (s : Set (Fin n)) :
    (sideEdgeFinset G (liftOldSet s).toFinset).card =
      (sideEdgeFinset H s.toFinset).card := by
  rw [sideEdgeFinset_liftOldSet_eq_map H G hHG s, card_map]

private lemma edgeInsideOutside_card_le_sideEdgeFinset
    {n : ℕ} (H : SimpleGraph (Fin n)) (X D S : Finset (Fin n))
    (hXS : X ⊆ S) :
    (edgesInsideOutside H X D).card ≤ (sideEdgeFinset H S).card := by
  apply card_le_card
  intro e he
  rcases mem_filter.mp he with ⟨heH, heSub⟩
  exact mem_filter.mpr ⟨heH, heSub.trans (sdiff_subset.trans hXS)⟩

private def twoStarFamily {α : Type*} [Fintype α] [DecidableEq α]
    {G : SimpleGraph α} (M N : G.Subgraph) (z w : α) :
    Finset (Finset α) :=
  attachedMatchingTriangles M z ∪ attachedMatchingTriangles N w

private lemma attachedMatchingTriangles_filter_side_card
    {α : Type*} [Fintype α] [DecidableEq α]
    {G : SimpleGraph α} (M : G.Subgraph) (z : α) (S : Set α)
    (hMS : M.verts ⊆ S) (hz : z ∉ S) :
    ∀ t ∈ attachedMatchingTriangles M z,
      (t.filter fun x ↦ x ∈ S).card = 2 := by
  intro t ht
  obtain ⟨e, _he, rfl⟩ := mem_image.mp ht
  have hbase : e.1.toFinset ⊆ S.toFinset := by
    intro v hv
    have hv' : v ∈ M.verts := M.mem_verts_of_mem_edge e.2 (by simpa using hv)
    simpa using hMS hv'
  have hze : z ∉ e.1.toFinset := by
    intro hzedge
    exact hz (hMS (M.mem_verts_of_mem_edge e.2 (by simpa using hzedge)))
  have heq : (insert z e.1.toFinset).filter (fun x ↦ x ∈ S) =
      e.1.toFinset := by
    ext v
    by_cases hvz : v = z
    · subst v
      simp [hz, hze]
    · simp only [mem_filter, mem_insert, hvz, false_or]
      constructor
      · exact And.left
      · intro hv
        exact ⟨hv, by simpa using hbase hv⟩
  rw [heq]
  exact Sym2.card_toFinset_of_not_isDiag e.1
    (G.not_isDiag_of_mem_edgeSet (M.edgeSet_subset e.2))

/-- If every cross triangle has its two base vertices in `S`, then all
covered internal edges are edges inside `S` (rather than inside its
complement). -/
private lemma coveredInternalEdges_subset_side_of_filter_card_two
    {α : Type*} [Fintype α] [DecidableEq α]
    {G : SimpleGraph α} {S : Set α} {P : Finset (Finset α)}
    (hP : IsInternalCrossPacking G S P)
    (htwo : ∀ t ∈ P, (t.filter fun x ↦ x ∈ S).card = 2) :
    coveredInternalEdges G S P ⊆ sideEdgeFinset G S.toFinset := by
  intro e he
  rcases mem_filter.mp he with ⟨heInternal, t, htP, het⟩
  rcases mem_filter.mp heInternal with ⟨heG, heSame⟩
  refine mem_filter.mpr ⟨heG, ?_⟩
  induction e using Sym2.inductionOn with
  | hf a b =>
      have habG : G.Adj a b := SimpleGraph.mem_edgeFinset.mp heG
      have habT := Finset.mk_mem_sym2_iff.mp het
      have htClique := (mem_internalCrossTriangles.mp (hP.1 htP)).1
      have heSame' : a ∈ S ↔ b ∈ S := by
        simpa [sameSide_mk] using heSame
      have haS : a ∈ S := by
        by_contra haS
        have hbS : b ∉ S := by
          intro hb
          exact haS (heSame'.mpr hb)
        have hdis : Disjoint ({a, b} : Finset α)
            (t.filter fun x ↦ x ∈ S) := by
          rw [Finset.disjoint_left]
          intro x hx hxf
          rcases mem_insert.mp hx with rfl | hx
          · exact haS (mem_filter.mp hxf).2
          · have hxb : x = b := mem_singleton.mp hx
            subst x
            exact hbS (mem_filter.mp hxf).2
        have hsub : ({a, b} : Finset α) ∪
            (t.filter fun x ↦ x ∈ S) ⊆ t := by
          intro x hx
          rcases mem_union.mp hx with hx | hx
          · rcases mem_insert.mp hx with rfl | hx
            · exact habT.1
            · exact mem_singleton.mp hx ▸ habT.2
          · exact (mem_filter.mp hx).1
        have hcard := card_le_card hsub
        rw [card_union_of_disjoint hdis, card_pair habG.ne,
          htwo t htP, htClique.card_eq] at hcard
        omega
      have hbS : b ∈ S := heSame'.mp haS
      intro x hx
      have hx' : x = a ∨ x = b := by
        simpa [Sym2.toFinset_mk_eq] using hx
      rcases hx' with rfl | rfl
      · simpa using haS
      · simpa using hbS

/-- Combine the two endpoint-cover matchings based in one old side into the
two-star red packing used on that side in Claim 4.5.  The matching
subgraphs are retained in the output for the final cross-side
edge-disjointness check. -/
private lemma exists_twoStarRedPacking_on_oldSide
    {n : ℕ} (H : SimpleGraph (Fin n)) (G : SimpleGraph (Fin (n + 1)))
    (hHG : IsInitialVertexExtension H G)
    (S A R D : Finset (Fin n)) (z w : Fin (n + 1))
    (hAS : A ⊆ S) (hRS : R ⊆ S) (hAR : Disjoint A R)
    (hz : z ∉ liftOldSet (S : Set (Fin n)))
    (hw : w ∉ liftOldSet (S : Set (Fin n))) (hzw : z ≠ w)
    (hstarA : ∀ v ∈ (A \ D) \
        chosenEndpointCover (edgesInsideOutside H A D),
      Gᶜ.Adj z v.castSucc)
    (hstarR : ∀ v ∈ (R \ ∅) \
        chosenEndpointCover (edgesInsideOutside H R ∅),
      Gᶜ.Adj w v.castSucc) :
    ∃ MA MR : Gᶜ.Subgraph,
      let PA := attachedMatchingTriangles MA z
      let PR := attachedMatchingTriangles MR w
      let P := twoStarFamily MA MR z w
      MA.IsMatching ∧ MR.IsMatching ∧
        MA.verts ⊆ Fin.castSucc ''
          (((((A \ D) \
            chosenEndpointCover (edgesInsideOutside H A D) :
              Finset (Fin n))) : Set (Fin n))) ∧
        MR.verts ⊆ Fin.castSucc ''
          (((((R \ ∅) \
            chosenEndpointCover (edgesInsideOutside H R ∅) :
              Finset (Fin n))) : Set (Fin n))) ∧
        IsInternalCrossPacking Gᶜ (liftOldSet (S : Set (Fin n))) P ∧
        P.card = Fintype.card MA.edgeSet + Fintype.card MR.edgeSet ∧
        ((A \ D) \
            chosenEndpointCover (edgesInsideOutside H A D)).card ≤
          2 * (attachedMatchingTriangles MA z).card + 1 ∧
        ((R \ ∅) \
            chosenEndpointCover (edgesInsideOutside H R ∅)).card ≤
          2 * (attachedMatchingTriangles MR w).card + 1 := by
  obtain ⟨MA, hMA, hMAverts, hPATri, hPAEd, hPAcard, hPAbound⟩ :=
    exists_lifted_attachedRedMatching H G hHG A D z hstarA
  obtain ⟨MR, hMR, hMRverts, hPRTri, hPREd, hPRcard, hPRbound⟩ :=
    exists_lifted_attachedRedMatching H G hHG R ∅ w hstarR
  have hMAold : MA.verts ⊆ liftOldSet (S : Set (Fin n)) := by
    intro v hv
    rcases hMAverts hv with ⟨u, hu, rfl⟩
    exact (castSucc_mem_liftOldSet (S : Set (Fin n)) u).mpr
      (hAS (mem_sdiff.mp (mem_sdiff.mp hu).1).1)
  have hMRold : MR.verts ⊆ liftOldSet (S : Set (Fin n)) := by
    intro v hv
    rcases hMRverts hv with ⟨u, hu, rfl⟩
    exact (castSucc_mem_liftOldSet (S : Set (Fin n)) u).mpr
      (hRS (mem_sdiff.mp (mem_sdiff.mp hu).1).1)
  have hMAMR : Disjoint MA.verts MR.verts := by
    rw [Set.disjoint_left]
    intro v hvA hvR
    rcases hMAverts hvA with ⟨a, ha, rfl⟩
    rcases hMRverts hvR with ⟨r, hr, har⟩
    have har' : a = r := Fin.castSuccEmb.injective har.symm
    subst r
    exact Finset.disjoint_left.mp hAR
      (mem_sdiff.mp (mem_sdiff.mp ha).1).1
      (mem_sdiff.mp (mem_sdiff.mp hr).1).1
  have hstarMA : ∀ v ∈ MA.verts, Gᶜ.Adj z v := by
    intro v hv
    rcases hMAverts hv with ⟨u, hu, rfl⟩
    exact hstarA u (by simpa using hu)
  have hstarMR : ∀ v ∈ MR.verts, Gᶜ.Adj w v := by
    intro v hv
    rcases hMRverts hv with ⟨u, hu, rfl⟩
    exact hstarR u (by simpa using hu)
  have hpack := attachedMatchingTriangles_union_isInternalCrossPacking
    hMA hMR hMAMR hzw hMAold hMRold hz hw hstarMA hstarMR
  refine ⟨MA, MR, hMA, hMR, hMAverts, hMRverts,
    hpack.1, hpack.2, ?_, ?_⟩
  · simpa [hPAcard] using hPAbound
  · simpa [hPRcard] using hPRbound

/-- The two (initially untruncated) red triangle families in Claim 4.5,
with the exact lower bounds from the endpoint-cover matching argument. -/
private lemma exists_claim45_redSidePackings
    {n : ℕ} (H : SimpleGraph (Fin n)) (G : SimpleGraph (Fin (n + 1)))
    (hHG : IsInitialVertexExtension H G) (s : Set (Fin n))
    (hn : 22 ≤ n) (hsum : s.ncard + sᶜ.ncard = n)
    (hparts : sᶜ.ncard ≤ s.ncard)
    (hk : (internalEdgeFinset H s).card ≤ n / 8)
    (M : Finset (Fin n × Fin n))
    (hM : IsBluePairMatching H (newBlueNeighbors G s)
      (newBlueNeighbors G sᶜ) M)
    (hmax : ∀ N : Finset (Fin n × Fin n),
      IsBluePairMatching H (newBlueNeighbors G s)
        (newBlueNeighbors G sᶜ) N → N.card ≤ M.card)
    (hlt₁ : M.card < (newBlueNeighbors G s).card)
    (hlt₂ : M.card < (newBlueNeighbors G sᶜ).card) :
    ∃ a₁ a₂ : Fin n, ∃ MA₁ MR₁ MA₂ MR₂ : Gᶜ.Subgraph,
      let P₁ := twoStarFamily MA₁ MR₁ a₂.castSucc (Fin.last n)
      let P₂ := twoStarFamily MA₂ MR₂ a₁.castSucc (Fin.last n)
      MA₁.IsMatching ∧ MR₁.IsMatching ∧ MA₂.IsMatching ∧ MR₂.IsMatching ∧
        IsInternalCrossPacking Gᶜ (liftOldSet s) P₁ ∧
        IsInternalCrossPacking Gᶜ (liftOldSet sᶜ) P₂ ∧
        (∀ t ∈ P₁, (t.filter fun x ↦ x ∈ liftOldSet s).card = 2) ∧
        (∀ t ∈ P₂, (t.filter fun x ↦ x ∈ liftOldSet sᶜ).card = 2) ∧
        EdgeDisjoint (P₁ ∪ P₂) ∧
        (s.ncard : ℝ) - M.card - 3 -
            2 * (sideEdgeFinset H s.toFinset).card ≤ 2 * P₁.card ∧
        (sᶜ.ncard : ℝ) - M.card - 2 -
            2 * (sideEdgeFinset H sᶜ.toFinset).card ≤ 2 * P₂.card ∧
        P₁.card + (sideEdgeFinset H s.toFinset).card ≤ s.ncard - 4 := by
  let B₁ := newBlueNeighbors G s
  let B₂ := newBlueNeighbors G sᶜ
  let A₁ := unsaturatedBlueLeft B₁ M
  let A₂ := unsaturatedBlueRight B₂ M
  let R₁ := s.toFinset \ B₁
  let R₂ := sᶜ.toFinset \ B₂
  obtain ⟨a₁, ha₁B, ha₁unsat⟩ := exists_unsaturated_left hM hlt₁
  obtain ⟨a₂, ha₂B, ha₂unsat⟩ := exists_unsaturated_right hM hlt₂
  have ha₁A : a₁ ∈ A₁ := mem_sdiff.mpr ⟨ha₁B, ha₁unsat⟩
  have ha₂A : a₂ ∈ A₂ := mem_sdiff.mpr ⟨ha₂B, ha₂unsat⟩
  have hB₁S : B₁ ⊆ s.toFinset := by
    intro v hv
    simpa [B₁] using ((mem_newBlueNeighbors G s v).mp hv).1
  have hB₂S : B₂ ⊆ sᶜ.toFinset := by
    intro v hv
    simpa [B₂] using ((mem_newBlueNeighbors G sᶜ v).mp hv).1
  have hBdis : Disjoint B₁ B₂ := by
    rw [Finset.disjoint_left]
    intro v hv₁ hv₂
    have hvS : v ∈ s := by simpa using hB₁S hv₁
    have hvT : v ∉ s := by simpa using hB₂S hv₂
    exact hvT hvS
  have hA₁S : A₁ ⊆ s.toFinset :=
    (sdiff_subset.trans hB₁S)
  have hA₂S : A₂ ⊆ sᶜ.toFinset :=
    (sdiff_subset.trans hB₂S)
  have hR₁S : R₁ ⊆ s.toFinset := sdiff_subset
  have hR₂S : R₂ ⊆ sᶜ.toFinset := sdiff_subset
  have hA₁R₁ : Disjoint A₁ R₁ := by
    rw [Finset.disjoint_left]
    intro v hvA hvR
    exact (mem_sdiff.mp hvR).2 (mem_sdiff.mp hvA).1
  have hA₂R₂ : Disjoint A₂ R₂ := by
    rw [Finset.disjoint_left]
    intro v hvA hvR
    exact (mem_sdiff.mp hvR).2 (mem_sdiff.mp hvA).1
  have hstarA₁ : ∀ v ∈ (A₁ \ {a₁}) \
      chosenEndpointCover (edgesInsideOutside H A₁ {a₁}),
      Gᶜ.Adj a₂.castSucc v.castSucc := by
    intro v hv
    have hvA : v ∈ A₁ := (mem_sdiff.mp (mem_sdiff.mp hv).1).1
    have hvRed := maximum_bluePairMatching_compl_adj_unsaturated
      hM hmax hBdis (by simpa [A₁, B₁] using hvA)
        (by simpa [A₂, B₂] using ha₂A)
    exact ((oldRedHom H G hHG).map_adj hvRed).symm
  have hstarA₂ : ∀ v ∈ (A₂ \ ∅) \
      chosenEndpointCover (edgesInsideOutside H A₂ ∅),
      Gᶜ.Adj a₁.castSucc v.castSucc := by
    intro v hv
    have hvA : v ∈ A₂ := (mem_sdiff.mp (mem_sdiff.mp hv).1).1
    have hvRed := maximum_bluePairMatching_compl_adj_unsaturated
      hM hmax hBdis (by simpa [A₁, B₁] using ha₁A)
        (by simpa [A₂, B₂] using hvA)
    exact (oldRedHom H G hHG).map_adj hvRed
  have hstarR₁ : ∀ v ∈ (R₁ \ ∅) \
      chosenEndpointCover (edgesInsideOutside H R₁ ∅),
      Gᶜ.Adj (Fin.last n) v.castSucc := by
    intro v hv
    exact last_red_adj_of_mem_side_sdiff_newBlue G s
      (by simpa [R₁, B₁] using
        (mem_sdiff.mp (mem_sdiff.mp hv).1).1)
  have hstarR₂ : ∀ v ∈ (R₂ \ ∅) \
      chosenEndpointCover (edgesInsideOutside H R₂ ∅),
      Gᶜ.Adj (Fin.last n) v.castSucc := by
    intro v hv
    exact last_red_adj_of_mem_side_sdiff_newBlue G sᶜ
      (by simpa [R₂, B₂] using
        (mem_sdiff.mp (mem_sdiff.mp hv).1).1)
  have ha₂out : a₂.castSucc ∉ liftOldSet s := by
    intro ha
    have haS : a₂ ∈ s := (castSucc_mem_liftOldSet s a₂).mp ha
    have haT : a₂ ∉ s := by simpa using hB₂S ha₂B
    exact haT haS
  have ha₁out : a₁.castSucc ∉ liftOldSet sᶜ := by
    intro ha
    have haT : a₁ ∈ sᶜ := (castSucc_mem_liftOldSet sᶜ a₁).mp ha
    have haS : a₁ ∈ s := by simpa using hB₁S ha₁B
    exact haT haS
  obtain ⟨MA₁, MR₁, hMA₁, hMR₁, hMA₁verts, hMR₁verts,
      hP₁, hP₁card, hMA₁bound, hMR₁bound⟩ :=
    exists_twoStarRedPacking_on_oldSide H G hHG s.toFinset A₁ R₁ {a₁}
      a₂.castSucc (Fin.last n) hA₁S hR₁S hA₁R₁
      (by simpa only [liftOldSet_toFinset] using ha₂out)
      (by simpa only [liftOldSet_toFinset] using last_not_mem_liftOldSet s)
      (Fin.castSucc_ne_last a₂)
      hstarA₁ hstarR₁
  have hP₁' : IsInternalCrossPacking Gᶜ (liftOldSet s)
      (twoStarFamily MA₁ MR₁ a₂.castSucc (Fin.last n)) := by
    simpa only [liftOldSet_toFinset] using hP₁
  have hscompl : (↑(sᶜ.toFinset) : Set (Fin n)) = sᶜ :=
    Set.coe_toFinset sᶜ
  obtain ⟨MA₂, MR₂, hMA₂, hMR₂, hMA₂verts, hMR₂verts,
      hP₂, hP₂card, hMA₂bound, hMR₂bound⟩ :=
    exists_twoStarRedPacking_on_oldSide H G hHG sᶜ.toFinset A₂ R₂ ∅
      a₁.castSucc (Fin.last n) hA₂S hR₂S hA₂R₂
      (by
        rw [hscompl]
        exact ha₁out)
      (by
        rw [hscompl]
        exact last_not_mem_liftOldSet sᶜ)
      (Fin.castSucc_ne_last a₁)
      hstarA₂ hstarR₂
  have hP₂' : IsInternalCrossPacking Gᶜ (liftOldSet sᶜ)
      (twoStarFamily MA₂ MR₂ a₁.castSucc (Fin.last n)) := by
    rw [hscompl] at hP₂
    exact hP₂
  have hC_A₁ : (chosenEndpointCover
      (edgesInsideOutside H A₁ {a₁})).card ≤
      (sideEdgeFinset H s.toFinset).card :=
    (card_chosenEndpointCover_le _).trans
      (edgeInsideOutside_card_le_sideEdgeFinset H A₁ {a₁} s.toFinset hA₁S)
  have hC_R₁ : (chosenEndpointCover
      (edgesInsideOutside H R₁ ∅)).card ≤
      (sideEdgeFinset H s.toFinset).card :=
    (card_chosenEndpointCover_le _).trans
      (edgeInsideOutside_card_le_sideEdgeFinset H R₁ ∅ s.toFinset hR₁S)
  have hC_A₂ : (chosenEndpointCover
      (edgesInsideOutside H A₂ ∅)).card ≤
      (sideEdgeFinset H sᶜ.toFinset).card :=
    (card_chosenEndpointCover_le _).trans
      (edgeInsideOutside_card_le_sideEdgeFinset H A₂ ∅ sᶜ.toFinset hA₂S)
  have hC_R₂ : (chosenEndpointCover
      (edgesInsideOutside H R₂ ∅)).card ≤
      (sideEdgeFinset H sᶜ.toFinset).card :=
    (card_chosenEndpointCover_le _).trans
      (edgeInsideOutside_card_le_sideEdgeFinset H R₂ ∅ sᶜ.toFinset hR₂S)
  have hA₁account := card_le_card_sdiff_sdiff_add_card_filter_add_card
    A₁ {a₁} (chosenEndpointCover (edgesInsideOutside H A₁ {a₁}))
  have hR₁account := card_le_card_sdiff_sdiff_add_card_filter_add_card
    R₁ ∅ (chosenEndpointCover (edgesInsideOutside H R₁ ∅))
  have hA₂account := card_le_card_sdiff_sdiff_add_card_filter_add_card
    A₂ ∅ (chosenEndpointCover (edgesInsideOutside H A₂ ∅))
  have hR₂account := card_le_card_sdiff_sdiff_add_card_filter_add_card
    R₂ ∅ (chosenEndpointCover (edgesInsideOutside H R₂ ∅))
  have hB₁card : B₁.card ≤ s.toFinset.card := card_le_card hB₁S
  have hB₂card : B₂.card ≤ sᶜ.toFinset.card := card_le_card hB₂S
  have hA₁card : A₁.card = B₁.card - M.card := by
    simpa [A₁, B₁] using hM.card_unsaturatedBlueLeft
  have hA₂card : A₂.card = B₂.card - M.card := by
    simpa [A₂, B₂] using hM.card_unsaturatedBlueRight
  have hR₁card : R₁.card = s.toFinset.card - B₁.card := by
    dsimp only [R₁]
    rw [card_sdiff_of_subset hB₁S]
  have hR₂card : R₂.card = sᶜ.toFinset.card - B₂.card := by
    dsimp only [R₂]
    rw [card_sdiff_of_subset hB₂S]
  have hMB₁ : M.card ≤ B₁.card := by
    exact Nat.le_of_lt (by simpa [B₁] using hlt₁)
  have hMB₂ : M.card ≤ B₂.card := by
    exact Nat.le_of_lt (by simpa [B₂] using hlt₂)
  have hA₁card' : A₁.card + M.card = B₁.card := by
    rw [hA₁card, Nat.sub_add_cancel hMB₁]
  have hA₂card' : A₂.card + M.card = B₂.card := by
    rw [hA₂card, Nat.sub_add_cancel hMB₂]
  have hR₁card' : R₁.card + B₁.card = s.toFinset.card := by
    rw [hR₁card, Nat.sub_add_cancel hB₁card]
  have hR₂card' : R₂.card + B₂.card = sᶜ.toFinset.card := by
    rw [hR₂card, Nat.sub_add_cancel hB₂card]
  have hlower₁ : (s.ncard : ℝ) - M.card - 3 -
      2 * (sideEdgeFinset H s.toFinset).card ≤
      2 * (twoStarFamily MA₁ MR₁ a₂.castSucc (Fin.last n)).card := by
    have hnat : s.toFinset.card ≤ M.card + 3 +
        2 * (sideEdgeFinset H s.toFinset).card +
          2 * (twoStarFamily MA₁ MR₁ a₂.castSucc (Fin.last n)).card := by
      have hsingle : (({a₁} : Finset (Fin n)).filter
          fun x ↦ x ∈ A₁).card ≤ 1 := by
        have h := Finset.card_filter_le ({a₁} : Finset (Fin n))
          (fun x ↦ x ∈ A₁)
        simpa using h
      have hempty₁ : ((∅ : Finset (Fin n)).filter
          fun x ↦ x ∈ R₁).card = 0 := by
        rw [Finset.filter_empty, Finset.card_empty]
      have hMA₁old : MA₁.verts ⊆ liftOldSet s := by
        intro v hv
        rcases hMA₁verts hv with ⟨u, hu, rfl⟩
        exact (castSucc_mem_liftOldSet s u).mpr
          (by simpa using hA₁S (mem_sdiff.mp (mem_sdiff.mp hu).1).1)
      have hMR₁old : MR₁.verts ⊆ liftOldSet s := by
        intro v hv
        rcases hMR₁verts hv with ⟨u, hu, rfl⟩
        exact (castSucc_mem_liftOldSet s u).mpr
          (by simpa using hR₁S (mem_sdiff.mp (mem_sdiff.mp hu).1).1)
      have hPAcard : (attachedMatchingTriangles MA₁ a₂.castSucc).card =
          Fintype.card MA₁.edgeSet :=
        card_attachedMatchingTriangles _ (fun hz ↦ ha₂out (hMA₁old hz))
      have hPRcard : (attachedMatchingTriangles MR₁ (Fin.last n)).card =
          Fintype.card MR₁.edgeSet :=
        card_attachedMatchingTriangles _
          (fun hz ↦ last_not_mem_liftOldSet s (hMR₁old hz))
      have hPsum :
          (twoStarFamily MA₁ MR₁ a₂.castSucc (Fin.last n)).card =
            (attachedMatchingTriangles MA₁ a₂.castSucc).card +
              (attachedMatchingTriangles MR₁ (Fin.last n)).card := by
        calc
          _ = Fintype.card MA₁.edgeSet + Fintype.card MR₁.edgeSet := hP₁card
          _ = _ := by rw [hPAcard, hPRcard]
      omega
    have hncard : s.toFinset.card = s.ncard :=
      (Set.ncard_eq_toFinset_card' s).symm
    rw [hncard] at hnat
    have hnatR : (s.ncard : ℝ) ≤ (M.card : ℝ) + 3 +
        2 * ((sideEdgeFinset H s.toFinset).card : ℝ) +
          2 * ((twoStarFamily MA₁ MR₁ a₂.castSucc
            (Fin.last n)).card : ℝ) := by
      exact_mod_cast hnat
    linarith
  have hlower₂ : (sᶜ.ncard : ℝ) - M.card - 2 -
      2 * (sideEdgeFinset H sᶜ.toFinset).card ≤
      2 * (twoStarFamily MA₂ MR₂ a₁.castSucc (Fin.last n)).card := by
    have hnat : sᶜ.toFinset.card ≤ M.card + 2 +
        2 * (sideEdgeFinset H sᶜ.toFinset).card +
          2 * (twoStarFamily MA₂ MR₂ a₁.castSucc (Fin.last n)).card := by
      have hemptyA : ((∅ : Finset (Fin n)).filter
          fun x ↦ x ∈ A₂).card = 0 := by
        rw [Finset.filter_empty, Finset.card_empty]
      have hemptyR : ((∅ : Finset (Fin n)).filter
          fun x ↦ x ∈ R₂).card = 0 := by
        rw [Finset.filter_empty, Finset.card_empty]
      have hMA₂old : MA₂.verts ⊆ liftOldSet sᶜ := by
        intro v hv
        rcases hMA₂verts hv with ⟨u, hu, rfl⟩
        exact (castSucc_mem_liftOldSet sᶜ u).mpr
          (by simpa using hA₂S (mem_sdiff.mp (mem_sdiff.mp hu).1).1)
      have hMR₂old : MR₂.verts ⊆ liftOldSet sᶜ := by
        intro v hv
        rcases hMR₂verts hv with ⟨u, hu, rfl⟩
        exact (castSucc_mem_liftOldSet sᶜ u).mpr
          (by simpa using hR₂S (mem_sdiff.mp (mem_sdiff.mp hu).1).1)
      have hPAcard : (attachedMatchingTriangles MA₂ a₁.castSucc).card =
          Fintype.card MA₂.edgeSet :=
        card_attachedMatchingTriangles _ (fun hz ↦ ha₁out (hMA₂old hz))
      have hPRcard : (attachedMatchingTriangles MR₂ (Fin.last n)).card =
          Fintype.card MR₂.edgeSet :=
        card_attachedMatchingTriangles _
          (fun hz ↦ last_not_mem_liftOldSet sᶜ (hMR₂old hz))
      have hPsum :
          (twoStarFamily MA₂ MR₂ a₁.castSucc (Fin.last n)).card =
            (attachedMatchingTriangles MA₂ a₁.castSucc).card +
              (attachedMatchingTriangles MR₂ (Fin.last n)).card := by
        calc
          _ = Fintype.card MA₂.edgeSet + Fintype.card MR₂.edgeSet := hP₂card
          _ = _ := by rw [hPAcard, hPRcard]
      omega
    have hncard : sᶜ.toFinset.card = sᶜ.ncard :=
      (Set.ncard_eq_toFinset_card' (sᶜ : Set (Fin n))).symm
    rw [hncard] at hnat
    have hnatR : (sᶜ.ncard : ℝ) ≤ (M.card : ℝ) + 2 +
        2 * ((sideEdgeFinset H sᶜ.toFinset).card : ℝ) +
          2 * ((twoStarFamily MA₂ MR₂ a₁.castSucc
            (Fin.last n)).card : ℝ) := by
      exact_mod_cast hnat
    linarith
  let S' : Finset (Fin (n + 1)) := s.toFinset.map Fin.castSuccEmb
  have hbaseDisjoint : Disjoint MA₁.verts.toFinset MR₁.verts.toFinset := by
    rw [Finset.disjoint_left]
    intro v hvA hvR
    have hvA' : v ∈ MA₁.verts := by simpa using hvA
    have hvR' : v ∈ MR₁.verts := by simpa using hvR
    rcases hMA₁verts hvA' with ⟨a, ha, rfl⟩
    rcases hMR₁verts hvR' with ⟨r, hr, har⟩
    have har' : a = r := Fin.castSuccEmb.injective har.symm
    subst r
    exact Finset.disjoint_left.mp hA₁R₁
      (mem_sdiff.mp (mem_sdiff.mp ha).1).1
      (mem_sdiff.mp (mem_sdiff.mp hr).1).1
  have hbaseSubset : MA₁.verts.toFinset ∪ MR₁.verts.toFinset ⊆
      S'.erase a₁.castSucc := by
    intro v hv
    rcases mem_union.mp hv with hv | hv
    · have hv' : v ∈ MA₁.verts := by simpa using hv
      rcases hMA₁verts hv' with ⟨a, ha, rfl⟩
      apply mem_erase.mpr
      refine ⟨?_, mem_map.mpr ⟨a,
        (by simpa using hA₁S (mem_sdiff.mp (mem_sdiff.mp ha).1).1), rfl⟩⟩
      intro haa
      have haa' : a = a₁ := Fin.castSuccEmb.injective haa
      subst a
      exact (mem_sdiff.mp (mem_sdiff.mp ha).1).2 (by simp)
    · have hv' : v ∈ MR₁.verts := by simpa using hv
      rcases hMR₁verts hv' with ⟨r, hr, rfl⟩
      apply mem_erase.mpr
      refine ⟨?_, mem_map.mpr ⟨r,
        (by simpa using hR₁S (mem_sdiff.mp (mem_sdiff.mp hr).1).1), rfl⟩⟩
      intro hra
      have hra' : r = a₁ := Fin.castSuccEmb.injective hra
      subst r
      have haR : a₁ ∈ R₁ := (mem_sdiff.mp (mem_sdiff.mp hr).1).1
      exact (mem_sdiff.mp haR).2 (by simpa [B₁] using ha₁B)
  have ha₁S' : a₁.castSucc ∈ S' := by
    exact mem_map.mpr ⟨a₁,
      (by simpa using hB₁S (by simpa [B₁] using ha₁B)), rfl⟩
  have hcardS' : S'.card = s.ncard := by
    dsimp only [S']
    rw [card_map]
    exact (Set.ncard_eq_toFinset_card' s).symm
  have hbaseCard : MA₁.verts.toFinset.card + MR₁.verts.toFinset.card ≤
      s.ncard - 1 := by
    rw [← card_union_of_disjoint hbaseDisjoint]
    calc
      (MA₁.verts.toFinset ∪ MR₁.verts.toFinset).card ≤
          (S'.erase a₁.castSucc).card := card_le_card hbaseSubset
      _ = s.ncard - 1 := by rw [card_erase_of_mem ha₁S', hcardS']
  have htwiceP₁ : 2 *
      (twoStarFamily MA₁ MR₁ a₂.castSucc (Fin.last n)).card ≤
        s.ncard - 1 := by
    rw [SimpleGraph.Subgraph.IsMatching.card_verts_eq_two_mul_card_edgeFinset_GL
        hMA₁,
      SimpleGraph.Subgraph.IsMatching.card_verts_eq_two_mul_card_edgeFinset_GL
        hMR₁] at hbaseCard
    omega
  have hk₁ : (sideEdgeFinset H s.toFinset).card ≤ n / 8 := by
    apply (card_le_card ?_).trans hk
    rw [internalEdgeFinset_eq_union_sides H s]
    exact subset_union_left
  have hcap₁ : (twoStarFamily MA₁ MR₁ a₂.castSucc (Fin.last n)).card +
      (sideEdgeFinset H s.toFinset).card ≤ s.ncard - 4 :=
    claim45_first_cap_arithmetic n s.ncard sᶜ.ncard
      (sideEdgeFinset H s.toFinset).card
      (twoStarFamily MA₁ MR₁ a₂.castSucc (Fin.last n)).card
      hn hsum hparts hk₁ htwiceP₁
  have hMA₁old : MA₁.verts ⊆ liftOldSet s := by
    intro v hv
    rcases hMA₁verts hv with ⟨u, hu, rfl⟩
    exact (castSucc_mem_liftOldSet s u).mpr
      (by simpa using hA₁S (mem_sdiff.mp (mem_sdiff.mp hu).1).1)
  have hMR₁old : MR₁.verts ⊆ liftOldSet s := by
    intro v hv
    rcases hMR₁verts hv with ⟨u, hu, rfl⟩
    exact (castSucc_mem_liftOldSet s u).mpr
      (by simpa using hR₁S (mem_sdiff.mp (mem_sdiff.mp hu).1).1)
  have hMA₂old : MA₂.verts ⊆ liftOldSet sᶜ := by
    intro v hv
    rcases hMA₂verts hv with ⟨u, hu, rfl⟩
    exact (castSucc_mem_liftOldSet sᶜ u).mpr
      (by simpa using hA₂S (mem_sdiff.mp (mem_sdiff.mp hu).1).1)
  have hMR₂old : MR₂.verts ⊆ liftOldSet sᶜ := by
    intro v hv
    rcases hMR₂verts hv with ⟨u, hu, rfl⟩
    exact (castSucc_mem_liftOldSet sᶜ u).mpr
      (by simpa using hR₂S (mem_sdiff.mp (mem_sdiff.mp hu).1).1)
  have hP₁side : ∀ t ∈ twoStarFamily MA₁ MR₁ a₂.castSucc (Fin.last n),
      (t.filter fun x ↦ x ∈ liftOldSet s).card = 2 := by
    intro t ht
    rcases mem_union.mp ht with ht | ht
    · exact attachedMatchingTriangles_filter_side_card MA₁ a₂.castSucc
        (liftOldSet s) hMA₁old ha₂out t ht
    · exact attachedMatchingTriangles_filter_side_card MR₁ (Fin.last n)
        (liftOldSet s) hMR₁old (last_not_mem_liftOldSet s) t ht
  have hP₂side : ∀ t ∈ twoStarFamily MA₂ MR₂ a₁.castSucc (Fin.last n),
      (t.filter fun x ↦ x ∈ liftOldSet sᶜ).card = 2 := by
    intro t ht
    rcases mem_union.mp ht with ht | ht
    · exact attachedMatchingTriangles_filter_side_card MA₂ a₁.castSucc
        (liftOldSet sᶜ) hMA₂old ha₁out t ht
    · exact attachedMatchingTriangles_filter_side_card MR₂ (Fin.last n)
        (liftOldSet sᶜ) hMR₂old (last_not_mem_liftOldSet sᶜ) t ht
  have disjointAcross : ∀ (U V : Gᶜ.Subgraph),
      U.verts ⊆ liftOldSet s → V.verts ⊆ liftOldSet sᶜ →
      Disjoint U.verts V.verts := by
    intro U V hU hV
    rw [Set.disjoint_left]
    intro v hvU hvV
    exact Set.disjoint_left.mp (liftOldSet_disjoint_compl s) (hU hvU) (hV hvV)
  have ha₂MA₁ : a₂.castSucc ∉ MA₁.verts := fun h ↦ ha₂out (hMA₁old h)
  have ha₁MA₂ : a₁.castSucc ∉ MA₂.verts := fun h ↦ ha₁out (hMA₂old h)
  have hlastMR₁ : Fin.last n ∉ MR₁.verts := fun h ↦
    last_not_mem_liftOldSet s (hMR₁old h)
  have hlastMR₂ : Fin.last n ∉ MR₂.verts := fun h ↦
    last_not_mem_liftOldSet sᶜ (hMR₂old h)
  have ha₁MA₁ : a₁.castSucc ∉ MA₁.verts := by
    intro ha
    rcases hMA₁verts ha with ⟨u, hu, hua⟩
    have hua' : u = a₁ := Fin.castSuccEmb.injective hua
    subst u
    exact (mem_sdiff.mp (mem_sdiff.mp hu).1).2 (by simp)
  have ha₂MR₂ : a₂.castSucc ∉ MR₂.verts := by
    intro ha
    rcases hMR₂verts ha with ⟨u, hu, hua⟩
    have hua' : u = a₂ := Fin.castSuccEmb.injective hua
    subst u
    have huR₂ : a₂ ∈ R₂ := (mem_sdiff.mp (mem_sdiff.mp hu).1).1
    have huNotB₂ : a₂ ∉ B₂ := (mem_sdiff.mp huR₂).2
    exact huNotB₂ (by simpa [B₂] using ha₂B)
  have hcrossAA := attachedMatchingTriangles_cross_inter_card_le_one
    (disjointAcross MA₁ MA₂ hMA₁old hMA₂old) ha₂MA₁ ha₁MA₂
      (Or.inr (Or.inr ha₁MA₁))
  have hcrossAR := attachedMatchingTriangles_cross_inter_card_le_one
    (disjointAcross MA₁ MR₂ hMA₁old hMR₂old) ha₂MA₁ hlastMR₂
      (Or.inr (Or.inl ha₂MR₂))
  have hlastMA₂ : Fin.last n ∉ MA₂.verts := fun h ↦
    last_not_mem_liftOldSet sᶜ (hMA₂old h)
  have hcrossRA := attachedMatchingTriangles_cross_inter_card_le_one
    (disjointAcross MR₁ MA₂ hMR₁old hMA₂old) hlastMR₁ ha₁MA₂
      (Or.inr (Or.inl hlastMA₂))
  have hcrossRR := attachedMatchingTriangles_cross_inter_card_le_one
    (disjointAcross MR₁ MR₂ hMR₁old hMR₂old) hlastMR₁ hlastMR₂
      (Or.inl rfl)
  have hcross : ∀ t ∈ twoStarFamily MA₁ MR₁ a₂.castSucc (Fin.last n),
      ∀ u ∈ twoStarFamily MA₂ MR₂ a₁.castSucc (Fin.last n),
        (t ∩ u).card ≤ 1 := by
    intro t ht u hu
    rcases mem_union.mp ht with ht | ht <;>
      rcases mem_union.mp hu with hu | hu
    · exact hcrossAA t ht u hu
    · exact hcrossAR t ht u hu
    · exact hcrossRA t ht u hu
    · exact hcrossRR t ht u hu
  have hPUnion : EdgeDisjoint
      (twoStarFamily MA₁ MR₁ a₂.castSucc (Fin.last n) ∪
        twoStarFamily MA₂ MR₂ a₁.castSucc (Fin.last n)) := by
    intro t ht u hu htu
    rcases mem_union.mp ht with ht₁ | ht₂ <;>
      rcases mem_union.mp hu with hu₁ | hu₂
    · exact hP₁'.2 ht₁ hu₁ htu
    · exact hcross t ht₁ u hu₂
    · simpa [Finset.inter_comm] using hcross u hu₁ t ht₂
    · exact hP₂'.2 ht₂ hu₂ htu
  exact ⟨a₁, a₂, MA₁, MR₁, MA₂, MR₂, hMA₁, hMR₁, hMA₂, hMR₂,
    hP₁', hP₂', hP₁side, hP₂side, hPUnion, hlower₁, hlower₂, hcap₁⟩

/-- Truncate the second red family at the almost-complete admissibility
cap.  The first family is already below its cap by the matching support
estimate. -/
private lemma exists_claim45_truncated_redSidePackings
    {n : ℕ} (H : SimpleGraph (Fin n)) (G : SimpleGraph (Fin (n + 1)))
    (hHG : IsInitialVertexExtension H G) (s : Set (Fin n))
    (hn : 22 ≤ n) (hsum : s.ncard + sᶜ.ncard = n)
    (hparts : sᶜ.ncard ≤ s.ncard)
    (hk : (internalEdgeFinset H s).card ≤ n / 8)
    (hsize₂ : (internalEdgeFinset H s).card + 4 ≤ sᶜ.ncard)
    (M : Finset (Fin n × Fin n))
    (hM : IsBluePairMatching H (newBlueNeighbors G s)
      (newBlueNeighbors G sᶜ) M)
    (hmax : ∀ N : Finset (Fin n × Fin n),
      IsBluePairMatching H (newBlueNeighbors G s)
        (newBlueNeighbors G sᶜ) N → N.card ≤ M.card)
    (hlt₁ : M.card < (newBlueNeighbors G s).card)
    (hlt₂ : M.card < (newBlueNeighbors G sᶜ).card) :
    ∃ P₁ P₂ : Finset (Finset (Fin (n + 1))),
      IsInternalCrossPacking Gᶜ (liftOldSet s) P₁ ∧
      IsInternalCrossPacking Gᶜ (liftOldSet sᶜ) P₂ ∧
      (∀ t ∈ P₁, (t.filter fun x ↦ x ∈ liftOldSet s).card = 2) ∧
      (∀ t ∈ P₂, (t.filter fun x ↦ x ∈ liftOldSet sᶜ).card = 2) ∧
      EdgeDisjoint (P₁ ∪ P₂) ∧
      (s.ncard : ℝ) - M.card - 3 -
          2 * (sideEdgeFinset H s.toFinset).card ≤ 2 * P₁.card ∧
      ((sᶜ.ncard : ℝ) - M.card - 2 -
          2 * (sideEdgeFinset H sᶜ.toFinset).card ≤ 2 * P₂.card ∨
        (P₂.card : ℝ) = sᶜ.ncard -
          (sideEdgeFinset H sᶜ.toFinset).card - 4) ∧
      P₁.card + (sideEdgeFinset H s.toFinset).card ≤ s.ncard - 4 ∧
      P₂.card + (sideEdgeFinset H sᶜ.toFinset).card ≤ sᶜ.ncard - 4 := by
  obtain ⟨a₁, a₂, MA₁, MR₁, MA₂, MR₂, _hMA₁, _hMR₁, _hMA₂, _hMR₂,
      hP₁, hP₂raw, hP₁side, hP₂rawside, hPUnion, hlower₁, hlower₂, hcap₁⟩ :=
    exists_claim45_redSidePackings H G hHG s hn hsum hparts hk M hM hmax
      hlt₁ hlt₂
  let P₁ := twoStarFamily MA₁ MR₁ a₂.castSucc (Fin.last n)
  let P₂raw := twoStarFamily MA₂ MR₂ a₁.castSucc (Fin.last n)
  let c₂ := sᶜ.ncard - (sideEdgeFinset H sᶜ.toFinset).card - 4
  obtain ⟨P₂, hP₂sub, hP₂card⟩ :=
    Finset.exists_subset_card_eq (s := P₂raw)
      (n := min P₂raw.card c₂) (min_le_left _ _)
  have hP₂ : IsInternalCrossPacking Gᶜ (liftOldSet sᶜ) P₂ := by
    refine ⟨hP₂sub.trans hP₂raw.1, ?_⟩
    intro t ht u hu htu
    exact hP₂raw.2 (hP₂sub ht) (hP₂sub hu) htu
  have hP₂side : ∀ t ∈ P₂,
      (t.filter fun x ↦ x ∈ liftOldSet sᶜ).card = 2 := by
    intro t ht
    exact hP₂rawside t (hP₂sub ht)
  have hUnion : EdgeDisjoint (P₁ ∪ P₂) := by
    intro t ht u hu htu
    apply hPUnion
    · rcases mem_union.mp ht with ht | ht
      · exact mem_union_left _ ht
      · exact mem_union_right _ (hP₂sub ht)
    · rcases mem_union.mp hu with hu | hu
      · exact mem_union_left _ hu
      · exact mem_union_right _ (hP₂sub hu)
    · exact htu
  have hk₂le : (sideEdgeFinset H sᶜ.toFinset).card + 4 ≤ sᶜ.ncard := by
    have hside : (sideEdgeFinset H sᶜ.toFinset).card ≤
        (internalEdgeFinset H s).card := by
      rw [internalEdgeFinset_eq_union_sides H s]
      exact card_le_card subset_union_right
    omega
  have hcap₂ : P₂.card + (sideEdgeFinset H sᶜ.toFinset).card ≤
      sᶜ.ncard - 4 := by
    have hP₂le : P₂.card ≤ c₂ := by
      rw [hP₂card]
      exact min_le_right _ _
    dsimp only [c₂] at hP₂le
    omega
  have hsecond :
      (sᶜ.ncard : ℝ) - M.card - 2 -
          2 * (sideEdgeFinset H sᶜ.toFinset).card ≤ 2 * P₂.card ∨
        (P₂.card : ℝ) = sᶜ.ncard -
          (sideEdgeFinset H sᶜ.toFinset).card - 4 := by
    by_cases hraw : P₂raw.card ≤ c₂
    · left
      have hcard : P₂.card = P₂raw.card := by
        rw [hP₂card, min_eq_left hraw]
      rw [hcard]
      exact hlower₂
    · right
      have hc₂ : c₂ ≤ P₂raw.card := Nat.le_of_not_ge hraw
      have hcard : P₂.card = c₂ := by
        rw [hP₂card, min_eq_right hc₂]
      have hcast : (c₂ : ℝ) = (sᶜ.ncard : ℝ) -
          (sideEdgeFinset H sᶜ.toFinset).card - 4 := by
        dsimp only [c₂]
        rw [Nat.cast_sub]
        · rw [Nat.cast_sub]
          · norm_num
          · omega
        · omega
      rw [hcard, hcast]
  exact ⟨P₁, P₂, hP₁, hP₂, hP₁side, hP₂side, hUnion, hlower₁,
    hsecond, hcap₁, hcap₂⟩

/-! ## The residual red packing for Claim 4.5 -/

private lemma pair_not_mem_triangle_of_disjoint_two_side
    {α : Type*} [DecidableEq α]
    {S T t : Finset α} (hST : Disjoint S T)
    (htcard : t.card = 3)
    (htT : (t.filter fun x ↦ x ∈ T).card = 2)
    {e : Sym2 α} (hecard : e.toFinset.card = 2)
    (heS : e.toFinset ⊆ S) : e ∉ t.sym2 := by
  intro het
  have heSub : e.toFinset ⊆ t := by
    intro v hv
    exact (mem_sym2_iff.mp het) v (by simpa using hv)
  have hdisj : Disjoint e.toFinset (t.filter fun x ↦ x ∈ T) := by
    rw [Finset.disjoint_left]
    intro v hvE hvT
    exact Finset.disjoint_left.mp hST (heS hvE) (mem_filter.mp hvT).2
  have hunion : e.toFinset ∪ (t.filter fun x ↦ x ∈ T) ⊆ t := by
    intro v hv
    rcases mem_union.mp hv with hv | hv
    · exact heSub hv
    · exact (mem_filter.mp hv).1
  have hcard := card_le_card hunion
  rw [card_union_of_disjoint hdisj, hecard, htT, htcard] at hcard
  omega

private lemma triangleFamilies_disjoint_of_two_disjoint_sides
    {α : Type*} [DecidableEq α]
    {S T : Finset α} (hST : Disjoint S T)
    {P₁ P₂ : Finset (Finset α)}
    (htri : ∀ t ∈ P₁ ∪ P₂, t.card = 3)
    (hP₁side : ∀ t ∈ P₁, (t.filter fun x ↦ x ∈ S).card = 2)
    (hP₂side : ∀ t ∈ P₂, (t.filter fun x ↦ x ∈ T).card = 2) :
    Disjoint P₁ P₂ := by
  rw [Finset.disjoint_left]
  intro t ht₁ ht₂
  have hfilters : Disjoint (t.filter fun x ↦ x ∈ S)
      (t.filter fun x ↦ x ∈ T) := by
    rw [Finset.disjoint_left]
    intro v hvS hvT
    exact Finset.disjoint_left.mp hST (mem_filter.mp hvS).2
      (mem_filter.mp hvT).2
  have hunion : (t.filter fun x ↦ x ∈ S) ∪
      (t.filter fun x ↦ x ∈ T) ⊆ t := by
    exact union_subset (filter_subset _ _) (filter_subset _ _)
  have hcard := card_le_card hunion
  rw [card_union_of_disjoint hfilters, hP₁side t ht₁,
    hP₂side t ht₂, htri t (mem_union_left _ ht₁)] at hcard
  omega

/-- If `P₁` uses two vertices of `S` in every triangle and `P₂` uses two
vertices of a disjoint set `T`, then the pairs of `P₁ ∪ P₂` lying wholly
inside `S` are precisely among the internal base edges covered by `P₁`.
This is the localization needed to apply the almost-complete theorem after
deleting every pair used by the two integral families. -/
private lemma familyPairs_inter_side_subset_covered_first
    {α : Type*} [Fintype α] [DecidableEq α]
    (R : SimpleGraph α) (S T : Finset α) (hST : Disjoint S T)
    (P₁ P₂ : Finset (Finset α))
    (hP₁ : IsInternalCrossPacking R (S : Set α) P₁)
    (hP₂ : IsInternalCrossPacking R (T : Set α) P₂)
    (hP₂side : ∀ t ∈ P₂,
      (t.filter fun x ↦ x ∈ T).card = 2) :
    familyPairFinset (P₁ ∪ P₂) ∩ sideEdgeFinset R S ⊆
      coveredInternalEdges R (S : Set α) P₁ := by
  intro e he
  rcases mem_inter.mp he with ⟨heFamily, heSide⟩
  rcases mem_familyPairFinset.mp heFamily with ⟨t, ht, het⟩
  rcases mem_union.mp ht with ht₁ | ht₂
  · apply mem_filter.mpr
    refine ⟨?_, t, ht₁, het⟩
    rcases mem_filter.mp heSide with ⟨heR, heS⟩
    apply mem_filter.mpr
    refine ⟨heR, (sameSide_iff_subset_side_or_compl
      (S : Set α) e).mpr (Or.inl ?_)⟩
    simpa using heS
  · have htcard : t.card = 3 :=
      (mem_internalCrossTriangles.mp (hP₂.1 ht₂)).1.card_eq
    have hecard : e.toFinset.card = 2 :=
      SimpleGraph.card_toFinset_mem_edgeFinset ⟨e, (mem_filter.mp heSide).1⟩
    exact ((pair_not_mem_triangle_of_disjoint_two_side hST htcard
      (hP₂side t ht₂) hecard (mem_filter.mp heSide).2) het).elim

private lemma familyPairs_inter_side_subset_covered_second
    {α : Type*} [Fintype α] [DecidableEq α]
    (R : SimpleGraph α) (S T : Finset α) (hST : Disjoint S T)
    (P₁ P₂ : Finset (Finset α))
    (hP₁ : IsInternalCrossPacking R (S : Set α) P₁)
    (hP₂ : IsInternalCrossPacking R (T : Set α) P₂)
    (hP₁side : ∀ t ∈ P₁,
      (t.filter fun x ↦ x ∈ S).card = 2) :
    familyPairFinset (P₁ ∪ P₂) ∩ sideEdgeFinset R T ⊆
      coveredInternalEdges R (T : Set α) P₂ := by
  rw [union_comm P₁ P₂]
  exact familyPairs_inter_side_subset_covered_first R T S hST.symm
    P₂ P₁ hP₂ hP₁ hP₁side

/-- The complete fractional red construction in Claim 4.5.  Delete every
pair used by the two integral triangle families, decompose the two induced
residual graphs by the almost-complete theorem, extend the decompositions,
and finally restore the integral triangles.  The displayed lower bound is
the exact `-p + 3p = 2p` accounting from the paper. -/
private lemma exists_claim45_residual_and_integral_packing
    (hAC : AlmostCompleteFractionalDecomposition)
    {α : Type*} [Fintype α] [DecidableEq α]
    (R : SimpleGraph α) (S T : Finset α) (hST : Disjoint S T)
    (k₁ k₂ : ℕ) (P₁ P₂ : Finset (Finset α))
    (hP₁ : IsInternalCrossPacking R (S : Set α) P₁)
    (hP₂ : IsInternalCrossPacking R (T : Set α) P₂)
    (hP₁side : ∀ t ∈ P₁,
      (t.filter fun x ↦ x ∈ S).card = 2)
    (hP₂side : ∀ t ∈ P₂,
      (t.filter fun x ↦ x ∈ T).card = 2)
    (hUnion : EdgeDisjoint (P₁ ∪ P₂))
    (hsevenS : 7 ≤ S.card) (hsevenT : 7 ≤ T.card)
    (hmissingS : missingEdgeCount (R.induce (S : Set α)) ≤ k₁)
    (hmissingT : missingEdgeCount (R.induce (T : Set α)) ≤ k₂)
    (hcapS : P₁.card + k₁ ≤ S.card - 4)
    (hcapT : P₂.card + k₂ ≤ T.card - 4) :
    ∃ w : Finset α → ℝ, IsFractionalPacking R w ∧
      (((S.card.choose 2 + T.card.choose 2 : ℕ) : ℝ) - k₁ - k₂ +
          2 * (P₁.card + P₂.card) ≤ fractionalCoveredSize R w) := by
  let P := P₁ ∪ P₂
  let D := familyPairFinset P
  let K := R.deleteEdges (D : Set (Sym2 α))
  letI : DecidableRel K.Adj := Classical.decRel _
  have htri : ∀ t ∈ P, R.IsNClique 3 t := by
    intro t ht
    rcases mem_union.mp ht with ht | ht
    · exact (mem_internalCrossTriangles.mp (hP₁.1 ht)).1
    · exact (mem_internalCrossTriangles.mp (hP₂.1 ht)).1
  have hPdisj : Disjoint P₁ P₂ :=
    triangleFamilies_disjoint_of_two_disjoint_sides hST
      (fun t ht ↦ (htri t ht).card_eq) hP₁side hP₂side
  have hPcard : P.card = P₁.card + P₂.card := by
    exact card_union_of_disjoint hPdisj
  have hlocalS : (D ∩ sideEdgeFinset R S).card ≤ P₁.card := by
    apply (card_le_card ?_).trans_eq (card_coveredInternalEdges_eq_card hP₁)
    exact familyPairs_inter_side_subset_covered_first R S T hST
      P₁ P₂ hP₁ hP₂ hP₂side
  have hlocalT : (D ∩ sideEdgeFinset R T).card ≤ P₂.card := by
    apply (card_le_card ?_).trans_eq (card_coveredInternalEdges_eq_card hP₂)
    exact familyPairs_inter_side_subset_covered_second R S T hST
      P₁ P₂ hP₁ hP₂ hP₁side
  have hmissKS : missingEdgeCount (K.induce (S : Set α)) ≤
      k₁ + P₁.card := by
    have h := missingEdgeCount_induce_deleteEdges_le_inter_side R S D
    dsimp only [K]
    omega
  have hmissKT : missingEdgeCount (K.induce (T : Set α)) ≤
      k₂ + P₂.card := by
    have h := missingEdgeCount_induce_deleteEdges_le_inter_side R T D
    dsimp only [K]
    omega
  have hallowedS : missingEdgeCount (K.induce (S : Set α)) ≤
      Fintype.card S - 4 := by
    rw [Fintype.card_coe]
    omega
  have hallowedT : missingEdgeCount (K.induce (T : Set α)) ≤
      Fintype.card T - 4 := by
    rw [Fintype.card_coe]
    omega
  obtain ⟨wS, hwS⟩ := almostCompleteFractionalDecomposition_fintype_forExtension
    hAC (K.induce (S : Set α)) (by simpa using hsevenS) hallowedS
  obtain ⟨wT, hwT⟩ := almostCompleteFractionalDecomposition_fintype_forExtension
    hAC (K.induce (T : Set α)) (by simpa using hsevenT) hallowedT
  obtain ⟨u, hu, husize⟩ := residualPacking_of_sideDecompositions
    K S T hST wS wT hwS hwT
  have hKR : K ≤ R := by
    intro a b hab
    exact (SimpleGraph.deleteEdges_adj.mp hab).1
  let u₀ : Finset α → ℝ := zeroExtendTriangleWeight K u
  have hu₀ : IsFractionalPacking R u₀ := by
    exact hu.zeroExtendToSupergraph hKR
  have hu₀size : fractionalCoveredSize R u₀ =
      Nat.card (K.induce (S : Set α)).edgeSet +
        Nat.card (K.induce (T : Set α)).edgeSet := by
    dsimp only [u₀]
    unfold fractionalCoveredSize
    rw [fractionalSize_zeroExtend_mono hKR]
    simpa only [fractionalCoveredSize] using husize
  have hzero : ∀ e ∈ R.edgeFinset, e ∈ familyPairFinset P →
      fractionalEdgeLoad R u₀ e = 0 := by
    intro e heR heD
    dsimp only [u₀]
    rw [fractionalEdgeLoad_zeroExtend hKR]
    have heND : ¬ e.IsDiag := R.not_isDiag_of_mem_edgeFinset heR
    apply fractionalEdgeLoad_eq_zero_of_not_edge K u heND
    intro heK
    induction e using Sym2.inductionOn with
    | hf a b =>
        have hab := SimpleGraph.mem_edgeFinset.mp heK
        exact (SimpleGraph.deleteEdges_adj.mp hab).2 (by simpa [D] using heD)
  let w := addTriangleWeight (integralPackingWeight P) u₀
  have hw : IsFractionalPacking R w := by
    exact isFractionalPacking_add_integral_of_zero_load R P hUnion u₀ hu₀ hzero
  have hwsize : fractionalCoveredSize R w =
      3 * (P.card : ℝ) +
        (Nat.card (K.induce (S : Set α)).edgeSet +
          Nat.card (K.induce (T : Set α)).edgeSet : ℕ) := by
    dsimp only [w]
    rw [fractionalCoveredSize_add_integral R P htri u₀, hu₀size]
    norm_num
  have hedgeS : S.card.choose 2 ≤
      Nat.card (K.induce (S : Set α)).edgeSet + k₁ + P₁.card := by
    have hsum := natCard_edgeSet_add_missing_forExtension
      (K.induce (S : Set α))
    have hcard : Fintype.card (S : Set α) = S.card := by
      symm
      simpa using Set.toFinset_card (S : Set α)
    rw [hcard] at hsum
    omega
  have hedgeT : T.card.choose 2 ≤
      Nat.card (K.induce (T : Set α)).edgeSet + k₂ + P₂.card := by
    have hsum := natCard_edgeSet_add_missing_forExtension
      (K.induce (T : Set α))
    have hcard : Fintype.card (T : Set α) = T.card := by
      symm
      simpa using Set.toFinset_card (T : Set α)
    rw [hcard] at hsum
    omega
  refine ⟨w, hw, ?_⟩
  rw [hwsize, hPcard]
  push_cast
  have hedgeSR : (S.card.choose 2 : ℝ) ≤
      Nat.card (K.induce (S : Set α)).edgeSet + k₁ + P₁.card := by
    exact_mod_cast hedgeS
  have hedgeTR : (T.card.choose 2 : ℝ) ≤
      Nat.card (K.induce (T : Set α)).edgeSet + k₂ + P₂.card := by
    exact_mod_cast hedgeT
  calc
    (S.card.choose 2 : ℝ) + T.card.choose 2 - k₁ - k₂ +
          2 * (P₁.card + P₂.card) ≤
        (Nat.card (K.induce (S : Set α)).edgeSet : ℝ) +
          Nat.card (K.induce (T : Set α)).edgeSet +
            3 * (P₁.card + P₂.card) := by
      linarith [hedgeSR, hedgeTR]
    _ = 3 * ((P₁.card : ℝ) + P₂.card) +
        ((Nat.card (K.induce (S : Set α)).edgeSet : ℝ) +
          Nat.card (K.induce (T : Set α)).edgeSet) := by ring

/-- Claim 4.5: a maximum blue matching between the two sets of blue
neighbours of the new vertex saturates the smaller set.  The contrary
branch is discharged by the red construction above and the exact numerical
contradiction `claim45_numerical_contradiction`. -/
private lemma maximum_bluePairMatching_saturates
    (hAC : AlmostCompleteFractionalDecomposition)
    (hcross : AlmostBipartiteIntegralCrossPackingAvoiding)
    {n : ℕ} (hn : 22 ≤ n)
    (H : SimpleGraph (Fin n)) (G : SimpleGraph (Fin (n + 1)))
    (hHG : IsInitialVertexExtension H G)
    (hH : FractionalCoveredSizeAtMost H
      ((n : ℝ) * ((n : ℝ) - 1) / 4))
    (hG : FractionalCoveredSizeAtMost G
      ((n : ℝ) * ((n : ℝ) + 1) / 4))
    (s : Set (Fin n))
    (hsum : s.ncard + sᶜ.ncard = n)
    (hparts : sᶜ.ncard ≤ s.ncard)
    (hk : (internalEdgeFinset H s).card ≤ n / 8)
    (hsize₂ : (internalEdgeFinset H s).card + 4 ≤ sᶜ.ncard)
    (hseven₁ : 7 ≤ s.ncard) (hseven₂ : 7 ≤ sᶜ.ncard)
    (M : Finset (Fin n × Fin n))
    (hM : IsBluePairMatching H (newBlueNeighbors G s)
      (newBlueNeighbors G sᶜ) M)
    (hmax : ∀ N : Finset (Fin n × Fin n),
      IsBluePairMatching H (newBlueNeighbors G s)
        (newBlueNeighbors G sᶜ) N → N.card ≤ M.card) :
    M.card = min (newBlueNeighbors G s).card
      (newBlueNeighbors G sᶜ).card := by
  let B₁ := newBlueNeighbors G s
  let B₂ := newBlueNeighbors G sᶜ
  have hMle₁ : M.card ≤ B₁.card := by
    calc
      M.card = (blueMatchingLeftVertices M).card := hM.card_leftVertices.symm
      _ ≤ B₁.card := card_le_card hM.leftVertices_subset
  have hMle₂ : M.card ≤ B₂.card := by
    calc
      M.card = (blueMatchingRightVertices M).card := hM.card_rightVertices.symm
      _ ≤ B₂.card := card_le_card hM.rightVertices_subset
  have hMle : M.card ≤ min B₁.card B₂.card := by omega
  by_contra hnot
  have hnot' : ¬ M.card = min B₁.card B₂.card := by
    simpa [B₁, B₂] using hnot
  have hltmin : M.card < min B₁.card B₂.card := by omega
  have hlt₁ : M.card < B₁.card := by
    omega
  have hlt₂ : M.card < B₂.card := by
    omega
  obtain ⟨P₁, P₂, hP₁, hP₂, hP₁side, hP₂side, hUnion,
      hlower₁, hlower₂, hcap₁, hcap₂⟩ :=
    exists_claim45_truncated_redSidePackings H G hHG s hn hsum hparts
      hk hsize₂ M hM hmax (by simpa [B₁] using hlt₁)
        (by simpa [B₂] using hlt₂)
  let S := (liftOldSet s).toFinset
  let T := (liftOldSet sᶜ).toFinset
  let k := (internalEdgeFinset H s).card
  let k₁ := (sideEdgeFinset H s.toFinset).card
  let k₂ := (sideEdgeFinset H sᶜ.toFinset).card
  have hST : Disjoint S T := by
    rw [Finset.disjoint_left]
    intro v hvS hvT
    exact Set.disjoint_left.mp (liftOldSet_disjoint_compl s)
      (by simpa [S] using hvS) (by simpa [T] using hvT)
  have hScard : S.card = s.ncard := by
    dsimp only [S]
    exact card_liftOldSet_toFinset s
  have hTcard : T.card = sᶜ.ncard := by
    dsimp only [T]
    exact card_liftOldSet_toFinset sᶜ
  have hk₁₂ : k₁ + k₂ = k := by
    dsimp only [k, k₁, k₂]
    rw [internalEdgeFinset_eq_union_sides H s,
      card_union_of_disjoint (sideEdgeFinset_disjoint_compl H s)]
  have hmissingS : missingEdgeCount (Gᶜ.induce (S : Set (Fin (n + 1)))) ≤ k₁ := by
    rw [missingEdgeCount_compl_induce_forExtension G S,
      ← card_sideEdgeFinset G S]
    simpa [S, k₁] using (card_sideEdgeFinset_liftOldSet H G hHG s).le
  have hmissingT : missingEdgeCount (Gᶜ.induce (T : Set (Fin (n + 1)))) ≤ k₂ := by
    rw [missingEdgeCount_compl_induce_forExtension G T,
      ← card_sideEdgeFinset G T]
    simpa [T, k₂] using (card_sideEdgeFinset_liftOldSet H G hHG sᶜ).le
  obtain ⟨wRed, hwRed, hRedLower⟩ :=
    exists_claim45_residual_and_integral_packing hAC Gᶜ S T hST
      k₁ k₂ P₁ P₂ (by simpa [S] using hP₁) (by simpa [T] using hP₂)
      (by simpa [S] using hP₁side) (by simpa [T] using hP₂side)
      hUnion (by simpa [hScard] using hseven₁)
      (by simpa [hTcard] using hseven₂) hmissingS hmissingT
      (by simpa [hScard, k₁, add_comm] using hcap₁)
      (by simpa [hTcard, k₂, add_comm] using hcap₂)
  let E := bluePairMatchingEdges M
  have hB₁side : newBlueNeighbors G s ⊆ s.toFinset := by
    intro v hv
    simpa using ((mem_newBlueNeighbors G s v).mp hv).1
  have hB₂side : newBlueNeighbors G sᶜ ⊆ sᶜ.toFinset := by
    intro v hv
    simpa using ((mem_newBlueNeighbors G sᶜ v).mp hv).1
  have hEMatch : IsCrossMatching s E :=
    hM.isCrossMatching_bluePairMatchingEdges hB₁side hB₂side
  obtain ⟨PBlue, hPBlue⟩ := hcross n hn H s E hEMatch hk hH
  have hInternalOld :
      internalEdgeFinset (H.deleteEdges (E : Set (Sym2 (Fin n)))) s =
        internalEdgeFinset H s :=
    internalEdgeFinset_deleteEdges_of_cross H s E hEMatch.1
  have hPBlueCard : PBlue.card = k := by
    dsimp only [k]
    rw [hPBlue.2.2.2.2, hInternalOld]
  have hBlueCert := extensionBlueTriangles_certificate hHG s
    (newBlueNeighbors G s) (newBlueNeighbors G sᶜ) M hM
    (fun _ h ↦ h) (fun _ h ↦ h) PBlue (by simpa [E] using hPBlue)
  let Q := extensionBlueTriangles PBlue M
  let wBlue : Finset (Fin (n + 1)) → ℝ := integralPackingWeight Q
  have hwBlue : IsFractionalPacking G wBlue := by
    exact isFractionalPacking_integralPackingWeight hBlueCert.2.1
  have hQcard : Q.card = k + M.card := by
    dsimp only [Q]
    rw [hBlueCert.2.2, hPBlueCard]
  have hBlueSize : fractionalCoveredSize G wBlue =
      3 * ((k + M.card : ℕ) : ℝ) := by
    dsimp only [wBlue]
    rw [fractionalCoveredSize,
      fractionalSize_integralPackingWeight hBlueCert.1, hQcard]
  have hRedLower' :
      (((s.ncard.choose 2 + sᶜ.ncard.choose 2 : ℕ) : ℝ) - k₁ - k₂ +
          2 * (P₁.card + P₂.card) ≤ fractionalCoveredSize Gᶜ wRed) := by
    simpa [hScard, hTcard] using hRedLower
  have hPack := hG wBlue wRed hwBlue hwRed
  have hupper :
      ((s.ncard.choose 2 + sᶜ.ncard.choose 2 : ℕ) : ℝ) + 2 * k +
          3 * M.card + 2 * (P₁.card + P₂.card) ≤
        (n : ℝ) * ((n : ℝ) + 1) / 4 := by
    rw [twoColorCoveredSize, hBlueSize] at hPack
    push_cast at hPack hRedLower' ⊢
    have hkR : (k₁ : ℝ) + k₂ = k := by exact_mod_cast hk₁₂
    nlinarith
  exact claim45_numerical_contradiction n s.ncard sᶜ.ncard k k₁ k₂
    M.card P₁.card P₂.card hn hsum hk₁₂ hlower₁ hlower₂ hupper

/-- Claims 4.5 and 4.6, with the maximum matching chosen internally, extend
a fixed almost-bipartite partition of the old graph to the new graph. -/
private lemma closeToBipartite_extension_of_partition
    (hAC : AlmostCompleteFractionalDecomposition)
    (hcross : AlmostBipartiteIntegralCrossPackingAvoiding)
    {n : ℕ} (hn : 22 ≤ n)
    (H : SimpleGraph (Fin n)) (G : SimpleGraph (Fin (n + 1)))
    (hHG : IsInitialVertexExtension H G)
    (hH : FractionalCoveredSizeAtMost H
      ((n : ℝ) * ((n : ℝ) - 1) / 4))
    (hG : FractionalCoveredSizeAtMost G
      ((n : ℝ) * ((n : ℝ) + 1) / 4))
    (s : Set (Fin n))
    (hparts : sᶜ.ncard ≤ s.ncard)
    (hk : (internalEdgeFinset H s).card ≤ n / 8)
    (hsize₁ : (internalEdgeFinset H s).card + 4 ≤ s.ncard)
    (hsize₂ : (internalEdgeFinset H s).card + 4 ≤ sᶜ.ncard)
    (hseven₁ : 7 ≤ s.ncard) (hseven₂ : 7 ≤ sᶜ.ncard) :
    CloseToBipartite G ((n + 1) / 8) := by
  obtain ⟨M, hM, hmax⟩ := exists_maximum_bluePairMatching H
    (newBlueNeighbors G s) (newBlueNeighbors G sᶜ)
  have hsum : s.ncard + sᶜ.ncard = n := by
    rw [Set.ncard_add_ncard_compl]
    simp
  have hsat := maximum_bluePairMatching_saturates hAC hcross hn H G hHG
    hH hG s hsum hparts hk hsize₂ hseven₁ hseven₂ M hM hmax
  have hbound := claim46_final_neighbor_bound_of_saturating_matching
    hAC hcross hn H G hHG hH hG s hk hsize₁ hsize₂ hseven₁ hseven₂
      M hM hsat
  exact closeToBipartite_of_partitionClose
    (exists_extension_partition_of_neighbor_bound H G hHG s hbound)

/-- Lemma 2.7 of Gruslys--Letzter, fully discharged from the
almost-complete decomposition theorem and the matching-avoidance form of
Proposition 4.2. -/
theorem almostBipartiteStabilityExtension_of_components
    (hAC : AlmostCompleteFractionalDecomposition)
    (hcross : AlmostBipartiteIntegralCrossPackingAvoiding) :
    AlmostBipartiteStabilityExtension := by
  intro n hn H G hHG hH hG hclose
  have hH' : FractionalCoveredSizeAtMost H
      ((n : ℝ) * ((n : ℝ) - 1) / 4) := by
    simpa [stabilityThreshold] using hH
  have hG' : FractionalCoveredSizeAtMost G
      ((n : ℝ) * ((n : ℝ) + 1) / 4) := by
    simpa [stabilityThreshold, mul_comm] using hG
  rcases hclose with hclose | hclose
  · obtain ⟨s, hk⟩ := hclose.partition_witness
    obtain ⟨hsize₁, hsize₂, hseven₁, hseven₂⟩ :=
      almostBipartitePartSizeBound hAC n (by omega) H s hk hH'
    by_cases hparts : sᶜ.ncard ≤ s.ncard
    · exact Or.inl (closeToBipartite_extension_of_partition hAC hcross hn
        H G hHG hH' hG' s hparts hk hsize₁ hsize₂ hseven₁ hseven₂)
    · have hparts' : (sᶜ)ᶜ.ncard ≤ sᶜ.ncard := by
        simpa using Nat.le_of_not_ge hparts
      have hk' : (internalEdgeFinset H sᶜ).card ≤ n / 8 := by
        simpa using hk
      exact Or.inl (closeToBipartite_extension_of_partition hAC hcross hn
        H G hHG hH' hG' sᶜ hparts' hk'
          (by simpa using hsize₂) (by simpa using hsize₁)
          (by simpa using hseven₂) (by simpa using hseven₁))
  · have hHGc : IsInitialVertexExtension Hᶜ Gᶜ :=
      initialVertexExtension_compl hHG
    have hHc : FractionalCoveredSizeAtMost Hᶜ
        ((n : ℝ) * ((n : ℝ) - 1) / 4) := hH'.compl
    have hGc : FractionalCoveredSizeAtMost Gᶜ
        ((n : ℝ) * ((n : ℝ) + 1) / 4) := hG'.compl
    obtain ⟨s, hk⟩ := hclose.partition_witness
    obtain ⟨hsize₁, hsize₂, hseven₁, hseven₂⟩ :=
      almostBipartitePartSizeBound hAC n (by omega) Hᶜ s hk hHc
    by_cases hparts : sᶜ.ncard ≤ s.ncard
    · exact Or.inr (closeToBipartite_extension_of_partition hAC hcross hn
        Hᶜ Gᶜ hHGc hHc hGc s hparts hk hsize₁ hsize₂ hseven₁ hseven₂)
    · have hparts' : (sᶜ)ᶜ.ncard ≤ sᶜ.ncard := by
        simpa using Nat.le_of_not_ge hparts
      have hk' : (internalEdgeFinset Hᶜ sᶜ).card ≤ n / 8 := by
        simpa using hk
      exact Or.inr (closeToBipartite_extension_of_partition hAC hcross hn
        Hᶜ Gᶜ hHGc hHc hGc sᶜ hparts' hk'
          (by simpa using hsize₂) (by simpa using hsize₁)
          (by simpa using hseven₂) (by simpa using hseven₁))

end

end Erdos76
