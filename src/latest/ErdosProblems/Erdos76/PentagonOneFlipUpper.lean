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
import ErdosProblems.Erdos76.PentagonBasePacking

/-!
# The dual upper bound for a one-edge flip

This module proves the upper-bound half of Proposition 7.4(b).  If `H` is
a pentagon blow-up and `G` differs from `H` in one edge, every
monochromatic triangle of `G` either contains an edge internal to a blob or
contains the flipped edge.  The corresponding fractional edge covers have
total two-colour weight equal to the number of internal pairs plus the flip
distance.
-/

open Finset
open scoped BigOperators

namespace Erdos76

noncomputable section

attribute [local instance] Classical.propDecidable

open LPDuality

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The edge-cover weight for a graph `G` compared with a reference graph
`H`: internal blob edges and edges present only in `G` both receive one. -/
def pentagonFlipEdgeCover (G H : SimpleGraph α) (blob : α → Fin 5)
    (e : Sym2 α) : ℝ :=
  pentagonInternalEdgeCover blob e +
    if e ∈ G.edgeSet ∧ e ∉ H.edgeSet then 1 else 0

lemma pentagonFlipEdgeCover_nonneg
    (G H : SimpleGraph α) (blob : α → Fin 5) (e : Sym2 α) :
    0 ≤ pentagonFlipEdgeCover G H blob e := by
  classical
  unfold pentagonFlipEdgeCover
  have hInternal := pentagonInternalEdgeCover_nonneg blob e
  split_ifs <;> linarith

lemma one_le_pentagonInternalEdgeCover_of_subset
    {blob : α → Fin 5} {e : Sym2 α} {i : Fin 5}
    (hei : e.toFinset ⊆ pentagonBlobFinset blob i) :
    1 ≤ pentagonInternalEdgeCover blob e := by
  classical
  unfold pentagonInternalEdgeCover
  let f : Fin 5 → ℝ := fun j ↦
    if e.toFinset ⊆ pentagonBlobFinset blob j then 1 else 0
  change 1 ≤ ∑ j : Fin 5, f j
  have hfi : f i = 1 := by simp [f, hei]
  rw [← hfi]
  apply single_le_sum
  · intro j _hj
    simp only [f]
    split_ifs <;> norm_num
  · exact mem_univ i

lemma one_le_pentagonFlipEdgeCover_of_internal
    {G H : SimpleGraph α} {blob : α → Fin 5} {e : Sym2 α}
    {i : Fin 5} (hei : e.toFinset ⊆ pentagonBlobFinset blob i) :
    1 ≤ pentagonFlipEdgeCover G H blob e := by
  unfold pentagonFlipEdgeCover
  have h := one_le_pentagonInternalEdgeCover_of_subset hei
  split_ifs <;> linarith

lemma one_le_pentagonFlipEdgeCover_of_difference
    {G H : SimpleGraph α} {blob : α → Fin 5} {e : Sym2 α}
    (heG : e ∈ G.edgeSet) (heH : e ∉ H.edgeSet) :
    1 ≤ pentagonFlipEdgeCover G H blob e := by
  unfold pentagonFlipEdgeCover
  rw [if_pos ⟨heG, heH⟩]
  exact le_add_of_nonneg_left (pentagonInternalEdgeCover_nonneg blob e)

/-- A graph triangle is either already a triangle of the reference graph,
or contains an edge present in the graph and absent from the reference. -/
lemma triangle_internal_or_difference
    {G H : SimpleGraph α} {blob : α → Fin 5}
    (hReference : ∀ {t : Finset α}, H.IsNClique 3 t →
      ∃ e : Sym2 α, e ∈ H.edgeSet ∧ e ∈ t.sym2 ∧
        ∃ i : Fin 5, e.toFinset ⊆ pentagonBlobFinset blob i)
    {t : Finset α} (ht : G.IsNClique 3 t) :
    (∃ e : Sym2 α, e ∈ G.edgeSet ∧ e ∈ t.sym2 ∧
        ∃ i : Fin 5, e.toFinset ⊆ pentagonBlobFinset blob i) ∨
      ∃ e : Sym2 α, e ∈ G.edgeSet ∧ e ∉ H.edgeSet ∧ e ∈ t.sym2 := by
  classical
  by_cases htH : H.IsNClique 3 t
  · left
    obtain ⟨e, heH, het, i, hei⟩ := hReference htH
    induction e using Sym2.inductionOn with
    | hf u v =>
        have huvMem := Finset.mk_mem_sym2_iff.mp het
        have huv : u ≠ v := by
          simpa [Sym2.mk_isDiag_iff] using
            (H.not_isDiag_of_mem_edgeSet heH)
        have huvG : G.Adj u v := ht.isClique huvMem.1 huvMem.2 huv
        refine ⟨s(u, v), ?_, het, i, hei⟩
        simpa [SimpleGraph.mem_edgeSet] using huvG
  · right
    have hnotClique : ¬H.IsClique (t : Set α) := by
      intro hclique
      exact htH ⟨hclique, ht.card_eq⟩
    obtain ⟨u, v, huv, huvNotH⟩ := H.not_isClique_iff.mp hnotClique
    let e : Sym2 α := s((u : α), (v : α))
    have huvG : G.Adj (u : α) (v : α) :=
      ht.isClique u.property v.property (Subtype.val_injective.ne huv)
    refine ⟨e, ?_, ?_, ?_⟩
    · simpa [e, SimpleGraph.mem_edgeSet] using huvG
    · intro heH
      apply huvNotH
      simpa [e, SimpleGraph.mem_edgeSet] using heH
    · exact Finset.mk_mem_sym2_iff.mpr ⟨u.property, v.property⟩

/-- The flip cover is feasible whenever every reference triangle contains
an internal blob edge. -/
lemma isFractionalEdgeCover_pentagonFlip
    {G H : SimpleGraph α} {blob : α → Fin 5}
    (hReference : ∀ {t : Finset α}, H.IsNClique 3 t →
      ∃ e : Sym2 α, e ∈ H.edgeSet ∧ e ∈ t.sym2 ∧
        ∃ i : Fin 5, e.toFinset ⊆ pentagonBlobFinset blob i) :
    IsFractionalEdgeCover G (pentagonFlipEdgeCover G H blob) := by
  classical
  constructor
  · intro e _he
    exact pentagonFlipEdgeCover_nonneg G H blob e
  · intro t ht
    rcases triangle_internal_or_difference hReference
        (SimpleGraph.mem_cliqueFinset_iff.mp ht) with hInternal | hDifference
    · obtain ⟨e, heG, het, i, hei⟩ := hInternal
      calc
        1 ≤ pentagonFlipEdgeCover G H blob e :=
          one_le_pentagonFlipEdgeCover_of_internal hei
        _ ≤ ∑ f ∈ G.edgeFinset.filter (fun f ↦ f ∈ t.sym2),
            pentagonFlipEdgeCover G H blob f := by
          apply single_le_sum
          · intro f _hf
            exact pentagonFlipEdgeCover_nonneg G H blob f
          · exact mem_filter.mpr
              ⟨SimpleGraph.mem_edgeFinset.mpr heG, het⟩
    · obtain ⟨e, heG, heH, het⟩ := hDifference
      calc
        1 ≤ pentagonFlipEdgeCover G H blob e :=
          one_le_pentagonFlipEdgeCover_of_difference heG heH
        _ ≤ ∑ f ∈ G.edgeFinset.filter (fun f ↦ f ∈ t.sym2),
            pentagonFlipEdgeCover G H blob f := by
          apply single_le_sum
          · intro f _hf
            exact pentagonFlipEdgeCover_nonneg G H blob f
          · exact mem_filter.mpr
              ⟨SimpleGraph.mem_edgeFinset.mpr heG, het⟩

/-- The indicator part of the flip cover sums to the number of graph edges
missing from the reference. -/
lemma ncard_edgeSet_sdiff_eq_card_edgeFinset_sdiff
    (G H : SimpleGraph α) :
    (G.edgeSet \ H.edgeSet).ncard =
      (G.edgeFinset \ H.edgeFinset).card := by
  classical
  rw [← Set.ncard_coe_finset]
  congr 1
  ext e
  simp [SimpleGraph.mem_edgeFinset]

lemma sum_pentagonFlipIndicator
    (G H : SimpleGraph α) :
    (∑ e ∈ G.edgeFinset,
      if e ∈ G.edgeSet ∧ e ∉ H.edgeSet then (1 : ℝ) else 0) =
      ((G.edgeSet \ H.edgeSet).ncard : ℝ) := by
  classical
  calc
    (∑ e ∈ G.edgeFinset,
        if e ∈ G.edgeSet ∧ e ∉ H.edgeSet then (1 : ℝ) else 0) =
      ∑ _e ∈ G.edgeFinset.filter
          (fun e ↦ e ∈ G.edgeSet ∧ e ∉ H.edgeSet), (1 : ℝ) := by
        rw [sum_filter]
    _ = ((G.edgeFinset.filter
          (fun e ↦ e ∈ G.edgeSet ∧ e ∉ H.edgeSet)).card : ℝ) := by simp
    _ = ((G.edgeFinset \ H.edgeFinset).card : ℝ) := by
      congr 2
      ext e
      simp [SimpleGraph.mem_edgeFinset]
    _ = ((G.edgeSet \ H.edgeSet).ncard : ℝ) := by
      exact_mod_cast (ncard_edgeSet_sdiff_eq_card_edgeFinset_sdiff G H).symm

/-- Exact objective of the flip edge cover. -/
lemma sum_pentagonFlipEdgeCover
    (G H : SimpleGraph α) (blob : α → Fin 5) :
    (∑ e ∈ G.edgeFinset, pentagonFlipEdgeCover G H blob e) =
      (∑ i : Fin 5,
        ((blobPairFinset G (pentagonBlobFinset blob i)).card : ℝ)) +
      ((G.edgeSet \ H.edgeSet).ncard : ℝ) := by
  classical
  simp only [pentagonFlipEdgeCover, sum_add_distrib]
  rw [sum_pentagonInternalEdgeCover, sum_pentagonFlipIndicator]

/-- Weak duality with the flip cover. -/
theorem fractionalSize_oneFlip_le_internal_add_difference
    {G H : SimpleGraph α} {blob : α → Fin 5}
    (hReference : ∀ {t : Finset α}, H.IsNClique 3 t →
      ∃ e : Sym2 α, e ∈ H.edgeSet ∧ e ∈ t.sym2 ∧
        ∃ i : Fin 5, e.toFinset ⊆ pentagonBlobFinset blob i)
    {w : Finset α → ℝ} (hw : IsFractionalPacking G w) :
    fractionalSize G w ≤
      (∑ i : Fin 5,
        ((blobPairFinset G (pentagonBlobFinset blob i)).card : ℝ)) +
      ((G.edgeSet \ H.edgeSet).ncard : ℝ) := by
  rw [← sum_pentagonFlipEdgeCover G H blob]
  exact fractionalSize_le_edgeCover_sum G w
    (pentagonFlipEdgeCover G H blob) hw
    (isFractionalEdgeCover_pentagonFlip hReference)

/-- Complementation exchanges the two directed edge differences.  The set
form is independent of all finite-set decidability witnesses. -/
lemma ncard_compl_edgeSet_sdiff_compl
    (G H : SimpleGraph α) :
    (Gᶜ.edgeSet \ Hᶜ.edgeSet).ncard =
      (H.edgeSet \ G.edgeSet).ncard := by
  classical
  apply congrArg Set.ncard
  ext e
  simp only [Set.mem_diff]
  induction e using Sym2.inductionOn with
  | hf u v =>
      simp only [SimpleGraph.mem_edgeSet, SimpleGraph.compl_adj]
      constructor
      · rintro ⟨⟨huv, hnG⟩, hnHc⟩
        have hH : H.Adj u v := by
          by_contra hnH
          exact hnHc ⟨huv, hnH⟩
        exact ⟨hH, hnG⟩
      · rintro ⟨hH, hnG⟩
        exact ⟨⟨hH.ne, hnG⟩, fun hHc ↦ hHc.2 hH⟩

/-- Proposition 7.4(b), upper-bound half.  A graph one edge-flip away
from a pentagon blow-up has two-colour fractional covered size at most
three times the number of internal pairs plus one. -/
theorem twoColorCoveredSize_oneFlipFromPentagonBlowup_le
    {G H : SimpleGraph α} {blob : α → Fin 5}
    (hH : IsPentagonBlowup H blob)
    (hflip : edgeFlipDistance G H = 1)
    {wR wB : Finset α → ℝ}
    (hwR : IsFractionalPacking G wR)
    (hwB : IsFractionalPacking Gᶜ wB) :
    fractionalCoveredSize G wR + fractionalCoveredSize Gᶜ wB ≤
      3 * ((∑ i : Fin 5,
        ((pentagonBlobFinset blob i).card.choose 2 : ℕ)) + 1) := by
  have hR := fractionalSize_oneFlip_le_internal_add_difference
    (fun ht ↦ pentagonBlowup_redTriangle_has_internal_edge hH ht) hwR
  have hB := fractionalSize_oneFlip_le_internal_add_difference
    (G := Gᶜ) (H := Hᶜ)
    (fun ht ↦ pentagonBlowup_blueTriangle_has_internal_edge hH ht) hwB
  have hB' : fractionalSize Gᶜ wB ≤
      (∑ i : Fin 5,
        ((blobPairFinset Gᶜ (pentagonBlobFinset blob i)).card : ℝ)) +
      ((H.edgeSet \ G.edgeSet).ncard : ℝ) := by
    calc
      fractionalSize Gᶜ wB ≤
          (∑ i : Fin 5,
            ((blobPairFinset Gᶜ (pentagonBlobFinset blob i)).card : ℝ)) +
          ((Gᶜ.edgeSet \ Hᶜ.edgeSet).ncard : ℝ) := hB
      _ = _ := by rw [ncard_compl_edgeSet_sdiff_compl]
  rw [fractionalCoveredSize, fractionalCoveredSize]
  push_cast
  calc
    3 * fractionalSize G wR + 3 * fractionalSize Gᶜ wB ≤
        3 * ((∑ i : Fin 5,
          ((blobPairFinset G (pentagonBlobFinset blob i)).card : ℝ)) +
          ((G.edgeSet \ H.edgeSet).ncard : ℝ)) +
        3 * ((∑ i : Fin 5,
          ((blobPairFinset Gᶜ (pentagonBlobFinset blob i)).card : ℝ)) +
          ((H.edgeSet \ G.edgeSet).ncard : ℝ)) := by
      gcongr
    _ = 3 * ((∑ i : Fin 5,
          (((blobPairFinset G (pentagonBlobFinset blob i)).card : ℝ) +
            ((blobPairFinset Gᶜ (pentagonBlobFinset blob i)).card : ℝ))) +
          (((G.edgeSet \ H.edgeSet).ncard : ℝ) +
            ((H.edgeSet \ G.edgeSet).ncard : ℝ))) := by
      rw [sum_add_distrib]
      ring
    _ = 3 * ((∑ i : Fin 5,
          ((pentagonBlobFinset blob i).card.choose 2 : ℝ)) + 1) := by
      have hflipR :
          (((G.edgeSet \ H.edgeSet).ncard : ℝ) +
            ((H.edgeSet \ G.edgeSet).ncard : ℝ)) = 1 := by
        have hflipNat :
            (G.edgeSet \ H.edgeSet).ncard +
              (H.edgeSet \ G.edgeSet).ncard = 1 := by
          rw [ncard_edgeSet_sdiff_eq_card_edgeFinset_sdiff,
            ncard_edgeSet_sdiff_eq_card_edgeFinset_sdiff]
          exact hflip
        exact_mod_cast hflipNat
      rw [hflipR]
      apply congrArg (fun z : ℝ ↦ 3 * (z + 1))
      apply sum_congr rfl
      intro i _hi
      exact_mod_cast card_blobPairFinset_add_compl G
        (pentagonBlobFinset blob i)

end

end Erdos76
