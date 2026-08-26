import Mathlib

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Decoupled regularity edge-retention bound

Mathlib's `SimpleGraph.regularityReduced_edges_card_aux` is hard-wired to
uniformity parameter `ε/8` and density threshold `ε/4`, tying the two together.
For the direct off--Turán proof we keep the
**density threshold `δ` decoupled from the uniformity parameter `ε₁`** (and from
the equipartition granularity parameter `εB`), so that a large density threshold
can be combined with a fine uniformity parameter without the edge loss forcing the
reduced graph to be empty.

This file supplies exactly that:

* `Erdos550.unreduced_edges_subset_decoupled` — the set of edges of `G` *not*
  kept in `G.regularityReduced P ε₁ δ` lies in the union of the non-`ε₁`-uniform
  pairs, the within-part (off-diagonal) pairs, and the density-`< δ` (sparse)
  pairs.  This is the generalisation of `SimpleGraph.unreduced_edges_subset`
  to independent `(ε₁, δ)`.

* `Erdos550.regularityReduced_edges_card_decoupled` — the reduced graph loses
  fewer than `(4·ε₁ + εB/2 + 4·δ)·N²` edges (`N = |α|`), for **any** choice of
  uniformity `ε₁ > 0`, density threshold `δ ≥ 0` and granularity `εB > 0` with
  `4/εB ≤ #P.parts`.  Specialising `ε₁ = εB = ε/8`, `δ = ε/4` recovers the
  Mathlib bound `2·ε·N²`.

Both follow by adapting the Mathlib argument and replacing the fixed constants
`ε/8`, `ε/4` by the free parameters.
-/

open SimpleGraph Finset Finpartition

namespace Erdos550

variable {α : Type*} [DecidableEq α] [Fintype α] {G : SimpleGraph α} [DecidableRel G.Adj]
  {P : Finpartition (univ : Finset α)}

/-- **Decoupled unreduced-edges containment.**  Every edge of `G` that is dropped
when forming `G.regularityReduced P ε₁ δ` lies in a non-`ε₁`-uniform pair, an
off-diagonal (within-part) pair, or a density-`< δ` sparse pair. -/
lemma unreduced_edges_subset_decoupled {ε₁ δ : ℝ} :
    (univ ×ˢ univ).filter
        (fun (xy : α × α) ↦ G.Adj xy.1 xy.2 ∧ ¬ (G.regularityReduced P ε₁ δ).Adj xy.1 xy.2) ⊆
      (P.nonUniforms G ε₁).biUnion (fun (UV : Finset α × Finset α) ↦ UV.1 ×ˢ UV.2)
        ∪ P.parts.biUnion offDiag
        ∪ (P.sparsePairs G δ).biUnion (fun (UV : Finset α × Finset α) ↦ G.interedges UV.1 UV.2) := by
  rintro ⟨x, y⟩
  simp only [mem_filter, regularityReduced_adj, not_and, not_exists,
    not_le, mem_biUnion, mem_union, mem_product, Prod.exists, mem_offDiag, and_imp,
    or_assoc, and_assoc, P.mk_mem_nonUniforms, Finpartition.mk_mem_sparsePairs, mem_interedges_iff]
  intro hx hy h h'
  replace h' := h' h
  obtain ⟨U, hU, hx⟩ := P.exists_mem (mem_univ x)
  obtain ⟨V, hV, hy⟩ := P.exists_mem (mem_univ y)
  obtain rfl | hUV := eq_or_ne U V
  · exact Or.inr (Or.inl ⟨U, hU, hx, hy, G.ne_of_adj h⟩)
  by_cases h₂ : G.IsUniform ε₁ U V
  · exact Or.inr <| Or.inr ⟨U, V, hU, hV, hUV, h' _ hU _ hV hx hy hUV h₂, hx, hy, h⟩
  · exact Or.inl ⟨U, V, hU, hV, hUV, h₂, hx, hy⟩

/-- **Decoupled regularity edge-retention bound.**  For an `ε₁`-uniform
equipartition `P` with `4/εB ≤ #P.parts`, the reduced graph
`G.regularityReduced P ε₁ δ` loses fewer than `(4·ε₁ + εB/2 + 4·δ)·N²` edges,
with the density threshold `δ` completely independent of the uniformity `ε₁`.

Specialising `ε₁ = εB = ε/8` and `δ = ε/4` recovers Mathlib's
`regularityReduced_edges_card_aux` bound `2·ε·N²`. -/
lemma regularityReduced_edges_card_decoupled [Nonempty α] {ε₁ δ εB : ℝ}
    (hε₁ : 0 < ε₁) (hδ : 0 ≤ δ) (hεB : 0 < εB)
    (hP : P.IsEquipartition) (hPε : P.IsUniform G ε₁) (hP' : 4 / εB ≤ (#P.parts : ℝ)) :
    2 * ((#G.edgeFinset : ℝ) - #(G.regularityReduced P ε₁ δ).edgeFinset)
      < (4 * ε₁ + εB / 2 + 4 * δ) * (Fintype.card α ^ 2 : ℕ) := by
  let A := (P.nonUniforms G ε₁).biUnion fun (x : Finset α × Finset α) ↦ x.1 ×ˢ x.2
  let B := P.parts.biUnion (offDiag : Finset α → _)
  let C := (P.sparsePairs G δ).biUnion fun (x : Finset α × Finset α) ↦ G.interedges x.1 x.2
  have hsub :
      (univ ×ˢ univ).filter
          (fun (xy : α × α) ↦ G.Adj xy.1 xy.2 ∧ ¬ (G.regularityReduced P ε₁ δ).Adj xy.1 xy.2)
        ⊆ A ∪ B ∪ C := unreduced_edges_subset_decoupled
  calc
    _ = (#((univ ×ˢ univ).filter fun (xy : α × α) ↦
          G.Adj xy.1 xy.2 ∧ ¬(G.regularityReduced P ε₁ δ).Adj xy.1 xy.2) : ℝ) := by
      rw [univ_product_univ, mul_sub, filter_and_not, cast_card_sdiff]
      · norm_cast
        rw [two_mul_card_edgeFinset, two_mul_card_edgeFinset]
      · gcongr with xy _
        exact fun hxy ↦ regularityReduced_le hxy
    _ ≤ #(A ∪ B ∪ C) := by exact_mod_cast Finset.card_le_card hsub
    _ ≤ #(A ∪ B) + #C := mod_cast (card_union_le _ _)
    _ ≤ #A + #B + #C := by gcongr; exact mod_cast card_union_le _ _
    _ < 4 * ε₁ * Fintype.card α ^ 2 + _ + _ := by
      gcongr; exact hP.sum_nonUniforms_lt univ_nonempty hε₁ hPε
    _ ≤ 4 * ε₁ * Fintype.card α ^ 2 + εB / 2 * Fintype.card α ^ 2 + 4 * δ * Fintype.card α ^ 2 := by
      gcongr
      · exact hP.card_biUnion_offDiag_le hεB hP'
      · exact hP.card_interedges_sparsePairs_le (G := G) (ε := δ) hδ
    _ = _ := by push_cast; ring

/-- **Tight decoupled regularity edge-retention bound.**  Like
`regularityReduced_edges_card_decoupled`, but using Mathlib's tighter sparse-pairs
count `card_interedges_sparsePairs_le'`, so the sparse-pair loss term is
`δ·(N + #P.parts)²` instead of `4·δ·N²`.  When the number of parts `k = #P.parts`
is small compared with `N` (which is the relevant regime — `k` depends only on the
regularity parameters, not on `N`), `(N + k)² ≈ N²`, so the density-threshold loss
is essentially `δ·N²`.  This factor-4 improvement is what turns the reduced-graph
capacity from unusable (`≈ δN²/4` of usable edges → total capacity `< n`) into
usable (total capacity up to `≈ δN`, which can exceed `n`). -/
lemma regularityReduced_edges_card_decoupled' [Nonempty α] {ε₁ δ εB : ℝ}
    (hε₁ : 0 < ε₁) (hδ : 0 ≤ δ) (hεB : 0 < εB)
    (hP : P.IsEquipartition) (hPε : P.IsUniform G ε₁) (hP' : 4 / εB ≤ (#P.parts : ℝ)) :
    2 * ((#G.edgeFinset : ℝ) - #(G.regularityReduced P ε₁ δ).edgeFinset)
      < 4 * ε₁ * (Fintype.card α : ℝ) ^ 2 + εB / 2 * (Fintype.card α : ℝ) ^ 2
          + δ * ((Fintype.card α : ℝ) + (#P.parts : ℝ)) ^ 2 := by
  let A := (P.nonUniforms G ε₁).biUnion fun (x : Finset α × Finset α) ↦ x.1 ×ˢ x.2
  let B := P.parts.biUnion (offDiag : Finset α → _)
  let C := (P.sparsePairs G δ).biUnion fun (x : Finset α × Finset α) ↦ G.interedges x.1 x.2
  have hsub :
      (univ ×ˢ univ).filter
          (fun (xy : α × α) ↦ G.Adj xy.1 xy.2 ∧ ¬ (G.regularityReduced P ε₁ δ).Adj xy.1 xy.2)
        ⊆ A ∪ B ∪ C := unreduced_edges_subset_decoupled
  calc
    _ = (#((univ ×ˢ univ).filter fun (xy : α × α) ↦
          G.Adj xy.1 xy.2 ∧ ¬(G.regularityReduced P ε₁ δ).Adj xy.1 xy.2) : ℝ) := by
      rw [univ_product_univ, mul_sub, filter_and_not, cast_card_sdiff]
      · norm_cast
        rw [two_mul_card_edgeFinset, two_mul_card_edgeFinset]
      · gcongr with xy _
        exact fun hxy ↦ regularityReduced_le hxy
    _ ≤ #(A ∪ B ∪ C) := by exact_mod_cast Finset.card_le_card hsub
    _ ≤ #(A ∪ B) + #C := mod_cast (card_union_le _ _)
    _ ≤ #A + #B + #C := by gcongr; exact mod_cast card_union_le _ _
    _ < 4 * ε₁ * Fintype.card α ^ 2 + _ + _ := by
      gcongr; exact hP.sum_nonUniforms_lt univ_nonempty hε₁ hPε
    _ ≤ 4 * ε₁ * Fintype.card α ^ 2 + εB / 2 * Fintype.card α ^ 2
          + δ * ((Fintype.card α : ℝ) + (#P.parts : ℝ)) ^ 2 := by
      gcongr
      · exact_mod_cast hP.card_biUnion_offDiag_le hεB hP'
      · have := hP.card_interedges_sparsePairs_le' (G := G) (ε := δ) hδ
        simpa using! this
    _ = _ := by ring

/-- **Decoupled cluster / reduced-graph construction.**  Companion of
`Erdos550.exists_regular_clusters`, but with the density threshold `d` and the
uniformity parameter `ε` chosen *independently* (plus a granularity parameter
`εB` controlling the off-diagonal loss).  For every `ε > 0`, `d ≥ 0`, `εB > 0`
and any finite nonempty graph `G` with at least `⌈4/εB⌉` vertices there is a
cluster family `C : ι → Finset W` (the parts of a Szemerédi `ε`-regular
equipartition) and a reduced graph `R` on `ι` together with the reduced subgraph
`G' ≤ G` such that:

* the clusters are nonempty and pairwise disjoint;
* every `R`-edge `(i,j)` is an `ε`-uniform pair `(C i, C j)` of density `≥ d`;
* every edge of `G'` runs between two `R`-adjacent clusters; and
* `G'` retains all but `≤ (2·ε + εB/4 + 2·d)·N²` of the edges of `G`.

Decoupling `d` from `ε` is what allows a large density threshold to coexist with
a fine uniformity parameter (impossible with Mathlib's fixed `ε/8`, `ε/4`). -/
lemma exists_regular_clusters_decoupled {W : Type} [Fintype W] [DecidableEq W] [Nonempty W]
    (G : SimpleGraph W) [DecidableRel G.Adj] (ε d εB : ℝ)
    (hε : 0 < ε) (hd : 0 ≤ d) (hεB : 0 < εB)
    (hcard : ⌈4/εB⌉₊ ≤ Fintype.card W) :
    ∃ (ι : Type) (_ : DecidableEq ι) (C : ι → Finset W) (R : SimpleGraph ι)
      (G' : SimpleGraph W) (_ : DecidableRel G'.Adj),
      (∀ i, (C i).Nonempty) ∧
      (∀ i j, i ≠ j → Disjoint (C i) (C j)) ∧
      (∀ i j, R.Adj i j → G.IsUniform ε (C i) (C j)) ∧
      (∀ i j, R.Adj i j → (d : ℝ) ≤ (G.edgeDensity (C i) (C j) : ℝ)) ∧
      (∀ x y, G'.Adj x y → G.Adj x y) ∧
      (∀ x y, G'.Adj x y → ∃ i j, R.Adj i j ∧ x ∈ C i ∧ y ∈ C j) ∧
      ((G.edgeFinset.card : ℝ) - (2 * ε + εB / 4 + 2 * d) * (Fintype.card W : ℝ) ^ 2
        ≤ (G'.edgeFinset.card : ℝ)) := by
  obtain ⟨ P, hP₁, hP₂, hP₃, hP₄ ⟩ :=
    szemeredi_regularity G hε (le_trans hcard (le_refl _));
  have hparts : 4 / εB ≤ (P.parts.card : ℝ) :=
    le_trans (Nat.le_ceil _) (mod_cast hP₂)
  refine' ⟨ P.parts, _, fun i => i, _, _, _, _ ⟩ <;> norm_num;
  all_goals try infer_instance;
  refine' { Adj := fun i j => i ≠ j ∧ G.IsUniform ε i.val j.val ∧ (d : ℝ) ≤ (G.edgeDensity i.val j.val : ℝ), symm := _, loopless := _ };
  any_goals exact G.regularityReduced P ε d;
  all_goals try infer_instance;
  all_goals norm_num [ Symmetric, Std.Irrefl ];
  · exact ⟨fun a b h => ⟨Ne.symm h.1, h.2.1.symm, by simpa only [SimpleGraph.edgeDensity_comm] using h.2.2⟩⟩;
  · exact ⟨ fun i hi => hi.1 rfl ⟩;
  · refine' ⟨ _, _, _, _, _ ⟩;
    · exact fun x hx => P.nonempty_of_mem_parts hx;
    · exact fun x hx y hy hxy => P.disjoint hx hy hxy;
    · tauto;
    · grind;
    · refine' ⟨ _, _ ⟩;
      · exact fun x y hxy U hU V hV hx hy hUV hUV' hUV'' => ⟨ U, hU, V, ⟨ hUV, hUV', hV, hUV'' ⟩, hx, hy ⟩;
      · have := regularityReduced_edges_card_decoupled hε hd hεB hP₁ hP₄ hparts;
        push_cast at * ; nlinarith [ this ]

end Erdos550
