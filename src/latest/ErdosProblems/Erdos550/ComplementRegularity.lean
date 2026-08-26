import Mathlib
import ErdosProblems.Erdos550.Basic
import ErdosProblems.Erdos550.RemovalLemma

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Complement (red-graph) regularity

The off-Turán tree-embedding argument
uses the *red* graph `Gᵇᶜ` (the complement of the blue host).  When a pair of
clusters is `ε`-regular of **blue** density below `d`, it is `ε`-regular of **red**
density above `1 − d`, so a large *independent set* of the blue reduced graph
carries a red blow-up of `K_{q+1}` — the Turán/α(Q) step.

This file supplies the complement-regularity ingredients:

* `edgeDensity_compl_add_disjoint` — for nonempty **disjoint** `s, t`, the blue
  and red edge densities of `(s,t)` sum to `1`;
* `edgeDensity_compl_disjoint` — hence the red density is `1 − blue density`;
* `isUniform_compl` — `ε`-uniformity is preserved under complementation on
  disjoint pairs (indeed on all pairs);
* `exists_red_multipartite_of_sparse` — the red-graph blow-up/embedding lemma:
  `q+1` pairwise-disjoint, pairwise-`ε₀`-uniform clusters of blue density
  `≤ 1 − d` contain a red copy of any `(q+1)`-colourable `F` (in particular the
  complete multipartite graph), for a uniform `ε₀ > 0` and size threshold `m₀`.

These components give the F-freeness (`α(Q) < ηℓ`) step of the direct
off-Turán embedding.
-/

open SimpleGraph Finset

namespace Erdos550

/-
For nonempty **disjoint** finite sets `s, t`, the blue and red edge densities
of the pair `(s,t)` sum to `1`.
-/
lemma edgeDensity_compl_add_disjoint {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {s t : Finset V}
    (hs : s.Nonempty) (ht : t.Nonempty) (hd : Disjoint s t) :
    (G.edgeDensity s t : ℝ) + (Gᶜ.edgeDensity s t : ℝ) = 1 := by
  rw [ SimpleGraph.edgeDensity, SimpleGraph.edgeDensity ];
  unfold Rel.edgeDensity;
  simp +decide [ Rel.interedges, SimpleGraph.compl_adj ];
  rw [ ← add_div, div_eq_iff ] <;> norm_cast <;> simp_all +decide [ Finset.disjoint_left ];
  · rw [ ← Finset.card_union_of_disjoint ];
    · convert! Finset.card_product s t using 2 ; ext ⟨ x, y ⟩ ; by_cases h : G.Adj x y <;> aesop;
    · exact Finset.disjoint_filter.mpr ( by aesop );
  · exact ⟨ hs.ne_empty, ht.ne_empty ⟩

/-- The red density of a nonempty disjoint pair is `1 −` the blue density. -/
lemma edgeDensity_compl_disjoint {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {s t : Finset V}
    (hs : s.Nonempty) (ht : t.Nonempty) (hd : Disjoint s t) :
    (Gᶜ.edgeDensity s t : ℝ) = 1 - (G.edgeDensity s t : ℝ) := by
  have := edgeDensity_compl_add_disjoint G hs ht hd
  linarith

/-
`ε`-uniformity is preserved under complementation on **disjoint** pairs.
-/
lemma isUniform_compl {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {ε : ℝ} {s t : Finset V}
    (hd : Disjoint s t) (h : G.IsUniform ε s t) : Gᶜ.IsUniform ε s t := by
  intro s' hs' t' ht' hs ht; specialize h hs' ht' hs ht; by_cases hs'0 : s' = ∅ <;> by_cases ht'0 : t' = ∅ <;> simp_all +decide [ SimpleGraph.edgeDensity ] ;
  · contrapose! hs;
    exact mul_pos ( Nat.cast_pos.mpr ( Finset.card_pos.mpr ( by contrapose! h; aesop ) ) ) ( lt_of_le_of_lt ( abs_nonneg _ ) h );
  · contrapose! hs;
    refine' mul_pos ( Nat.cast_pos.mpr _ ) ( lt_of_le_of_lt ( abs_nonneg _ ) h );
    contrapose! hs; aesop;
  · by_cases hs0 : s = ∅ <;> by_cases ht0 : t = ∅ <;> simp_all +decide [ Rel.edgeDensity ];
    exact absurd ht ( not_le_of_gt ( mul_pos ( Nat.cast_pos.mpr ( Finset.card_pos.mpr ( Finset.nonempty_of_ne_empty ht0 ) ) ) ( lt_of_le_of_lt ( abs_nonneg _ ) h ) ) );
  · have h_edgeDensity_compl : (Rel.edgeDensity Gᶜ.Adj s' t' : ℝ) = 1 - (Rel.edgeDensity G.Adj s' t' : ℝ) ∧ (Rel.edgeDensity Gᶜ.Adj s t : ℝ) = 1 - (Rel.edgeDensity G.Adj s t : ℝ) := by
      exact ⟨ edgeDensity_compl_disjoint G ( Finset.nonempty_of_ne_empty hs'0 ) ( Finset.nonempty_of_ne_empty ht'0 ) ( Finset.disjoint_of_subset_left hs' ( Finset.disjoint_of_subset_right ht' hd ) ), edgeDensity_compl_disjoint G ( Finset.nonempty_of_ne_empty ( by aesop_cat ) ) ( Finset.nonempty_of_ne_empty ( by aesop_cat ) ) hd ⟩;
    grind

/-
**Red-graph blow-up / embedding lemma (`α(Q)` step).**  For a `(q+1)`-colourable
graph `F` on `W` and density slack `d > 0`, there are `ε₀ > 0` and a size threshold
`m₀` such that any `q+1` pairwise-disjoint clusters, each of size `≥ m₀`, pairwise
`ε₀`-uniform and of **blue** density `≤ 1 − d`, contain a **red** copy of `F`
(i.e. `F ⊑ Gᶜ`).
-/
lemma exists_red_multipartite_of_sparse {W : Type} [Fintype W] (F : SimpleGraph W)
    (q : ℕ) (hcol : F.Colorable (q + 1)) (d : ℝ) (hd : 0 < d) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ m₀ : ℕ, ∀ {V : Type} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj] (P : Fin (q + 1) → Finset V),
      (∀ i, m₀ ≤ (P i).card) →
      (∀ i j, i ≠ j → Disjoint (P i) (P j)) →
      (∀ i j, i ≠ j → G.IsUniform ε₀ (P i) (P j)) →
      (∀ i j, i ≠ j → (G.edgeDensity (P i) (P j) : ℝ) ≤ 1 - d) →
      F ⊑ Gᶜ := by
  obtain ⟨ε₀, hε₀⟩ : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ m₀ : ℕ, ∀ {V : Type} [Fintype V] [DecidableEq V]
      (Gr : SimpleGraph V) [DecidableRel Gr.Adj] (P : Fin (q + 1) → Finset V),
      (∀ i, m₀ ≤ (P i).card) →
      (∀ i j, i ≠ j → Disjoint (P i) (P j)) →
      (∀ i j, i ≠ j → Gr.IsUniform ε₀ (P i) (P j)) →
      (∀ i j, i ≠ j → (d : ℝ) ≤ (Gr.edgeDensity (P i) (P j) : ℝ)) →
      Kmult (q + 1) (fun _ => Fintype.card W) ⊑ Gr := by
        exact Erdos550.exists_blowup_of_regular q ( Fintype.card W ) d hd;
  obtain ⟨ m₀, hm₀ ⟩ := hε₀.2;
  refine' ⟨ ε₀, hε₀.1, Max.max m₀ 1, _ ⟩;
  intro V _ _ G _ P hP₁ hP₂ hP₃ hP₄;
  refine' SimpleGraph.IsContained.trans _ ( hm₀ Gᶜ P _ _ _ _ );
  · exact colorable_embeds_Kmult F q ( Fintype.card W ) hcol ( by simp +decide );
  · exact fun i => le_trans ( le_max_left _ _ ) ( hP₁ i );
  · exact hP₂;
  · exact fun i j hij => isUniform_compl G ( hP₂ i j hij ) ( hP₃ i j hij );
  · intro i j hij; specialize hP₄ i j hij; rw [ edgeDensity_compl_disjoint G ( Finset.card_pos.mp ( by linarith [ hP₁ i, le_max_right m₀ 1 ] ) ) ( Finset.card_pos.mp ( by linarith [ hP₁ j, le_max_right m₀ 1 ] ) ) ( hP₂ i j hij ) ] ; linarith;

end Erdos550
