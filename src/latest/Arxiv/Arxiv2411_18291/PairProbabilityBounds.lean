import Arxiv.Arxiv2411_18291.BlockPairCounts
import Arxiv.Arxiv2411_18291.BlockPairFamilyBounds

/-!
# Joint permutation bounds from rooted clique counts

The exact orbit denominator cancels the number of ways to choose the
intersection inside the first block. The remaining bound is a marginal
density times a rooted-family count divided by the available extensions.
-/

open Finset MeasureTheory

noncomputable section

namespace Arxiv2411_18291

variable {V : Type*} [Fintype V] [DecidableEq V] {a b s : ℕ}

theorem IntersectingBlockPair.parameters (P : IntersectingBlockPair V a b s) :
    s ≤ a ∧ s ≤ b ∧ a + b - s ≤ Fintype.card V := by
  have h1 := card_le_card (inter_subset_left (s₁ := P.val.1.val) (s₂ := P.val.2.val))
  have h2 := card_le_card (inter_subset_right (s₁ := P.val.1.val) (s₂ := P.val.2.val))
  have hu := card_union_add_card_inter P.val.1.val P.val.2.val
  have hn := card_le_univ (P.val.1.val ∪ P.val.2.val)
  rw [P.property, P.val.1.property] at h1
  rw [P.property, P.val.2.property] at h2
  rw [P.property, P.val.1.property, P.val.2.property] at hu
  omega

variable [MeasurableSpace (Equiv.Perm V)] [MeasurableSingletonClass (Equiv.Perm V)]

theorem uniform_permuted_pair_probability_le (P : IntersectingBlockPair V a b s)
    (G : Hypergraph V a) (H : Hypergraph V b) {L : ℝ}
    (hL : ∀ I : Block V s, ((H.filter fun B => I.val ⊆ B.val).card : ℝ) ≤ L) :
    (PMF.uniformOfFintype (Equiv.Perm V)).toMeasure.real
      {σ | P.val.1 ∈ mapGraph σ.toEmbedding G ∧ P.val.2 ∈ mapGraph σ.toEmbedding H} ≤
      (G.card / ((Fintype.card V).choose a : ℝ)) *
        (L / ((Fintype.card V - a).choose (b - s) : ℝ)) := by
  obtain ⟨hsa, hsb, hsize⟩ := P.parameters
  have hna : a ≤ Fintype.card V := by omega
  have hnb : b - s ≤ Fintype.card V - a := by omega
  have hc1 : (0 : ℝ) < (Fintype.card V).choose a := by exact_mod_cast Nat.choose_pos hna
  have hc2 : (0 : ℝ) < a.choose s := by exact_mod_cast Nat.choose_pos hsa
  have hc3 : (0 : ℝ) < (Fintype.card V - a).choose (b - s) :=
    by exact_mod_cast Nat.choose_pos hnb
  rw [uniform_permuted_pair_probability]
  calc
    _ ≤ ((G.card : ℝ) * a.choose s * L) /
        (Fintype.card (IntersectingBlockPair V a b s) : ℝ) :=
      div_le_div_of_nonneg_right (card_blockPairFamily_le G H s hL) (Nat.cast_nonneg _)
    _ = _ := by
      rw [card_intersectingBlockPair a b s hsb]
      push_cast
      field_simp

end Arxiv2411_18291
