import Arxiv.Arxiv2411_18291.Incidence
import Arxiv.Arxiv2411_18291.EmbeddingCountBounds
import Mathlib.Data.Nat.Choose.Bounds

/-!
# Rooted cliques avoiding previously used vertices

For cliques through an `a`-vertex root, one additional forbidden vertex
eliminates at most `n^(q-a-1)` choices. A union bound over the forbidden
set preserves half of any family larger than twice this collision budget.
-/

open Finset
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

variable {V : Type*} [Fintype V] [DecidableEq V] {a q : ℕ}

theorem rooted_clique_vertex_count_le (e : Block V a) (haq : a < q) (v : V)
    (hv : v ∉ e.val) :
    (univ.filter fun Q : Block V q => e.val ⊆ Q.val ∧ v ∈ Q.val).card ≤
      Fintype.card V ^ (q - a - 1) := by
  have hi : (insert v e.val).card ≤ q := by rw [card_insert_of_notMem hv, e.property]; omega
  have heq :
      (univ.filter fun Q : Block V q => e.val ⊆ Q.val ∧ v ∈ Q.val).card =
        (Fintype.card V - (a + 1)).choose (q - (a + 1)) := by
    simpa only [insert_subset_iff, subset_univ, and_true, true_and, and_comm, card_univ,
      card_insert_of_notMem hv, e.property] using
      card_blocks_between (insert v e.val) univ (subset_univ _) hi
  rw [heq, show q - (a + 1) = q - a - 1 by omega]
  exact (Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_left (Nat.sub_le _ _) _)

def avoidingRootedCliques (D : Finset (Block V q)) (e : Block V a) (U : Finset V) :
    Finset (Block V q) := D.filter fun Q => Disjoint (Q.val \ e.val) U

theorem avoidingRootedCliques_bad_count (D : Finset (Block V q)) (e : Block V a)
    (haq : a < q) (hD : ∀ Q ∈ D, e.val ⊆ Q.val) (U : Finset V) :
    (D \ avoidingRootedCliques D e U).card ≤ U.card * Fintype.card V ^ (q - a - 1) := by
  classical
  let B := U \ e.val
  let H (v : V) := univ.filter fun Q : Block V q => e.val ⊆ Q.val ∧ v ∈ Q.val
  have hsub : D \ avoidingRootedCliques D e U ⊆ B.biUnion H := by
    intro Q hQ
    obtain ⟨hQD, hQnot⟩ := mem_sdiff.mp hQ
    have hbad : ¬Disjoint (Q.val \ e.val) U := fun hd =>
      hQnot (mem_filter.mpr ⟨hQD, hd⟩)
    have hex : ∃ v, v ∈ Q.val \ e.val ∧ v ∈ U := by
      by_contra hn
      exact hbad (disjoint_left.mpr (fun v hv hU => hn ⟨v, hv, hU⟩))
    obtain ⟨v, hv, hU⟩ := hex
    exact mem_biUnion.mpr ⟨v, mem_sdiff.mpr ⟨hU, (mem_sdiff.mp hv).2⟩,
      mem_filter.mpr ⟨mem_univ _, hD Q hQD, (mem_sdiff.mp hv).1⟩⟩
  calc
    _ ≤ (B.biUnion H).card := card_le_card hsub
    _ ≤ ∑ v ∈ B, (H v).card := card_biUnion_le
    _ ≤ ∑ _v ∈ B, Fintype.card V ^ (q - a - 1) :=
      sum_le_sum (fun v hv => rooted_clique_vertex_count_le e haq v (mem_sdiff.mp hv).2)
    _ = B.card * Fintype.card V ^ (q - a - 1) := by
      rw [sum_const, nsmul_eq_mul, Nat.cast_id]
    _ ≤ _ := Nat.mul_le_mul_right _ (card_le_card sdiff_subset)

theorem avoidingRootedCliques_card_half (D : Finset (Block V q)) (e : Block V a)
    (haq : a < q) (hD : ∀ Q ∈ D, e.val ⊆ Q.val) (U : Finset V) {L : ℝ}
    (hsize : L ≤ D.card)
    (hsmall : U.card * (Fintype.card V : ℝ) ^ (q - a - 1) ≤ L / 2) :
    L / 2 ≤ (avoidingRootedCliques D e U).card := by
  have hbad : ((D \ avoidingRootedCliques D e U).card : ℝ) ≤
      U.card * (Fintype.card V : ℝ) ^ (q - a - 1) := by
    exact_mod_cast avoidingRootedCliques_bad_count D e haq hD U
  have hcard : ((D \ avoidingRootedCliques D e U).card : ℝ) +
      (avoidingRootedCliques D e U).card = D.card := by
    exact_mod_cast card_sdiff_add_card_eq_card (filter_subset _ D)
  linarith only [hbad, hsmall, hcard, hsize]

end Arxiv2411_18291
