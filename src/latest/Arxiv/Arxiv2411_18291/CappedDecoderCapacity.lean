import Arxiv.Arxiv2411_18291.WeightedDecoderDegrees
import Arxiv.Arxiv2411_18291.VariableSplittingMultiplicity

/-! # Separated decoder regions retain a linear edge-capacity bound

An edge is contained in at most one decoder region. Summing the weighted
clique capacities through that edge therefore costs only one original
edge multiplicity, multiplied by the fixed decoder coefficient.
-/

open Finset
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

theorem IsCliqueCover.weighted_edge_degree_le
    {I V : Type*} [Fintype I] [Fintype V] [DecidableEq V] {s r : ℕ}
    {R : Hypergraph V (r + 1)} {E : I → Block V (r + 1)} {Z : I → Block V s}
    (hZ : IsCliqueCover R E Z) (w : I → ℕ) {M : ℝ} (hM : 0 ≤ M)
    (hw : ∀ i, (w i : ℝ) ≤ M) (e : Block V (r + 1)) :
    (weightedFamilyDegree Z w e.val : ℝ) ≤ M := by
  classical
  unfold weightedFamilyDegree
  by_cases hex : ∃ i, e.val ⊆ (Z i).val
  · obtain ⟨i, hi⟩ := hex
    rw [sum_eq_single i]
    · simpa only [if_pos hi] using hw i
    · intro j _ hji
      exact if_neg (fun hj => hji (hZ.subclique_unique le_rfl e hj hi))
    · intro h
      exact (h (mem_univ _)).elim
  · have hz : (∑ i, if e.val ⊆ (Z i).val then w i else 0) = 0 := by
      apply sum_eq_zero
      intro i _
      exact if_neg (fun hi => hex ⟨i, hi⟩)
    simpa only [hz, Nat.cast_zero] using hM

theorem IsCliqueCover.decoder_capacity_edge_le
    {V : Type*} [Fintype V] [DecidableEq V] {q r : ℕ}
    (hqr : r + 1 ≤ q) (D : Finset (Block V q))
    {R B : Hypergraph V (r + 1)} {Z : B → Block V (q + (r + 1))}
    (hZ : IsCliqueCover R (fun e : B => e.val) Z) {M : ℝ} (hM : 0 ≤ M)
    (hcap : ∀ e : Block V (r + 1), ((D.filter fun Q => e.val ⊆ Q.val).card : ℝ) ≤ M)
    (e : Block V (r + 1)) :
    (cliqueCapacityDegree (D ∪ cliqueRefinement q (univ.image Z))
      (edgewiseDecoderCapacity D Z) e.val : ℝ) ≤
        ((2 ^ q * (r + 1).factorial * (1 + q.choose (r + 1)) : ℕ) : ℝ) * M := by
  let w (i : B) : ℕ := (D.filter fun Q => i.val.val ⊆ Q.val).card
  have hw' (i : B) : (w i : ℝ) ≤ M := hcap i.val
  have hw : (weightedFamilyDegree Z w e.val : ℝ) ≤ M :=
    IsCliqueCover.weighted_edge_degree_le (I := B) (V := V) (r := r) hZ w hM hw' e
  rw [edgewiseDecoderCapacity_edge_degree hqr D Z e, Nat.cast_mul, Nat.cast_add,
    Nat.cast_mul]
  have hh := mul_le_mul_of_nonneg_left
    (add_le_add (hcap e) (mul_le_mul_of_nonneg_left hw (Nat.cast_nonneg (q.choose (r + 1)))))
    (Nat.cast_nonneg (2 ^ q * (r + 1).factorial) : (0 : ℝ) ≤ _)
  simpa only [w, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
    mul_add, add_mul, one_mul, mul_assoc] using hh

theorem VariableSplittingFamily.decoder_clique_multiplicity
    {W V : Type*} [Fintype W] [Fintype V] [DecidableEq W] [DecidableEq V] {q r : ℕ}
    {S : ExchangeSystem W q (r + 1)} (hqr : r + 1 ≤ q) (D : Finset (Block V q))
    {R B B' : Hypergraph V (r + 1)} {Z : B → Block V (q + (r + 1))}
    (hZ : IsCliqueCover R (fun e : B => e.val) Z) {M θ : ℝ} (hM : 0 ≤ M)
    (hcap : ∀ e : Block V (r + 1), ((D.filter fun Q => e.val ⊆ Q.val).card : ℝ) ≤ M)
    (F : VariableSplittingFamily S (D ∪ cliqueRefinement q (univ.image Z)) B'
      (edgewiseDecoderCapacity D Z) θ) (e : Block V (r + 1)) :
    ((F.cliques.filter fun Q => e.val ⊆ Q.val).card : ℝ) ≤
      2 * ((2 ^ q * (r + 1).factorial * (1 + q.choose (r + 1)) : ℕ) : ℝ) * M + 2 := by
  by_cases he : e ∈ B'
  · have hcount : ((F.cliques.filter fun Q => e.val ⊆ Q.val).card : ℝ) ≤
        2 * cliqueCapacityDegree (D ∪ cliqueRefinement q (univ.image Z))
          (edgewiseDecoderCapacity D Z) e.val := by
      exact_mod_cast F.clique_count_original e he
    have hbound := mul_le_mul_of_nonneg_left (hZ.decoder_capacity_edge_le hqr D hM hcap e)
      (by norm_num : (0 : ℝ) ≤ 2)
    linarith only [hcount, hbound]
  · have hcount : ((F.cliques.filter fun Q => e.val ⊆ Q.val).card : ℝ) ≤ 2 := by
      exact_mod_cast F.clique_count_outside e he
    have hp : 0 ≤ 2 * ((2 ^ q * (r + 1).factorial * (1 + q.choose (r + 1)) : ℕ) : ℝ) * M :=
      mul_nonneg (by positivity) hM
    linarith only [hcount, hp]

end Arxiv2411_18291
