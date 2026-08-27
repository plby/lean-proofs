import Arxiv.Arxiv2411_18291.VariableDecoderRepresentation
import Arxiv.Arxiv2411_18291.WeightedFamilyDegrees

/-! # Decoder capacities from weighted region incidences

At a face, each decoder region contributes exactly the number of its
containing cliques times its own edge multiplicity. This avoids multiplying
the unweighted region degree by the largest multiplicity.
-/

open Finset
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

variable {I V : Type*} [Fintype I] [Fintype V] [DecidableEq V] {q r k : ℕ}

theorem sum_weighted_clique_incidences (Z : I → Block V k) (w : I → ℕ)
    (S : Finset V) (hS : S.card ≤ q) :
    (∑ Q : Block V q, if S ⊆ Q.val then
      ∑ i, if Q.val ⊆ (Z i).val then w i else 0 else 0) =
        (k - S.card).choose (q - S.card) * weightedFamilyDegree Z w S := by
  simp only [Finset.ite_sum_zero, weightedFamilyDegree]
  rw [sum_comm, mul_sum]
  apply sum_congr rfl
  intro i _
  by_cases hSZ : S ⊆ (Z i).val
  · rw [if_pos hSZ]
    calc
      _ = ∑ Q ∈ univ.filter (fun Q : Block V q => S ⊆ Q.val ∧ Q.val ⊆ (Z i).val),
          w i := by
        rw [sum_filter]
        apply sum_congr rfl
        intro Q _
        split_ifs <;> simp_all
      _ = _ := by
        rw [sum_const, card_blocks_between S (Z i).val hSZ hS,
          (Z i).property, nsmul_eq_mul]
        simp only [Nat.cast_id]
  · rw [if_neg hSZ, mul_zero]
    apply sum_eq_zero
    intro Q _
    by_cases hSQ : S ⊆ Q.val
    · have hQZ : ¬ Q.val ⊆ (Z i).val := fun h => hSZ (hSQ.trans h)
      simp only [hSQ, hQZ, if_true, if_false]
    · simp only [hSQ, if_false]

theorem edgewiseDecoderCapacity_degree_of_card_le (D : Finset (Block V q))
    {B : Hypergraph V (r + 1)} (Z : B → Block V (q + (r + 1))) (S : Finset V) (hS : S.card ≤ q) :
    cliqueCapacityDegree (D ∪ cliqueRefinement q (univ.image Z))
        (edgewiseDecoderCapacity D Z) S =
      (2 ^ q * (r + 1).factorial) *
        ((D.filter fun Q => S ⊆ Q.val).card +
          (q + (r + 1) - S.card).choose (q - S.card) * weightedFamilyDegree Z
            (fun i => (D.filter fun P => i.val.val ⊆ P.val).card) S) := by
  classical
  have hterm (Q : Block V q) :
      (if S ⊆ Q.val then edgewiseDecoderCapacity D Z Q else 0) =
        (2 ^ q * (r + 1).factorial) *
          ((if S ⊆ Q.val ∧ Q ∈ D then 1 else 0) +
            if S ⊆ Q.val then ∑ i : B, if Q.val ⊆ (Z i).val then
              (D.filter fun P => i.val.val ⊆ P.val).card else 0 else 0) := by
    unfold edgewiseDecoderCapacity
    by_cases hS : S ⊆ Q.val <;> simp [hS]
  calc
    _ = ∑ Q ∈ D ∪ cliqueRefinement q (univ.image Z),
        if S ⊆ Q.val then edgewiseDecoderCapacity D Z Q else 0 := by
      rw [cliqueCapacityDegree, sum_filter]
    _ = ∑ Q : Block V q, if S ⊆ Q.val then edgewiseDecoderCapacity D Z Q else 0 := by
      apply sum_subset (subset_univ _)
      intro Q _ hQ
      rw [edgewiseDecoderCapacity_support D Z Q hQ]
      simp only [ite_self]
    _ = _ := by
      simp only [hterm, ← mul_sum, sum_add_distrib]
      have hcount : (∑ Q : Block V q, if S ⊆ Q.val ∧ Q ∈ D then 1 else 0) =
          (D.filter fun Q => S ⊆ Q.val).card := by
        rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one]
        simp only [Nat.cast_id]
        congr 1
        ext Q
        simp only [mem_filter, mem_univ, true_and, and_comm]
      rw [hcount, sum_weighted_clique_incidences Z _ S hS]

theorem edgewiseDecoderCapacity_degree (hqr : r ≤ q) (D : Finset (Block V q))
    {B : Hypergraph V (r + 1)} (Z : B → Block V (q + (r + 1))) (S : Block V r) :
    cliqueCapacityDegree (D ∪ cliqueRefinement q (univ.image Z))
        (edgewiseDecoderCapacity D Z) S.val =
      (2 ^ q * (r + 1).factorial) *
        ((D.filter fun Q => S.val ⊆ Q.val).card +
          (q + 1).choose (q - r) * weightedFamilyDegree Z
            (fun i => (D.filter fun P => i.val.val ⊆ P.val).card) S.val) := by
  simpa only [S.property, show q + (r + 1) - r = q + 1 by omega] using
    edgewiseDecoderCapacity_degree_of_card_le D Z S.val (by rw [S.property]; exact hqr)

theorem edgewiseDecoderCapacity_edge_degree (hqr : r + 1 ≤ q) (D : Finset (Block V q))
    {B : Hypergraph V (r + 1)} (Z : B → Block V (q + (r + 1))) (e : Block V (r + 1)) :
    cliqueCapacityDegree (D ∪ cliqueRefinement q (univ.image Z))
        (edgewiseDecoderCapacity D Z) e.val =
      (2 ^ q * (r + 1).factorial) *
        ((D.filter fun Q => e.val ⊆ Q.val).card +
          q.choose (r + 1) * weightedFamilyDegree Z
            (fun i => (D.filter fun P => i.val.val ⊆ P.val).card) e.val) := by
  simpa only [e.property, Nat.add_sub_cancel, Nat.choose_symm hqr] using
    edgewiseDecoderCapacity_degree_of_card_le D Z e.val (by rw [e.property]; exact hqr)

theorem edgewiseDecoderCapacity_bounded (hqr : r + 1 ≤ q)
    {D : Finset (Block V q)} {B : Hypergraph V (r + 1)}
    (Z : B → Block V (q + (r + 1))) {θD θZ : ℝ}
    (hD : IsCliqueFamilyBounded r D θD)
    (hZ : IsWeightedFamilyBounded r Z
      (fun i => (D.filter fun P => i.val.val ⊆ P.val).card) θZ) :
    IsCliqueCapacityBounded r (D ∪ cliqueRefinement q (univ.image Z))
      (edgewiseDecoderCapacity D Z)
      ((2 ^ q * (r + 1).factorial : ℕ) * (θD + (q + 1).choose (q - r) * θZ)) := by
  intro S
  rw [edgewiseDecoderCapacity_degree (by omega) D Z S, Nat.cast_mul, Nat.cast_add,
    Nat.cast_mul]
  have hcount : ((D.filter fun Q => S.val ⊆ Q.val).card : ℝ) < θD * Fintype.card V := by
    have hle : ((D.filter fun Q => S.val ⊆ Q.val).card : ℝ) ≤
        ((degree (boundary (r + 1) (indicator D)) S.val : ℤ) : ℝ) := by
      exact_mod_cast face_clique_count_le_boundary_degree hqr D S
    exact hle.trans_lt (hD S)
  have hsum := add_lt_add_of_lt_of_le hcount
    (mul_le_mul_of_nonneg_left (hZ S).le
      (Nat.cast_nonneg ((q + 1).choose (q - r)) : (0 : ℝ) ≤ _))
  have hpos : (0 : ℝ) < (2 ^ q * (r + 1).factorial : ℕ) := by positivity
  have hh := mul_lt_mul_of_pos_left hsum hpos
  rw [show θD * (Fintype.card V : ℝ) + (q + 1).choose (q - r) *
      (θZ * Fintype.card V) = (θD + (q + 1).choose (q - r) * θZ) *
        Fintype.card V by ring] at hh
  simpa only [Nat.cast_mul, mul_assoc] using hh

end Arxiv2411_18291
