import Arxiv.Arxiv2411_18291.Incidence
import Arxiv.Arxiv2411_18291.Decomposition

/-!
# Counting decoding assignments through a fixed clique

A `(q+r)`-set containing a fixed `q`-clique has at most `choose(q+r,r)`
possible root edges. Double counting bounds the total number of assigned
decoders that can affect one clique, independently of the chosen families.
-/

open Finset
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

variable {V : Type*} [Fintype V] [DecidableEq V] {q r : ℕ}

theorem decoder_assignment_count_le (G : Hypergraph V r)
    (Z : Block V r → Finset (Block V (q + r)))
    (hroot : ∀ e ∈ G, ∀ z ∈ Z e, e.val ⊆ z.val) (Q : Block V q) :
    (∑ e ∈ G, ((Z e).filter fun z => Q.val ⊆ z.val).card) ≤
      (q + r).choose r * (Fintype.card V - q).choose r := by
  have he (e : Block V r) : ((Z e).filter fun z => Q.val ⊆ z.val).card =
      ∑ z : Block V (q + r), if z ∈ Z e ∧ Q.val ⊆ z.val then 1 else 0 := by
    have hset : (Z e).filter (fun z => Q.val ⊆ z.val) =
        univ.filter (fun z : Block V (q + r) => z ∈ Z e ∧ Q.val ⊆ z.val) := by
      ext z
      simp
    rw [hset, card_eq_sum_ones, sum_filter]
  have hcount : (univ.filter fun z : Block V (q + r) => Q.val ⊆ z.val).card =
      (Fintype.card V - q).choose r := by
    have h := card_blocks_between (r := q + r) Q.val univ (subset_univ _)
      (by rw [Q.property]; omega)
    simpa only [subset_univ, and_true, card_univ, Q.property, Nat.add_sub_cancel_left] using h
  simp_rw [he]
  rw [sum_comm]
  calc
    _ ≤ ∑ z : Block V (q + r), if Q.val ⊆ z.val then (q + r).choose r else 0 := by
      apply sum_le_sum
      intro z _
      by_cases hQ : Q.val ⊆ z.val
      · simp only [hQ, and_true, if_true]
        rw [← sum_filter, sum_const, nsmul_eq_mul, Nat.cast_id, mul_one]
        apply (card_le_card (show G.filter (fun e => z ∈ Z e) ⊆ cliqueEdges r z from ?_)).trans_eq
          (card_cliqueEdges z)
        intro e he
        exact (mem_cliqueEdges _ _).mpr (hroot e (mem_filter.mp he).1 z (mem_filter.mp he).2)
      · simp only [hQ, and_false, if_false, sum_const_zero, le_refl]
    _ = _ := by
      rw [← sum_filter, sum_const, nsmul_eq_mul, Nat.cast_id, hcount, mul_comm]

end Arxiv2411_18291
