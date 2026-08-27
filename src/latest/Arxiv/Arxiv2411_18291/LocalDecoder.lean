import Arxiv.Arxiv2411_18291.Incidence
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring

/-!
# The integer local decoder

Lemma `lem:decode` of arXiv:2411.18291. We use the explicit
inclusion–exclusion formula from Section 7, and verify it by interchanging
the two finite sums. Every surviving summand has the same factorial weight.
-/

open scoped BigOperators
open Finset

noncomputable section

namespace Arxiv2411_18291

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {q r : ℕ}

/-- The signed weight of an `i`-subset in Wilson's local decoder. -/
def decoderWeight (q r i : ℕ) : ℤ :=
  (-1) ^ i * (q.descFactorial i : ℤ) * ((r - i).factorial : ℤ)

/-- An explicit integer vector on the `q`-cliques. -/
def localDecoder (q : ℕ) (e : Block V r) (Q : Block V q) : ℤ :=
  ∑ I ∈ e.val.powerset, if Disjoint I Q.val then decoderWeight q r I.card else 0

/-- The counting step in the local decoder: cliques containing an edge and
avoiding an `i`-set, in an ambient set of size `q+r`. -/
theorem card_cliques_avoiding (hn : Fintype.card V = q + r) (hqr : r ≤ q)
    (I : Finset V) (e : Block V r) (hIr : I.card ≤ r) (hIe : Disjoint I e.val) :
    (univ.filter fun Q : Block V q => e.val ⊆ Q.val ∧ Disjoint I Q.val).card =
      (q - I.card).choose (r - I.card) := by
  have heT : e.val ⊆ univ \ I :=
    subset_sdiff.mpr ⟨subset_univ _, hIe.symm⟩
  have hcard := card_blocks_between (r := q) e.val (univ \ I) heT
    (by simpa only [e.property] using hqr)
  have heq : (univ.filter fun Q : Block V q => e.val ⊆ Q.val ∧ Disjoint I Q.val) =
      (univ.filter fun Q : Block V q => e.val ⊆ Q.val ∧ Q.val ⊆ univ \ I) := by
    ext Q
    simp [subset_sdiff, disjoint_comm]
  rw [heq, hcard, card_sdiff_of_subset (subset_univ _), card_univ, hn, e.property]
  have hsub : q + r - I.card - r = q - I.card := by omega
  rw [hsub, ← Nat.choose_symm (by omega : q - r ≤ q - I.card)]
  congr 1
  omega

theorem decoderWeight_mul_choose {i : ℕ} (hi : i ≤ r) :
    decoderWeight q r i * ((q - i).choose (r - i) : ℤ) =
      (-1 : ℤ) ^ i * q.descFactorial r := by
  have h : q.descFactorial i * (r - i).factorial * (q - i).choose (r - i) =
      q.descFactorial r := by
    rw [mul_assoc, ← Nat.descFactorial_eq_factorial_mul_choose, mul_comm,
      Nat.descFactorial_mul_descFactorial hi]
  unfold decoderWeight
  rw [mul_assoc, mul_assoc, ← Nat.cast_mul, ← Nat.cast_mul, ← Nat.mul_assoc, h]

private theorem decoder_sum_at (hn : Fintype.card V = q + r) (hqr : r ≤ q)
    (e' : Block V r) (I : Finset V) (hIr : I.card ≤ r) :
    (∑ Q : Block V q, if e'.val ⊆ Q.val then
        if Disjoint I Q.val then decoderWeight q r I.card else 0 else 0) =
      if Disjoint I e'.val then (-1 : ℤ) ^ I.card * q.descFactorial r else 0 := by
  by_cases hIe : Disjoint I e'.val
  · rw [if_pos hIe]
    calc
      _ = ∑ Q ∈ univ.filter
          (fun Q : Block V q => e'.val ⊆ Q.val ∧ Disjoint I Q.val),
          decoderWeight q r I.card := by
        rw [sum_filter]
        apply sum_congr rfl
        intro Q _
        split_ifs <;> simp_all
      _ = _ := by
        rw [sum_const, card_cliques_avoiding hn hqr I e' hIr hIe,
          nsmul_eq_mul, mul_comm, decoderWeight_mul_choose hIr]
  · rw [if_neg hIe]
    apply sum_eq_zero
    intro Q _
    by_cases heQ : e'.val ⊆ Q.val
    · have hIQ : ¬Disjoint I Q.val := fun h =>
        hIe (disjoint_of_subset_right heQ h)
      simp [heQ, hIQ]
    · simp [heQ]

omit [Fintype V] in
/-- Inclusion–exclusion cancels unless the two equal-sized edges coincide. -/
theorem decoder_sign_sum (e e' : Block V r) (N : ℤ) :
    (∑ I ∈ e.val.powerset,
      if Disjoint I e'.val then (-1 : ℤ) ^ I.card * N else 0) =
      if e' = e then N else 0 := by
  rw [← sum_filter]
  have hfilter : e.val.powerset.filter (fun I => Disjoint I e'.val) =
      (e.val \ e'.val).powerset := by
    ext I
    simp [subset_sdiff]
  rw [hfilter, ← sum_mul, sum_powerset_neg_one_pow_card]
  have heq : e.val \ e'.val = ∅ ↔ e' = e := by
    rw [sdiff_eq_empty_iff_subset]
    constructor
    · intro h
      exact (Subtype.ext (eq_of_subset_of_card_le h (by rw [e.property, e'.property]))).symm
    · rintro rfl
      exact Subset.rfl
  simp only [heq]
  split_ifs <;> simp

/-- The decoder's boundary is `(q)_r` times the single-edge vector. -/
theorem boundary_localDecoder (hn : Fintype.card V = q + r) (hqr : r ≤ q)
    (e : Block V r) :
    boundary r (localDecoder q e) =
      fun e' => if e' = e then (q.descFactorial r : ℤ) else 0 := by
  funext e'
  unfold boundary localDecoder
  simp only [Finset.ite_sum_zero]
  rw [sum_comm]
  calc
    _ = ∑ I ∈ e.val.powerset,
        if Disjoint I e'.val then (-1 : ℤ) ^ I.card * q.descFactorial r else 0 := by
      apply sum_congr rfl
      intro I hI
      exact decoder_sum_at hn hqr e' I
        (by simpa only [e.property] using card_le_card (mem_powerset.mp hI))
    _ = _ := decoder_sign_sum e e' _

end Arxiv2411_18291
