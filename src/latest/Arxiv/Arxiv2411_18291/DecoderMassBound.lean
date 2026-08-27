import Arxiv.Arxiv2411_18291.ExactLocalDecoder
import Arxiv.Arxiv2411_18291.ContainedBlockIntersections

/-! # A bound for the total absolute mass of a local decoder row -/

open Finset
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

theorem choose_mul_decoder_magnitude_le (q r t : ℕ) (hqr : r ≤ q) (htr : t ≤ r) :
    q.choose (r - t) * ((q - r).ascFactorial t * (r - t).factorial) ≤
      q.descFactorial r := by
  have hsub : q - (r - t) = q - r + t := by omega
  have hrest : r - (r - t) = t := by omega
  calc
    _ = (q - r).ascFactorial t * q.descFactorial (r - t) := by
      rw [Nat.descFactorial_eq_factorial_mul_choose]
      ring
    _ ≤ (q - r + 1).ascFactorial t * q.descFactorial (r - t) :=
      Nat.mul_le_mul_right _ (Nat.ascFactorial_le t (Nat.le_succ _))
    _ = (q - (r - t)).descFactorial (r - (r - t)) * q.descFactorial (r - t) := by
      rw [hsub, hrest, Nat.add_descFactorial_eq_ascFactorial]
    _ = _ := Nat.descFactorial_mul_descFactorial (Nat.sub_le r t)

theorem sum_abs_localDecoder_le {V : Type*} [Fintype V] [DecidableEq V] {q r : ℕ}
    (hqr : r < q) (Z : Finset V) (hZ : Z.card = q + r) (Q : Block V q)
    (hQZ : Q.val ⊆ Z) :
    (∑ e ∈ univ.filter (fun e : Block V r => e.val ⊆ Z), |localDecoder q e Q|) ≤
      (2 ^ r * q.descFactorial r : ℕ) := by
  let E := univ.filter fun e : Block V r => e.val ⊆ Z
  let a : ℕ → ℤ := fun t => ((q - r).ascFactorial t * (r - t).factorial : ℕ)
  have hmaps : ∀ e ∈ E, (e.val \ Q.val).card ∈ range (r + 1) := by
    intro e _
    have h := card_le_card (sdiff_subset : e.val \ Q.val ⊆ e.val)
    rw [e.property] at h
    exact mem_range.mpr (by omega)
  have hcount (t : ℕ) (ht : t ∈ range (r + 1)) :
      (E.filter fun e => (e.val \ Q.val).card = t).card = q.choose (r - t) * r.choose t := by
    have heq : E.filter (fun e => (e.val \ Q.val).card = t) =
        univ.filter (fun e : Block V r => e.val ⊆ Z ∧ (e.val \ Q.val).card = t) := by
      ext e
      simp [E]
    rw [heq, card_contained_blocks_with_sdiff Z Q.val hQZ r t (by simpa using ht),
      Q.property, hZ, Nat.add_sub_cancel_left]
  calc
    _ = ∑ e ∈ E, a (e.val \ Q.val).card := by
      apply sum_congr rfl
      intro e _
      exact abs_localDecoder_eq hqr e Q
    _ = ∑ t ∈ range (r + 1),
        ∑ e ∈ E.filter (fun e => (e.val \ Q.val).card = t), a (e.val \ Q.val).card :=
      (sum_fiberwise_of_maps_to hmaps _).symm
    _ = ∑ t ∈ range (r + 1), (q.choose (r - t) * r.choose t : ℕ) * a t := by
      apply sum_congr rfl
      intro t ht
      rw [sum_congr rfl (fun e he => congrArg a (mem_filter.mp he).2),
        sum_const, nsmul_eq_mul, hcount t ht]
    _ ≤ ∑ t ∈ range (r + 1), (r.choose t : ℤ) * q.descFactorial r := by
      apply sum_le_sum
      intro t ht
      have hb := choose_mul_decoder_magnitude_le q r t hqr.le (by simpa using ht)
      have hm := Nat.mul_le_mul_left (r.choose t) hb
      dsimp only [a]
      exact_mod_cast (by nlinarith only [hm] :
        q.choose (r - t) * r.choose t *
            ((q - r).ascFactorial t * (r - t).factorial) ≤
          r.choose t * q.descFactorial r)
    _ = _ := by
      rw [← sum_mul]
      norm_cast
      rw [Nat.sum_range_choose]

end Arxiv2411_18291
