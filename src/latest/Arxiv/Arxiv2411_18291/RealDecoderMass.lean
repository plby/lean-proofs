import Arxiv.Arxiv2411_18291.DecoderMassBound
import Arxiv.Arxiv2411_18291.RealLocalDecoder

/-! # Total absolute mass of normalized real local decoders -/

open Finset
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

theorem sum_abs_realLocalDecoderOn_le {V : Type*} [Fintype V] [DecidableEq V] {q r : ℕ}
    (hqr : r < q) (Z : Finset V) (hZ : Z.card = q + r) (Q : Block V q)
    (hQZ : Q.val ⊆ Z) :
    (∑ e ∈ univ.filter (fun e : Block V r => e.val ⊆ Z),
      |realLocalDecoderOn q Z e Q|) ≤ (2 : ℝ) ^ r := by
  have hN : (0 : ℝ) < q.descFactorial r := by
    exact_mod_cast Nat.descFactorial_pos.mpr hqr.le
  have hraw : (∑ e ∈ univ.filter (fun e : Block V r => e.val ⊆ Z),
      |(localDecoder q e Q : ℝ)|) ≤ (2 : ℝ) ^ r * q.descFactorial r := by
    exact_mod_cast sum_abs_localDecoder_le hqr Z hZ Q hQZ
  simp only [realLocalDecoderOn, localDecoderOn, if_pos hQZ, abs_mul, abs_inv,
    abs_of_pos hN]
  rw [← mul_sum]
  calc
    _ ≤ (q.descFactorial r : ℝ)⁻¹ * ((2 : ℝ) ^ r * q.descFactorial r) :=
      mul_le_mul_of_nonneg_left hraw (inv_nonneg.mpr hN.le)
    _ = _ := by field_simp

theorem sum_decoder_assignment_mass_le {V : Type*} [Fintype V] [DecidableEq V]
    {q r : ℕ} (hqr : r < q) (G : Hypergraph V r)
    (Z : Block V r → Finset (Block V (q + r)))
    (hroot : ∀ e ∈ G, ∀ z ∈ Z e, e.val ⊆ z.val) (Q : Block V q) :
    (∑ e ∈ G, ∑ z ∈ Z e, |realLocalDecoderOn q z.val e Q|) ≤
      (2 : ℝ) ^ r * (Fintype.card V - q).choose r := by
  have he (e : Block V r) : (∑ z ∈ Z e, |realLocalDecoderOn q z.val e Q|) =
      ∑ z : Block V (q + r), if z ∈ Z e then |realLocalDecoderOn q z.val e Q| else 0 := by
    rw [← sum_filter]
    simp
  have hcount : (univ.filter fun z : Block V (q + r) => Q.val ⊆ z.val).card =
      (Fintype.card V - q).choose r := by
    have h := card_blocks_between (r := q + r) Q.val univ (subset_univ _)
      (by rw [Q.property]; omega)
    simpa only [subset_univ, and_true, card_univ, Q.property, Nat.add_sub_cancel_left] using h
  simp_rw [he]
  rw [sum_comm]
  calc
    _ ≤ ∑ z : Block V (q + r), if Q.val ⊆ z.val then (2 : ℝ) ^ r else 0 := by
      apply sum_le_sum
      intro z _
      by_cases hQ : Q.val ⊆ z.val
      · rw [if_pos hQ, ← sum_filter]
        have hsub : G.filter (fun e => z ∈ Z e) ⊆
            univ.filter (fun e : Block V r => e.val ⊆ z.val) := by
          intro e he
          exact mem_filter.mpr ⟨mem_univ _,
            hroot e (mem_filter.mp he).1 z (mem_filter.mp he).2⟩
        exact (sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => abs_nonneg _)).trans
          (sum_abs_realLocalDecoderOn_le hqr z.val z.property Q hQ)
      · simp only [if_neg hQ, realLocalDecoderOn_eq_zero z.val _ Q hQ, abs_zero,
          ite_self, sum_const_zero, le_refl]
    _ = _ := by
      rw [← sum_filter, sum_const, nsmul_eq_mul, hcount, mul_comm]

end Arxiv2411_18291
