import Arxiv.Arxiv2411_18291.RealLocalDecoder

/-!
# Averaging local decoders across many decoding sets

Each average still decodes its root edge exactly. The coefficient bound
counts only decoding sets containing the target clique, divided by the
total number of available decoding sets. This is the dilution required
for the fractional correction in regularity boosting.
-/

open Finset
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

variable {V : Type*} [DecidableEq V] {q r : ℕ}

def averagedLocalDecoder (q : ℕ) (Z : Finset (Block V (q + r)))
    (e : Block V r) (Q : Block V q) : ℝ :=
  (Z.card : ℝ)⁻¹ * ∑ z ∈ Z, realLocalDecoderOn q z.val e Q

theorem averagedLocalDecoder_eq_zero (Z : Finset (Block V (q + r)))
    (e : Block V r) (Q : Block V q) (hQ : ∀ z ∈ Z, ¬Q.val ⊆ z.val) :
    averagedLocalDecoder q Z e Q = 0 := by
  unfold averagedLocalDecoder
  rw [sum_eq_zero (fun z hz => realLocalDecoderOn_eq_zero z.val e Q (hQ z hz)), mul_zero]

theorem averagedLocalDecoder_abs_le (hqr : r ≤ q) (Z : Finset (Block V (q + r)))
    (e : Block V r) (Q : Block V q) :
    |averagedLocalDecoder q Z e Q| ≤
      ((Z.filter fun z => Q.val ⊆ z.val).card : ℝ) / Z.card *
        ((2 ^ q * r.factorial : ℕ) / (q.descFactorial r : ℝ)) := by
  let B : ℝ := (2 ^ q * r.factorial : ℕ) / (q.descFactorial r : ℝ)
  have hsum : |∑ z ∈ Z, realLocalDecoderOn q z.val e Q| ≤
      ((Z.filter fun z => Q.val ⊆ z.val).card : ℝ) * B := by
    calc
      _ ≤ ∑ z ∈ Z, |realLocalDecoderOn q z.val e Q| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ z ∈ Z, if Q.val ⊆ z.val then B else 0 := by
        apply sum_le_sum
        intro z hz
        by_cases h : Q.val ⊆ z.val
        · simpa only [if_pos h] using realLocalDecoderOn_abs_le hqr z.val e Q
        · rw [if_neg h, realLocalDecoderOn_eq_zero z.val e Q h, abs_zero]
      _ = _ := by rw [← sum_filter]; simp only [sum_const, nsmul_eq_mul]
  rw [averagedLocalDecoder, abs_mul, abs_inv, abs_of_nonneg (Nat.cast_nonneg Z.card)]
  calc
    _ ≤ (Z.card : ℝ)⁻¹ * (((Z.filter fun z => Q.val ⊆ z.val).card : ℝ) * B) :=
      mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr (Nat.cast_nonneg _))
    _ = _ := by dsimp only [B]; ring

variable [Fintype V]

theorem boundary_averagedLocalDecoder (hqr : r ≤ q) (Z : Finset (Block V (q + r)))
    (hZ : Z.Nonempty) (e : Block V r) (heZ : ∀ z ∈ Z, e.val ⊆ z.val) :
    boundary r (averagedLocalDecoder q Z e) = fun e' => if e' = e then (1 : ℝ) else 0 := by
  have hcard : (Z.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hZ.card_pos.ne'
  unfold averagedLocalDecoder
  rw [boundary_mul]
  funext e'
  have hb : boundary r (fun Q => ∑ z ∈ Z, realLocalDecoderOn q z.val e Q) e' =
      ∑ z ∈ Z, boundary r (realLocalDecoderOn q z.val e) e' := by
    simp only [boundary, Finset.ite_sum_zero]
    rw [sum_comm]
  rw [hb]
  have heq : (∑ z ∈ Z, boundary r (realLocalDecoderOn q z.val e) e') =
      ∑ _z ∈ Z, if e' = e then (1 : ℝ) else 0 := by
    apply sum_congr rfl
    intro z hz
    exact congrFun (boundary_realLocalDecoderOn z.val z.property hqr e (heZ z hz)) e'
  rw [heq]
  by_cases h : e' = e <;> simp [h, hcard]

end Arxiv2411_18291
