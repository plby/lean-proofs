import Arxiv.Arxiv2411_18291.FractionalDecoderCorrection
import Arxiv.Arxiv2411_18291.DecoderAssignmentCounts

/-!
# Uniform coefficient bounds for the fractional decoder correction

A lower bound on the number of decoding sets dilutes each edge error.
Double counting decoding assignments through a fixed clique gives a
uniform correction bound, without assuming the decoding families disjoint.
-/

open Finset
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

variable {V : Type*} [Fintype V] [DecidableEq V] {q r : ℕ}

theorem fractionalDecoderCorrection_abs_le (hqr : r ≤ q) (G : Hypergraph V r)
    (Z : Block V r → Finset (Block V (q + r)))
    (hroot : ∀ e ∈ G, ∀ z ∈ Z e, e.val ⊆ z.val)
    (c : Block V r → ℝ) {a L : ℝ} (ha : 0 ≤ a) (hL : 0 < L)
    (hsize : ∀ e ∈ G, L ≤ ((Z e).card : ℝ)) (hc : ∀ e ∈ G, |c e| ≤ a)
    (Q : Block V q) :
    |fractionalDecoderCorrection G Z c Q| ≤
      a / L * ((2 ^ q * r.factorial : ℕ) / (q.descFactorial r : ℝ)) *
        ((q + r).choose r * (Fintype.card V - q).choose r : ℕ) := by
  let M : ℝ := (2 ^ q * r.factorial : ℕ) / (q.descFactorial r : ℝ)
  let A : ℝ := a / L * M
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  have hA : 0 ≤ A := mul_nonneg (div_nonneg ha hL.le) hM
  have hterm (e : Block V r) (he : e ∈ G) :
      |c e * averagedLocalDecoder q (Z e) e Q| ≤
        A * ((Z e).filter fun z => Q.val ⊆ z.val).card := by
    have hratio := div_le_div_of_nonneg_left
      (Nat.cast_nonneg ((Z e).filter fun z => Q.val ⊆ z.val).card : (0 : ℝ) ≤ _)
      hL (hsize e he)
    have hlocal := averagedLocalDecoder_abs_le hqr (Z e) e Q
    rw [abs_mul]
    calc
      _ ≤ a * (((((Z e).filter fun z => Q.val ⊆ z.val).card : ℝ) / (Z e).card) * M) :=
        mul_le_mul (hc e he) hlocal (abs_nonneg _) ha
      _ ≤ a * (((((Z e).filter fun z => Q.val ⊆ z.val).card : ℝ) / L) * M) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hratio hM) ha
      _ = _ := by dsimp only [A]; ring
  have hcount : (∑ e ∈ G, (((Z e).filter fun z => Q.val ⊆ z.val).card : ℝ)) ≤
      ((q + r).choose r * (Fintype.card V - q).choose r : ℕ) := by
    exact_mod_cast decoder_assignment_count_le G Z hroot Q
  calc
    _ = |∑ e ∈ G, c e * averagedLocalDecoder q (Z e) e Q| := by
      simp only [fractionalDecoderCorrection, Finset.sum_apply]
    _ ≤ ∑ e ∈ G, |c e * averagedLocalDecoder q (Z e) e Q| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ e ∈ G, A * ((Z e).filter fun z => Q.val ⊆ z.val).card := sum_le_sum hterm
    _ = A * ∑ e ∈ G, (((Z e).filter fun z => Q.val ⊆ z.val).card : ℝ) := (mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hcount hA

end Arxiv2411_18291
