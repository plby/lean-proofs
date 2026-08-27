import Arxiv.Arxiv2411_18291.RealDecoderMass
import Arxiv.Arxiv2411_18291.FiniteFractionalBoost

/-! # Fractional correction using the total decoder mass -/

open Finset
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

variable {V : Type*} [Fintype V] [DecidableEq V] {q r : ℕ}

theorem fractionalDecoderCorrection_abs_le_mass (hqr : r < q) (G : Hypergraph V r)
    (Z : Block V r → Finset (Block V (q + r)))
    (hroot : ∀ e ∈ G, ∀ z ∈ Z e, e.val ⊆ z.val)
    (c : Block V r → ℝ) {a L : ℝ} (ha : 0 ≤ a) (hL : 0 < L)
    (hsize : ∀ e ∈ G, L ≤ ((Z e).card : ℝ)) (hc : ∀ e ∈ G, |c e| ≤ a)
    (Q : Block V q) :
    |fractionalDecoderCorrection G Z c Q| ≤
      a / L * ((2 : ℝ) ^ r * (Fintype.card V - q).choose r) := by
  have hterm (e : Block V r) (he : e ∈ G) :
      |c e * averagedLocalDecoder q (Z e) e Q| ≤
        a / L * ∑ z ∈ Z e, |realLocalDecoderOn q z.val e Q| := by
    have hinv : ((Z e).card : ℝ)⁻¹ ≤ L⁻¹ := inv_anti₀ hL (hsize e he)
    have hnorm : |∑ z ∈ Z e, realLocalDecoderOn q z.val e Q| ≤
        ∑ z ∈ Z e, |realLocalDecoderOn q z.val e Q| := abs_sum_le_sum_abs _ _
    have hcard : (0 : ℝ) ≤ (Z e).card := Nat.cast_nonneg _
    simp only [averagedLocalDecoder, abs_mul, abs_inv, abs_of_nonneg hcard]
    calc
      _ ≤ a * (L⁻¹ * ∑ z ∈ Z e, |realLocalDecoderOn q z.val e Q|) := by
        apply mul_le_mul (hc e he) _ (by positivity) ha
        exact mul_le_mul hinv hnorm (abs_nonneg _) (inv_nonneg.mpr hL.le)
      _ = _ := by ring
  calc
    _ = |∑ e ∈ G, c e * averagedLocalDecoder q (Z e) e Q| := by
      simp only [fractionalDecoderCorrection, Finset.sum_apply]
    _ ≤ ∑ e ∈ G, |c e * averagedLocalDecoder q (Z e) e Q| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ e ∈ G, a / L * ∑ z ∈ Z e, |realLocalDecoderOn q z.val e Q| :=
      sum_le_sum hterm
    _ = a / L * ∑ e ∈ G, ∑ z ∈ Z e, |realLocalDecoderOn q z.val e Q| :=
      (mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_decoder_assignment_mass_le hqr G Z hroot Q)
      (div_nonneg ha hL.le)

theorem exists_fractional_boost_of_decoder_mass (hqr : r < q) (G : Hypergraph V r)
    (Z : Block V r → Finset (Block V (q + r)))
    (hroot : ∀ e ∈ G, ∀ z ∈ Z e, e.val ⊆ z.val)
    (hZG : ∀ e ∈ G, ∀ z ∈ Z e, cliqueEdges r z ⊆ G)
    {d a L : ℝ} (ha : 0 ≤ a) (hL : 0 < L)
    (hsize : ∀ e ∈ G, L ≤ ((Z e).card : ℝ))
    (hcounts : ∀ e ∈ G, |(((cliqueFamily G q).filter fun Q => e.val ⊆ Q.val).card : ℝ) - d| ≤
      2 * a)
    (hsmall : a / L * ((2 : ℝ) ^ r * (Fintype.card V - q).choose r) ≤ 1 / 2) :
    ∃ p : Block V q → ℝ, (∀ Q, 0 ≤ p Q ∧ p Q ≤ 1) ∧
      (∀ Q, ¬cliqueEdges r Q ⊆ G → p Q = 0) ∧
      boundary r p = fun e => if e ∈ G then d / 2 else 0 := by
  refine exists_fractional_boost_of_uniform_correction hqr.le G Z hroot hZG ?_ hcounts ?_
  · intro e he
    apply card_pos.mp
    exact_mod_cast hL.trans_le (hsize e he)
  · intro c hc Q
    exact (fractionalDecoderCorrection_abs_le_mass hqr G Z hroot c ha hL hsize hc Q).trans
      hsmall

end Arxiv2411_18291
