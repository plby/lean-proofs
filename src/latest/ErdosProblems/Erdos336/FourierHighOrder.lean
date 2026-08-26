import ErdosProblems.Erdos336.LowOrderFrequencies

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos336

open scoped Pointwise BigOperators ComplexConjugate Combinatorics.Additive

lemma fourier_high_order_four_fifths_arithmetic
    (a d e n f : ℝ)
    (ha : 238 ≤ a) (hda : 2 * a ≤ d + 1) (hd : 4 * d < 9 * a)
    (he : a ^ 4 ≤ d * e) (hf : 1 ≤ f)
    (hn : (10000000 * f) * (d - 1) ≤ n)
    (he0 : 0 ≤ e) :
    16 * n * a ^ 2 * d + 25 * f * a ^ 2 * d ^ 2 +
        25 * n * a ^ 2 < 25 * n * (a ^ 3 + e) := by
  have ha0 : 0 < a := by linarith
  have hd6 : 6 ≤ d := by nlinarith
  have hn10 : 10000 * f * d ≤ n := by nlinarith
  have hn0 : 0 < n := by nlinarith
  have hde : 4 * d * e ≤ 9 * a * e :=
    mul_le_mul_of_nonneg_right (le_of_lt hd) he0
  have haeMul : a * (4 * a ^ 3) ≤ a * (9 * e) := by nlinarith
  have hae : 4 * a ^ 3 ≤ 9 * e := le_of_mul_le_mul_left haeMul ha0
  have hD : 4 * (6401 * a ^ 2 * d) ≤ 9 * (6401 * a ^ 3) := by
    have h := mul_le_mul_of_nonneg_left (le_of_lt hd)
      (show 0 ≤ 6401 * a ^ 2 by positivity)
    nlinarith
  have hlarge : 360000 * a ^ 2 < 1519 * a ^ 3 := by
    have hh : 360000 < 1519 * a := by nlinarith
    have h := mul_lt_mul_of_pos_right hh (show 0 < a ^ 2 by positivity)
    nlinarith
  have hbase : 6401 * a ^ 2 * d + 10000 * a ^ 2 <
      10000 * (a ^ 3 + e) := by
    nlinarith
  have hbase' : 16 * a ^ 2 * d + (1 / 400 : ℝ) * a ^ 2 * d +
      25 * a ^ 2 < 25 * (a ^ 3 + e) := by
    nlinarith
  have hlow : 25 * f * a ^ 2 * d ^ 2 ≤
      (1 / 400 : ℝ) * n * a ^ 2 * d := by
    have h := mul_le_mul_of_nonneg_right hn10
      (show 0 ≤ a ^ 2 * d by positivity)
    nlinarith
  have hm := mul_lt_mul_of_pos_left hbase' hn0
  nlinarith

variable {N : ℕ} [NeZero N]

/-- Under factorially strengthened sparsity, the large Fourier coefficient can
be chosen to have additive order greater than 36. -/
theorem exists_high_order_fourier_gt_four_fifths
    (A : Finset (ZMod N))
    (hcard : 238 ≤ A.card)
    (hdoub : 4 * (A + A).card < 9 * A.card)
    (hsparse : (10000000 * Nat.factorial 36) *
      ((A + A).card - 1) ≤ N)
    (hexpand : ∀ B : Finset (ZMod N), B.Nonempty → B ⊆ A →
      A.card + B.card ≤ (A + B).card + 1) :
    ∃ k : ZMod N, 36 < addOrderOf k ∧
      16 * (A.card : ℝ) ^ 2 <
        25 * ‖cyclicFinsetFourier A k‖ ^ 2 := by
  by_contra hno
  push_neg at hno
  let S := A + A
  let a : ℝ := A.card
  let d : ℝ := S.card
  let e : ℝ := A.addEnergy A
  let n : ℝ := N
  let f : ℝ := Nat.factorial 36
  have ha : 238 ≤ a := by
    dsimp [a]
    exact_mod_cast hcard
  have hAne : A.Nonempty := Finset.card_pos.mp (by omega)
  have hdaNat : 2 * A.card ≤ S.card + 1 := by
    simpa [S, two_mul] using hexpand A hAne (by simp)
  have hda : 2 * a ≤ d + 1 := by
    dsimp [a, d]
    exact_mod_cast hdaNat
  have hd : 4 * d < 9 * a := by
    dsimp [a, d, S]
    exact_mod_cast hdoub
  have heNat : A.card ^ 4 ≤ S.card * A.addEnergy A := by
    simpa [S] using card_four_le_card_double_mul_addEnergy A
  have he : a ^ 4 ≤ d * e := by
    dsimp [a, d, e]
    exact_mod_cast heNat
  have hf : 1 ≤ f := by
    dsimp [f]
    exact_mod_cast Nat.factorial_pos 36
  have hn : (10000000 * f) * (d - 1) ≤ n := by
    have hdpos : 1 ≤ S.card := by omega
    dsimp [d, n, f]
    norm_num [Nat.cast_sub hdpos]
    exact_mod_cast (show (10000000 * Nat.factorial 36) *
      (S.card - 1) ≤ N by simpa [S] using hsparse)
  have he0 : 0 ≤ e := by positivity
  have harith := fourier_high_order_four_fifths_arithmetic a d e n f
    ha hda hd he hf hn he0
  have hrefNat := card_cube_add_addEnergy_le_overlapSigma_add_sq A hexpand
  have href : a ^ 3 + e ≤ (overlapSigma A : ℝ) + a ^ 2 := by
    dsimp [a, e]
    exact_mod_cast hrefNat
  have hcorrNat := overlapSigma_le_overlap_correlation A
  have hcorr : (overlapSigma A : ℝ) ≤
      ∑ x : ZMod N, (differenceOverlap A x).card *
        (differenceOverlap S x).card := by
    exact_mod_cast hcorrNat
  have hFourier := sum_normSq_fourier_eq_overlap_correlation A S
  have hupperPoint (k : ZMod N) :
      25 * (‖cyclicFinsetFourier A k‖ ^ 2 *
          ‖cyclicFinsetFourier S k‖ ^ 2) ≤
        (if addOrderOf k ≤ 36 then 25 * a ^ 2 * d ^ 2
         else 16 * a ^ 2 * ‖cyclicFinsetFourier S k‖ ^ 2) := by
    by_cases hk : addOrderOf k ≤ 36
    · simp only [hk, if_true]
      have hAcoeff := norm_cyclicFinsetFourier_le_card A k
      have hScoeff := norm_cyclicFinsetFourier_le_card S k
      have hA0 : 0 ≤ ‖cyclicFinsetFourier A k‖ := norm_nonneg _
      have hS0 : 0 ≤ ‖cyclicFinsetFourier S k‖ := norm_nonneg _
      have hAsq : ‖cyclicFinsetFourier A k‖ ^ 2 ≤ (A.card : ℝ) ^ 2 := by
        nlinarith
      have hSsq : ‖cyclicFinsetFourier S k‖ ^ 2 ≤ (S.card : ℝ) ^ 2 := by
        nlinarith
      have hprod := mul_le_mul hAsq hSsq (sq_nonneg _) (sq_nonneg _)
      dsimp [a, d]
      nlinarith
    · simp only [hk, if_false]
      have hk' : 36 < addOrderOf k := by omega
      have hkBound := hno k hk'
      have hnonneg : 0 ≤ ‖cyclicFinsetFourier S k‖ ^ 2 := sq_nonneg _
      nlinarith
  have hupperSum := Finset.sum_le_sum
    (fun k (_hk : k ∈ (Finset.univ : Finset (ZMod N))) => hupperPoint k)
  rw [← Finset.mul_sum] at hupperSum
  have hsplit : (∑ k : ZMod N,
      if addOrderOf k ≤ 36 then 25 * a ^ 2 * d ^ 2
      else 16 * a ^ 2 * ‖cyclicFinsetFourier S k‖ ^ 2) ≤
      25 * f * a ^ 2 * d ^ 2 +
        16 * a ^ 2 * (∑ k : ZMod N,
          ‖cyclicFinsetFourier S k‖ ^ 2) := by
    have hp (k : ZMod N) :
        (if addOrderOf k ≤ 36 then 25 * a ^ 2 * d ^ 2
          else 16 * a ^ 2 * ‖cyclicFinsetFourier S k‖ ^ 2) ≤
        (if addOrderOf k ≤ 36 then 25 * a ^ 2 * d ^ 2 else 0) +
          16 * a ^ 2 * ‖cyclicFinsetFourier S k‖ ^ 2 := by
      by_cases hk : addOrderOf k ≤ 36 <;> simp [hk] <;> positivity
    have hs := Finset.sum_le_sum
      (fun k (_hk : k ∈ (Finset.univ : Finset (ZMod N))) => hp k)
    simp only [Finset.sum_add_distrib] at hs
    rw [← Finset.mul_sum] at hs
    have hconst : (∑ k : ZMod N,
        if addOrderOf k ≤ 36 then 25 * a ^ 2 * d ^ 2 else 0) =
        (lowOrderFrequencies N 36).card * (25 * a ^ 2 * d ^ 2) := by
      rw [← Finset.sum_filter]
      simp [lowOrderFrequencies]
    rw [hconst] at hs
    have hlowCard := card_lowOrderFrequencies_le_factorial (N := N) 36
    have hcast : ((lowOrderFrequencies N 36).card : ℝ) ≤ f := by
      dsimp [f]
      exact_mod_cast hlowCard
    have hc0 : 0 ≤ 25 * a ^ 2 * d ^ 2 := by positivity
    have hconstle : ((lowOrderFrequencies N 36).card : ℝ) *
        (25 * a ^ 2 * d ^ 2) ≤ f * (25 * a ^ 2 * d ^ 2) :=
      mul_le_mul_of_nonneg_right hcast hc0
    calc
      _ ≤ ((lowOrderFrequencies N 36).card : ℝ) *
          (25 * a ^ 2 * d ^ 2) +
          16 * a ^ 2 * (∑ k : ZMod N,
            ‖cyclicFinsetFourier S k‖ ^ 2) := hs
      _ ≤ f * (25 * a ^ 2 * d ^ 2) +
          16 * a ^ 2 * (∑ k : ZMod N,
            ‖cyclicFinsetFourier S k‖ ^ 2) :=
        add_le_add hconstle (le_refl _)
      _ = 25 * f * a ^ 2 * d ^ 2 +
          16 * a ^ 2 * (∑ k : ZMod N,
            ‖cyclicFinsetFourier S k‖ ^ 2) := by ring
  rw [sum_norm_sq_cyclicFinsetFourier S] at hsplit
  have hupper : 25 * (∑ k : ZMod N,
      ‖cyclicFinsetFourier A k‖ ^ 2 *
        ‖cyclicFinsetFourier S k‖ ^ 2) ≤
      25 * f * a ^ 2 * d ^ 2 + 16 * a ^ 2 * n * d := by
    dsimp [n, d]
    nlinarith
  have hlowCorr : 25 * n * (a ^ 3 + e) ≤
      25 * n * (∑ x : ZMod N,
        (differenceOverlap A x).card * (differenceOverlap S x).card) +
      25 * n * a ^ 2 := by
    have hbase : a ^ 3 + e ≤
        (∑ x : ZMod N, (differenceOverlap A x).card *
          (differenceOverlap S x).card : ℕ) + a ^ 2 := by
      nlinarith
    have hc := mul_le_mul_of_nonneg_left hbase
      (show 0 ≤ 25 * n by positivity)
    nlinarith
  have hid : (∑ k : ZMod N,
      ‖cyclicFinsetFourier A k‖ ^ 2 *
        ‖cyclicFinsetFourier S k‖ ^ 2) =
      n * (∑ x : ZMod N, (differenceOverlap A x).card *
        (differenceOverlap S x).card) := by
    simpa [n] using hFourier
  nlinarith [hid]

end Erdos336
