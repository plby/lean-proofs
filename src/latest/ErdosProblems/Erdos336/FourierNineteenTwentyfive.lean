import ErdosProblems.Erdos336.FourierHalfPlane

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos336

open scoped Pointwise BigOperators ComplexConjugate Combinatorics.Additive

lemma fourier_nineteen_twentyfive_arithmetic
    (a d e n : ℝ)
    (ha : 7 ≤ a) (hda : 2 * a ≤ d + 1) (hd : 4 * d < 9 * a)
    (he : a ^ 4 ≤ d * e) (hn : 12000 * (d - 1) ≤ n)
    (he0 : 0 ≤ e) :
    361 * n * a ^ 2 * d + 625 * a ^ 2 * d ^ 2 +
        625 * n * a ^ 2 < 625 * n * (a ^ 3 + e) := by
  have ha0 : 0 < a := by linarith
  have hd6 : 6 ≤ d := by nlinarith
  have hn10 : 10000 * d ≤ n := by nlinarith
  have hn0 : 0 < n := by nlinarith
  have hde : 4 * d * e ≤ 9 * a * e :=
    mul_le_mul_of_nonneg_right (le_of_lt hd) he0
  have haeMul : a * (4 * a ^ 3) ≤ a * (9 * e) := by nlinarith
  have hae : 4 * a ^ 3 ≤ 9 * e := le_of_mul_le_mul_left haeMul ha0
  have hD : 4 * (5777 * a ^ 2 * d) ≤ 9 * (5777 * a ^ 3) := by
    have h := mul_le_mul_of_nonneg_left (le_of_lt hd)
      (show 0 ≤ 5777 * a ^ 2 by positivity)
    nlinarith
  have hlarge : 360000 * a ^ 2 < 52063 * a ^ 3 := by
    have hh : 360000 < 52063 * a := by nlinarith
    have h := mul_lt_mul_of_pos_right hh (show 0 < a ^ 2 by positivity)
    nlinarith
  have hbase : 5777 * a ^ 2 * d + 10000 * a ^ 2 <
      10000 * (a ^ 3 + e) := by
    nlinarith
  have hbase' : 361 * a ^ 2 * d + (1 / 16 : ℝ) * a ^ 2 * d +
      625 * a ^ 2 < 625 * (a ^ 3 + e) := by
    nlinarith
  have hzero : 625 * a ^ 2 * d ^ 2 ≤
      (1 / 16 : ℝ) * n * a ^ 2 * d := by
    have h := mul_le_mul_of_nonneg_right hn10
      (show 0 ≤ a ^ 2 * d by positivity)
    nlinarith
  have hm := mul_lt_mul_of_pos_left hbase' hn0
  nlinarith

variable {N : ℕ} [NeZero N]

/-- Almost expansion suffices for a robust Fourier coefficient: under the
same sparse strict-`9/4` hypotheses, the coefficient exceeds `19/25` of the
set size. -/
theorem exists_nonzero_fourier_gt_nineteen_twentyfive
    (A : Finset (ZMod N))
    (hcard : 7 ≤ A.card)
    (hdoub : 4 * (A + A).card < 9 * A.card)
    (hsparse : 12000 * ((A + A).card - 1) ≤ N)
    (hexpand : ∀ B : Finset (ZMod N), B.Nonempty → B ⊆ A →
      A.card + B.card ≤ (A + B).card + 1) :
    ∃ k : ZMod N, k ≠ 0 ∧
      361 * (A.card : ℝ) ^ 2 <
        625 * ‖cyclicFinsetFourier A k‖ ^ 2 := by
  by_contra hno
  push_neg at hno
  let S := A + A
  let a : ℝ := A.card
  let d : ℝ := S.card
  let e : ℝ := A.addEnergy A
  let n : ℝ := N
  have ha : 7 ≤ a := by
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
  have hn : 12000 * (d - 1) ≤ n := by
    have hdpos : 1 ≤ S.card := by omega
    dsimp [d, n]
    norm_num [Nat.cast_sub hdpos]
    exact_mod_cast (show 12000 * (S.card - 1) ≤ N by simpa [S] using hsparse)
  have he0 : 0 ≤ e := by positivity
  have harith := fourier_nineteen_twentyfive_arithmetic a d e n
    ha hda hd he hn he0
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
      625 * (‖cyclicFinsetFourier A k‖ ^ 2 *
          ‖cyclicFinsetFourier S k‖ ^ 2) ≤
        (if k = 0 then 625 * a ^ 2 * d ^ 2
         else 361 * a ^ 2 * ‖cyclicFinsetFourier S k‖ ^ 2) := by
    by_cases hk : k = 0
    · subst k
      simp [a, d, S]
      nlinarith
    · simp only [hk, if_false]
      have hkBound := hno k hk
      have hnonneg : 0 ≤ ‖cyclicFinsetFourier S k‖ ^ 2 := sq_nonneg _
      nlinarith
  have hupperSum := Finset.sum_le_sum
    (fun k (_hk : k ∈ (Finset.univ : Finset (ZMod N))) => hupperPoint k)
  rw [← Finset.mul_sum] at hupperSum
  have hzeroSum : (∑ k : ZMod N,
      if k = 0 then 625 * a ^ 2 * d ^ 2
      else 361 * a ^ 2 * ‖cyclicFinsetFourier S k‖ ^ 2) ≤
      625 * a ^ 2 * d ^ 2 +
        361 * a ^ 2 * (∑ k : ZMod N,
          ‖cyclicFinsetFourier S k‖ ^ 2) := by
    have hp (k : ZMod N) :
        (if k = 0 then 625 * a ^ 2 * d ^ 2
          else 361 * a ^ 2 * ‖cyclicFinsetFourier S k‖ ^ 2) ≤
        (if k = 0 then 625 * a ^ 2 * d ^ 2 else 0) +
          361 * a ^ 2 * ‖cyclicFinsetFourier S k‖ ^ 2 := by
      by_cases hk : k = 0 <;> simp [hk] <;> positivity
    have hs := Finset.sum_le_sum
      (fun k (_hk : k ∈ (Finset.univ : Finset (ZMod N))) => hp k)
    simp only [Finset.sum_add_distrib] at hs
    rw [← Finset.mul_sum] at hs
    simpa using hs
  rw [sum_norm_sq_cyclicFinsetFourier S] at hzeroSum
  have hupper : 625 * (∑ k : ZMod N,
      ‖cyclicFinsetFourier A k‖ ^ 2 *
        ‖cyclicFinsetFourier S k‖ ^ 2) ≤
      625 * a ^ 2 * d ^ 2 + 361 * a ^ 2 * n * d := by
    dsimp [n, d]
    nlinarith
  have hlowCorr : 625 * n * (a ^ 3 + e) ≤
      625 * n * (∑ x : ZMod N,
        (differenceOverlap A x).card * (differenceOverlap S x).card) +
      625 * n * a ^ 2 := by
    have hbase : a ^ 3 + e ≤
        (∑ x : ZMod N, (differenceOverlap A x).card *
          (differenceOverlap S x).card : ℕ) + a ^ 2 := by
      nlinarith
    have hc := mul_le_mul_of_nonneg_left hbase
      (show 0 ≤ 625 * n by positivity)
    nlinarith
  have hid : (∑ k : ZMod N,
      ‖cyclicFinsetFourier A k‖ ^ 2 *
        ‖cyclicFinsetFourier S k‖ ^ 2) =
      n * (∑ x : ZMod N, (differenceOverlap A x).card *
        (differenceOverlap S x).card) := by
    simpa [n] using hFourier
  nlinarith [hid]

/-- A coefficient larger than `19/25` puts more than `19/25` of the
character values in its positive open half-plane. -/
theorem nineteen_mul_card_lt_twentyfive_mul_positiveHalf
    (A : Finset (ZMod N)) (k : ZMod N)
    (hk : 361 * (A.card : ℝ) ^ 2 <
      625 * ‖cyclicFinsetFourier A k‖ ^ 2) :
    19 * A.card < 25 * (fourierPositiveHalf A k).card := by
  have hnorm : 19 * (A.card : ℝ) <
      25 * ‖cyclicFinsetFourier A k‖ := by
    have hn := norm_nonneg (cyclicFinsetFourier A k)
    have ha : 0 ≤ (A.card : ℝ) := by positivity
    nlinarith
  have hle := norm_fourier_le_card_positiveHalf A k
  exact_mod_cast (show (19 : ℝ) * A.card <
    25 * (fourierPositiveHalf A k).card by nlinarith)

end Erdos336
