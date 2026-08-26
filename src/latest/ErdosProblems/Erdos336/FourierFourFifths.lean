import ErdosProblems.Erdos336.RefinedOverlapEnergy

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos336

open scoped Pointwise BigOperators ComplexConjugate

/-- Pure arithmetic margin behind the `4/5` Fourier coefficient. -/
lemma fourier_four_fifths_arithmetic
    (a d e u n : ℝ)
    (ha : 62 ≤ a) (hda : 2 * a ≤ d) (hd : 4 * d < 9 * a)
    (hu : 4 * u ≤ a ^ 2) (he : a ^ 4 ≤ d * e)
    (hn : 12000 * (d - 1) ≤ n)
    (he0 : 0 ≤ e) :
    16 * n * a ^ 2 * d + 25 * a ^ 2 * d ^ 2 +
        25 * n * (2 * a ^ 2 + u) <
      25 * n * (a ^ 3 + e + a * d) := by
  have ha0 : 0 < a := by linarith
  have hd2 : 2 ≤ d := by nlinarith
  have hn6 : 6000 * d ≤ n := by nlinarith
  have hn0 : 0 < n := by nlinarith
  have hde : 4 * d * e ≤ 9 * a * e :=
    mul_le_mul_of_nonneg_right (le_of_lt hd) he0
  have haeMul : a * (4 * a ^ 3) ≤ a * (9 * e) := by nlinarith
  have hae : 4 * a ^ 3 ≤ 9 * e :=
    le_of_mul_le_mul_left haeMul ha0
  have hDmul : 4 * (3841 * a ^ 2 * d) ≤
      9 * (3841 * a ^ 3) := by
    have h := mul_le_mul_of_nonneg_left (le_of_lt hd)
      (show 0 ≤ 3841 * a ^ 2 by positivity)
    nlinarith
  have hEmul : 8000 * a ^ 3 ≤ 18000 * e := by nlinarith
  have hUmul : 6000 * u ≤ 1500 * a ^ 2 := by nlinarith
  have hDlow : 12000 * a ^ 2 ≤ 6000 * a * d := by nlinarith
  have hlarge : 18000 * a ^ 2 < 293 * a ^ 3 := by
    have h293 : 18000 < 293 * a := by nlinarith
    have h := mul_lt_mul_of_pos_right h293 (show 0 < a ^ 2 by positivity)
    nlinarith
  have hbase :
      3841 * a ^ 2 * d + 6000 * (2 * a ^ 2 + u) <
        6000 * (a ^ 3 + e + a * d) := by
    nlinarith
  have hzero : 25 * a ^ 2 * d ^ 2 ≤
      (1 / 240 : ℝ) * n * a ^ 2 * d := by
    have h := mul_le_mul_of_nonneg_right hn6
      (show 0 ≤ a ^ 2 * d by positivity)
    nlinarith
  have hbase' :
      16 * a ^ 2 * d + (1 / 240 : ℝ) * a ^ 2 * d +
          25 * (2 * a ^ 2 + u) <
        25 * (a ^ 3 + e + a * d) := by
    nlinarith
  have hmul := mul_lt_mul_of_pos_left hbase' hn0
  nlinarith

variable {N : ℕ} [NeZero N]

/-- A sparse, fully expanding strict-`9/4` set of size at least 62 has a
nonzero Fourier coefficient strictly larger than four fifths of its size.
The proof uses the corrected quarter-square difference bound, so it does not
rely on Lev's false unique-difference lemma. -/
theorem exists_nonzero_fourier_gt_four_fifths
    (A : Finset (ZMod N))
    (hcard : 62 ≤ A.card)
    (hdoub : 4 * (A + A).card < 9 * A.card)
    (hsparse : 12000 * ((A + A).card - 1) ≤ N)
    (hexpand : ∀ B : Finset (ZMod N), B ⊆ A → 2 ≤ B.card →
      A.card + B.card ≤ (A + B).card) :
    ∃ k : ZMod N, k ≠ 0 ∧
      16 * (A.card : ℝ) ^ 2 <
        25 * ‖cyclicFinsetFourier A k‖ ^ 2 := by
  by_contra hno
  push_neg at hno
  let S := A + A
  let a : ℝ := A.card
  let d : ℝ := S.card
  let e : ℝ := A.addEnergy A
  let u : ℝ := singletonOverlapCount A
  let n : ℝ := N
  have ha : 62 ≤ a := by
    dsimp [a]
    exact_mod_cast hcard
  have hA2 : 2 ≤ A.card := by omega
  have hdaNat : 2 * A.card ≤ S.card := by
    simpa [S, two_mul] using hexpand A (by simp) hA2
  have hda : 2 * a ≤ d := by
    dsimp [a, d]
    exact_mod_cast hdaNat
  have hd : 4 * d < 9 * a := by
    dsimp [a, d, S]
    exact_mod_cast hdoub
  have huNat : 4 * singletonOverlapCount A ≤ A.card ^ 2 :=
    four_mul_singletonOverlapCount_le_sq A (by omega) hdoub
  have hu : 4 * u ≤ a ^ 2 := by
    dsimp [u, a]
    exact_mod_cast huNat
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
  have harith := fourier_four_fifths_arithmetic a d e u n
    ha hda hd hu he hn he0
  have hrefNat := refined_overlap_lower_bound A hexpand
  have href :
      a ^ 3 + e + a * d ≤
        (overlapSigma A : ℝ) + 2 * a ^ 2 + u := by
    dsimp [a, d, e, u, S]
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
        (if k = 0 then 25 * a ^ 2 * d ^ 2
         else 16 * a ^ 2 * ‖cyclicFinsetFourier S k‖ ^ 2) := by
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
      if k = 0 then 25 * a ^ 2 * d ^ 2
      else 16 * a ^ 2 * ‖cyclicFinsetFourier S k‖ ^ 2) ≤
      25 * a ^ 2 * d ^ 2 +
        16 * a ^ 2 * (∑ k : ZMod N,
          ‖cyclicFinsetFourier S k‖ ^ 2) := by
    have hp (k : ZMod N) :
        (if k = 0 then 25 * a ^ 2 * d ^ 2
          else 16 * a ^ 2 * ‖cyclicFinsetFourier S k‖ ^ 2) ≤
        (if k = 0 then 25 * a ^ 2 * d ^ 2 else 0) +
          16 * a ^ 2 * ‖cyclicFinsetFourier S k‖ ^ 2 := by
      by_cases hk : k = 0 <;> simp [hk] <;> positivity
    have hs := Finset.sum_le_sum
      (fun k (_hk : k ∈ (Finset.univ : Finset (ZMod N))) => hp k)
    simp only [Finset.sum_add_distrib] at hs
    rw [← Finset.mul_sum] at hs
    simpa using hs
  rw [sum_norm_sq_cyclicFinsetFourier S] at hzeroSum
  have hupper : 25 * (∑ k : ZMod N,
      ‖cyclicFinsetFourier A k‖ ^ 2 *
        ‖cyclicFinsetFourier S k‖ ^ 2) ≤
      25 * a ^ 2 * d ^ 2 + 16 * a ^ 2 * n * d := by
    dsimp [n, d]
    nlinarith
  have hNpos : 0 < n := by
    dsimp [n]
    exact_mod_cast (NeZero.pos N)
  have hlowCorr :
      25 * n * (a ^ 3 + e + a * d) ≤
        25 * n * (∑ x : ZMod N,
          (differenceOverlap A x).card *
            (differenceOverlap S x).card) +
          25 * n * (2 * a ^ 2 + u) := by
    have hbaseCorr : a ^ 3 + e + a * d ≤
        (∑ x : ZMod N, (differenceOverlap A x).card *
          (differenceOverlap S x).card : ℕ) + 2 * a ^ 2 + u := by
      nlinarith
    have hc := mul_le_mul_of_nonneg_left hbaseCorr
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
