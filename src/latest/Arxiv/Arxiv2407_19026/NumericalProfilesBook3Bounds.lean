import Arxiv.Arxiv2407_19026.NumericalProfilesBook3PowerSemantics

/-!
# Semantic bound for the third numerical-profile book interval

The analytic lower bound is positive because its exact degree-116 numerator has
strictly positive Bernstein coefficients on `[1 / 2, 1]`.
-/

namespace Arxiv2407_19026
namespace NumericalProfilesBook3Bounds

noncomputable section

open NumericalProfilesBook3Certificate

private def bookThreeDen (z : ℝ) : ℝ :=
  let V := beta0VLarge z
  let X := 1 - z * V
  let W := V - 1 / 100000
  let Z := z + 2
  let K : ℝ :=
    decimalNat [15000, 0, 0, 0, 0, 0, 0, 0]
  let B₁ := 105 * Z ^ 7
  let Bₓ := 420 * X * (X + 1) ^ 5
  let Bᵥ := 600 * W * (W + 1) ^ 3
  K * (2 * B₁ * Bₓ * Bᵥ)

private def logLowerAboveFourClosed (x : ℝ) : ℝ :=
  let t := x - 1
  let p := x + 1
  2 *
    (105 * t * p ^ 6 + 35 * t ^ 3 * p ^ 4 +
      21 * t ^ 5 * p ^ 2 + 15 * t ^ 7) /
    (105 * p ^ 7)

private def logLowerBelowThreeClosed (x : ℝ) : ℝ :=
  let t := 1 - x
  let p := 1 + x
  (-2) *
    (28 * x *
        (15 * t * p ^ 4 + 5 * t ^ 3 * p ^ 2 +
          3 * t ^ 5) +
      15 * t ^ 7) /
    (420 * x * p ^ 5)

private def logLowerNearOneClosed (x : ℝ) : ℝ :=
  let t := x - 1
  let p := x + 1
  2 *
    (200 * x * (3 * t * p ^ 2 + t ^ 3) -
      21 * t ^ 4 * p) /
    (600 * x * p ^ 3)

private lemma log_lower_above_four_closed {x : ℝ}
    (hxplus : x + 1 ≠ 0) :
    logLowerAboveFour x =
      logLowerAboveFourClosed x := by
  dsimp [logLowerAboveFour,
    logLowerAboveFourClosed]
  field_simp [hxplus]
  ring

private lemma log_lower_below_three_closed {x : ℝ}
    (hx : 0 < x) :
    logLowerBelowThreeSharp x =
      logLowerBelowThreeClosed x := by
  have hxplus : 0 < x + 1 := by linarith
  let y : ℝ := (1 - x) / (1 + x)
  have hysquare : 0 < 1 - y ^ 2 := by
    rw [show
      1 - y ^ 2 = 4 * x / (1 + x) ^ 2 by
        dsimp [y]
        field_simp [hxplus.ne']
        ring]
    positivity
  dsimp [logLowerBelowThreeSharp,
    logLowerBelowThreeClosed, y]
  field_simp [hx.ne', hxplus.ne', hysquare.ne']
  ring_nf
  field_simp [hx.ne']
  ring

private lemma log_lower_near_one_closed {x : ℝ}
    (hx : 0 < x) :
    logLowerNearOne x = logLowerNearOneClosed x := by
  have hxplus : 0 < x + 1 := by linarith
  let y : ℝ := (x - 1) / (x + 1)
  have hysquare : 0 < 1 - y ^ 2 := by
    rw [show
      1 - y ^ 2 = 4 * x / (x + 1) ^ 2 by
        dsimp [y]
        field_simp [hxplus.ne']
        ring]
    positivity
  dsimp [logLowerNearOne,
    logLowerNearOneClosed, y]
  field_simp [hx.ne', hxplus.ne', hysquare.ne']
  ring_nf
  field_simp [hx.ne']
  ring

private lemma book_three_clear_identity
    (z onePlus entropy correction below above b₁ bₓ bᵥ k : ℝ)
    (hb₁ : b₁ ≠ 0) (hbₓ : bₓ ≠ 0) (hbᵥ : bᵥ ≠ 0) :
    (onePlus * (entropy / b₁) + correction +
        (below / bₓ - z ^ 2 + z * (above / bᵥ)) / 2) *
        (k * (2 * b₁ * bₓ * bᵥ)) =
      k *
        (2 * onePlus * entropy * bₓ * bᵥ +
          2 * correction * b₁ * bₓ * bᵥ +
          below * b₁ * bᵥ - z ^ 2 * b₁ * bₓ * bᵥ +
          z * above * b₁ * bₓ) := by
  field_simp [hb₁, hbₓ, hbᵥ]
  ring

private lemma bernstein_sum_pos
    (n : ℕ) (coeffs : List ℕ) {z : ℝ}
    (hz : z ∈ Set.Icc 0 1)
    (hfirst : 0 < coeffs.getD 0 0)
    (hlast : 0 < coeffs.getD n 0) :
    0 < ∑ i ∈ Finset.range (n + 1),
      (coeffs.getD i 0 : ℝ) * z ^ i *
        (1 - z) ^ (n - i) := by
  have hterm (i : ℕ) :
      0 ≤ (coeffs.getD i 0 : ℝ) * z ^ i *
        (1 - z) ^ (n - i) :=
    mul_nonneg
      (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hz.1 _))
      (pow_nonneg (sub_nonneg.mpr hz.2) _)
  by_cases hhalf : z ≤ 1 / 2
  · have hone : 0 < 1 - z := by linarith
    have hzero :
        0 < (coeffs.getD 0 0 : ℝ) * z ^ 0 *
          (1 - z) ^ (n - 0) := by
      norm_num
      exact mul_pos (Nat.cast_pos.mpr hfirst)
        (pow_pos hone n)
    exact hzero.trans_le (Finset.single_le_sum
      (fun i _ => hterm i) (by simp))
  · have hzpos : 0 < z := by linarith
    have hn :
        0 < (coeffs.getD n 0 : ℝ) * z ^ n *
          (1 - z) ^ (n - n) := by
      norm_num
      exact mul_pos (Nat.cast_pos.mpr hlast)
        (pow_pos hzpos n)
    exact hn.trans_le (Finset.single_le_sum
      (fun i _ => hterm i) (by simp))

private lemma beta0_book_lower_three_pos {z : ℝ}
    (hz : z ∈ Set.Ioc (1 / 2 : ℝ) 1) :
    0 < beta0BookLowerThree z := by
  let u : ℝ := 2 * z - 1
  have hu : u ∈ Set.Icc (0 : ℝ) 1 := by
    dsimp [u]
    constructor <;> nlinarith [hz.1, hz.2]
  have hsum := bernstein_sum_pos 116
    bookThreeBernsteinCoeffs hu (by
      norm_num [bookThreeBernsteinCoeffs, decimalNat]) (by
      norm_num [bookThreeBernsteinCoeffs, decimalNat])
  have hzunit : z ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> nlinarith [hz.1, hz.2]
  have hcut : ¬z ≤ 3 / 1000 := by
    norm_num at hz ⊢
    linarith [hz.1]
  have hWbounds := beta0_vlarge_book3_near_one
    ⟨le_of_lt hz.1, hz.2⟩
  have hXlower := Beta0Affine.x_lower z hzunit
  have hX :
      (1 / 5 : ℝ) ≤ 1 - z * beta0VLarge z := by
    simpa [beta0PolynomialX, beta0V, if_neg hcut] using hXlower
  have hzplus : 0 < z + 2 := by nlinarith [hz.1]
  have hWplus :
      0 < beta0VLarge z - 1 / 100000 + 1 := by
    linarith [hWbounds.1]
  have hWpos :
      0 < beta0VLarge z - 1 / 100000 := by
    linarith [hWbounds.1]
  have hXpos : 0 < 1 - z * beta0VLarge z := by
    linarith
  have hXplus :
      0 < (1 - z * beta0VLarge z) + 1 := by
    linarith
  have hden : 0 < bookThreeDen z := by
    have hK :
        (0 : ℝ) <
          decimalNat
            [15000, 0, 0, 0, 0, 0, 0, 0] := by
      norm_num [decimalNat]
    dsimp [bookThreeDen]
    positivity
  have hEntropyPlus : 1 + z + 1 ≠ 0 := by
    linarith
  have hid :
      beta0BookLowerThree z =
        ((∑ i ∈ Finset.range 117,
          (bookThreeBernsteinCoeffs.getD i 0 : ℝ) *
            u ^ i * (1 - u) ^ (116 - i)) /
          bookThreeScale) /
          bookThreeDen z := by
    apply (eq_div_iff hden.ne').2
    calc
      beta0BookLowerThree z * bookThreeDen z =
          bookThreeCleared z := by
        dsimp only [beta0BookLowerThree]
        rw [log_lower_above_four_closed hEntropyPlus,
          log_lower_below_three_closed hXpos,
          log_lower_near_one_closed hWpos]
        dsimp [bookThreeDen, bookThreeCleared,
          logLowerAboveFourClosed,
          logLowerBelowThreeClosed,
          logLowerNearOneClosed]
        generalize beta0CorrectionLower z = C at ⊢
        generalize
          beta0VLarge z - 1 / 100000 = W at hWpos hWplus ⊢
        generalize
          1 - z * beta0VLarge z = X at hXpos hXplus ⊢
        have hzSub : 1 + z - 1 = z := by ring
        have hzAdd : 1 + z + 1 = z + 2 := by ring
        have hXAdd : 1 + X = X + 1 := by ring
        rw [hzSub, hzAdd, hXAdd]
        apply book_three_clear_identity
        · positivity
        · positivity
        · positivity
      _ = bookThreePower bookThreePowerCoeffs z :=
        book_three_cleared_eq_power z
      _ = _ := by
        have hidentity := book_three_bernstein_identity u
        have hzFromU :
            ((1 + u) / 2 : ℝ) = z := by
          dsimp [u]
          ring
        rw [hzFromU] at hidentity
        rw [eq_div_iff (by
          norm_num [bookThreeScale, decimalNat] :
            (bookThreeScale : ℝ) ≠ 0)]
        simpa [mul_comm] using hidentity
  rw [hid]
  exact div_pos
    (div_pos hsum (by
      norm_num [bookThreeScale, decimalNat]))
    hden

/-- Positivity of the third numerical-profile book interval. -/
lemma beta0_polynomial_book_margin_pos_three :
    ∀ z ∈ Set.Ioc (1 / 2 : ℝ) 1,
      0 < beta0PolynomialBookMargin z := by
  intro z hz
  exact (beta0_book_lower_three_pos hz).trans_le
    (beta0_book_lower_three_le hz)

end

end NumericalProfilesBook3Bounds
end Arxiv2407_19026
