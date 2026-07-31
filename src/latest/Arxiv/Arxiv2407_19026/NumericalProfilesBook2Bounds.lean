import Arxiv.Arxiv2407_19026.NumericalProfilesBook2Certificate

/-!
# Semantic bound for the second numerical-profile book interval

The analytic lower bound is positive because its exact degree-83 numerator has
strictly positive Bernstein coefficients on `[1 / 10, 1 / 2]`.
-/

namespace Arxiv2407_19026
namespace NumericalProfilesBook2Bounds

noncomputable section

open NumericalProfilesBook2Certificate

private def bookTwoDen (z : ℝ) : ℝ :=
  let V := beta0VLarge z
  let X := 1 - z * V
  let W := V - 1 / 100000
  let Z := z + 2
  let S : ℝ :=
    2 * decimalNat [10500000, 0, 0, 0, 0, 0]
  let B₁ := 3 * Z ^ 3
  let Bₓ := 30 * X * (X + 1) ^ 3
  let Bᵥ := 3 * (W + 1) ^ 3
  S * (2 * B₁ * Bₓ * Bᵥ)

private def logLowerBelowTwoClosed (x : ℝ) : ℝ :=
  (x - 1) *
    (3 * x ^ 4 + 68 * x ^ 3 + 98 * x ^ 2 +
      68 * x + 3) /
    (30 * x * (x + 1) ^ 3)

private def logLowerAboveTwoClosed (x : ℝ) : ℝ :=
  2 * (x - 1) *
    (3 * (x + 1) ^ 2 + (x - 1) ^ 2) /
    (3 * (x + 1) ^ 3)

private lemma log_lower_above_two_closed {x : ℝ}
    (hxplus : x + 1 ≠ 0) :
    logLowerAboveTwo x = logLowerAboveTwoClosed x := by
  dsimp [logLowerAboveTwo, logLowerAboveTwoClosed]
  field_simp [hxplus]

private lemma log_lower_below_two_closed {x : ℝ}
    (hx : 0 < x) :
    logLowerBelowTwoSharp x =
      logLowerBelowTwoClosed x := by
  have hxplus : 0 < x + 1 := by linarith
  let y : ℝ := (1 - x) / (1 + x)
  have hysquare : 0 < 1 - y ^ 2 := by
    rw [show
      1 - y ^ 2 = 4 * x / (1 + x) ^ 2 by
        dsimp [y]
        field_simp [hxplus.ne']
        ring]
    positivity
  dsimp [logLowerBelowTwoSharp,
    logLowerBelowTwoClosed, y]
  field_simp [hx.ne', hxplus.ne', hysquare.ne']
  ring_nf
  field_simp [hx.ne']
  ring

private def bookTwoCleared (z : ℝ) : ℝ :=
  let V := beta0VLarge z
  let X := 1 - z * V
  let W := V - 1 / 100000
  let Z := z + 2
  let S : ℝ :=
    2 * decimalNat [10500000, 0, 0, 0, 0, 0]
  let entropyNumerator :=
    2 * z * (3 * Z ^ 2 + z ^ 2)
  let belowNumerator :=
    (X - 1) *
      (3 * X ^ 4 + 68 * X ^ 3 + 98 * X ^ 2 +
        68 * X + 3)
  let aboveNumerator :=
    2 * (W - 1) *
      (3 * (W + 1) ^ 2 + (W - 1) ^ 2)
  let B₁ := 3 * Z ^ 3
  let Bₓ := 30 * X * (X + 1) ^ 3
  let Bᵥ := 3 * (W + 1) ^ 3
  S *
    (2 * (1 + z) * entropyNumerator * Bₓ * Bᵥ +
      2 * beta0CorrectionLower z * B₁ * Bₓ * Bᵥ +
      belowNumerator * B₁ * Bᵥ -
      z ^ 2 * B₁ * Bₓ * Bᵥ +
      z * aboveNumerator * B₁ * Bₓ)

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

set_option maxHeartbeats 0 in
-- Normalizing the exact degree-83 rational identity exceeds the default heartbeat budget.
set_option maxRecDepth 20000 in
-- The expanded identity also exceeds the default simplifier recursion depth.
private lemma beta0_book_lower_two_pos {z : ℝ}
    (hz : z ∈ Set.Ioc (1 / 10 : ℝ) (1 / 2)) :
    0 < beta0BookLowerTwo z := by
  let u : ℝ := (10 * z - 1) / 4
  have hu : u ∈ Set.Icc (0 : ℝ) 1 := by
    dsimp [u]
    constructor <;> nlinarith [hz.1, hz.2]
  have hsum := bernstein_sum_pos 83
    bookTwoBernsteinCoeffs hu (by
      norm_num [bookTwoBernsteinCoeffs, decimalNat]) (by
      norm_num [bookTwoBernsteinCoeffs, decimalNat])
  have hzunit : z ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> nlinarith [hz.1, hz.2]
  have hcut : ¬z ≤ 3 / 1000 := by
    norm_num at hz ⊢
    linarith [hz.1]
  have hVarg := beta0_vlarge_book2_log_argument
    ⟨le_of_lt hz.1, hz.2⟩
  have hXlower := Beta0Affine.x_lower z hzunit
  have hX :
      (1 / 5 : ℝ) ≤ 1 - z * beta0VLarge z := by
    simpa [beta0PolynomialX, beta0V, if_neg hcut] using hXlower
  have hzplus : 0 < z + 2 := by nlinarith [hz.1]
  have hWplus :
      0 < beta0VLarge z - 1 / 100000 + 1 := by
    linarith
  have hXpos : 0 < 1 - z * beta0VLarge z := by
    linarith
  have hXplus :
      0 < (1 - z * beta0VLarge z) + 1 := by
    linarith
  have hden : 0 < bookTwoDen z := by
    have hS :
        (0 : ℝ) <
          2 * decimalNat
            [10500000, 0, 0, 0, 0, 0] := by
      norm_num [decimalNat]
    dsimp [bookTwoDen]
    positivity
  have hEntropyPlus : 1 + z + 1 ≠ 0 := by
    linarith
  have hid :
      beta0BookLowerTwo z =
        ((∑ i ∈ Finset.range 84,
          (bookTwoBernsteinCoeffs.getD i 0 : ℝ) *
            u ^ i * (1 - u) ^ (83 - i)) /
          bookTwoScale) /
          bookTwoDen z := by
    apply (eq_div_iff hden.ne').2
    calc
      beta0BookLowerTwo z * bookTwoDen z =
          bookTwoCleared z := by
        dsimp only [beta0BookLowerTwo]
        rw [log_lower_above_two_closed hEntropyPlus,
          log_lower_below_two_closed hXpos,
          log_lower_above_two_closed hWplus.ne']
        dsimp [bookTwoDen, bookTwoCleared,
          logLowerAboveTwoClosed,
          logLowerBelowTwoClosed]
        generalize
          beta0VLarge z - 1 / 100000 = W at hWplus ⊢
        generalize
          1 - z * beta0VLarge z = X at hXpos hXplus ⊢
        field_simp [hEntropyPlus, hzplus.ne',
          hWplus.ne', hXpos.ne', hXplus.ne']
        ring
      _ = bookTwoPower bookTwoPowerCoeffs z := by
        dsimp [bookTwoCleared, beta0CorrectionLower,
          expNegUpper, KernelBounds.expNegTaylor9,
          KernelBounds.expNegError10, beta0VLarge,
          bookTwoPower, bookTwoPowerCoeffs,
          decimalNat]
        norm_num [Nat.factorial]
        ring
      _ = _ := by
        have hBernstein :
            Polynomial.eval₂ (Int.castRingHom ℝ) u
                bookTwoBernsteinPolynomial =
              ∑ i ∈ Finset.range 84,
                (bookTwoBernsteinCoeffs.getD i 0 : ℝ) *
                  u ^ i * (1 - u) ^ (83 - i) := by
          dsimp [bookTwoBernsteinPolynomial]
          change
            (Polynomial.eval₂RingHom (Int.castRingHom ℝ) u)
                (∑ i ∈ Finset.range 84,
                  (bookTwoBernsteinCoeffs.getD i 0 :
                      Polynomial ℤ) *
                    Polynomial.X ^ i *
                      ((1 : Polynomial ℤ) - Polynomial.X) ^
                        (83 - i)) =
              _
          simp [Polynomial.eval₂_pow]
        have hpoly := congrArg
          (Polynomial.eval₂ (Int.castRingHom ℝ) u)
          book_two_polynomial_identity
        have hzFromU :
            ((1 + 4 * u) / 10 : ℝ) = z := by
          dsimp [u]
          ring
        have hhom :=
          eval₂_bookTwoHomogenized bookTwoPowerCoeffs u
        change
          Polynomial.eval₂ (Int.castRingHom ℝ) u
                (bookTwoHomogenized bookTwoPowerCoeffs) *
              10 =
            10 ^ 84 *
              bookTwoPower bookTwoPowerCoeffs
                ((1 + 4 * u) / 10) at hhom
        rw [hzFromU] at hhom
        have hhom' :
            Polynomial.eval₂ (Int.castRingHom ℝ) u
                (bookTwoHomogenized bookTwoPowerCoeffs) =
              10 ^ 83 *
                bookTwoPower bookTwoPowerCoeffs z := by
          apply mul_right_cancel₀
            (by norm_num : (10 : ℝ) ≠ 0)
          calc
            _ = 10 ^ 84 *
                bookTwoPower bookTwoPowerCoeffs z := hhom
            _ = _ := by ring
        simp only [Polynomial.eval₂_mul,
          Polynomial.eval₂_pow,
          Polynomial.eval₂_ofNat] at hpoly
        rw [hBernstein, hhom'] at hpoly
        rw [eq_div_iff (by
          norm_num [bookTwoScale, decimalNat] :
            (bookTwoScale : ℝ) ≠ 0)]
        apply mul_left_cancel₀
          (by positivity : (10 : ℝ) ^ 83 ≠ 0)
        calc
          _ = (bookTwoScale : ℝ) *
              (10 ^ 83 *
                bookTwoPower bookTwoPowerCoeffs z) := by
            ring
          _ = _ := by
            simpa using hpoly
  rw [hid]
  exact div_pos
    (div_pos hsum (by
      norm_num [bookTwoScale, decimalNat]))
    hden

/-- Positivity of the second numerical-profile book interval. -/
lemma beta0_polynomial_book_margin_pos_two :
    ∀ z ∈ Set.Ioc (1 / 10 : ℝ) (1 / 2),
      0 < beta0PolynomialBookMargin z := by
  intro z hz
  exact (beta0_book_lower_two_pos hz).trans_le
    (beta0_book_lower_two_le hz)

end

end NumericalProfilesBook2Bounds
end Arxiv2407_19026
