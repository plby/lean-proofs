import ErdosProblems.Erdos67.MRRealCenteredTwoLength

/-!
# Prefix-mean reduction for the real MR long average

The Lipschitz lemma used in the real-valued Matomäki--Radziwiłł argument is
proved in the source in two stages.  Its analytic stage is the uniform
stability of positive prefix means on a fixed multiplicative scale (equation
(13) there), with a `log X ^ (-1/4)` error.  The elementary stage subtracts
two such prefixes across an interval of length at least
`X / log X ^ (1/5)`, losing one factor `log X ^ (1/5)`.

This file formalizes that elementary stage without an asymptotic or a hidden
local-mean hypothesis.  Thus the remaining analytic input is exactly the
Granville--Soundararajan prefix-mean comparison, rather than the desired
short-interval conclusion.
-/

open scoped BigOperators
open Finset

namespace Erdos67

noncomputable section

/-- Sum over the positive integers at most `N`, written using a range so that
differences of two prefixes reduce directly to `Finset.sum_Ico_eq_sub`. -/
def positivePrefixSum (a : ℕ → ℂ) (N : ℕ) : ℂ :=
  (∑ n ∈ Finset.range (N + 1), a n) - a 0

/-- The normalized positive prefix mean. -/
def positivePrefixMean (a : ℕ → ℂ) (N : ℕ) : ℂ :=
  positivePrefixSum a N / (N : ℂ)

theorem sum_Ioc_eq_positivePrefixSum_sub
    (a : ℕ → ℂ) {A B : ℕ} (hAB : A ≤ B) :
    (∑ n ∈ Finset.Ioc A B, a n) =
      positivePrefixSum a B - positivePrefixSum a A := by
  rw [← Finset.Ico_add_one_add_one_eq_Ioc]
  rw [Finset.sum_Ico_eq_sub a (by omega)]
  unfold positivePrefixSum
  ring

theorem positivePrefixSum_eq_mul_positivePrefixMean
    (a : ℕ → ℂ) {N : ℕ} (hN : 0 < N) :
    positivePrefixSum a N = (N : ℂ) * positivePrefixMean a N := by
  unfold positivePrefixMean
  have hNC : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp

/-- A normalized translated interval average is the difference of its two
normalized positive prefixes, with the endpoint weights left explicit. -/
theorem normalizedShortAverage_eq_positivePrefixMeans
    (a : ℕ → ℂ) {x H : ℕ} (hx : 0 < x) (hH : 0 < H) :
    (∑ j ∈ Finset.Icc 1 H, a (x + j)) / (H : ℂ) =
      (((x + H : ℕ) : ℂ) * positivePrefixMean a (x + H) -
        (x : ℂ) * positivePrefixMean a x) / (H : ℂ) := by
  rw [sum_Icc_add_eq_sum_Ioc]
  rw [sum_Ioc_eq_positivePrefixSum_sub a (by omega)]
  rw [positivePrefixSum_eq_mul_positivePrefixMean a (by omega),
    positivePrefixSum_eq_mul_positivePrefixMean a hx]

/-- The reference mean on `(X,2X]` is the corresponding difference of
positive prefix means. -/
theorem longIntervalMean_eq_positivePrefixMeans
    (a : ℕ → ℂ) {X : ℕ} (hX : 0 < X) :
    longIntervalMean a X =
      2 * positivePrefixMean a (2 * X) - positivePrefixMean a X := by
  unfold longIntervalMean
  rw [sum_Ioc_eq_positivePrefixSum_sub a (by omega)]
  rw [positivePrefixSum_eq_mul_positivePrefixMean a (by omega),
    positivePrefixSum_eq_mul_positivePrefixMean a hX]
  have hXC : (X : ℂ) ≠ 0 := by exact_mod_cast hX.ne'
  field_simp
  push_cast
  ring

/-- Exact algebraic decomposition behind the source deduction of Lemma 4
from its prefix-mean estimate (13). -/
theorem normalizedShortAverage_sub_longIntervalMean_eq_prefixErrors
    (a : ℕ → ℂ) {X x H : ℕ} (hX : 0 < X) (hx : 0 < x)
    (hH : 0 < H) (mu : ℂ) :
    (∑ j ∈ Finset.Icc 1 H, a (x + j)) / (H : ℂ) -
        longIntervalMean a X =
      (((x + H : ℕ) : ℂ) / (H : ℂ)) *
          (positivePrefixMean a (x + H) - mu) -
        ((x : ℂ) / (H : ℂ)) * (positivePrefixMean a x - mu) -
        2 * (positivePrefixMean a (2 * X) - mu) +
        (positivePrefixMean a X - mu) := by
  rw [normalizedShortAverage_eq_positivePrefixMeans a hx hH,
    longIntervalMean_eq_positivePrefixMeans a hX]
  have hHC : (H : ℂ) ≠ 0 := by exact_mod_cast hH.ne'
  field_simp
  push_cast
  ring

/-- A uniform prefix-mean error on `[X,3X]` gives the pointwise local-mean
stability needed by the centered two-length reduction.  The factor `8X/H`
is the precise elementary loss used to turn exponent `1/4` into `1/20` at
`H = X / log(X)^(1/5)`. -/
theorem norm_normalizedShortAverage_sub_longIntervalMean_le_of_prefixStable
    (a : ℕ → ℂ) {X x H : ℕ} (hX : 0 < X)
    (hx : x ∈ Finset.Ioc X (2 * X)) (hH : 0 < H) (hHX : H ≤ X)
    {mu : ℂ} {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    (hstable : ∀ Z : ℕ, X ≤ Z → Z ≤ 3 * X →
      ‖positivePrefixMean a Z - mu‖ ≤ epsilon) :
    ‖(∑ j ∈ Finset.Icc 1 H, a (x + j)) / (H : ℂ) -
        longIntervalMean a X‖ ≤
      8 * (X : ℝ) / (H : ℝ) * epsilon := by
  have hxBounds := Finset.mem_Ioc.mp hx
  have hxpos : 0 < x := hX.trans hxBounds.1
  rw [normalizedShortAverage_sub_longIntervalMean_eq_prefixErrors
    a hX hxpos hH mu]
  have hX3 : X ≤ 3 * X := by omega
  have h2Xlow : X ≤ 2 * X := by omega
  have h2Xhigh : 2 * X ≤ 3 * X := by omega
  have hxlow : X ≤ x := hxBounds.1.le
  have hxhigh : x ≤ 3 * X := hxBounds.2.trans (by omega)
  have hxhLow : X ≤ x + H := hxlow.trans (Nat.le_add_right x H)
  have hxhHigh : x + H ≤ 3 * X := by omega
  have hEX := hstable X le_rfl hX3
  have hE2X := hstable (2 * X) h2Xlow h2Xhigh
  have hEx := hstable x hxlow hxhigh
  have hExh := hstable (x + H) hxhLow hxhHigh
  have hHR : (0 : ℝ) < H := by exact_mod_cast hH
  have hXR : (0 : ℝ) < X := by exact_mod_cast hX
  have hxR : (x : ℝ) ≤ 2 * X := by exact_mod_cast hxBounds.2
  have hxhR : ((x + H : ℕ) : ℝ) ≤ 3 * X := by exact_mod_cast hxhHigh
  have hratio : (1 : ℝ) ≤ (X : ℝ) / H := by
    rw [le_div_iff₀ hHR]
    norm_num
    exact_mod_cast hHX
  have hxhDiv : ((x + H : ℕ) : ℝ) / H ≤ 3 * (X : ℝ) / H :=
    div_le_div_of_nonneg_right hxhR hHR.le
  have hxhDiv' : ((x : ℝ) + H) / H ≤ 3 * (X : ℝ) / H := by
    simpa only [Nat.cast_add] using hxhDiv
  have hxDiv : (x : ℝ) / H ≤ 2 * (X : ℝ) / H :=
    div_le_div_of_nonneg_right hxR hHR.le
  calc
    ‖(((x + H : ℕ) : ℂ) / (H : ℂ)) *
          (positivePrefixMean a (x + H) - mu) -
        ((x : ℂ) / (H : ℂ)) * (positivePrefixMean a x - mu) -
        2 * (positivePrefixMean a (2 * X) - mu) +
        (positivePrefixMean a X - mu)‖ ≤
      ‖(((x + H : ℕ) : ℂ) / (H : ℂ)) *
          (positivePrefixMean a (x + H) - mu)‖ +
        ‖((x : ℂ) / (H : ℂ)) * (positivePrefixMean a x - mu)‖ +
        ‖2 * (positivePrefixMean a (2 * X) - mu)‖ +
        ‖positivePrefixMean a X - mu‖ := by
      calc
        _ ≤ ‖(((x + H : ℕ) : ℂ) / (H : ℂ)) *
                (positivePrefixMean a (x + H) - mu) -
              ((x : ℂ) / (H : ℂ)) * (positivePrefixMean a x - mu) -
              2 * (positivePrefixMean a (2 * X) - mu)‖ +
              ‖positivePrefixMean a X - mu‖ := norm_add_le _ _
        _ ≤ (‖(((x + H : ℕ) : ℂ) / (H : ℂ)) *
                (positivePrefixMean a (x + H) - mu) -
              ((x : ℂ) / (H : ℂ)) * (positivePrefixMean a x - mu)‖ +
              ‖2 * (positivePrefixMean a (2 * X) - mu)‖) +
              ‖positivePrefixMean a X - mu‖ := by gcongr; exact norm_sub_le _ _
        _ ≤ ((‖(((x + H : ℕ) : ℂ) / (H : ℂ)) *
                (positivePrefixMean a (x + H) - mu)‖ +
              ‖((x : ℂ) / (H : ℂ)) *
                (positivePrefixMean a x - mu)‖) +
              ‖2 * (positivePrefixMean a (2 * X) - mu)‖) +
              ‖positivePrefixMean a X - mu‖ := by gcongr; exact norm_sub_le _ _
        _ = _ := by ring
    _ ≤ ((3 * (X : ℝ) / H) * epsilon) +
          ((2 * (X : ℝ) / H) * epsilon) + 2 * epsilon + epsilon := by
      rw [norm_mul, norm_div, Complex.norm_natCast, Complex.norm_natCast,
        norm_mul, norm_div, Complex.norm_natCast, Complex.norm_natCast,
        norm_mul]
      norm_num
      exact add_le_add
        (add_le_add (add_le_add
          (mul_le_mul hxhDiv' hExh (norm_nonneg _) (by positivity))
          (mul_le_mul hxDiv hEx (norm_nonneg _) (by positivity)))
          (mul_le_mul_of_nonneg_left hE2X (by norm_num))) hEX
    _ ≤ 8 * (X : ℝ) / H * epsilon := by
      have hepsRatio : epsilon ≤ ((X : ℝ) / H) * epsilon := by
        simpa using mul_le_mul_of_nonneg_right hratio hepsilon
      calc
        3 * (X : ℝ) / H * epsilon + 2 * (X : ℝ) / H * epsilon +
              2 * epsilon + epsilon =
            5 * ((X : ℝ) / H) * epsilon + 3 * epsilon := by ring
        _ ≤ 5 * ((X : ℝ) / H) * epsilon +
              3 * (((X : ℝ) / H) * epsilon) := by
          exact add_le_add le_rfl
            (mul_le_mul_of_nonneg_left hepsRatio (by norm_num))
        _ = 8 * (X : ℝ) / H * epsilon := by ring

/-- Pointwise prefix stability implies the centered long mean-square bound
with no further analytic input. -/
theorem centeredNormalizedShortAverageMeanSquare_le_of_prefixStable
    (a : ℕ → ℂ) {X H : ℕ} (hX : 0 < X) (hH : 0 < H) (hHX : H ≤ X)
    {mu : ℂ} {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    (hstable : ∀ Z : ℕ, X ≤ Z → Z ≤ 3 * X →
      ‖positivePrefixMean a Z - mu‖ ≤ epsilon) :
    centeredNormalizedShortAverageMeanSquare a X H ≤
      (X : ℝ) * (8 * (X : ℝ) / (H : ℝ) * epsilon) ^ 2 := by
  unfold centeredNormalizedShortAverageMeanSquare
  calc
    (∑ x ∈ Finset.Ioc X (2 * X),
        Complex.normSq
          ((∑ j ∈ Finset.Icc 1 H, a (x + j)) / (H : ℂ) -
            longIntervalMean a X)) ≤
      ∑ _x ∈ Finset.Ioc X (2 * X),
        (8 * (X : ℝ) / (H : ℝ) * epsilon) ^ 2 := by
      apply Finset.sum_le_sum
      intro x hx
      rw [Complex.normSq_eq_norm_sq]
      exact sq_le_sq₀ (norm_nonneg _) (by positivity) |>.2
        (norm_normalizedShortAverage_sub_longIntervalMean_le_of_prefixStable
          a hX hx hH hHX hepsilon hstable)
    _ = (X : ℝ) * (8 * (X : ℝ) / (H : ℝ) * epsilon) ^ 2 := by
      simp only [Finset.sum_const, card_Ioc_self_two_mul, nsmul_eq_mul]

/-- Source-ready centered two-length join whose only near-zero analytic
input is prefix-mean stability.  Both dyadic Perron differences remain
explicit for the compiled near/medium/far estimates. -/
theorem shortIntervalMeanSquare_le_twoDyadicTwoLength_add_prefixStable
    (a : ℕ → ℂ) {X H₁ H₂ : ℕ}
    (hX : 0 < X) (hH₁ : 0 < H₁) (hH₂ : 0 < H₂)
    (hH₁X : H₁ ≤ X) (hH₂X : H₂ ≤ X)
    {mu : ℂ} {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    (hstable : ∀ Z : ℕ, X ≤ Z → Z ≤ 3 * X →
      ‖positivePrefixMean a Z - mu‖ ≤ epsilon) :
    shortIntervalMeanSquare a X H₁ ≤
      4 * (H₁ : ℝ) ^ 2 *
        (dyadicTwoLengthShortMeanSquareAt
            (Finset.Ioc X (2 * X)) a X X H₁ H₂ +
          dyadicTwoLengthShortMeanSquareAt
            (Finset.Ioc (2 * X) (4 * X)) a (2 * X) X H₁ H₂) +
      2 * (H₁ : ℝ) ^ 2 *
        ((X : ℝ) * (8 * (X : ℝ) / (H₂ : ℝ) * epsilon) ^ 2) := by
  have hbase := shortIntervalMeanSquare_le_twoDyadicTwoLength_add_centeredLong
    a hH₁ hH₂ hH₁X hH₂X
  have hcenter := centeredNormalizedShortAverageMeanSquare_le_of_prefixStable
    a hX hH₂ hH₂X hepsilon hstable
  exact hbase.trans (by gcongr)

end

end Erdos67
