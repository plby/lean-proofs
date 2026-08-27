import Arxiv.Arxiv2411_18291.FiniteGeneratorCoefficient

/-! # The full generator coefficient fits the paper's assembly budget

Keeping the binomial and power factors together bounds the complete palette
coefficient by `(4*q)^(6*q)`. The direct assembly theorem therefore needs no
additional coefficient-dependent size threshold.
-/

namespace Arxiv2411_18291

theorem paperGeneratorCoefficientUpperBound_factor (q r h : ℕ) :
    paperGeneratorCoefficientUpperBound q r h =
      (6 * q.choose r + 4) * (paperColourTrialCount q r (2 * q) * h + 1) * 2 ^ q := by
  unfold paperGeneratorCoefficientUpperBound paperPaletteUpperBound
  ring

theorem paperGeneratorCoefficientUpperBound_product {q r : ℕ} (hqr : r + 1 < q) :
    paperGeneratorCoefficientUpperBound q (r + 1)
        (3 * (2 * q) ^ (r + 1) * (q.choose (r + 1)) ^ 2) + 1 ≤
      207360 * (2 * q + 1) * ((2 * q) ^ (r + 1)) ^ 2 *
        (q.choose (r + 1)) ^ 5 * 2 ^ q := by
  let k := q.choose (r + 1)
  let a := (2 * q) ^ (r + 1)
  let X := 5184 * (2 * q + 1) * a ^ 2 * k ^ 4
  have hq : 0 < q := by omega
  have hk : 1 ≤ k := Nat.choose_pos hqr.le
  have ha : 0 < a := by dsimp only [a]; positivity
  have hX : 1 ≤ X := Nat.succ_le_of_lt (by dsimp only [X]; positivity)
  have hfactor : paperGeneratorCoefficientUpperBound q (r + 1) (3 * a * k ^ 2) =
      (6 * k + 4) * (X + 1) * 2 ^ q := by
    rw [paperGeneratorCoefficientUpperBound_factor]
    dsimp only [paperColourTrialCount, paperInverseAlpha, X, a, k]
    ring
  have hpos := paperGeneratorCoefficientUpperBound_pos q (r + 1) (3 * a * k ^ 2)
  calc
    _ ≤ 2 * paperGeneratorCoefficientUpperBound q (r + 1) (3 * a * k ^ 2) := by
      calc
        _ ≤ paperGeneratorCoefficientUpperBound q (r + 1) (3 * a * k ^ 2) +
            paperGeneratorCoefficientUpperBound q (r + 1) (3 * a * k ^ 2) :=
          Nat.add_le_add_left hpos _
        _ = _ := (two_mul _).symm
    _ = 2 * ((6 * k + 4) * (X + 1) * 2 ^ q) := by rw [hfactor]
    _ ≤ 2 * ((10 * k) * (2 * X) * 2 ^ q) :=
      Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right (2 ^ q)
        (Nat.mul_le_mul (by omega) (by omega)))
    _ = _ := by dsimp only [X, a, k]; ring

theorem paperGeneratorCoefficientUpperBound_six_q {q r : ℕ} (hqr : r + 1 < q) :
    paperGeneratorCoefficientUpperBound q (r + 1)
        (3 * (2 * q) ^ (r + 1) * (q.choose (r + 1)) ^ 2) + 1 ≤
      (4 * q) ^ (6 * q) := by
  have hq2 : 2 ≤ q := by omega
  by_cases hq : 4 ≤ q
  · have hb : 1 ≤ 4 * q := by omega
    have hc : 207360 ≤ (4 * q) ^ 5 := by
      calc
        _ ≤ 16 ^ 5 := by norm_num
        _ ≤ _ := Nat.pow_le_pow_left (by omega) 5
    have hfront : 207360 * (2 * q + 1) ≤ (4 * q) ^ 6 := by
      calc
        _ ≤ (4 * q) ^ 5 * (4 * q) := Nat.mul_le_mul hc (by omega)
        _ = _ := (pow_succ _ 5).symm
    have hk : (q.choose (r + 1)) ^ 5 * 2 ^ q ≤ 64 ^ q := by
      calc
        _ ≤ (2 ^ q) ^ 5 * 2 ^ q :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (Nat.choose_le_two_pow _ _) 5)
        _ = (2 ^ q) ^ 6 := (pow_succ _ 5).symm
        _ = _ := by rw [← pow_mul, Nat.mul_comm q 6, pow_mul]; norm_num
    have ha : ((2 * q) ^ (r + 1)) ^ 2 ≤ ((2 * q) ^ 2) ^ q := by
      calc
        _ ≤ ((2 * q) ^ q) ^ 2 :=
          Nat.pow_le_pow_left (Nat.pow_le_pow_right (by omega) hqr.le) 2
        _ = _ := by rw [← pow_mul, Nat.mul_comm q 2, pow_mul]
    have hbase : (2 * q) ^ 2 * 64 ≤ (4 * q) ^ 3 := by
      have hh := Nat.mul_le_mul_left (q ^ 2) hq
      nlinarith only [hh]
    have hback : ((2 * q) ^ (r + 1)) ^ 2 *
        ((q.choose (r + 1)) ^ 5 * 2 ^ q) ≤ (4 * q) ^ (3 * q) := by
      calc
        _ ≤ ((2 * q) ^ 2) ^ q * 64 ^ q := Nat.mul_le_mul ha hk
        _ = ((2 * q) ^ 2 * 64) ^ q := (mul_pow _ _ _).symm
        _ ≤ ((4 * q) ^ 3) ^ q := Nat.pow_le_pow_left hbase q
        _ = _ := (pow_mul _ _ _).symm
    calc
      _ ≤ 207360 * (2 * q + 1) * ((2 * q) ^ (r + 1)) ^ 2 *
          (q.choose (r + 1)) ^ 5 * 2 ^ q :=
        paperGeneratorCoefficientUpperBound_product hqr
      _ = (207360 * (2 * q + 1)) *
          (((2 * q) ^ (r + 1)) ^ 2 * ((q.choose (r + 1)) ^ 5 * 2 ^ q)) := by ring
      _ ≤ (4 * q) ^ 6 * (4 * q) ^ (3 * q) := Nat.mul_le_mul hfront hback
      _ = (4 * q) ^ (6 + 3 * q) := (pow_add _ _ _).symm
      _ ≤ _ := Nat.pow_le_pow_right hb (by omega)
  · have hr : r ≤ 1 := by omega
    interval_cases q <;> interval_cases r <;>
      norm_num [paperGeneratorCoefficientUpperBound, paperPaletteUpperBound,
        paperColourTrialCount, paperInverseAlpha] at *

theorem paperIntegralGeneratorCoefficient_six_q
    {W : Type*} [Fintype W] [DecidableEq W] {q r : ℕ} (hqr : r + 1 < q)
    (S : ExchangeSystem W q (r + 1)) (P : Block W q)
    (hqh : q.choose (r + 1) ≤ S.graph.card)
    (hS : S.graph.card ≤ 3 * (2 * q) ^ (r + 1) * (q.choose (r + 1)) ^ 2) :
    paperIntegralGeneratorCoefficient S P + 1 ≤ (4 * q : ℝ) ^ (6 * q) := by
  have hc := paperIntegralGeneratorCoefficient_le hqr S P (hqh.trans hS) hS
  have hb : (paperGeneratorCoefficientUpperBound q (r + 1)
      (3 * (2 * q) ^ (r + 1) * (q.choose (r + 1)) ^ 2) : ℝ) + 1 ≤
      (4 * q : ℝ) ^ (6 * q) := by
    exact_mod_cast paperGeneratorCoefficientUpperBound_six_q hqr
  linarith only [hc, hb]

end Arxiv2411_18291
