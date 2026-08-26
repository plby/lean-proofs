import Mathlib

/-! # Polynomial comparisons for unbalanced sparse cuts -/

namespace Erdos1010.ChargeArithmetic

lemma affine_bound {r q r₀ q₀ a b c T W : ℤ} (hr : r₀ ≤ r) (hq : q ≤ r + q₀)
    (ha : 0 ≤ a) (hcoef : a + b ≤ T)
    (hbase : a * (r₀ + q₀) + b * r₀ + c ≤ T * r₀)
    (hW : W ≤ a * q + b * r + c) : W ≤ T * r := by
  have hq' := mul_le_mul_of_nonneg_left hq ha
  have hslack := mul_nonneg (sub_nonneg.mpr hr) (sub_nonneg.mpr hcoef)
  nlinarith

lemma unbalanced_large_s2 {r s D k q W : ℤ} (hs : 2 ≤ s) (hk : 1 ≤ k)
    (hD : 2 * k + 1 ≤ D) (hr : D + s ^ 2 + 2 ≤ r) (hq : q ≤ r + D + s ^ 2 - 1)
    (hW : k * W ≤ k * (k + s) * q + D * (D - 1)) : W ≤ r * (D + s ^ 2) := by
  let S := s - 2
  let a := D - 2 * k - 1
  have hS : 0 ≤ S := by dsimp [S]; omega
  have ha : 0 ≤ a := by dsimp [a]; omega
  have hk0 : 0 ≤ k - 1 := by omega
  have hk2 : 0 ≤ 2 * k ^ 2 + 4 * k - 1 := by nlinarith
  have hcoef : k * (k + s) + 0 ≤ k * (D + s ^ 2) := by
    have : 0 ≤ D + s ^ 2 - k - s := by nlinarith
    have := mul_nonneg (show 0 ≤ k by omega) this
    nlinarith
  have hbase : k * (k + s) * ((D + s ^ 2 + 2) + (D + s ^ 2 - 1)) +
      0 * (D + s ^ 2 + 2) + D * (D - 1) ≤ k * (D + s ^ 2) * (D + s ^ 2 + 2) := by
    have hid : k * (D + s ^ 2) * (D + s ^ 2 + 2) -
        (k * (k + s) * ((D + s ^ 2 + 2) + (D + s ^ 2 - 1)) + D * (D - 1)) =
        k * S ^ 4 + 6 * k * S ^ 3 + 2 * k * (a + k + 8) * S ^ 2 +
        k * (6 * a + 4 * k + 21) * S + a ^ 2 * (k - 1) +
        a * (2 * k ^ 2 + 4 * k - 1) + k ^ 2 + 11 * k := by dsimp [S, a]; ring
    have hp : 0 ≤ k * S ^ 4 + 6 * k * S ^ 3 + 2 * k * (a + k + 8) * S ^ 2 +
        k * (6 * a + 4 * k + 21) * S + a ^ 2 * (k - 1) +
        a * (2 * k ^ 2 + 4 * k - 1) + k ^ 2 + 11 * k := by positivity
    nlinarith only [hid, hp]
  have hb := affine_bound hr (by linarith : q ≤ r + (D + s ^ 2 - 1))
    (show 0 ≤ k * (k + s) by positivity) hcoef hbase (by simpa using hW)
  have hb' : k * W ≤ k * (r * (D + s ^ 2)) := by nlinarith only [hb]
  exact (mul_le_mul_iff_right₀ (show 0 < k by omega)).mp hb'

lemma unbalanced_equal_s2 {r s k q W : ℤ} (hs : 2 ≤ s) (hk : 1 ≤ k)
    (hr : 2 * k + s ^ 2 + 2 ≤ r) (hq : q ≤ r + 2 * k + s ^ 2 - 1)
    (hW : W ≤ (k + s) * q + 2 * k) : W ≤ r * (2 * k + s ^ 2) := by
  let S := s - 2
  have hS : 0 ≤ S := by dsimp [S]; omega
  have hcoef : k + s + 0 ≤ 2 * k + s ^ 2 := by nlinarith
  have hbase : (k + s) * ((2 * k + s ^ 2 + 2) + (2 * k + s ^ 2 - 1)) +
      0 * (2 * k + s ^ 2 + 2) + 2 * k ≤ (2 * k + s ^ 2) * (2 * k + s ^ 2 + 2) := by
    have hid : (2 * k + s ^ 2) * (2 * k + s ^ 2 + 2) -
        ((k + s) * ((2 * k + s ^ 2 + 2) + (2 * k + s ^ 2 - 1)) + 2 * k) =
        S ^ 4 + 6 * S ^ 3 + 2 * (k + 7) * S ^ 2 + (4 * k + 15) * S + k + 6 := by
      dsimp [S]; ring
    have hp : 0 ≤ S ^ 4 + 6 * S ^ 3 + 2 * (k + 7) * S ^ 2 + (4 * k + 15) * S + k + 6 := by positivity
    nlinarith only [hid, hp]
  have hb := affine_bound hr (by linarith : q ≤ r + (2 * k + s ^ 2 - 1))
    (show 0 ≤ k + s by omega) hcoef hbase (by simpa using hW)
  nlinarith only [hb]

lemma unbalanced_gap_single_s2 {r s k q W : ℤ} (hs : 2 ≤ s) (hk : 2 ≤ k)
    (hr : 2 * k - 1 + s ^ 2 + 2 ≤ r) (hq : q ≤ r + (2 * k - 1) + s ^ 2 - 1)
    (hW : W ≤ (k - 1 + s) * q + r + s - k + 3 * k - 2) :
    W ≤ r * (2 * k - 1 + s ^ 2) := by
  let S := s - 2
  have hS : 0 ≤ S := by dsimp [S]; omega
  have hcoef : (k - 1 + s) + 1 ≤ 2 * k - 1 + s ^ 2 := by nlinarith
  have hbase : (k - 1 + s) * ((2 * k - 1 + s ^ 2 + 2) + (2 * k - 1 + s ^ 2 - 1)) +
      1 * (2 * k - 1 + s ^ 2 + 2) + (s - k + 3 * k - 2) ≤
      (2 * k - 1 + s ^ 2) * (2 * k - 1 + s ^ 2 + 2) := by
    have hid : (2 * k - 1 + s ^ 2) * (2 * k - 1 + s ^ 2 + 2) -
        ((k - 1 + s) * ((2 * k - 1 + s ^ 2 + 2) + (2 * k - 1 + s ^ 2 - 1)) +
        (2 * k - 1 + s ^ 2 + 2) + (s - k + 3 * k - 2)) =
        S ^ 4 + 6 * S ^ 3 + (2 * k + 13) * S ^ 2 + 4 * (k + 3) * S + k + 3 := by
      dsimp [S]; ring
    have hp : 0 ≤ S ^ 4 + 6 * S ^ 3 + (2 * k + 13) * S ^ 2 + 4 * (k + 3) * S + k + 3 := by positivity
    nlinarith only [hid, hp]
  have hb := affine_bound hr (by linarith : q ≤ r + (2 * k - 1 + s ^ 2 - 1))
    (show 0 ≤ k - 1 + s by omega) hcoef hbase (by linarith : W ≤
      (k - 1 + s) * q + 1 * r + (s - k + 3 * k - 2))
  nlinarith only [hb]

lemma unbalanced_gap_double_s2 {r s k q W : ℤ} (hs : 2 ≤ s) (hk : 3 ≤ k)
    (hr : 2 * k - 1 + s ^ 2 + 2 ≤ r) (hq : q ≤ r + (2 * k - 1) + s ^ 2 - 1)
    (hW : W ≤ (s + 2) * q + (k - 2) * (2 * r - 2 * k - 1) + 2 * k - 2) :
    W ≤ r * (2 * k - 1 + s ^ 2) := by
  let S := s - 2
  have hS : 0 ≤ S := by dsimp [S]; omega
  have hk3 : 0 ≤ k - 3 := by omega
  have hcoef : (s + 2) + 2 * (k - 2) ≤ 2 * k - 1 + s ^ 2 := by nlinarith
  have hbase : (s + 2) * ((2 * k - 1 + s ^ 2 + 2) + (2 * k - 1 + s ^ 2 - 1)) +
      2 * (k - 2) * (2 * k - 1 + s ^ 2 + 2) + ((k - 2) * (-2 * k - 1) + 2 * k - 2) ≤
      (2 * k - 1 + s ^ 2) * (2 * k - 1 + s ^ 2 + 2) := by
    have hid : (2 * k - 1 + s ^ 2) * (2 * k - 1 + s ^ 2 + 2) -
        ((s + 2) * ((2 * k - 1 + s ^ 2 + 2) + (2 * k - 1 + s ^ 2 - 1)) +
        2 * (k - 2) * (2 * k - 1 + s ^ 2 + 2) + ((k - 2) * (-2 * k - 1) + 2 * k - 2)) =
        S ^ 4 + 6 * S ^ 3 + 2 * (k + 6) * S ^ 2 + (4 * k + 9) * S +
        2 * (k - 3) ^ 2 + 5 * (k - 3) + 4 := by dsimp [S]; ring
    have hp : 0 ≤ S ^ 4 + 6 * S ^ 3 + 2 * (k + 6) * S ^ 2 + (4 * k + 9) * S +
        2 * (k - 3) ^ 2 + 5 * (k - 3) + 4 := by positivity
    nlinarith only [hid, hp]
  have hb := affine_bound hr (by linarith : q ≤ r + (2 * k - 1 + s ^ 2 - 1))
    (show 0 ≤ s + 2 by omega) hcoef hbase (by nlinarith only [hW] : W ≤
      (s + 2) * q + 2 * (k - 2) * r + ((k - 2) * (-2 * k - 1) + 2 * k - 2))
  nlinarith only [hb]

lemma unbalanced_gap_double_two_s2 {r s q W : ℤ} (hs : 2 ≤ s)
    (hr : 3 + s ^ 2 + 2 ≤ r) (hq : q ≤ r + 3 + s ^ 2 - 1)
    (hW : W ≤ (s + 1) * q + 2 * r - 3) : W ≤ r * (3 + s ^ 2) := by
  let S := s - 2
  have hS : 0 ≤ S := by dsimp [S]; omega
  have hcoef : (s + 1) + 2 ≤ 3 + s ^ 2 := by nlinarith
  have hbase : (s + 1) * ((3 + s ^ 2 + 2) + (3 + s ^ 2 - 1)) +
      2 * (3 + s ^ 2 + 2) + (-3) ≤ (3 + s ^ 2) * (3 + s ^ 2 + 2) := by
    have hid : (3 + s ^ 2) * (3 + s ^ 2 + 2) -
        ((s + 1) * ((3 + s ^ 2 + 2) + (3 + s ^ 2 - 1)) + 2 * (3 + s ^ 2 + 2) - 3) =
        S ^ 4 + 6 * S ^ 3 + 16 * S ^ 2 + 17 * S + 3 := by dsimp [S]; ring
    have hp : 0 ≤ S ^ 4 + 6 * S ^ 3 + 16 * S ^ 2 + 17 * S + 3 := by positivity
    nlinarith only [hid, hp]
  have hb := affine_bound hr (by linarith : q ≤ r + (3 + s ^ 2 - 1))
    (show 0 ≤ s + 1 by omega) hcoef hbase (by linarith : W ≤ (s + 1) * q + 2 * r + (-3))
  nlinarith only [hb]

lemma unbalanced_dominant_s2 {r s k h q W : ℤ} (hs : 2 ≤ s) (hh : 1 ≤ h)
    (hhk : h ≤ k - 2) (hr : k + h + s ^ 2 + 2 ≤ r) (hq : q ≤ r + k + h + s ^ 2 - 1)
    (hW : W ≤ (h + 1 + s) * q + (k - h - 1) * (r + s - k) + k + h - 1) :
    W ≤ r * (k + h + s ^ 2) := by
  let S := s - 2
  let b := k - h - 2
  have hS : 0 ≤ S := by dsimp [S]; omega
  have hb : 0 ≤ b := by dsimp [b]; omega
  have hbh : 0 ≤ b + h - 1 := by omega
  have hcoef : (h + 1 + s) + (k - h - 1) ≤ k + h + s ^ 2 := by nlinarith
  have hbase : (h + 1 + s) * ((k + h + s ^ 2 + 2) + (k + h + s ^ 2 - 1)) +
      (k - h - 1) * (k + h + s ^ 2 + 2) + ((k - h - 1) * (s - k) + k + h - 1) ≤
      (k + h + s ^ 2) * (k + h + s ^ 2 + 2) := by
    have hid : (k + h + s ^ 2) * (k + h + s ^ 2 + 2) -
        ((h + 1 + s) * ((k + h + s ^ 2 + 2) + (k + h + s ^ 2 - 1)) +
        (k - h - 1) * (k + h + s ^ 2 + 2) + ((k - h - 1) * (s - k) + k + h - 1)) =
        S ^ 4 + 6 * S ^ 3 + (b + 2 * h + 15) * S ^ 2 + (b + 4 * h + 14) * S + b * (b + h - 1) := by
      dsimp [S, b]; ring
    have hp : 0 ≤ S ^ 4 + 6 * S ^ 3 + (b + 2 * h + 15) * S ^ 2 +
        (b + 4 * h + 14) * S + b * (b + h - 1) := by positivity
    nlinarith only [hid, hp]
  have hbound := affine_bound hr (by linarith : q ≤ r + (k + h + s ^ 2 - 1))
    (show 0 ≤ h + 1 + s by omega) hcoef hbase (by nlinarith only [hW] : W ≤
      (h + 1 + s) * q + (k - h - 1) * r + ((k - h - 1) * (s - k) + k + h - 1))
  nlinarith only [hbound]

lemma unbalanced_large_s1 {r D k q W : ℤ} (hk : 1 ≤ k) (hD : 2 * k + 2 ≤ D)
    (hr : D + 3 ≤ r) (hq : q ≤ r + D)
    (hW : k * W ≤ k * (k + 1) * q + D * (D - 1)) : W ≤ r * (D + 1) := by
  let a := D - 2 * k - 2
  have ha : 0 ≤ a := by dsimp [a]; omega
  have hk0 : 0 ≤ k - 1 := by omega
  have hk2 : 0 ≤ 2 * k ^ 2 + 2 * k - 3 := by nlinarith
  have hk3 : 0 ≤ k ^ 2 + 2 * k - 2 := by nlinarith
  have hcoef : k * (k + 1) + 0 ≤ k * (D + 1) := by
    have := mul_nonneg (show 0 ≤ k by omega) (show 0 ≤ D - k by omega)
    nlinarith
  have hbase : k * (k + 1) * (D + 3 + D) + 0 * (D + 3) + D * (D - 1) ≤ k * (D + 1) * (D + 3) := by
    have hid : k * (D + 1) * (D + 3) - (k * (k + 1) * (D + 3 + D) + D * (D - 1)) =
        a ^ 2 * (k - 1) + a * (2 * k ^ 2 + 2 * k - 3) + (k ^ 2 + 2 * k - 2) := by dsimp [a]; ring
    have hp : 0 ≤ a ^ 2 * (k - 1) + a * (2 * k ^ 2 + 2 * k - 3) + (k ^ 2 + 2 * k - 2) := by positivity
    nlinarith only [hid, hp]
  have hb := affine_bound hr hq (show 0 ≤ k * (k + 1) by positivity) hcoef hbase (by simpa using hW)
  have hb' : k * W ≤ k * (r * (D + 1)) := by nlinarith only [hb]
  exact (mul_le_mul_iff_right₀ (show 0 < k by omega)).mp hb'

lemma unbalanced_star_right {r s D q p W : ℤ} (hs : 1 ≤ s) (hD : 0 ≤ D)
    (hr : D + s ^ 2 + 2 ≤ r) (hq : q ≤ r + D + s ^ 2 - 1) (hp : p ≤ r - s - 1 - D)
    (hW : W ≤ D * p + s * q) : W ≤ r * (D + s ^ 2) := by
  have hp' := mul_le_mul_of_nonneg_left hp hD
  have hq' := mul_le_mul_of_nonneg_left hq (show 0 ≤ s by omega)
  have hrs : 0 ≤ r - s - 1 := by nlinarith
  have hs0 : 0 ≤ s - 1 := by omega
  have hgap : 0 ≤ s * (s - 1) * (r - s - 1) + D ^ 2 + D := by positivity
  nlinarith

lemma unbalanced_star_left_large {r s D q p W : ℤ} (hs : 1 ≤ s)
    (hD : 2 * s + 2 ≤ D) (hr : D + s ^ 2 + 2 ≤ r)
    (hq : q ≤ r + D + s ^ 2 - 1) (hp : p ≤ r + s - D)
    (hW : W ≤ (s + 2) * q + (D - 2 * s - 2) * p) : W ≤ r * (D + s ^ 2) := by
  let h := D - 2 * s - 2
  let u := r - (D + s ^ 2) - 2
  have hh : 0 ≤ h := by dsimp [h]; omega
  have hu : 0 ≤ u := by dsimp [u]; omega
  have hs3 : 0 ≤ s ^ 3 - 1 := by nlinarith [sq_nonneg (s - 1)]
  have hs4 : 0 ≤ s ^ 4 - s := by
    have := mul_nonneg (show 0 ≤ s by omega) hs3
    nlinarith only [this]
  have hid : r * (D + s ^ 2) -
      ((s + 2) * (r + D + s ^ 2 - 1) + (D - 2 * s - 2) * (r + s - D)) =
      h ^ 2 + h * s * (s + 1) + (s ^ 4 - s) + 2 * (s ^ 3 - 1) +
      2 * s ^ 2 + u * (s ^ 2 + s) := by dsimp [h, u]; ring
  have hpoly : 0 ≤ h ^ 2 + h * s * (s + 1) + (s ^ 4 - s) + 2 * (s ^ 3 - 1) +
      2 * s ^ 2 + u * (s ^ 2 + s) := by positivity
  have hp' := mul_le_mul_of_nonneg_left hp (show 0 ≤ D - 2 * s - 2 by omega)
  have hq' := mul_le_mul_of_nonneg_left hq (show 0 ≤ s + 2 by omega)
  nlinarith only [hid, hpoly, hp', hq', hW]

lemma unbalanced_star_left_small_s3 {r s D q W : ℤ} (hs : 3 ≤ s) (hD : 1 ≤ D)
    (hr : D + s ^ 2 + 2 ≤ r) (hq : q ≤ r + D + s ^ 2 - 1)
    (hW : W ≤ (s + 2) * q) : W ≤ r * (D + s ^ 2) := by
  let S := s - 3
  let d := D - 1
  have hS : 0 ≤ S := by dsimp [S]; omega
  have hd : 0 ≤ d := by dsimp [d]; omega
  have hcoef : s + 2 + 0 ≤ D + s ^ 2 := by nlinarith
  have hbase : (s + 2) * ((D + s ^ 2 + 2) + (D + s ^ 2 - 1)) +
      0 * (D + s ^ 2 + 2) + 0 ≤ (D + s ^ 2) * (D + s ^ 2 + 2) := by
    have hid : (D + s ^ 2) * (D + s ^ 2 + 2) -
        (s + 2) * ((D + s ^ 2 + 2) + (D + s ^ 2 - 1)) =
        d ^ 2 + d * (2 * s ^ 2 - 2 * s) +
        S ^ 4 + 10 * S ^ 3 + 36 * S ^ 2 + 51 * S + 15 := by dsimp [d, S]; ring
    have hsc : 0 ≤ 2 * s ^ 2 - 2 * s := by nlinarith
    have hp : 0 ≤ d ^ 2 + d * (2 * s ^ 2 - 2 * s) +
        S ^ 4 + 10 * S ^ 3 + 36 * S ^ 2 + 51 * S + 15 := by positivity
    nlinarith only [hid, hp]
  have hb := affine_bound hr (by linarith : q ≤ r + (D + s ^ 2 - 1))
    (show 0 ≤ s + 2 by omega) hcoef hbase (by simpa using hW)
  nlinarith only [hb]

lemma unbalanced_star_left_small_s2 {r D q W : ℤ} (hD : 3 ≤ D)
    (hr : D + 6 ≤ r) (hq : q ≤ r + D + 3) (hW : W ≤ 4 * q) : W ≤ r * (D + 4) := by
  have hq' := mul_le_mul_of_nonneg_left hq (by omega : (0 : ℤ) ≤ 4)
  have hslack := mul_nonneg (show 0 ≤ D by omega) (show 0 ≤ r - D - 6 by omega)
  have hpoly : 0 ≤ (D - 3) ^ 2 + 8 * (D - 3) + 3 := by positivity
  nlinarith

lemma unbalanced_star_one {r s q W : ℤ} (hs : 1 ≤ s) (hr : s ^ 2 + 3 ≤ r)
    (hq : q ≤ r + s ^ 2) (hW : W ≤ r - s - 2 + s * q) : W ≤ r * (1 + s ^ 2) := by
  have hq' := mul_le_mul_of_nonneg_left hq (show 0 ≤ s by omega)
  have hrs : 0 ≤ r - s - 1 := by nlinarith
  have hs0 : 0 ≤ s - 1 := by omega
  have hgap : 0 ≤ s * (s - 1) * (r - s - 1) + 2 := by positivity
  nlinarith

lemma unbalanced_star_two {r s q W : ℤ} (hs : 1 ≤ s) (hr : s ^ 2 + 4 ≤ r)
    (hq : q ≤ r + s ^ 2 + 1) (hW : W ≤ (s + 1) * q + 1) : W ≤ r * (2 + s ^ 2) := by
  have hs0 : 0 ≤ s - 1 := by omega
  have hcoef : s + 1 + 0 ≤ 2 + s ^ 2 := by nlinarith
  have hbase : (s + 1) * ((s ^ 2 + 4) + (s ^ 2 + 1)) + 0 * (s ^ 2 + 4) + 1 ≤
      (2 + s ^ 2) * (s ^ 2 + 4) := by
    have hid : (2 + s ^ 2) * (s ^ 2 + 4) - ((s + 1) * ((s ^ 2 + 4) + (s ^ 2 + 1)) + 1) =
        (s - 1) * (s ^ 2 * (s - 1) + (3 * s - 2)) := by ring
    have hs3 : 0 ≤ 3 * s - 2 := by omega
    have hp : 0 ≤ (s - 1) * (s ^ 2 * (s - 1) + (3 * s - 2)) := by positivity
    nlinarith only [hid, hp]
  have hb := affine_bound hr (by linarith : q ≤ r + (s ^ 2 + 1))
    (show 0 ≤ s + 1 by omega) hcoef hbase (by simpa using hW)
  nlinarith only [hb]

lemma unbalanced_near_large_s1 {r k q W : ℤ} (hk : 1 ≤ k) (hr : 2 * k + 4 ≤ r)
    (hq : q ≤ r + 2 * k + 1) (hW : W ≤ (k + 1) * q + 2 * k + 4) :
    W ≤ r * (2 * k + 2) := by
  have hq' := mul_le_mul_of_nonneg_left hq (show 0 ≤ k + 1 by omega)
  have hslack := mul_nonneg (show 0 ≤ k + 1 by omega) (show 0 ≤ r - 2 * k - 4 by omega)
  nlinarith

lemma unbalanced_equal_s1 {r k q W : ℤ} (hk : 0 ≤ k) (hr : 2 * k + 3 ≤ r)
    (hq : q ≤ r + 2 * k) (hW : W ≤ (k + 1) * q + k) : W ≤ r * (2 * k + 1) := by
  have hq' := mul_le_mul_of_nonneg_left hq (show 0 ≤ k + 1 by omega)
  have hslack := mul_nonneg hk (show 0 ≤ r - 2 * k - 3 by omega)
  nlinarith

lemma unbalanced_gap_left_s1 {r k q W : ℤ} (hk : 1 ≤ k) (hr : 2 * k + 2 ≤ r)
    (hq : q ≤ r + 2 * k - 1) (hW : W ≤ k * q + 2 * k - 1) : W ≤ r * (2 * k) := by
  have hq' := mul_le_mul_of_nonneg_left hq (show 0 ≤ k by omega)
  have hslack := mul_nonneg (show 0 ≤ k by omega) (show 0 ≤ r - 2 * k - 2 by omega)
  nlinarith

lemma unbalanced_gap_right_s1 {r k q p W : ℤ} (hk : 2 ≤ k) (hr : 2 * k + 2 ≤ r)
    (hq : q ≤ r + 2 * k - 1) (hp : p ≤ r - k - 2)
    (hW : W ≤ k * q + p + 2 * k - 1) : W ≤ r * (2 * k) := by
  have hq' := mul_le_mul_of_nonneg_left hq (show 0 ≤ k by omega)
  have hslack := mul_nonneg (show 0 ≤ k - 1 by omega) (show 0 ≤ r - 2 * k - 2 by omega)
  nlinarith

lemma unbalanced_dominant_left_s1 {r k h q p W : ℤ} (hh : 1 ≤ h) (hhk : h + 3 ≤ k)
    (hr : k + h + 3 ≤ r) (hq : q ≤ r + k + h) (hp : p ≤ r + 1 - k)
    (hW : W ≤ (h + 2) * q + (k - h - 3) * p + k + h - 1) :
    W ≤ r * (k + h + 1) := by
  let b := k - h - 3
  have hb : 0 ≤ b := by dsimp [b]; omega
  have hp' := mul_le_mul_of_nonneg_left hp (show 0 ≤ k - h - 3 by omega)
  have hq' := mul_le_mul_of_nonneg_left hq (show 0 ≤ h + 2 by omega)
  have hslack := mul_nonneg (show 0 ≤ h + 2 by omega) (show 0 ≤ r - k - h - 3 by omega)
  have hid : r * (k + h + 1) - ((h + 2) * (r + k + h) +
      (k - h - 3) * (r + 1 - k) + k + h - 1) =
      b ^ 2 + b * h + b + h + 4 + (h + 2) * (r - k - h - 3) := by dsimp [b]; ring
  have hpoly : 0 ≤ b ^ 2 + b * h + b + h + 4 := by positivity
  nlinarith only [hid, hpoly, hslack, hp', hq', hW]

lemma unbalanced_dominant_right_s1 {r k h q p W : ℤ} (hh : 1 ≤ h) (hhk : h + 2 ≤ k)
    (hr : k + h + 3 ≤ r) (hq : q ≤ r + k + h) (hp : p ≤ r - k - 2)
    (hW : W ≤ (h + 1) * q + (k - h) * p + h) : W ≤ r * (k + h + 1) := by
  let b := k - h - 2
  have hb : 0 ≤ b := by dsimp [b]; omega
  have hp' := mul_le_mul_of_nonneg_left hp (show 0 ≤ k - h by omega)
  have hq' := mul_le_mul_of_nonneg_left hq (show 0 ≤ h + 1 by omega)
  have hslack := mul_nonneg (show 0 ≤ h by omega) (show 0 ≤ r - k - h - 3 by omega)
  have hid : r * (k + h + 1) - ((h + 1) * (r + k + h) + (k - h) * (r - k - 2) + h) =
      b ^ 2 + b * h + 5 * b + 2 * h + 6 + h * (r - k - h - 3) := by dsimp [b]; ring
  have hpoly : 0 ≤ b ^ 2 + b * h + 5 * b + 2 * h + 6 := by positivity
  nlinarith only [hid, hpoly, hslack, hp', hq', hW]

lemma unbalanced_dominant_edge_s1 {r k q W : ℤ} (hk : 1 ≤ k) (hr : 2 * k + 1 ≤ r)
    (hq : q ≤ r + 2 * k - 2) (hW : W ≤ k * q + k - 1) : W ≤ r * (2 * k - 1) := by
  have hq' := mul_le_mul_of_nonneg_left hq (show 0 ≤ k by omega)
  have hgap := mul_nonneg (show 0 ≤ k - 1 by omega) (show 0 ≤ r - 2 * k - 1 by omega)
  nlinarith

lemma unbalanced_double_s1 {r k q pA pB W : ℤ} (hk : 4 ≤ k) (hr : 2 * k + 2 ≤ r)
    (hq : q ≤ r + 2 * k - 1) (hpA : pA ≤ r + 1 - k) (hpB : pB ≤ r - k - 2)
    (hW : W ≤ 3 * q + (k - 4) * pA + (k - 2) * pB + 2 * k - 2) :
    W ≤ r * (2 * k) := by
  have hpa := mul_le_mul_of_nonneg_left hpA (show 0 ≤ k - 4 by omega)
  have hpb := mul_le_mul_of_nonneg_left hpB (show 0 ≤ k - 2 by omega)
  have hpoly : 0 ≤ 2 * (k - 4) ^ 2 + 9 * (k - 4) + 15 := by positivity
  nlinarith

end Erdos1010.ChargeArithmetic
