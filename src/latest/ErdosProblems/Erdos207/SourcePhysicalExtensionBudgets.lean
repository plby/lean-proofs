/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.RegularizationInputPowerScalars

/-! # Physical exponent gaps discharge the source-extension hypotheses -/

namespace Erdos207

open scoped NNReal

theorem source_auxiliary_extension_power
    (t n p z y : ℝ≥0) (q j b v D : ℕ) (ht : 1 ≤ t) (hy : 1 ≤ y)
    (hp : 1/t^b ≤ p) (hz : z ≤ t^v) (hn : t^D ≤ n)
    (hj : j ≤ q) (hgap : 3*b*(q-3)+v ≤ D) :
    z ≤ y*p^(3*(j-3))*n := by
  have hgap' : b*(3*(j-3))+v ≤ D := by
    have hs := Nat.mul_le_mul_left (3*b) (Nat.sub_le_sub_right hj 3)
    nlinarith only [hs, hgap]
  have hm := inversePower_density_ge_power t p n b (3*(j-3)) v D ht hp hgap' hn
  calc
    z ≤ t^v := hz
    _ ≤ p^(3*(j-3))*n := hm
    _ ≤ _ := by simpa only [one_mul, mul_assoc] using
      mul_le_mul_of_nonneg_right hy (show 0 ≤ p^(3*(j-3))*n from zero_le)

theorem source_left_extension_power
    (t n p r z y : ℝ≥0) (b reserveExp v L : ℕ) (ht : 1 ≤ t) (hy : 1 ≤ y)
    (hp : 1/t^b ≤ p) (hr : 1/t^reserveExp ≤ r) (hz : z ≤ t^v) (hn : t^L ≤ n)
    (hgap : 2*reserveExp+3*b+v ≤ L) : z ≤ y*r^2*p^3*n := by
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hm : t^v ≤ r^2*p^3*n := by
    calc
      _ ≤ n/t^(2*reserveExp+3*b) := powerRatio_ge_power t n _ v L ht hgap hn
      _ = (1/t^reserveExp)^2*(1/t^b)^3*n := by
        simp only [pow_add, pow_mul, div_pow, one_pow]
        field_simp
        ring
      _ ≤ _ := by gcongr
  have hmul : r^2*p^3*n ≤ y*r^2*p^3*n := by
    simpa only [one_mul, mul_assoc] using
      (mul_le_mul_of_nonneg_right hy (show 0 ≤ r^2*p^3*n from zero_le))
  exact (hz.trans hm).trans hmul

theorem source_future_quasi_extension_power
    (t n p z y : ℝ≥0) (b h L : ℕ) (ht : 1 ≤ t) (hy : 1 ≤ y)
    (hp : 1/t^b ≤ p) (hz : z ≤ t) (hn : t^L ≤ n)
    (hgap : b*(h+1)+1 ≤ L) : z ≤ y*p^(h+1)*n := by
  have hm : t ≤ p^(h+1)*n := by
    simpa only [pow_one] using inversePower_density_ge_power t p n b (h+1) 1 L ht hp hgap hn
  have hmul : p^(h+1)*n ≤ y*p^(h+1)*n := by
    simpa only [one_mul, mul_assoc] using
      (mul_le_mul_of_nonneg_right hy (show 0 ≤ p^(h+1)*n from zero_le))
  exact (hz.trans hm).trans hmul

theorem source_auxiliary_gap_of_marked_gap
    (q b reserveExp v D : ℕ) (hreserve : b ≤ reserveExp)
    (hmarked : v+(q+1)*(1+v+reserveExp+2*b)+2 ≤ D-v) :
    3*b*(q-3)+v ≤ D := by
  have hinner : 3*b ≤ 1+v+reserveExp+2*b := by omega
  have hprod := Nat.mul_le_mul hinner (show q-3 ≤ q+1 by omega)
  have hDv : D-v ≤ D := Nat.sub_le _ _
  nlinarith only [hprod, hmarked, hDv]

end Erdos207
