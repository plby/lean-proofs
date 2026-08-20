/-
Copyright 2026 The Lean-Proofs Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import ErdosProblems.Erdos722.NibbleFinite
import Mathlib

/-!
# Scalar finite-difference bounds for the nibble profiles

The profile verification repeatedly uses the two one-step estimates

`m h (x-h)^(m-1) ≤ x^m-(x-h)^m ≤ m h x^(m-1)`.

They are proved here directly from Bernoulli's inequality and Mathlib's
power Lipschitz estimate, including the exponent-zero cases.
-/

namespace Erdos722.NibbleProfileAlgebra

noncomputable section

lemma mul_pow_pred_le_pow_sub_pow
    {x h : ℝ} (m : ℕ) (hh : 0 ≤ h) (hhx : h ≤ x) :
    (m : ℝ) * h * (x - h) ^ (m - 1) ≤
      x ^ m - (x - h) ^ m := by
  have hy : 0 ≤ x - h := sub_nonneg.mpr hhx
  have htwo : 0 ≤ 2 * (x - h) + h := by positivity
  have hb := pow_add_mul_le_add_pow hy htwo m
  have heq : x - h + h = x := by ring
  rw [heq] at hb
  nlinarith

lemma pow_sub_pow_le_mul_pow_pred
    {x h : ℝ} (m : ℕ) (hh : 0 ≤ h) (hhx : h ≤ x) :
    x ^ m - (x - h) ^ m ≤
      (m : ℝ) * h * x ^ (m - 1) := by
  have hx : 0 ≤ x := hh.trans hhx
  have hy : 0 ≤ x - h := sub_nonneg.mpr hhx
  have hmono : (x - h) ^ m ≤ x ^ m :=
    pow_le_pow_left₀ hy (sub_le_self x hh) m
  have habs := abs_pow_sub_pow_le (a := x) (b := x - h) (n := m)
  rw [abs_of_nonneg (sub_nonneg.mpr hmono)] at habs
  have hdiff : |x - (x - h)| = h := by
    rw [show x - (x - h) = h by ring, abs_of_nonneg hh]
  have hyx : x - h ≤ x := sub_le_self x hh
  have hmax : max |x| |x - h| = x := by
    rw [abs_of_nonneg hx, abs_of_nonneg hy, max_eq_left hyx]
  rw [hdiff, hmax] at habs
  nlinarith

lemma pow_sub_pow_nonneg
    {x h : ℝ} (m : ℕ) (hh : 0 ≤ h) (hhx : h ≤ x) :
    0 ≤ x ^ m - (x - h) ^ m := by
  have : (x - h) ^ m ≤ x ^ m := by
    gcongr
    linarith
  linarith

/-- Upper finite difference for `D (x^m + A x^(m-1))`. -/
lemma upper_profile_sub_next_le
    {A D x h : ℝ} (m : ℕ)
    (hA : 0 ≤ A) (hD : 0 ≤ D) (hh : 0 ≤ h) (hhx : h ≤ x) :
    D * (x ^ m + A * x ^ (m - 1)) -
        D * ((x - h) ^ m + A * (x - h) ^ (m - 1)) ≤
      D * ((m : ℝ) * h * x ^ (m - 1) +
        A * ((m - 1 : ℕ) : ℝ) * h * x ^ (m - 2)) := by
  have hmain := pow_sub_pow_le_mul_pow_pred m hh hhx
  have herr := pow_sub_pow_le_mul_pow_pred (m - 1) hh hhx
  have hexp : m - 1 - 1 = m - 2 := by omega
  rw [hexp] at herr
  have hscaled := mul_le_mul_of_nonneg_left herr hA
  have hscaled' :
      A * (x ^ (m - 1) - (x - h) ^ (m - 1)) ≤
        A * ((m - 1 : ℕ) : ℝ) * h * x ^ (m - 2) := by
    calc
      _ ≤ A * (((m - 1 : ℕ) : ℝ) * h * x ^ (m - 2)) := hscaled
      _ = _ := by ring
  calc
    D * (x ^ m + A * x ^ (m - 1)) -
        D * ((x - h) ^ m + A * (x - h) ^ (m - 1)) =
      D * ((x ^ m - (x - h) ^ m) +
        A * (x ^ (m - 1) - (x - h) ^ (m - 1))) := by ring
    _ ≤ D * ((m : ℝ) * h * x ^ (m - 1) +
        A * ((m - 1 : ℕ) : ℝ) * h * x ^ (m - 2)) :=
      mul_le_mul_of_nonneg_left (add_le_add hmain hscaled') hD

/-- Lower finite difference for `D (x^m - A x^(m-1))`. -/
lemma lower_profile_sub_next_ge
    {A D x h : ℝ} (m : ℕ)
    (hA : 0 ≤ A) (hD : 0 ≤ D) (hh : 0 ≤ h) (hhx : h ≤ x) :
    D * ((m : ℝ) * h * (x - h) ^ (m - 1) -
        A * ((m - 1 : ℕ) : ℝ) * h * x ^ (m - 2)) ≤
      D * (x ^ m - A * x ^ (m - 1)) -
        D * ((x - h) ^ m - A * (x - h) ^ (m - 1)) := by
  have hmain := mul_pow_pred_le_pow_sub_pow m hh hhx
  have herr := pow_sub_pow_le_mul_pow_pred (m - 1) hh hhx
  have hexp : m - 1 - 1 = m - 2 := by omega
  rw [hexp] at herr
  have hscaled := mul_le_mul_of_nonneg_left herr hA
  have hscaled' :
      A * (x ^ (m - 1) - (x - h) ^ (m - 1)) ≤
        A * ((m - 1 : ℕ) : ℝ) * h * x ^ (m - 2) := by
    calc
      _ ≤ A * (((m - 1 : ℕ) : ℝ) * h * x ^ (m - 2)) := hscaled
      _ = _ := by ring
  calc
    D * ((m : ℝ) * h * (x - h) ^ (m - 1) -
        A * ((m - 1 : ℕ) : ℝ) * h * x ^ (m - 2)) ≤
      D * ((x ^ m - (x - h) ^ m) -
        A * (x ^ (m - 1) - (x - h) ^ (m - 1))) :=
      mul_le_mul_of_nonneg_left (sub_le_sub hmain hscaled') hD
    _ = D * (x ^ m - A * x ^ (m - 1)) -
        D * ((x - h) ^ m - A * (x - h) ^ (m - 1)) := by ring

lemma one_div_sub_one_div_sub
    {x h : ℝ} (hx : 0 < x) (hh : 0 ≤ h) (hhx : h < x) :
    1 / x - 1 / (x - h) = -h / (x * (x - h)) := by
  have hx0 : x ≠ 0 := hx.ne'
  have hy0 : x - h ≠ 0 := (sub_pos.mpr hhx).ne'
  field_simp [hx0, hy0]
  ring

/-- A reciprocal additive error makes the upper profile fall more slowly
than its mean-field centre. -/
lemma reciprocal_upper_sub_next_le
    {E D x h : ℝ} (m : ℕ)
    (hD : 0 ≤ D) (hx : 0 < x)
    (hh : 0 ≤ h) (hhx : h < x) :
    (D * x ^ m + E / x) -
        (D * (x - h) ^ m + E / (x - h)) ≤
      D * ((m : ℝ) * h * x ^ (m - 1)) -
        E * h / (x * (x - h)) := by
  have hpow := pow_sub_pow_le_mul_pow_pred m hh hhx.le
  have hscaled := mul_le_mul_of_nonneg_left hpow hD
  have hx0 : x ≠ 0 := hx.ne'
  have hy0 : x - h ≠ 0 := (sub_pos.mpr hhx).ne'
  calc
    (D * x ^ m + E / x) -
        (D * (x - h) ^ m + E / (x - h)) =
      D * (x ^ m - (x - h) ^ m) - E * h / (x * (x - h)) := by
        field_simp [hx0, hy0]
        ring
    _ ≤ D * ((m : ℝ) * h * x ^ (m - 1)) -
        E * h / (x * (x - h)) := by linarith

/-- A reciprocal additive error makes the lower profile fall more quickly
than its mean-field centre. -/
lemma reciprocal_lower_sub_next_ge
    {E D x h : ℝ} (m : ℕ)
    (hD : 0 ≤ D) (hx : 0 < x)
    (hh : 0 ≤ h) (hhx : h < x) :
    D * ((m : ℝ) * h * (x - h) ^ (m - 1)) +
        E * h / (x * (x - h)) ≤
      (D * x ^ m - E / x) -
        (D * (x - h) ^ m - E / (x - h)) := by
  have hpow := mul_pow_pred_le_pow_sub_pow m hh hhx.le
  have hscaled := mul_le_mul_of_nonneg_left hpow hD
  have hx0 : x ≠ 0 := hx.ne'
  have hy0 : x - h ≠ 0 := (sub_pos.mpr hhx).ne'
  calc
    D * ((m : ℝ) * h * (x - h) ^ (m - 1)) +
        E * h / (x * (x - h)) ≤
      D * (x ^ m - (x - h) ^ m) +
        E * h / (x * (x - h)) := by linarith
    _ = (D * x ^ m - E / x) -
        (D * (x - h) ^ m - E / (x - h)) := by
          field_simp [hx0, hy0]
          ring

/-- Quantitative growth of a reciprocal natural power after decreasing its
positive argument by `h`. -/
lemma reciprocal_pow_growth_lower
    {E x h : ℝ} (s : ℕ) (hE : 0 ≤ E) (hx : 0 < x)
    (hh : 0 ≤ h) (hhx : h < x) :
    E * (((s : ℝ) * h * (x - h) ^ (s - 1)) /
          (x ^ s * (x - h) ^ s)) ≤
      E / (x - h) ^ s - E / x ^ s := by
  have hy : 0 < x - h := sub_pos.mpr hhx
  have hxpow : 0 < x ^ s := pow_pos hx _
  have hypow : 0 < (x - h) ^ s := pow_pos hy _
  have hpow := mul_pow_pred_le_pow_sub_pow s hh hhx.le
  have hquot :
      ((s : ℝ) * h * (x - h) ^ (s - 1)) /
          (x ^ s * (x - h) ^ s) ≤
        (x ^ s - (x - h) ^ s) / (x ^ s * (x - h) ^ s) := by
    exact div_le_div_of_nonneg_right hpow (mul_pos hxpow hypow).le
  calc
    E * (((s : ℝ) * h * (x - h) ^ (s - 1)) /
          (x ^ s * (x - h) ^ s)) ≤
        E * ((x ^ s - (x - h) ^ s) /
          (x ^ s * (x - h) ^ s)) :=
      mul_le_mul_of_nonneg_left hquot hE
    _ = E / (x - h) ^ s - E / x ^ s := by
      field_simp [hx.ne', hy.ne']

/-- Quantitative upper bound for the growth of a reciprocal natural power
after decreasing its positive argument by `h`. -/
lemma reciprocal_pow_growth_upper
    {E x h : ℝ} (s : ℕ) (hE : 0 ≤ E) (hx : 0 < x)
    (hh : 0 ≤ h) (hhx : h < x) :
    E / (x - h) ^ s - E / x ^ s ≤
      E * (((s : ℝ) * h * x ^ (s - 1)) /
        (x ^ s * (x - h) ^ s)) := by
  have hy : 0 < x - h := sub_pos.mpr hhx
  have hxpow : 0 < x ^ s := pow_pos hx _
  have hypow : 0 < (x - h) ^ s := pow_pos hy _
  have hpow := pow_sub_pow_le_mul_pow_pred s hh hhx.le
  have hquot :
      (x ^ s - (x - h) ^ s) / (x ^ s * (x - h) ^ s) ≤
        ((s : ℝ) * h * x ^ (s - 1)) /
          (x ^ s * (x - h) ^ s) := by
    exact div_le_div_of_nonneg_right hpow (mul_pos hxpow hypow).le
  calc
    E / (x - h) ^ s - E / x ^ s =
        E * ((x ^ s - (x - h) ^ s) /
          (x ^ s * (x - h) ^ s)) := by
      field_simp [hx.ne', hy.ne']
    _ ≤ E * (((s : ℝ) * h * x ^ (s - 1)) /
        (x ^ s * (x - h) ^ s)) :=
      mul_le_mul_of_nonneg_left hquot hE

lemma reciprocal_pow_growth_le_one_sixth
    {E x h : ℝ} (s : ℕ) (hE : 0 ≤ E) (hx : 0 < x)
    (hh : 0 ≤ h) (hhx : h < x)
    (hfactor : 6 * (s : ℝ) * h * x ^ (s - 1) ≤ (x - h) ^ s) :
    E / (x - h) ^ s - E / x ^ s ≤ (E / x ^ s) / 6 := by
  have hy : 0 < x - h := sub_pos.mpr hhx
  have hupper := reciprocal_pow_growth_upper s hE hx hh hhx
  have hxpow : 0 < x ^ s := pow_pos hx _
  have hypow : 0 < (x - h) ^ s := pow_pos hy _
  have hmain :
      E * (((s : ℝ) * h * x ^ (s - 1)) /
          (x ^ s * (x - h) ^ s)) ≤ (E / x ^ s) / 6 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 6)).2
    apply (le_div_iff₀ hxpow).2
    calc
      E * (↑s * h * x ^ (s - 1) / (x ^ s * (x - h) ^ s)) * 6 * x ^ s =
          E * (6 * (s : ℝ) * h * x ^ (s - 1)) / (x - h) ^ s := by
        field_simp [hxpow.ne', hypow.ne']
      _ ≤ E := by
        apply (div_le_iff₀ hypow).2
        exact mul_le_mul_of_nonneg_left hfactor hE
  exact hupper.trans hmain

/-- Reciprocal-power upper profile finite difference. -/
lemma reciprocal_power_upper_sub_next_le
    {E D x h : ℝ} (m s : ℕ)
    (hE : 0 ≤ E) (hD : 0 ≤ D) (hx : 0 < x)
    (hh : 0 ≤ h) (hhx : h < x) :
    (D * x ^ m + E / x ^ s) -
        (D * (x - h) ^ m + E / (x - h) ^ s) ≤
      D * ((m : ℝ) * h * x ^ (m - 1)) -
        E * (((s : ℝ) * h * (x - h) ^ (s - 1)) /
          (x ^ s * (x - h) ^ s)) := by
  have hcenter := mul_le_mul_of_nonneg_left
    (pow_sub_pow_le_mul_pow_pred m hh hhx.le) hD
  have herror := reciprocal_pow_growth_lower s hE hx hh hhx
  linarith

/-- Reciprocal-power lower profile finite difference. -/
lemma reciprocal_power_lower_sub_next_ge
    {E D x h : ℝ} (m s : ℕ)
    (hE : 0 ≤ E) (hD : 0 ≤ D) (hx : 0 < x)
    (hh : 0 ≤ h) (hhx : h < x) :
    D * ((m : ℝ) * h * (x - h) ^ (m - 1)) +
        E * (((s : ℝ) * h * (x - h) ^ (s - 1)) /
          (x ^ s * (x - h) ^ s)) ≤
      (D * x ^ m - E / x ^ s) -
        (D * (x - h) ^ m - E / (x - h) ^ s) := by
  have hcenter := mul_le_mul_of_nonneg_left
    (mul_pow_pred_le_pow_sub_pow m hh hhx.le) hD
  have herror := reciprocal_pow_growth_lower s hE hx hh hhx
  linarith

end

end Erdos722.NibbleProfileAlgebra
