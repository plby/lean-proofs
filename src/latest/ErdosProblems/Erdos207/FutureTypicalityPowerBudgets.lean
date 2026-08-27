/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.LinkCollisionDensityScalars
import ErdosProblems.Erdos207.QuasiMomentNormalization

/-! # Explicit non-circular power gaps for the future-typicality tails -/

namespace Erdos207

open scoped NNReal

theorem full_link_overlap_le
    (overlap m r n : ℝ≥0) (hbound : overlap ≤ m * r^2 * n) (hone : 1 ≤ r^2*n) :
    overlap + 1 ≤ (m+1) * r^2 * n := by
  calc
    _ ≤ m * r^2*n + r^2*n := add_le_add hbound hone
    _ = _ := by ring

theorem link_inner_edge_mean_cancellation
    (overlap sigma m a r p n u : ℝ≥0) (hr : 0 < r) (hp : 0 < p) (hu : 0 < u)
    (hM : overlap ≤ m * r^2*n) (hsigma : sigma ≤ a / (r*p^2*u)) :
    overlap * sigma ≤ m * (a*r*n/(p^2*u)) := by
  calc
    _ ≤ (m*r^2*n) * (a/(r*p^2*u)) := by gcongr
    _ = _ := by field_simp

theorem link_inner_edge_density_power_decay
    (t n u K A a r p : ℝ≥0) (f reserveExp b v h decay : ℕ)
    (ht : 1 ≤ t) (hu : 0 < u) (ha : a ≤ A*t^f) (hr : r ≤ 1/t^reserveExp)
    (hp : 1/t^b ≤ p) (hsize : n ≤ K*t^v*u)
    (hgap : f+v+b*(h+2)+decay ≤ reserveExp) :
    a*r*n/(p^(h+2)*u) ≤ (A*K)/t^decay := by
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hp0 : 0 < 1/t^b := by positivity
  have hratio : t^(f+v+b*(h+2))/t^reserveExp ≤ 1/t^decay := by
    apply (div_le_div_iff₀ (pow_pos ht0 _) (pow_pos ht0 _)).mpr
    simpa only [one_mul, ← pow_add] using pow_le_pow_right₀ ht hgap
  calc
    _ ≤ (A*t^f)*(1/t^reserveExp)*(K*t^v*u)/((1/t^b)^(h+2)*u) := by gcongr
    _ = (A*K)*(t^(f+v+b*(h+2))/t^reserveExp) := by
      simp only [pow_add, pow_mul, div_pow, one_pow]
      field_simp
    _ ≤ (A*K)*(1/t^decay) := mul_le_mul_of_nonneg_left hratio zero_le
    _ = _ := by ring

theorem future_pattern_density_power_lower
    (t n p eta epsilon eta₀ epsilon₀ : ℝ≥0) (b e h L gain : ℕ)
    (ht : 1 ≤ t) (hp : 1/t^b ≤ p) (heta : eta₀ ≤ eta)
    (hepsilon : epsilon₀/t^e ≤ epsilon) (hn : t^L ≤ n)
    (hgap : b*h+e+gain ≤ L) :
    epsilon₀ * eta₀^(h^2) * t^gain ≤ epsilon * p^h * eta^(h^2) * n := by
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hpow : t^gain ≤ t^L/t^(b*h+e) := by
    apply (le_div_iff₀ (pow_pos ht0 _)).mpr
    rw [← pow_add]
    exact pow_le_pow_right₀ ht (by omega)
  calc
    _ ≤ epsilon₀ * eta₀^(h^2) * (t^L/t^(b*h+e)) := by gcongr
    _ = (epsilon₀/t^e) * (1/t^b)^h * eta₀^(h^2) * t^L := by
      simp only [pow_add, pow_mul, div_pow, one_pow]
      field_simp
    _ ≤ _ := by gcongr

theorem future_quasi_scale_power_bound
    (t n p z Z : ℝ≥0) (b h L zExp decay : ℕ)
    (ht : 1 ≤ t) (hp : 1/t^b ≤ p) (hn : t^L ≤ n) (hz : z ≤ Z*t^zExp)
    (hgap : zExp+b*(h+1)+decay ≤ L) :
    z/(p^(h+1)*n) ≤ Z/t^decay := by
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hp0 : 0 < 1/t^b := by positivity
  have hn0 : 0 < t^L := pow_pos ht0 _
  have hratio : t^(zExp+b*(h+1))/t^L ≤ 1/t^decay := by
    apply (div_le_div_iff₀ (pow_pos ht0 _) (pow_pos ht0 _)).mpr
    simpa only [one_mul, ← pow_add] using pow_le_pow_right₀ ht hgap
  calc
    _ ≤ (Z*t^zExp)/((1/t^b)^(h+1)*t^L) := by gcongr
    _ = Z*(t^(zExp+b*(h+1))/t^L) := by
      simp only [pow_add, pow_mul, div_pow, one_pow]
      field_simp
    _ ≤ Z*(1/t^decay) := mul_le_mul_of_nonneg_left hratio zero_le
    _ = _ := by ring

theorem future_quasi_normalized_main_power_decay
    (t K p epsilon eta epsilon₀ eta₀ : ℝ≥0) (b e q decay : ℕ)
    (ht : 1 ≤ t) (hepsilon₀ : 0 < epsilon₀) (heta₀ : 0 < eta₀)
    (hp : p ≤ 2/t^b) (hepsilon : epsilon₀/t^e ≤ epsilon) (heta : eta₀ ≤ eta)
    (hgap : e+decay ≤ b) :
    K*p/(epsilon*eta^q) ≤ (2*K/(epsilon₀*eta₀^q))/t^decay := by
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have he0 : 0 < epsilon₀/t^e := by positivity
  have hratio : t^e/t^b ≤ 1/t^decay := by
    apply (div_le_div_iff₀ (pow_pos ht0 _) (pow_pos ht0 _)).mpr
    simpa only [one_mul, ← pow_add] using pow_le_pow_right₀ ht hgap
  calc
    _ ≤ K*(2/t^b)/((epsilon₀/t^e)*eta₀^q) := by gcongr
    _ = (2*K/(epsilon₀*eta₀^q))*(t^e/t^b) := by field_simp
    _ ≤ (2*K/(epsilon₀*eta₀^q))*(1/t^decay) := mul_le_mul_of_nonneg_left hratio zero_le
    _ = _ := by ring

theorem future_quasi_error_factor_power_le
    (t N n K P p epsilon eta epsilon₀ eta₀ : ℝ≥0) (R b e h d : ℕ)
    (ht : 1 ≤ t) (hN : N ≤ t^R) (hn : 1 ≤ n)
    (hp : 1/t^b ≤ p) (hepsilon₀ : 0 < epsilon₀) (heta₀ : 0 < eta₀)
    (hepsilon : epsilon₀/t^e ≤ epsilon) (heta : eta₀ ≤ eta) :
    K * (P*(N+1)^d)/(epsilon*p^h*eta^(h^2)*n) ≤
      (K*P*2^d/(epsilon₀*eta₀^(h^2))) * t^(R*d+b*h+e) := by
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hN' : N+1 ≤ 2*t^R := by
    have hone : 1 ≤ t^R := one_le_pow₀ ht
    calc
      N+1 ≤ t^R+t^R := add_le_add hN hone
      _ = _ := by ring
  have hp0 : 0 < 1/t^b := by positivity
  have he0 : 0 < epsilon₀/t^e := by positivity
  calc
    _ ≤ K * (P*(2*t^R)^d)/((epsilon₀/t^e)*(1/t^b)^h*eta₀^(h^2)*1) := by gcongr
    _ = _ := by
      simp only [pow_add, pow_mul, mul_pow, div_pow, one_pow, mul_one]
      field_simp

theorem finite_moment_error_power_decay
    (t error factor A : ℝ≥0) (B d s decay : ℕ) (ht : 1 ≤ t)
    (herror : error ≤ 1/t^B) (hfactor : factor ≤ A*t^d) (hgap : d*s+decay ≤ B) :
    error * factor^s ≤ A^s/t^decay := by
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hratio : t^(d*s)/t^B ≤ 1/t^decay := by
    apply (div_le_div_iff₀ (pow_pos ht0 _) (pow_pos ht0 _)).mpr
    simpa only [one_mul, ← pow_add] using pow_le_pow_right₀ ht hgap
  calc
    _ ≤ (1/t^B)*(A*t^d)^s := by gcongr
    _ = A^s*(t^(d*s)/t^B) := by rw [mul_pow, pow_mul]; ring
    _ ≤ A^s*(1/t^decay) := mul_le_mul_of_nonneg_left hratio zero_le
    _ = _ := by ring

theorem finite_polynomial_union_power_decay
    (t tests failure K A : ℝ≥0) (d loss decay : ℕ) (ht : 1 ≤ t)
    (htests : tests ≤ K*t^d) (hfailure : failure ≤ A/t^loss) (hgap : d+decay ≤ loss) :
    tests*failure ≤ K*A/t^decay := by
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hratio : t^d/t^loss ≤ 1/t^decay := by
    apply (div_le_div_iff₀ (pow_pos ht0 _) (pow_pos ht0 _)).mpr
    simpa only [one_mul, ← pow_add] using pow_le_pow_right₀ ht hgap
  calc
    _ ≤ (K*t^d)*(A/t^loss) := by gcongr
    _ = K*A*(t^d/t^loss) := by ring
    _ ≤ K*A*(1/t^decay) := mul_le_mul_of_nonneg_left hratio zero_le
    _ = _ := by ring

end Erdos207
