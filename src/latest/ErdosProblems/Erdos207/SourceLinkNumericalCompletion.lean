/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceLinkScalarChoices
import ErdosProblems.Erdos207.EventualSourceMomentBudgets

/-! # The remaining marked-extension, reference-size, and recentering coefficients -/

namespace Erdos207

open scoped NNReal

theorem source_link_marked_numeric_budget
    (t n u A a p z y : ℝ≥0) (q b reserveExp v D : ℕ)
    (ht : 1 ≤ t) (hu : 0 < u) (ha : a ≤ A*t) (hp : 1/t^b ≤ p)
    (hz : z ≤ t^v) (hy : 1 ≤ y) (hn : t^D ≤ n) (hsize : n ≤ t^v*u)
    (hgap : v+(1+v+reserveExp+2*b)*(q+1)+1 ≤ D) (hconstant : A^(q+1) ≤ t) :
    z*(a*n/((1/t^reserveExp)*p^2*u))^(q+1)/n ≤ y := by
  have hw := link_marked_weight_ratio_power_le t n u 1 A a p 1 reserveExp b v ht hu
    (by simpa only [pow_one] using ha) hp (by simpa only [one_mul] using hsize)
  have hbound := link_marked_extension_power_decay t n z (a*n/((1/t^reserveExp)*p^2*u)) 1 A
    v (1+v+reserveExp+b*2) q D 1 ht hn (by simpa only [one_mul] using hz)
    (by simpa only [mul_one] using hw) (by simpa only [Nat.mul_comm b 2] using hgap)
  apply hbound.trans
  calc
    (1*A^(q+1))/t^1 = A^(q+1)/t := by simp only [one_mul, pow_one]
    _ ≤ 1 := (div_le_one (zero_lt_one.trans_le ht)).mpr hconstant
    _ ≤ _ := hy

theorem source_link_large_reference
    (t x eta0 : ℝ≥0) (ht : 1 ≤ t) (heta0 : 0 < eta0)
    (hsize : eta0*t^2 ≤ x) (hconstant : (18*(65537+4) : ℝ≥0)/eta0 ≤ t) :
    18*(65537+4*t) ≤ x := by
  have hcoef : (18*(65537+4) : ℝ≥0) ≤ eta0*t := by
    have hh := (div_le_iff₀ heta0).mp hconstant
    simpa only [mul_comm t eta0] using hh
  calc
    18*(65537+4*t) ≤ 18*(65537*t+4*t) := by
      gcongr
      simpa only [mul_one] using mul_le_mul_of_nonneg_left ht (zero_le (a := (65537 : ℝ≥0)))
    _ = (18*(65537+4))*t := by ring
    _ ≤ (eta0*t)*t := mul_le_mul_of_nonneg_right hcoef zero_le
    _ = eta0*t^2 := by ring
    _ ≤ _ := hsize

theorem source_link_recenter_power_budget
    (t p eta eta0 epsilon : ℝ≥0) (b reserveExp : ℕ)
    (ht : 1 ≤ t) (heta0 : 0 < eta0) (hepsilon : 0 < epsilon)
    (hp : 1/t^b ≤ p) (heta : eta0 ≤ eta) (hgap : b+1 ≤ reserveExp)
    (hconstant : 1/(128*epsilon*eta0) ≤ t) : 1/t^reserveExp ≤ 128*epsilon*p*eta := by
  have ht0 := zero_lt_one.trans_le ht
  have hinverse : 1/t ≤ 128*epsilon*eta0 := by
    apply (div_le_iff₀ ht0).mpr
    have hh := (div_le_iff₀ (by positivity : 0 < 128*epsilon*eta0)).mp hconstant
    simpa only [mul_comm t (128*epsilon*eta0)] using hh
  calc
    1/t^reserveExp ≤ 1/t^(b+1) := one_div_le_one_div_of_le (pow_pos ht0 _)
      (pow_le_pow_right₀ ht hgap)
    _ = (1/t^b)*(1/t) := by rw [pow_succ]; field_simp
    _ ≤ p*(128*epsilon*eta0) := mul_le_mul hp hinverse zero_le zero_le
    _ ≤ p*(128*epsilon*eta) := by gcongr
    _ = _ := by ring

theorem eventually_source_link_future_degree_moment
    (reserveExp b v h decay : ℕ) (A eta0 epsilon0 : ℝ≥0)
    (heta0 : 0 < eta0) (hepsilon0 : 0 < epsilon0)
    (hgap : v+b*(h+2)+4 ≤ reserveExp) :
    ∃ T : ℕ, 1 ≤ T ∧ ∀ t : ℕ, T ≤ t →
      ∀ (n u a r p eta epsilon overlap sigma : ℝ≥0), 0 < r → 0 < u →
        a ≤ A*t → r ≤ 1/(t : ℝ≥0)^reserveExp → 1/(t : ℝ≥0)^b ≤ p →
        eta0 ≤ eta → epsilon0/t ≤ epsilon → n ≤ (t : ℝ≥0)^v*u →
        overlap+1 ≤ (3*t)*r^2*n → sigma ≤ a/(r*p^2*u) →
        (2*(overlap+1)*sigma/(epsilon*p^h*eta^(h^2)))^(decay+1) ≤ 1/(t : ℝ≥0)^decay := by
  let coefficient := (6*A/(epsilon0*eta0^(h^2)))^(decay+1)
  let T := max 1 ⌈coefficient⌉₊
  refine ⟨T, le_max_left _ _, ?_⟩
  intro t ht n u a r p eta epsilon overlap sigma hr hu ha hrPower hp heta hepsilon hsize hoverlap hsigma
  have ht1 : (1 : ℝ≥0) ≤ t := by exact_mod_cast (le_max_left 1 ⌈coefficient⌉₊).trans ht
  have hcoef : coefficient ≤ (t : ℝ≥0) := (Nat.le_ceil _).trans
    (by exact_mod_cast (le_max_right 1 ⌈coefficient⌉₊).trans ht)
  have hratio := source_link_future_degree_ratio_power t n u A a r p eta eta0 epsilon epsilon0 overlap sigma
    reserveExp b v h ht1 hr hu heta0 hepsilon0 ha hrPower hp heta hepsilon hsize hgap hoverlap hsigma
  calc
    _ ≤ ((6*A/(epsilon0*eta0^(h^2)))/(t : ℝ≥0))^(decay+1) := pow_le_pow_left' hratio _
    _ = coefficient/(t : ℝ≥0)^(decay+1) := div_pow _ _ _
    _ ≤ _ := inverse_power_absorb_coefficient t coefficient decay (zero_lt_one.trans_le ht1) hcoef

end Erdos207
