/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.CoverDownDensityScalars

/-! # Simultaneous physical-scale budgets for the source link distribution -/

namespace Erdos207

open scoped NNReal

theorem source_link_remaining_numeric_budget
    (t n u A p : ℝ≥0) (b reserveExp v L : ℕ)
    (ht : 1 ≤ t) (hA : 1 ≤ A) (hthreshold : 2*A ≤ t)
    (hb : 2 ≤ b) (hp : 1/t^b ≤ p) (hpUpper : p ≤ 2/t^b) (hp1 : p ≤ 1)
    (hu : t^L ≤ u) (hun : u ≤ n) (hn : n ≤ t^v*u)
    (hreserveGap : v+b+2 ≤ reserveExp) (hpointGap : 2*b+reserveExp+2 ≤ L) :
    let r := 1/t^reserveExp
    let a := A*t
    r*a ≤ p*u/n ∧ p*a ≤ 1 ∧ 1 ≤ a*n/(r*p^2*u) ∧
      a/(r*p^2*u) ≤ 1 ∧ (a/(r*p^2*u))*p^3*r^2 ≤ p/n := by
  dsimp only
  let r := 1/t^reserveExp
  let a := A*t
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hu0 : 0 < u := (pow_pos ht0 L).trans_le hu
  have hn0 : 0 < n := hu0.trans_le hun
  have hp0 : 0 < p := (by positivity : 0 < 1/t^b).trans_le hp
  have hr0 : 0 < r := by dsimp only [r]; positivity
  have hr1 : r ≤ 1 := (div_le_one (pow_pos ht0 _)).mpr (one_le_pow₀ ht)
  have hA2 : A ≤ 2*A := by
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right (by norm_num : (1 : ℝ≥0) ≤ 2) (zero_le (a := A))
  have hAt : A ≤ t := hA2.trans hthreshold
  have ha1 : 1 ≤ a := by
    simpa only [one_mul] using mul_le_mul hA ht zero_le zero_le
  have ha : a ≤ t^2 := by
    simpa only [pow_two] using mul_le_mul_of_nonneg_right hAt (zero_le (a := t))
  have hbudget : a*r*n ≤ p*u := by
    have hpower : t^(b+2)*r*n ≤ u := by
      simpa only [one_mul] using link_sparsification_reserve_budget t n u 1 reserveExp (b+2) v
        ht (by simpa only [one_mul] using hn) (by omega)
    calc
      a*r*n ≤ t^2*r*n := by gcongr
      _ = (t^(b+2)*r*n)/t^b := by rw [pow_add]; field_simp
      _ ≤ u/t^b := div_le_div_of_nonneg_right hpower zero_le
      _ = (1/t^b)*u := by ring
      _ ≤ p*u := mul_le_mul_of_nonneg_right hp zero_le
  have hpa : p*a ≤ 1 := by
    calc
      _ ≤ (2/t^b)*(A*t) := mul_le_mul_of_nonneg_right hpUpper zero_le
      _ ≤ (2/t^2)*(A*t) := by gcongr
      _ = 2*A/t := by field_simp
      _ ≤ 1 := (div_le_one ht0).mpr hthreshold
  have hden : r*p^2*u ≤ a*n := by
    calc
      _ ≤ 1*1^2*u := by gcongr
      _ = u := by ring
      _ ≤ n := hun
      _ ≤ a*n := by simpa only [one_mul] using mul_le_mul_of_nonneg_right ha1 (zero_le (a := n))
  refine ⟨?_, hpa, (one_le_div (by positivity : 0 < r*p^2*u)).mpr hden, ?_, ?_⟩
  · change r*a ≤ p*u/n
    apply (le_div_iff₀ hn0).mpr
    simpa only [mul_comm r a] using hbudget
  · simpa only [pow_one] using inversePower_link_point_le_one t p u A b reserveExp 1 L
      ht hp hu hAt (by omega)
  · have hbudget' : a*r*n ≤ 1*u := hbudget.trans (mul_le_mul_of_nonneg_right hp1 zero_le)
    simpa only [one_mul] using link_point_density_cancellation (a/(r*p^2*u)) p r n u 1 a 1
      hp0 hr0 hn0 hu0 (by simp only [one_mul, le_refl]) hbudget'

end Erdos207
