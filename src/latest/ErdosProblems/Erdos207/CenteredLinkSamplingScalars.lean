/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.RawLinkMatchingGeometry
import ErdosProblems.Erdos207.CenteredHallReferenceParameters

/-! # Density cancellation and rounded degree budgets for actual centered link sampling -/

namespace Erdos207

open scoped NNReal

theorem link_reference_sampled_hall_budget
    (a r p eta u c : ℝ≥0) (Delta t : ℕ) (hr : 0 < r) (hp : 0 < p) (hu : 0 < u)
    (hc : r*p^2*eta*u/80 ≤ c) (hbudget : (Delta+t : ℝ≥0) ≤ a*eta/160) :
    (Delta+t : ℝ≥0) ≤ (a/(r*p^2*u))*c/2 := by
  have hcancel : (a/(r*p^2*u))*(r*p^2*eta*u/80)/2 = a*eta/160 := by field_simp; ring
  calc
    _ ≤ a*eta/160 := hbudget
    _ = (a/(r*p^2*u))*(r*p^2*eta*u/80)/2 := hcancel.symm
    _ ≤ _ := by gcongr

theorem exists_rounded_link_degree
    (x : ℝ) (hx : 1 ≤ x) : ∃ D : ℕ, 2*x ≤ D ∧ (D : ℝ) ≤ 3*x := by
  let D := ⌈2*x⌉₊
  have hlo : 2*x ≤ D := Nat.le_ceil _
  have hhi : (D : ℝ) < 2*x+1 := Nat.ceil_lt_add_one (by linarith only [hx])
  exact ⟨D, hlo, by linarith only [hhi, hx]⟩

theorem rawLinkGeometricFailure_le_dyadic
    (centers N degree overlap collisionCap s t : ℕ) (sigma : ℝ≥0)
    (hcollision : 4*(degree : ℝ≥0)*overlap*sigma^2 ≤ collisionCap+1) :
    rawLinkGeometricFailure centers N degree overlap collisionCap s t sigma ≤
      8*(centers : ℝ≥0)*(N+1 : ℝ≥0)^2*(1/2 : ℝ≥0)^t+
        2*(centers : ℝ≥0)*N*(1/2 : ℝ≥0)^s := by
  have hratio : 2*(degree : ℝ≥0)*overlap*sigma^2/(collisionCap+1) ≤ (1/2 : ℝ≥0) := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ≥0) < collisionCap+1)).mpr
    have hb := div_le_div_of_nonneg_right hcollision (show (0 : ℝ≥0) ≤ 2 by positivity)
    convert hb using 1 <;> ring
  apply add_le_add le_rfl
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left' hratio s) zero_le

theorem rawLinkGeometricFailure_le_single_dyadic
    (centers N degree overlap collisionCap s t : ℕ) (sigma : ℝ≥0) (hts : t ≤ s)
    (hcollision : 4*(degree : ℝ≥0)*overlap*sigma^2 ≤ collisionCap+1) :
    rawLinkGeometricFailure centers N degree overlap collisionCap s t sigma ≤
      10*(centers : ℝ≥0)*(N+1 : ℝ≥0)^2*(1/2 : ℝ≥0)^t := by
  have hp := NNReal.pow_antitone_exp t s hts (by norm_num : (1/2 : ℝ≥0) ≤ 1)
  have hN : (N : ℝ≥0) ≤ (N+1 : ℝ≥0)^2 := by nlinarith
  apply (rawLinkGeometricFailure_le_dyadic centers N degree overlap collisionCap s t sigma hcollision).trans
  calc
    _ ≤ 8*(centers : ℝ≥0)*(N+1 : ℝ≥0)^2*(1/2 : ℝ≥0)^t+
        2*(centers : ℝ≥0)*(N+1 : ℝ≥0)^2*(1/2 : ℝ≥0)^t := by
      apply add_le_add le_rfl
      exact mul_le_mul (mul_le_mul_of_nonneg_left hN zero_le) hp zero_le zero_le
    _ = _ := by ring

end Erdos207
