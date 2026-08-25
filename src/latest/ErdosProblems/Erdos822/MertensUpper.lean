/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos822.SingularFactorControl
import ErdosProblems.Erdos851.EulerMass

/-!
# Direct Mertens upper bound for the one-shift sieve product

The existing Erdős 851 development records the inverse-product estimate
needed by the beta sieve.  The energy summation needs the complementary
direct-product form: over a prime interval the one-shift Euler product is at
most a constant times the logarithm ratio.
-/

namespace Erdos822

/-- The direct one-shift Euler product is the quotient of the two partial
Mertens products in the opposite order from the inverse product. -/
theorem oneShift_localEulerProduct_eq_partial_ratio
    {z y : ℕ} (hzy : z ≤ y) :
    Erdos851.localEulerProduct Erdos851.oneShiftDensity z y =
      partial_euler_product z / partial_euler_product y := by
  have hinv := Erdos851.oneShift_inverseLocalEulerProduct_eq hzy
  rw [Erdos851.inverseLocalEulerProduct_eq_inv] at hinv
  have hzpos : 0 < partial_euler_product z :=
    lt_of_lt_of_le (by norm_num) partial_euler_trivial_lower_bound
  have hypos : 0 < partial_euler_product y :=
    lt_of_lt_of_le (by norm_num) partial_euler_trivial_lower_bound
  calc
    Erdos851.localEulerProduct Erdos851.oneShiftDensity z y =
        (Erdos851.localEulerProduct
          Erdos851.oneShiftDensity z y)⁻¹⁻¹ := by rw [inv_inv]
    _ = (partial_euler_product y / partial_euler_product z)⁻¹ := by
      rw [hinv]
    _ = partial_euler_product z / partial_euler_product y := by
      field_simp [hzpos.ne', hypos.ne']

/-- Weak Mertens gives a uniform direct-product upper bound. -/
theorem exists_oneShift_localEulerProduct_upper :
    ∃ C : ℝ, 0 < C ∧ ∀ z y : ℕ, 2 ≤ z → z ≤ y →
      Erdos851.localEulerProduct Erdos851.oneShiftDensity z y ≤
        C * (Real.log (z : ℝ) / Real.log (y : ℝ)) := by
  obtain ⟨Cu, hCu, hupper⟩ := weak_mertens_third_upper_all
  obtain ⟨Cl, hCl, hlower⟩ := weak_mertens_third_lower_all
  refine ⟨Cu / Cl, div_pos hCu hCl, ?_⟩
  intro z y hz hzy
  have hzR : (2 : ℝ) ≤ z := by exact_mod_cast hz
  have hyR : (2 : ℝ) ≤ y := by exact_mod_cast hz.trans hzy
  have hlogz : 0 ≤ Real.log (z : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ z by omega))
  have hlogy : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hPz : 0 < partial_euler_product z :=
    lt_of_lt_of_le (by norm_num) partial_euler_trivial_lower_bound
  have hPy : 0 < partial_euler_product y :=
    lt_of_lt_of_le (by norm_num) partial_euler_trivial_lower_bound
  have hupper' : partial_euler_product z ≤ Cu * Real.log (z : ℝ) := by
    simpa [Real.norm_of_nonneg hlogz,
      Real.norm_of_nonneg (zero_le_one.trans
        (partial_euler_trivial_lower_bound (n := z)))]
      using hupper (z : ℝ) hzR
  have hlower' : Cl * Real.log (y : ℝ) ≤ partial_euler_product y := by
    simpa [Real.norm_of_nonneg hlogy.le,
      Real.norm_of_nonneg (zero_le_one.trans
        (partial_euler_trivial_lower_bound (n := y)))]
      using hlower (y : ℝ) (by exact_mod_cast (show 1 ≤ y by omega))
  rw [oneShift_localEulerProduct_eq_partial_ratio hzy]
  calc
    partial_euler_product z / partial_euler_product y ≤
        (Cu * Real.log (z : ℝ)) / (Cl * Real.log (y : ℝ)) := by
      exact div_le_div₀ (mul_nonneg hCu.le hlogz) hupper'
        (mul_pos hCl hlogy) hlower'
    _ = (Cu / Cl) *
        (Real.log (z : ℝ) / Real.log (y : ℝ)) := by
      field_simp [hCl.ne', hlogy.ne']

end Erdos822
