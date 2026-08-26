/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
A square-root estimate for the determinant exponent over several residues.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.Counting.ResidueMonomials

namespace Erdos477.Counting

/-- The explicit leading determinant exponent for `s` columns and `q`
residue classes, with a linear error independent of `q`. -/
theorem residueExponent_lower_bound (q s : ℕ) (hq : 0 < q) :
    (2 : ℝ) / 3 * s * Real.sqrt (2 * s / q) - 3 * s ≤
      (residueExponent q s (Nat.sqrt (2 * s / q)) : ℝ) := by
  let m := Nat.sqrt (2 * s / q)
  let K := m * (m + 1) * (m + 2) / 6
  have hn : m * s ≤ residueExponent q s m + q * K := by
    dsimp only [residueExponent, K]
    omega
  have hk : 6 * K ≤ m * (m + 1) * (m + 2) := by
    dsimp only [K]
    omega
  have hnR : (m : ℝ) * s ≤ (residueExponent q s m : ℝ) + q * K := by exact_mod_cast hn
  have hkR : (6 : ℝ) * K ≤ (m : ℝ) * (m + 1) * (m + 2) := by exact_mod_cast hk
  have hm2nat : q * (m * m) ≤ 2 * s := by
    calc
      _ ≤ q * (2 * s / q) := Nat.mul_le_mul_left q (Nat.sqrt_le _)
      _ ≤ _ := Nat.mul_div_le _ _
  have hm1nat : q * m ≤ 2 * s :=
    (Nat.mul_le_mul_left q (Nat.le_mul_self m)).trans hm2nat
  have hm2 : (q : ℝ) * (m : ℝ) ^ 2 ≤ 2 * s := by
    rw [pow_two]
    exact_mod_cast hm2nat
  have hm1 : (q : ℝ) * m ≤ 2 * s := by exact_mod_cast hm1nat
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg _
  have hqpos : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg _
  have hm3 : (q : ℝ) * (m : ℝ) ^ 3 ≤ 2 * m * s := by
    have h := mul_le_mul_of_nonneg_left hm2 hm0
    nlinarith
  have hkq := mul_le_mul_of_nonneg_left hkR hq0
  have huppernat : 2 * s < (m + 1) * (m + 1) * q := by
    apply (Nat.div_lt_iff_lt_mul hq).mp
    exact Nat.sqrt_lt.mp (Nat.lt_succ_self m)
  have hupper : (2 : ℝ) * s ≤ ((m : ℝ) + 1) ^ 2 * q := by
    have h : (2 : ℝ) * s < ((m : ℝ) + 1) * ((m : ℝ) + 1) * q := by
      exact_mod_cast huppernat
    nlinarith
  have hroot : Real.sqrt (2 * (s : ℝ) / q) ≤ (m : ℝ) + 1 := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by positivity, ?_⟩
    exact (div_le_iff₀ hqpos).mpr hupper
  have hrootmul := mul_le_mul_of_nonneg_left hroot (show 0 ≤ (2 : ℝ) * s by positivity)
  have hmain : (4 : ℝ) * m * s ≤ 6 * (residueExponent q s m : ℝ) + 10 * s := by
    nlinarith
  change (2 : ℝ) / 3 * s * Real.sqrt (2 * s / q) - 3 * s ≤
    (residueExponent q s m : ℝ)
  nlinarith

#print axioms residueExponent_lower_bound
-- 'Erdos477.Counting.residueExponent_lower_bound' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Counting
