import ErdosProblems.Erdos587.HooleyProgressionLoglog

/-!
# The common-gcd factor in the short-progression mean

Dividing both signed coefficients by their positive gcd makes them
primitive. The Delta multiplication inequality contributes exactly the
divisor count of that gcd, with no coprimality hypothesis on the values.
-/

open scoped BigOperators

namespace Erdos587

theorem exists_hooleyDelta_progression_mean (r : ℕ) (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A B : ℤ), B ≠ 0 →
      ∀ N Y : ℕ, 2 ≤ N → 16 ≤ Y → N ≤ Y ^ r →
      (∀ n ∈ Finset.Icc 1 Y, (A + B * n).natAbs ≤ N) →
      (∑ n ∈ Finset.Icc 1 Y, (hooleyDelta (A + B * n).natAbs : ℝ)) ≤
        C * (Int.gcd A B).divisors.card * Y *
          (max 1 (Real.log (Real.log (N : ℝ)))) ^ 6 := by
  obtain ⟨C, hC, hmean⟩ := exists_hooleyDelta_primitive_progression_mean r hr
  refine ⟨C, hC, ?_⟩
  intro A B hB N Y hN hY hNY hvalues
  let g : ℕ := Int.gcd A B
  let a : ℤ := A / g
  let b : ℤ := B / g
  have hg : 0 < g := Int.gcd_pos_of_ne_zero_right A hB
  have hga : (g : ℤ) * a = A := Int.mul_ediv_cancel_of_dvd (Int.gcd_dvd_left A B)
  have hgb : (g : ℤ) * b = B := Int.mul_ediv_cancel_of_dvd (Int.gcd_dvd_right A B)
  have hb : b ≠ 0 := by intro h; rw [h, mul_zero] at hgb; exact hB hgb.symm
  have hab : IsCoprime a b := by
    apply Int.isCoprime_iff_gcd_eq_one.mpr
    exact Int.gcd_div_gcd_div_gcd hg
  have hfactor (n : ℕ) : (A + B * n).natAbs = g * (a + b * n).natAbs := by
    have h : (g : ℤ) * (a + b * n) = A + B * n := by
      rw [mul_add, ← mul_assoc, hga, hgb]
    have habs := congrArg Int.natAbs h
    simpa only [Int.natAbs_mul, Int.natAbs_natCast] using habs.symm
  have hsmall : ∀ n ∈ Finset.Icc 1 Y, (a + b * n).natAbs ≤ N := by
    intro n hn
    have h := hvalues n hn
    rw [hfactor n] at h
    nlinarith
  have hbound := hmean a b hb hab N Y hN hY hNY hsmall
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 Y, (g.divisors.card : ℝ) * hooleyDelta (a + b * n).natAbs := by
      apply Finset.sum_le_sum
      intro n hn
      rw [hfactor n]
      exact_mod_cast hooleyDelta_mul_le g (a + b * n).natAbs
    _ = (g.divisors.card : ℝ) *
        ∑ n ∈ Finset.Icc 1 Y, (hooleyDelta (a + b * n).natAbs : ℝ) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ (g.divisors.card : ℝ) *
        (C * Y * (max 1 (Real.log (Real.log (N : ℝ)))) ^ 6) :=
      mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = _ := by dsimp only [g]; ring

end Erdos587
