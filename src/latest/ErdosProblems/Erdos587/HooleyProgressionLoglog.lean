import ErdosProblems.Erdos587.HooleyShortProgression
import ErdosProblems.Erdos587.HooleyTotientRatio
import ErdosProblems.Erdos587.HooleyAffineCoefficients

/-!
# The sixth-log-log-power transfer to short progressions

The maximal-order totient bound absorbs the only remaining coefficient
factor. The full-interval corollary derives the slope bound from the
endpoint values and permits a zero affine value, whose Delta weight is zero.
-/

open scoped BigOperators

namespace Erdos587

theorem exists_hooleyDelta_short_progression_loglog_bound (r : ℕ) (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A B : ℤ), B ≠ 0 → IsCoprime A B →
      ∀ N Y : ℕ, 2 ≤ N → 16 ≤ Y → N ≤ Y ^ r → B.natAbs ≤ N ^ 2 →
      ∀ S : Finset ℕ, S ⊆ Finset.Icc 1 Y →
      (∀ n ∈ S, A + B * n ≠ 0) → (∀ n ∈ S, (A + B * n).natAbs ≤ N) →
      (∑ n ∈ S, (hooleyDelta (A + B * n).natAbs : ℝ)) ≤
        C * Y * (max 1 (Real.log (Real.log (N : ℝ)))) ^ 6 := by
  obtain ⟨C₀, hC₀, hmean⟩ := exists_hooleyDelta_short_progression_totient_bound r hr
  obtain ⟨C₁, hC₁, hratio⟩ := exists_delta_totient_ratio_square_bound
  refine ⟨C₀ * C₁, mul_pos hC₀ hC₁, ?_⟩
  intro A B hB hAB N Y hN hY hNY hBN S hS hnonzero hvalues
  have hrat := hratio N B.natAbs hN (Int.natAbs_pos.mpr hB) hBN
  calc
    _ ≤ C₀ * ((B.natAbs : ℝ) / B.natAbs.totient) * Y *
        (max 1 (Real.log (Real.log (N : ℝ)))) ^ 5 :=
      hmean A B hB hAB N Y hN hY hNY S hS hnonzero hvalues
    _ ≤ C₀ * (C₁ * max 1 (Real.log (Real.log (N : ℝ)))) * Y *
        (max 1 (Real.log (Real.log (N : ℝ)))) ^ 5 := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hrat hC₀.le) (by positivity))
        (by positivity)
    _ = _ := by ring

/-- Uniform short-progression transfer for primitive signed affine
coefficients, with no excluded zero-value hypothesis. -/
theorem exists_hooleyDelta_primitive_progression_mean (r : ℕ) (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A B : ℤ), B ≠ 0 → IsCoprime A B →
      ∀ N Y : ℕ, 2 ≤ N → 16 ≤ Y → N ≤ Y ^ r →
      (∀ n ∈ Finset.Icc 1 Y, (A + B * n).natAbs ≤ N) →
      (∑ n ∈ Finset.Icc 1 Y, (hooleyDelta (A + B * n).natAbs : ℝ)) ≤
        C * Y * (max 1 (Real.log (Real.log (N : ℝ)))) ^ 6 := by
  classical
  obtain ⟨C, hC, hmean⟩ := exists_hooleyDelta_short_progression_loglog_bound r hr
  refine ⟨C, hC, ?_⟩
  intro A B hB hAB N Y hN hY hNY hvalues
  have hfirst : (A + B).natAbs ≤ N := by
    simpa only [Nat.cast_one, mul_one] using hvalues 1 (Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩)
  have hlast := hvalues Y (Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩)
  have hBslope := (affine_coefficients_le (by omega : 2 ≤ Y) hfirst hlast).1
  have hBN : B.natAbs ≤ N ^ 2 := by nlinarith
  let S := (Finset.Icc 1 Y).filter (fun n : ℕ => A + B * n ≠ 0)
  have hS : S ⊆ Finset.Icc 1 Y := Finset.filter_subset _ _
  have hsum : (∑ n ∈ Finset.Icc 1 Y, (hooleyDelta (A + B * n).natAbs : ℝ)) =
      ∑ n ∈ S, (hooleyDelta (A + B * n).natAbs : ℝ) := by
    symm
    apply Finset.sum_subset hS
    intro n hn hnot
    have hzero : A + B * n = 0 := by
      by_contra hne
      exact hnot (Finset.mem_filter.mpr ⟨hn, hne⟩)
    simp only [hzero, Int.natAbs_zero, hooleyDelta_zero, Nat.cast_zero]
  rw [hsum]
  exact hmean A B hB hAB N Y hN hY hNY hBN S hS
    (fun n hn => (Finset.mem_filter.mp hn).2) (fun n hn => hvalues n (hS hn))

end Erdos587
