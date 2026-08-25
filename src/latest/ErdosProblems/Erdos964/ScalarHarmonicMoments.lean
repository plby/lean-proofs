import ErdosProblems.Erdos964.LogPowerRealAbel
import ErdosProblems.Erdos964.ScalarHarmonicConvolution

/-!
# Fixed-modulus harmonic logarithmic moments
-/

namespace Erdos964

open BoundedGaps.Maynard

theorem harmonic_quotient_log_bounds (x : ℝ) (hx : 1 ≤ x) (n : ℕ)
    (hn : n ∈ Finset.Ioc 0 ⌊x⌋₊) :
    1 ≤ x / n ∧ 0 ≤ Real.log (x / n) ∧ Real.log (x / n) ≤ Real.log x := by
  have hn0 := (Finset.mem_Ioc.mp hn).1
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn0
  have hnx : (n : ℝ) ≤ x := (Nat.cast_le.mpr (Finset.mem_Ioc.mp hn).2).trans
    (Nat.floor_le (zero_le_one.trans hx))
  have hquot : 1 ≤ x / n := (le_div_iff₀ hnpos).mpr (by simpa only [one_mul] using hnx)
  have hquotle : x / n ≤ x := div_le_self (zero_le_one.trans hx) (by exact_mod_cast hn0)
  exact ⟨hquot, Real.log_nonneg hquot,
    Real.log_le_log (zero_lt_one.trans_le hquot) hquotle⟩

theorem exists_coprime_harmonic_moment_error (M : ℕ) (hM : 0 < M) :
    ∃ B : ℝ, 0 ≤ B ∧
      (∀ x : ℝ, 1 ≤ x → abelCumulative (coprimeHarmonicAF M) x ≤ B * (1 + Real.log x)) ∧
      ∀ (k : ℕ) (x : ℝ), 1 ≤ x →
      |(∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, coprimeHarmonicAF M n * (Real.log (x / n)) ^ k) -
        coprimeHarmonicDensity M / (k + 1) * (Real.log x) ^ (k + 1)| ≤
        B * (1 + Real.log x) ^ k := by
  obtain ⟨E, hE, hmean⟩ := exists_coprime_harmonic_cumulative_bounded_error M hM
  let δ := coprimeHarmonicDensity M
  have hδ : 0 ≤ δ := by dsimp [δ, coprimeHarmonicDensity]; positivity
  refine ⟨E + δ, add_nonneg hE hδ, ?_, ?_⟩
  · intro x hx
    have h := (le_abs_self _).trans (hmean x hx)
    have hlog := Real.log_nonneg hx
    nlinarith
  · intro k x hx
    have h := log_power_weighted_abel_real_error (coprimeHarmonicAF M)
      ArithmeticFunction.map_zero δ E hδ hE hmean x hx k
    have hsum : (∑ n ∈ Finset.Icc 0 ⌊x⌋₊,
        (Real.log x - Real.log n) ^ k * coprimeHarmonicAF M n) =
        ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, coprimeHarmonicAF M n * (Real.log (x / n)) ^ k := by
      have hinterval (Q : ℕ) : Finset.Icc 0 Q = insert 0 (Finset.Ioc 0 Q) := by
        ext n
        simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ioc]
        omega
      rw [hinterval, Finset.sum_insert (by simp)]
      simp only [ArithmeticFunction.map_zero, mul_zero, zero_add]
      apply Finset.sum_congr rfl
      intro n hn
      have hn0 := (Finset.mem_Ioc.mp hn).1
      rw [Real.log_div (zero_lt_one.trans_le hx).ne' (by exact_mod_cast hn0.ne')]
      ring
    rwa [hsum] at h

end Erdos964
