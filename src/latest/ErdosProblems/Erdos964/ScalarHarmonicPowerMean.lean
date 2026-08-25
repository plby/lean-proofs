import ErdosProblems.Erdos964.ScalarHarmonicMoments

/-!
# Means of powers of the coprime harmonic arithmetic function

Dirichlet convolution raises the logarithmic degree by one. For every
positive power, the remainder loses one logarithmic degree.
-/

namespace Erdos964

open BoundedGaps.Maynard

theorem exists_coprime_harmonic_power_mean_error (M : ℕ) (hM : 0 < M) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x →
      |abelCumulative (coprimeHarmonicAF M ^ (k + 1) : ArithmeticFunction ℝ) x -
        coprimeHarmonicDensity M ^ (k + 1) / (Nat.factorial (k + 1) : ℝ) *
          (Real.log x) ^ (k + 1)| ≤ C * (1 + Real.log x) ^ k := by
  let δ := coprimeHarmonicDensity M
  have hδ : 0 ≤ δ := by dsimp [δ, coprimeHarmonicDensity]; positivity
  obtain ⟨B, hB, htotal, hmoment⟩ := exists_coprime_harmonic_moment_error M hM
  induction k with
  | zero =>
      obtain ⟨E, hE, hmean⟩ := exists_coprime_harmonic_cumulative_bounded_error M hM
      refine ⟨E, hE, ?_⟩
      intro x hx
      simpa only [Nat.zero_add, pow_one, Nat.factorial_one, Nat.cast_one,
        div_one, pow_zero, mul_one] using hmean x hx
  | succ k ih =>
      obtain ⟨C, hC, hmean⟩ := ih
      let c := δ ^ (k + 1) / (Nat.factorial (k + 1) : ℝ)
      have hc : 0 ≤ c := by dsimp [c]; positivity
      refine ⟨(C + c) * B, by positivity, ?_⟩
      intro x hx
      let T := (1 + Real.log x) ^ (k + 1)
      let V := ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊,
        coprimeHarmonicAF M n * (Real.log (x / n)) ^ (k + 1)
      have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
      have hpoint (n : ℕ) (hn : n ∈ Finset.Ioc 0 ⌊x⌋₊) :
          |coprimeHarmonicAF M n *
            abelCumulative (coprimeHarmonicAF M ^ (k + 1) : ArithmeticFunction ℝ) (x / n) -
            coprimeHarmonicAF M n * (c * (Real.log (x / n)) ^ (k + 1))| ≤
          coprimeHarmonicAF M n * (C * (1 + Real.log x) ^ k) := by
        obtain ⟨hq, hqlog, hqlogle⟩ := harmonic_quotient_log_bounds x hx n hn
        rw [← mul_sub, abs_mul, abs_of_nonneg (coprimeHarmonicAF_nonneg M n)]
        refine mul_le_mul_of_nonneg_left ((hmean (x / n) hq).trans ?_)
          (coprimeHarmonicAF_nonneg M n)
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by linarith) (by linarith) k) hC
      have herror :
          |abelCumulative (coprimeHarmonicAF M ^ ((k + 1) + 1) : ArithmeticFunction ℝ) x -
            c * V| ≤ C * B * T := by
        rw [coprimeHarmonicAF_pow_cumulative_succ]
        have hid : c * V = ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊,
            coprimeHarmonicAF M n * (c * (Real.log (x / n)) ^ (k + 1)) := by
          dsimp only [V]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro n hn
          ring
        rw [hid, ← Finset.sum_sub_distrib]
        calc
          _ ≤ ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊,
              |coprimeHarmonicAF M n *
                abelCumulative (coprimeHarmonicAF M ^ (k + 1) : ArithmeticFunction ℝ) (x / n) -
                coprimeHarmonicAF M n * (c * (Real.log (x / n)) ^ (k + 1))| :=
            Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊,
              coprimeHarmonicAF M n * (C * (1 + Real.log x) ^ k) :=
            Finset.sum_le_sum hpoint
          _ = abelCumulative (coprimeHarmonicAF M) x * (C * (1 + Real.log x) ^ k) := by
            rw [abelCumulative_arithmeticFunction, Finset.sum_mul]
          _ ≤ (B * (1 + Real.log x)) * (C * (1 + Real.log x) ^ k) :=
            mul_le_mul_of_nonneg_right (htotal x hx) (by positivity)
          _ = C * B * T := by dsimp only [T]; rw [pow_succ]; ring
      have hmoment' : |c * V - c * (δ / ((k + 1 : ℕ) + 1) *
          (Real.log x) ^ ((k + 1) + 1))| ≤ c * B * T := by
        rw [← mul_sub, abs_mul, abs_of_nonneg hc]
        simpa only [T, mul_assoc] using mul_le_mul_of_nonneg_left (hmoment (k + 1) x hx) hc
      have hconstant : c * (δ / ((k + 1 : ℕ) + 1)) =
          δ ^ ((k + 1) + 1) / (Nat.factorial ((k + 1) + 1) : ℝ) := by
        dsimp only [c]
        rw [Nat.factorial_succ (k + 1), Nat.cast_mul, pow_succ δ (k + 1)]
        simp only [Nat.cast_add, Nat.cast_one, div_eq_mul_inv, mul_inv_rev]
        ring
      have hcombined := (abs_sub_le
        (abelCumulative (coprimeHarmonicAF M ^ ((k + 1) + 1) : ArithmeticFunction ℝ) x)
        (c * V) (c * (δ / ((k + 1 : ℕ) + 1) * (Real.log x) ^ ((k + 1) + 1)))).trans
        (add_le_add herror hmoment')
      rw [← mul_assoc c, hconstant] at hcombined
      calc
        _ ≤ C * B * T + c * B * T := hcombined
        _ = (C + c) * B * (1 + Real.log x) ^ (k + 1) := by dsimp only [T]; ring

end Erdos964
