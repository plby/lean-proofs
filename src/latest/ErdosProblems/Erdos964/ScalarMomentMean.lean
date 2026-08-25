import ErdosProblems.Erdos964.LogConvolutionLimit
import ErdosProblems.Erdos964.ScalarCorrectionSummable

/-!
# The fixed-modulus dimension-two and dimension-three means

Both scalar moments use the same positive Euler correction constant.
The remaining density factors are the corresponding powers of `φ(M)/M`.
-/

namespace Erdos964

open BoundedGaps.Maynard Filter
open scoped Topology

noncomputable def scalarSieveEulerConstant (M : ℕ) : ℝ :=
  ∑' n : ℕ, scalarMomentCorrectionAF M 3 n

theorem scalarSieveEulerConstant_ge_one (M : ℕ) (h2M : 2 ∣ M) (h3M : 3 ∣ M) :
    1 ≤ scalarSieveEulerConstant M := scalarMomentCorrectionAF_tsum_three_ge_one M h2M h3M

theorem tendsto_scalarMomentAF_mean (M : ℕ) (hM : 0 < M) (h2M : 2 ∣ M) (h3M : 3 ∣ M)
    (k : ℕ) (hk : k + 1 ≤ 3) :
    Tendsto (fun x : ℝ => abelCumulative (scalarMomentAF M (k + 1)) x /
      (Real.log x) ^ (k + 1)) atTop
      (𝓝 ((∑' n : ℕ, scalarMomentCorrectionAF M (k + 1) n) *
        (coprimeHarmonicDensity M ^ (k + 1) / (Nat.factorial (k + 1) : ℝ)))) := by
  obtain ⟨C, hC, herror⟩ := exists_coprime_harmonic_power_mean_error M hM k
  let c := coprimeHarmonicDensity M ^ (k + 1) / (Nat.factorial (k + 1) : ℝ)
  have hgrowth : ∀ x : ℝ, 1 ≤ x →
      |abelCumulative (coprimeHarmonicAF M ^ (k + 1) : ArithmeticFunction ℝ) x| ≤
        (C + |c|) * (1 + Real.log x) ^ (k + 1) := by
    intro x hx
    exact log_power_error_abs_bound _ c C hC k x hx (herror x hx)
  have h := tendsto_log_mean_convolution (scalarMomentCorrectionAF M (k + 1))
    (coprimeHarmonicAF M ^ (k + 1) : ArithmeticFunction ℝ) (k + 1) c (C + |c|)
    (by positivity) (summable_abs_scalarMomentCorrectionAF M (k + 1) hk h2M h3M)
    (tendsto_coprime_harmonic_power_mean M hM k) hgrowth
  simpa only [scalarMomentCorrectionAF_mul_harmonic_pow, c] using h

theorem tendsto_scalarMomentAF_three_mean (M : ℕ) (hM : 0 < M)
    (h2M : 2 ∣ M) (h3M : 3 ∣ M) :
    Tendsto (fun x : ℝ => abelCumulative (scalarMomentAF M 3) x / (Real.log x) ^ 3)
      atTop (𝓝 (scalarSieveEulerConstant M * (coprimeHarmonicDensity M ^ 3 / 6))) := by
  have h := tendsto_scalarMomentAF_mean M hM h2M h3M 2 (by decide)
  simpa only [show 2 + 1 = 3 from rfl, show Nat.factorial 3 = 6 from rfl,
    Nat.cast_ofNat, scalarSieveEulerConstant] using h

theorem tendsto_scalarMomentAF_two_mean (M : ℕ) (hM : 0 < M)
    (h2M : 2 ∣ M) (h3M : 3 ∣ M) :
    Tendsto (fun x : ℝ => abelCumulative (scalarMomentAF M 2) x / (Real.log x) ^ 2)
      atTop (𝓝 (scalarSieveEulerConstant M * (coprimeHarmonicDensity M ^ 2 / 2))) := by
  have h := tendsto_scalarMomentAF_mean M hM h2M h3M 1 (by decide)
  simp only [show 1 + 1 = 2 from rfl, show Nat.factorial 2 = 2 from rfl, Nat.cast_ofNat] at h
  rw [scalarMomentCorrectionAF_tsum_two_eq_three M h2M h3M] at h
  exact h

end Erdos964
