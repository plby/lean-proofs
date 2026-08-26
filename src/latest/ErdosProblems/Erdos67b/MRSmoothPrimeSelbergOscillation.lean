import ErdosProblems.Erdos67b.MRSmoothPrimeOscillation
import ErdosProblems.Erdos67b.MRSmoothPrimeSelbergKernel

/-! # Oscillation of the actual positive Selberg prime kernel

The cutoff and polynomial-height conditions remain quantitative. There is
no assumed bound on the progression sums: they are supplied by the proved
first-derivative, transition, fixed-depth, and finite Abel estimates.
-/

open scoped BigOperators

namespace Erdos67b

noncomputable section

open LogWeylParameters ResidueLogPhase

theorem mrExists_smoothPrime_uniform_progression_oscillation (R : ℕ) (hR : 2 ≤ R) :
    ∃ A₀ : ℕ, 1 ≤ A₀ ∧ ∀ {P : ℝ}, 0 < P →
      ∀ {D : ℕ}, 1 ≤ D → 2 * (D : ℝ) ^ 2 ≤ P →
        (A₀ : ℝ) ≤ P / (2 * (D : ℝ) ^ 2) →
      ∀ {t : ℝ}, t ≠ 0 → positiveLogCoefficient t <
        (P / (2 * (D : ℝ) ^ 2)) ^ (R + 1) →
      ∀ {q : ℕ}, 0 < q → q ≤ D ^ 2 →
      ‖∑ n ∈ Finset.Icc ⌈P / 2⌉₊ ⌊3 * P⌋₊ with q ∣ n,
        mrSmoothPrimeKernelIntegrand P t n‖ ≤
        1400 * (3 * P / positiveLogCoefficient t +
          (mrPrimeWeylConstant R + 20) * P ^ (1 - savingExponent R)) := by
  obtain ⟨A₀, hA₀one, hA₀⟩ := mrExists_smoothPrime_progression_oscillation R hR
  refine ⟨A₀, hA₀one, ?_⟩
  intro P hP D hD hDP hscale t ht hu q hq hqD
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hqOne : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hqDR : (q : ℝ) ≤ (D : ℝ) ^ 2 := by exact_mod_cast hqD
  have hqP : 2 * (q : ℝ) ≤ P := by linarith
  let a : ℝ := (P / 2) / (q : ℝ)
  let A : ℕ := ⌈a⌉₊
  have ha : 1 ≤ a := (le_div_iff₀ hqR).2 (by linarith)
  have hN : P / (2 * (D : ℝ) ^ 2) ≤ a := by
    calc
      _ = (P / 2) / (D : ℝ) ^ 2 := by ring
      _ ≤ (P / 2) / (q : ℝ) := div_le_div_of_nonneg_left (by positivity) hqR hqDR
  have hceil : a ≤ (A : ℝ) := Nat.le_ceil _
  have hA : A₀ ≤ A := by exact_mod_cast hscale.trans (hN.trans hceil)
  have hAP : (A : ℝ) ≤ P := by
    have hh := Nat.ceil_lt_add_one (show 0 ≤ a by linarith)
    have hratio : 2 * a ≤ P := by
      have hdiv : P / (q : ℝ) ≤ P := (div_le_iff₀ hqR).2 (by nlinarith)
      calc
        _ = P / (q : ℝ) := by dsimp [a]; ring
        _ ≤ P := hdiv
    change (⌈a⌉₊ : ℝ) ≤ P
    linarith
  have hheight : positiveLogCoefficient t < (A : ℝ) ^ (R + 1) :=
    hu.trans_le (pow_le_pow_left₀ (by positivity) (hN.trans hceil) _)
  have hb := hA₀ hP hq hqP hA ht hheight
  have haFreq := positiveLogCoefficient_pos ht
  have hC := mrPrimeWeylConstant_pos R
  have hd := mrSavingExponent_le_one_div_sixtyFour hR
  have hpow : (A : ℝ) ^ (1 - savingExponent R) ≤ P ^ (1 - savingExponent R) :=
    Real.rpow_le_rpow (Nat.cast_nonneg A) hAP (by linarith)
  apply hb.trans
  gcongr

theorem mrExists_smoothPrimeSelberg_oscillation (R : ℕ) (hR : 2 ≤ R) :
    ∃ A₀ : ℕ, 1 ≤ A₀ ∧ ∀ {P : ℝ}, 0 < P →
      ∀ (D : ℕ) (hD : 1 ≤ D), 2 * (D : ℝ) ^ 2 ≤ P →
        (A₀ : ℝ) ≤ P / (2 * (D : ℝ) ^ 2) →
      ∀ {t : ℝ}, t ≠ 0 → positiveLogCoefficient t <
        (P / (2 * (D : ℝ) ^ 2)) ^ (R + 1) →
      ‖mrSmoothPrimeSelbergKernel D hD P t‖ ≤
        1400 * (D : ℝ) ^ 2 * (3 * P / positiveLogCoefficient t +
          (mrPrimeWeylConstant R + 20) * P ^ (1 - savingExponent R)) := by
  obtain ⟨A₀, hA₀one, hA₀⟩ := mrExists_smoothPrime_uniform_progression_oscillation R hR
  refine ⟨A₀, hA₀one, ?_⟩
  intro P hP D hD hDP hscale t ht hu
  have hE : 0 ≤ 1400 * (3 * P / positiveLogCoefficient t +
      (mrPrimeWeylConstant R + 20) * P ^ (1 - savingExponent R)) := by
    have := positiveLogCoefficient_pos ht
    have := mrPrimeWeylConstant_pos R
    positivity
  have hb := mrPrimeSelberg_weighted_error_le D hD (mrSmoothPrimeKernelSupport P)
    (fun n ↦ mrSmoothPrimeKernelIntegrand P t n) 0 hE (by
      intro q hq hqD
      simpa only [zero_div, sub_zero, mrSmoothPrimeKernelSupport] using
        hA₀ hP hD hDP hscale ht hu hq hqD)
  simp only [mul_zero, sub_zero] at hb
  change ‖mrSmoothPrimeSelbergKernel D hD P t‖ ≤ _ at hb
  exact hb.trans (by ring_nf; exact le_rfl)

end

end Erdos67b
