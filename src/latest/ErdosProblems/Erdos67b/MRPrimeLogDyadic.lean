import ErdosProblems.Erdos67b.MRPrimeLogTransition

/-! # Uniform dyadic logarithmic sums from low to polynomial heights -/

open scoped BigOperators

namespace Erdos67b

noncomputable section

open LogWeylParameters ResidueLogPhase

theorem mrExists_primeMellin_allHeight_dyadic_bound (R : ℕ) (hR : 2 ≤ R) :
    ∃ A₀ : ℕ, 1 ≤ A₀ ∧ ∀ {A M : ℕ}, A₀ ≤ A → M ≤ 2 * A →
      ∀ {t : ℝ}, t ≠ 0 → positiveLogCoefficient t < (A : ℝ) ^ (R + 1) →
        ‖∑ n ∈ Finset.Icc A M, mrPrimeMellinMonomial 0 t n‖ ≤
          3 * (A : ℝ) / positiveLogCoefficient t +
          (mrPrimeWeylConstant R + 20) * (A : ℝ) ^ (1 - savingExponent R) := by
  obtain ⟨A₁, hA₁one, hA₁⟩ := mrExists_primeMellin_dyadic_power_bound R hR
  obtain ⟨A₂, hA₂one, hA₂⟩ := mrExists_primeMellin_transition_power_bound R hR
  refine ⟨max A₁ A₂, hA₁one.trans (Nat.le_max_left _ _), ?_⟩
  intro A M hA hM t ht hu
  have hAfirst : A₁ ≤ A := (Nat.le_max_left A₁ A₂).trans hA
  have hAsecond : A₂ ≤ A := (Nat.le_max_right A₁ A₂).trans hA
  have hAone : 1 ≤ A := hA₁one.trans hAfirst
  have hAR : (1 : ℝ) ≤ A := by exact_mod_cast hAone
  have ha := positiveLogCoefficient_pos ht
  have hC := mrPrimeWeylConstant_pos R
  have hd := mrSavingExponent_le_one_div_sixtyFour hR
  have hV : 1 ≤ (A : ℝ) ^ (1 - savingExponent R) :=
    Real.one_le_rpow hAR (by linarith)
  have hlow : 0 ≤ 3 * (A : ℝ) / positiveLogCoefficient t := by positivity
  by_cases hsmall : positiveLogCoefficient t ≤ (A : ℝ) / 2
  · have hb := mrNorm_primeMellin_dyadic_le_firstDerivative hAone hM ht hsmall
    nlinarith
  by_cases hmiddle : positiveLogCoefficient t ≤ (A : ℝ)
  · have hb := hA₂ hAsecond hM (by linarith : (A : ℝ) ≤ 2 * positiveLogCoefficient t)
      hmiddle
    nlinarith
  · have hb := hA₁ hAfirst hM (by linarith : (A : ℝ) ≤ positiveLogCoefficient t) hu
    nlinarith

end

end Erdos67b
