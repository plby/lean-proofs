/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTActualDenominators
import ErdosProblems.Erdos4b.FGKMTModulusBounds

/-!
# The dimension-uniform cumulative sieve mean

One absolute constant controls the error for every dimension, every
eligible modulus, every actual sieve denominator, and every positive
integer endpoint. The only parameter loss is the cube of the explicit
logarithm-of-logarithm modulus scale.
-/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

theorem exists_roughSieveWeight_cumulative_error_logScale :
    ∃ C : ℝ, 0 < C ∧ ∀ {k M N : ℕ}, 0 < k → 0 < M → 1 ≤ N →
      (∀ p : ℕ, p.Prime → p ≤ k ^ 2 → p ∣ M) → ∀ g : ℕ → ℝ,
      (∀ p : ℕ, p.Prime → ¬p ∣ M → (p : ℝ) / 2 ≤ g p) →
      (∀ p : ℕ, p.Prime → ¬p ∣ M → |g p - p| ≤ 2 * (k : ℝ)) →
      (∀ p : ℕ, p.Prime → ¬p ∣ M → g p ≤ p - 1) →
      |(∑ n ∈ Finset.Ioc 0 N, roughSieveWeight M g n) -
        sieveMainConstant M g * Real.log N| ≤
          C * sieveMainConstant M g * modulusLogScale M ^ 3 := by
  obtain ⟨A, hA, htotient⟩ := exists_totientRatio_le_logScale
  obtain ⟨B, hB, hmass⟩ := exists_modulusPrimeLogMass_le_logScale
  let C := Real.exp 12 * A ^ 2 * (5 + B)
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro k M N hk hM hN hsmall g hg hclose hupper
  have hc := sieveMainConstant_pos hk hM hsmall g hg hclose hupper
  have hscale := one_le_modulusLogScale M
  have hscale0 : 0 ≤ modulusLogScale M := zero_le_one.trans hscale
  have hmass0 := modulusPrimeLogMass_nonneg M
  have hratio0 : (0 : ℝ) ≤ (M : ℝ) / M.totient := by positivity
  have hpow : ((M : ℝ) / M.totient) ^ 2 ≤ (A * modulusLogScale M) ^ 2 :=
    pow_le_pow_left₀ hratio0 (htotient M hM) 2
  have hmassBound : 5 + modulusPrimeLogMass M ≤ (5 + B) * modulusLogScale M := by
    have h := hmass M hM
    nlinarith
  have hrelative := roughSieveWeight_relative_cumulative_error_le
    hk hM hN hsmall g hg hclose hupper
  change |(∑ n ∈ Finset.Ioc 0 N, roughSieveWeight M g n) -
      sieveMainConstant M g * Real.log N| / sieveMainConstant M g ≤
    Real.exp 12 * ((M : ℝ) / M.totient) ^ 2 * (5 + modulusPrimeLogMass M) at hrelative
  calc
    _ ≤ (Real.exp 12 * ((M : ℝ) / M.totient) ^ 2 *
          (5 + modulusPrimeLogMass M)) * sieveMainConstant M g :=
      (div_le_iff₀ hc).1 hrelative
    _ ≤ (Real.exp 12 * (A * modulusLogScale M) ^ 2 *
          ((5 + B) * modulusLogScale M)) * sieveMainConstant M g := by
      apply mul_le_mul_of_nonneg_right _ hc.le
      exact mul_le_mul (mul_le_mul_of_nonneg_left hpow (Real.exp_pos 12).le)
        hmassBound (by linarith) (by positivity)
    _ = C * sieveMainConstant M g * modulusLogScale M ^ 3 := by
      dsimp [C]
      ring

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.exists_roughSieveWeight_cumulative_error_logScale
