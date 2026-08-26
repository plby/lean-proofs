import ErdosProblems.Erdos67b.MRPrimeBlockMass

/-!
# Finite beta-sieve density for moving auxiliary intervals

One fixed admissible sieve depth is chosen before both logarithmic
endpoints and the ambient scale. Its explicit remainder is bounded by
`exp (2 * S * b)` and then by a half-power of the ambient scale.
-/

namespace Erdos67b

noncomputable section

theorem mrAuxiliaryInterval_logRatio_le {a b : ℝ} (ha : 2 ≤ a) (hab : 2 * a ≤ b) :
    Real.log (((mrLogPrimeInterval a b).1 - 1 : ℕ) : ℝ) /
        Real.log ((mrLogPrimeInterval a b).2 : ℝ) ≤ 2 * a / b := by
  obtain ⟨_, _, hlow, hhigh⟩ := mrLogPrimeInterval_endpoint_bounds ha hab
  have hb : 0 < b / 2 := by linarith
  calc
    _ ≤ a / Real.log ((mrLogPrimeInterval a b).2 : ℝ) :=
      div_le_div_of_nonneg_right hlow (hb.le.trans hhigh)
    _ ≤ a / (b / 2) := div_le_div_of_nonneg_left (by linarith) hb hhigh
    _ = _ := by ring

theorem mrAuxiliaryInterval_sieveRemainder_le (a b : ℝ) (S : ℕ) :
    (((mrLogPrimeInterval a b).2 ^ S : ℕ) : ℝ) ^ 2 ≤
      Real.exp (2 * (S : ℝ) * b) := by
  have hu : ((mrLogPrimeInterval a b).2 : ℝ) ≤ Real.exp b :=
    Nat.floor_le (Real.exp_pos _).le
  calc
    _ ≤ (Real.exp b ^ S) ^ 2 := by push_cast; gcongr
    _ = Real.exp (2 * (S : ℝ) * b) := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
      congr 1
      push_cast
      ring

theorem mrExists_auxiliaryMissing_finite_density_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ S : ℕ, 101 ≤ S ∧
      ∀ (a b : ℝ) (Z : ℕ), 2 ≤ a → 2 * a ≤ b →
        ((missingPrimeBlockSet (mrLogPrimeInterval a b) Z).card : ℝ) ≤
          C * (a / b) * Z + Real.exp (2 * (S : ℝ) * b) := by
  obtain ⟨A, hA, hbeta⟩ := exists_card_missingPrimeBlockSet_mertens_beta_bound
  obtain ⟨S, hS, hlog⟩ := exists_admissible_betaSieveDepth A
  let K := (1 + (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)) *
    Real.exp (2 * PrimeEstimates.mertensBound)
  have hK : 0 < K := by
    have hA0 : 0 ≤ A := by linarith
    dsimp only [K]
    positivity
  refine ⟨2 * K, by positivity, S, hS, ?_⟩
  intro a b Z ha hab
  have hend := mrLogPrimeInterval_endpoint_bounds ha hab
  have hbase := hbeta Z (mrLogPrimeInterval a b).1 (mrLogPrimeInterval a b).2 S
    hend.1 hend.2.1 hS hlog
  have hbase' : ((missingPrimeBlockSet (mrLogPrimeInterval a b) Z).card : ℝ) ≤
      (Z : ℝ) * (K * (Real.log (((mrLogPrimeInterval a b).1 - 1 : ℕ) : ℝ) /
        Real.log ((mrLogPrimeInterval a b).2 : ℝ))) +
      (((mrLogPrimeInterval a b).2 ^ S : ℕ) : ℝ) ^ 2 := by
    simpa only [K, mul_assoc] using hbase
  calc
    _ ≤ (Z : ℝ) * (K * (2 * a / b)) + Real.exp (2 * (S : ℝ) * b) :=
      hbase'.trans (add_le_add
        (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (mrAuxiliaryInterval_logRatio_le ha hab) hK.le)
          (Nat.cast_nonneg _)) (mrAuxiliaryInterval_sieveRemainder_le a b S))
    _ = _ := by ring

theorem mrExists_auxiliaryMissing_normalized_density_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ S : ℕ, 101 ≤ S ∧
      ∀ {X : ℕ}, 0 < X → ∀ (a b : ℝ), 2 ≤ a → 2 * a ≤ b →
        b ≤ Real.log (X : ℝ) / Real.log (Real.log (X : ℝ)) →
        4 * (S : ℝ) ≤ Real.log (Real.log (X : ℝ)) →
        ((missingPrimeBlockSet (mrLogPrimeInterval a b) (2 * X)).card : ℝ) / X ≤
          2 * C * (a / b) + Real.exp (-Real.log (X : ℝ) / 2) := by
  obtain ⟨C, hC, S, hS, hfinite⟩ := mrExists_auxiliaryMissing_finite_density_bound
  refine ⟨C, hC, S, hS, ?_⟩
  intro X hX a b ha hab hb hLL
  have hXr : (0 : ℝ) < X := by exact_mod_cast hX
  have hL : 0 ≤ Real.log (X : ℝ) := Real.log_nonneg (by exact_mod_cast hX)
  have hSr : (101 : ℝ) ≤ S := by exact_mod_cast hS
  have hLLpos : 0 < Real.log (Real.log (X : ℝ)) := by linarith
  have hpaid : 2 * (S : ℝ) * b ≤ Real.log (X : ℝ) / 2 := by
    calc
      _ ≤ 2 * (S : ℝ) * (Real.log (X : ℝ) / Real.log (Real.log (X : ℝ))) := by
        gcongr
      _ = (2 * (S : ℝ) * Real.log (X : ℝ)) / Real.log (Real.log (X : ℝ)) := by ring
      _ ≤ Real.log (X : ℝ) / 2 := by
        apply (div_le_iff₀ hLLpos).mpr
        have hh := mul_le_mul_of_nonneg_right hLL hL
        nlinarith
  have hrem : Real.exp (2 * (S : ℝ) * b) / X ≤ Real.exp (-Real.log (X : ℝ) / 2) := by
    calc
      _ ≤ Real.exp (Real.log (X : ℝ) / 2) / X :=
        div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hpaid) hXr.le
      _ = Real.exp (Real.log (X : ℝ) / 2) / Real.exp (Real.log (X : ℝ)) := by
        rw [Real.exp_log hXr]
      _ = Real.exp (-Real.log (X : ℝ) / 2) := by
        rw [← Real.exp_sub]
        congr 1
        ring
  calc
    _ ≤ (C * (a / b) * (2 * X : ℕ) + Real.exp (2 * (S : ℝ) * b)) / X :=
      div_le_div_of_nonneg_right (hfinite a b (2 * X) ha hab) hXr.le
    _ = 2 * C * (a / b) + Real.exp (2 * (S : ℝ) * b) / X := by
      push_cast
      field_simp
    _ ≤ _ := add_le_add le_rfl hrem

end

end Erdos67b
