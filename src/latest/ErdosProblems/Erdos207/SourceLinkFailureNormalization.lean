/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceLinkJointForbiddenProbability
import ErdosProblems.Erdos207.FutureTypicalityPowerBudgets

/-! # Exact source-link moment normalization and finite polynomial-error budgets -/

namespace Erdos207

open scoped NNReal

def sourceLinkMomentMainCoefficient (k j s : ℕ) (C y : ℝ≥0) : ℝ≥0 :=
  (C^2)^(4*(j-2))*(boundedIntersectionMomentCoefficient (4*(j-2)) s : ℝ≥0)*
    ((4 : ℝ≥0)^(j-2)*((1+(k+1)^2 : ℕ)*(j^k : ℕ))*y)

def sourceLinkMomentErrorCoefficient (j : ℕ) (C : ℝ≥0) : ℝ≥0 :=
  (C^2)^(4*(j-2))*(4 : ℝ≥0)^(j-2)

theorem divided_configuration_moment_normalization
    (A K b P R : ℝ≥0) (d s : ℕ) :
    A^(s*d)*(K^s+b*P^s)/R^s = (A^d*K/R)^s+b*(A^d*P/R)^s := by
  rw [mul_add, add_div, quasi_moment_error_normalization]
  congr 1
  rw [Nat.mul_comm s d, pow_mul, ← mul_pow, ← div_pow]

theorem sourceLinkFailureBound_normalized
    (k j s N cap : ℕ) (C b y : ℝ≥0) :
    sourceLinkFailureBound k j s N cap C b y =
      (sourceLinkMomentMainCoefficient k j s C y/(cap+1 : ℝ≥0))^s+
        b*(sourceLinkMomentErrorCoefficient j C*(N+1 : ℝ≥0)^(3*j)/(cap+1 : ℝ≥0))^s := by
  simp only [sourceLinkFailureBound, divided_configuration_moment_normalization,
    sourceLinkMomentMainCoefficient, sourceLinkMomentErrorCoefficient, mul_assoc]

theorem sourceLinkFailureBound_power_le
    (k j s N cap R f B decay : ℕ) (t C b y kappa : ℝ≥0)
    (ht : 1 ≤ t) (hkappa : 0 < kappa) (hN : (N : ℝ≥0) ≤ t^R)
    (hcap : kappa*t^f ≤ cap+1) (herror : b ≤ 1/t^B)
    (hmain : decay ≤ f*s) (herrorGap : R*(3*j)*s+decay ≤ B) :
    sourceLinkFailureBound k j s N cap C b y ≤
      ((sourceLinkMomentMainCoefficient k j s C y/kappa)^s+
        (sourceLinkMomentErrorCoefficient j C*2^(3*j))^s)/t^decay := by
  let K := sourceLinkMomentMainCoefficient k j s C y
  let P := sourceLinkMomentErrorCoefficient j C
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hN' : (N+1 : ℝ≥0) ≤ 2*t^R := by
    have hone : (1 : ℝ≥0) ≤ t^R := one_le_pow₀ ht
    calc
      _ ≤ t^R+t^R := add_le_add hN hone
      _ = _ := by ring
  have hmainRatio : K/(cap+1 : ℝ≥0) ≤ (K/kappa)/t^f := by
    calc
      _ ≤ K/(kappa*t^f) := div_le_div_of_nonneg_left zero_le (by positivity) hcap
      _ = _ := by ring
  have hmainTerm : (K/(cap+1 : ℝ≥0))^s ≤ (K/kappa)^s/t^decay := by
    calc
      _ ≤ ((K/kappa)/t^f)^s := pow_le_pow_left' hmainRatio s
      _ = (K/kappa)^s/t^(f*s) := by rw [div_pow, pow_mul]
      _ ≤ _ := div_le_div_of_nonneg_left zero_le (pow_pos ht0 _) (pow_le_pow_right₀ ht hmain)
  have herrorRatio : P*(N+1 : ℝ≥0)^(3*j)/(cap+1 : ℝ≥0) ≤ (P*2^(3*j))*t^(R*(3*j)) := by
    calc
      _ ≤ P*(N+1 : ℝ≥0)^(3*j)/1 :=
        div_le_div_of_nonneg_left zero_le zero_lt_one (le_add_of_nonneg_left zero_le)
      _ ≤ P*(2*t^R)^(3*j) := by rw [div_one]; gcongr
      _ = _ := by rw [mul_pow, pow_mul]; ring
  have herrorTerm := finite_moment_error_power_decay t b (P*(N+1 : ℝ≥0)^(3*j)/(cap+1 : ℝ≥0))
    (P*2^(3*j)) B (R*(3*j)) s decay ht herror herrorRatio herrorGap
  rw [sourceLinkFailureBound_normalized, add_div]
  exact add_le_add hmainTerm herrorTerm

end Erdos207
