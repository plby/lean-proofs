/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.KSSSSharpPowerBudgets

/-! # Sparse pair ratios with separate analytic and stopping-density exponents -/

namespace Erdos207

open Finset

noncomputable section

theorem sparse_pair_error_power_budget
    (N t p x : ℝ) (s b c B : ℕ) (hN : 0 < N) (ht : 1 ≤ t)
    (hp : 1 / t ^ c ≤ p) (hx : 3 * (N / t ^ b) * p ^ 2 / t ≤ x)
    (hexp : b + c * (B + 3) + 2 ≤ s) :
    (N / t ^ s) / p ^ B ≤ (2 / t ^ (c + 1)) * x := by
  have htpos : 0 < t := by linarith
  have hppos : 0 < p := (by positivity : 0 < 1 / t ^ c).trans_le hp
  have hinverse := inverse_density_power_le t p c (B + 2) htpos hppos hp
  have hpow : t ^ (b + c * (B + 3) + 2) ≤ t ^ s := pow_le_pow_right₀ ht hexp
  have hgap : t ^ (b + 1) * t ^ (c * (B + 2)) / t ^ s ≤ 1 / t ^ (c + 1) := by
    apply (div_le_div_iff₀ (pow_pos htpos s) (pow_pos htpos _)).mpr
    simpa only [one_mul, ← pow_add, show b + 1 + c * (B + 2) + (c + 1) = b + c * (B + 3) + 2 by ring] using hpow
  have hrelative : ((N / t ^ s) / p ^ B) / (3 * (N / t ^ b) * p ^ 2 / t) ≤ 1 / (3 * t ^ (c + 1)) := by
    calc
      _ = (t ^ (b + 1) / (3 * t ^ s)) * (1 / p ^ (B + 2)) := by
        rw [pow_succ, pow_add]
        field_simp
        ring
      _ ≤ (t ^ (b + 1) / (3 * t ^ s)) * t ^ (c * (B + 2)) :=
        mul_le_mul_of_nonneg_left hinverse (by positivity)
      _ = (t ^ (b + 1) * t ^ (c * (B + 2)) / t ^ s) / 3 := by ring
      _ ≤ (1 / t ^ (c + 1)) / 3 := div_le_div_of_nonneg_right hgap (by norm_num)
      _ = _ := by ring
  have hlowerpos : 0 < 3 * (N / t ^ b) * p ^ 2 / t := by positivity
  have herr := (div_le_iff₀ hlowerpos).mp hrelative
  calc
    _ ≤ (1 / (3 * t ^ (c + 1))) * (3 * (N / t ^ b) * p ^ 2 / t) := herr
    _ ≤ (2 / t ^ (c + 1)) * x := by
      apply mul_le_mul _ hx hlowerpos.le (by positivity)
      apply (div_le_div_iff₀ (by positivity : 0 < 3 * t ^ (c + 1)) (pow_pos htpos _)).mpr
      nlinarith only [pow_pos htpos (c + 1)]

theorem ksssPairTrajectory_lower_power_ratio
    (orders : Finset ℕ) (a coeff : ℕ → ℝ) (E A time N t : ℝ) (b : ℕ)
    (hE : 0 < E) (hN : 0 < N) (ht : 0 < t) (htime : 0 ≤ time) (hclock : 3 * time < E)
    (ha : ∀ d ∈ orders, 0 ≤ a d) (hab : ∀ d ∈ orders, a d * E ^ d ≤ coeff d)
    (hratio : N / t ^ b ≤ A / E) (hexp : Real.exp (∑ d ∈ orders, coeff d) ≤ t) :
    3 * (N / t ^ b) * ksssEdgeDensity E time ^ 2 / t ≤ ksssPairTrajectory orders a E A time := by
  have hp := ksssEdgeDensity_pos hE hclock
  have he := ksssPoisson_exp_neg_ge_inverse_scale orders a coeff E time t ha hab htime (by linarith) hexp
  rw [ksssPairTrajectory_source orders a E A time hE.ne' hp.ne']
  calc
    _ = ksssEdgeDensity E time ^ 2 * (1 / t) * (3 * (N / t ^ b)) := by ring
    _ ≤ ksssEdgeDensity E time ^ 2 * Real.exp (-ksssPoissonExponent orders a time) * (3 * (A / E)) := by gcongr
    _ = _ := by ring

theorem ksss_pair_relative_error_sparse
    (orders : Finset ℕ) (a coeff : ℕ → ℝ) (E A time N t : ℝ) (b c B : ℕ)
    (hE : 0 < E) (hN : 0 < N) (ht : 1 ≤ t) (htime : 0 ≤ time) (hclock : 3 * time < E)
    (ha : ∀ d ∈ orders, 0 ≤ a d) (hab : ∀ d ∈ orders, a d * E ^ d ≤ coeff d)
    (hratio : N / t ^ b ≤ A / E) (hexp : Real.exp (∑ d ∈ orders, coeff d) ≤ t)
    (hfloor : 1 / t ^ c ≤ ksssEdgeDensity E time) (hgap : 2 * c ≤ b) :
    ksssErrorEnvelope E (N / t ^ ksssPowerErrorExponent b B) B time ≤
      (2 / t ^ (c + 1)) * ksssPairTrajectory orders a E A time := by
  apply sparse_pair_error_power_budget N t _ _ (ksssPowerErrorExponent b B) b c B hN ht hfloor
    (ksssPairTrajectory_lower_power_ratio orders a coeff E A time N t b hE hN (by linarith)
      htime hclock ha hab hratio hexp)
  have hmul := Nat.mul_le_mul_right (B + 2) hgap
  dsimp only [ksssPowerErrorExponent]
  nlinarith only [hmul, Nat.zero_le (c * B), Nat.zero_le c]

end

end Erdos207
