/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceMomentPowerBudgets
import ErdosProblems.Erdos207.SourceLinkFailureNormalization

/-! # Uniform eventual source-moment bounds with explicit finite exponents -/

namespace Erdos207

open scoped NNReal

theorem inverse_power_absorb_coefficient (t A : ℝ≥0) (e : ℕ)
    (ht : 0 < t) (hA : A ≤ t) : A/t^(e+1) ≤ 1/t^e := by
  calc
    _ ≤ t/t^(e+1) := div_le_div_of_nonneg_right hA zero_le
    _ = _ := by rw [pow_succ]; field_simp

theorem eventually_sourceLeftFailureBound_le_power
    (k j R b reserveExp decay : ℕ) (C y epsilon0 B0 : ℝ≥0)
    (hb : 1 ≤ b) (hepsilon0 : 0 < epsilon0) :
    ∃ s B T : ℕ, 0 < s ∧ 1 ≤ B ∧ 1 ≤ T ∧ ∀ t : ℕ, T ≤ t →
      ∀ (N : ℕ) (p r beta epsilon n : ℝ≥0), N ≤ t^R → 1 ≤ n →
        1/(t : ℝ≥0)^b ≤ p → p ≤ 2/(t : ℝ≥0)^b → 1/(t : ℝ≥0)^reserveExp ≤ r →
        epsilon0 ≤ epsilon → beta ≤ B0/(t : ℝ≥0)^B →
        sourceLeftFailureBound k j s N p r C beta y epsilon n ≤ 1/(t : ℝ≥0)^decay := by
  let s := decay+1
  let B := (R*(3*j)+2*b+2*reserveExp)*s+decay+1
  let K : ℝ≥0 := (C^2)^(j-1)*(boundedIntersectionMomentCoefficient (j-1) s : ℝ≥0)*
    2^(j-2)*(k+3 : ℕ)*(j^k : ℕ)*y
  let P : ℝ≥0 := (C^2)^(j-1)*2^(j-2)*2^(3*j)/epsilon0
  let coefficient := (2*K/epsilon0)^s+B0*P^s
  let T := max 1 ⌈coefficient⌉₊
  refine ⟨s, B, T, by dsimp only [s]; omega, by dsimp only [B]; omega, le_max_left _ _, ?_⟩
  intro t ht N p r beta epsilon n hN hn hp hpUpper hr hepsilon hbeta
  have ht1 : (1 : ℝ≥0) ≤ t := by exact_mod_cast (le_max_left 1 ⌈coefficient⌉₊).trans ht
  have hcoef : coefficient ≤ (t : ℝ≥0) := (Nat.le_ceil _).trans
    (by exact_mod_cast (le_max_right 1 ⌈coefficient⌉₊).trans ht)
  have hgap : decay+1 ≤ b*s := by
    dsimp only [s]
    simpa only [one_mul] using Nat.mul_le_mul_right (decay+1) hb
  have hbound := sourceLeftFailureBound_power_le k j s N R b reserveExp B (decay+1)
    t p r C beta y epsilon epsilon0 n B0 ht1 hepsilon0 hepsilon hp hpUpper hr
    (by exact_mod_cast hN) hn hbeta hgap (by dsimp only [B]; omega)
  exact hbound.trans (inverse_power_absorb_coefficient t coefficient decay (zero_lt_one.trans_le ht1) hcoef)

theorem eventually_sourceQuasiUniformFailureBound_le_power
    (k j h R b decay : ℕ) (C y epsilon0 eta0 B0 : ℝ≥0)
    (hb : 2 ≤ b) (hepsilon0 : 0 < epsilon0) (heta0 : 0 < eta0) :
    ∃ s B T : ℕ, 0 < s ∧ 1 ≤ B ∧ 1 ≤ T ∧ ∀ t : ℕ, T ≤ t →
      ∀ (N : ℕ) (p beta epsilon eta n : ℝ≥0), N ≤ t^R → 1 ≤ n →
        1/(t : ℝ≥0)^b ≤ p → p ≤ 2/(t : ℝ≥0)^b →
        epsilon0/t ≤ epsilon → eta0 ≤ eta → beta ≤ B0/(t : ℝ≥0)^B →
        sourceQuasiUniformFailureBound k j s h N p C beta y epsilon eta n ≤ 1/(t : ℝ≥0)^decay := by
  let s := decay+1
  let B := (R*(3*j)+b*h+1)*s+decay+1
  let K : ℝ≥0 := C^(j-3+h)*(boundedIntersectionMomentCoefficient (j-3+h) s : ℝ≥0)*
    2^(j-2)*(k+3 : ℕ)*(j^k : ℕ)*y
  let P : ℝ≥0 := C^(j-3+h)*2^(j-2)*2^(3*j)/(epsilon0*eta0^(h^2))
  let coefficient := (2*K/(epsilon0*eta0^(h^2)))^s+B0*P^s
  let T := max 1 ⌈coefficient⌉₊
  refine ⟨s, B, T, by dsimp only [s]; omega, by dsimp only [B]; omega, le_max_left _ _, ?_⟩
  intro t ht N p beta epsilon eta n hN hn hp hpUpper hepsilon heta hbeta
  have ht1 : (1 : ℝ≥0) ≤ t := by exact_mod_cast (le_max_left 1 ⌈coefficient⌉₊).trans ht
  have hcoef : coefficient ≤ (t : ℝ≥0) := (Nat.le_ceil _).trans
    (by exact_mod_cast (le_max_right 1 ⌈coefficient⌉₊).trans ht)
  have hbound := sourceQuasiUniformFailureBound_power_le k j s h N R b B (decay+1)
    t p C beta y epsilon epsilon0 eta eta0 n B0 ht1 hepsilon0 heta0 hepsilon heta hp hpUpper hb
    (by exact_mod_cast hN) hn hbeta le_rfl (by dsimp only [B]; omega)
  exact hbound.trans (inverse_power_absorb_coefficient t coefficient decay (zero_lt_one.trans_le ht1) hcoef)

theorem eventually_sourceLinkFailureBound_le_power
    (k j R decay : ℕ) (C y kappa B0 : ℝ≥0) (hkappa : 0 < kappa) :
    ∃ s B T : ℕ, 0 < s ∧ 1 ≤ B ∧ 1 ≤ T ∧ ∀ t : ℕ, T ≤ t →
      ∀ (N cap : ℕ) (beta : ℝ≥0), N ≤ t^R → kappa*t ≤ cap+1 →
        beta ≤ B0/(t : ℝ≥0)^B →
        sourceLinkFailureBound k j s N cap C beta y ≤ 1/(t : ℝ≥0)^decay := by
  let s := decay+1
  let B := R*(3*j)*s+decay+2
  let coefficient : ℝ≥0 := (sourceLinkMomentMainCoefficient k j s C y/kappa)^s+
    (sourceLinkMomentErrorCoefficient j C*2^(3*j))^s
  let T := max 1 (max ⌈coefficient⌉₊ ⌈B0⌉₊)
  refine ⟨s, B, T, by dsimp only [s]; omega, by dsimp only [B]; omega, le_max_left _ _, ?_⟩
  intro t ht N cap beta hN hcap hbeta
  have ht1 : (1 : ℝ≥0) ≤ t := by exact_mod_cast (le_max_left 1 _).trans ht
  have hcoef : coefficient ≤ (t : ℝ≥0) := (Nat.le_ceil _).trans
    (by exact_mod_cast (le_max_left ⌈coefficient⌉₊ ⌈B0⌉₊).trans ((le_max_right 1 _).trans ht))
  have hB0 : B0 ≤ (t : ℝ≥0) := (Nat.le_ceil _).trans
    (by exact_mod_cast (le_max_right ⌈coefficient⌉₊ ⌈B0⌉₊).trans ((le_max_right 1 _).trans ht))
  have hbeta' : beta ≤ 1/(t : ℝ≥0)^(R*(3*j)*s+decay+1) := by
    exact hbeta.trans (inverse_power_absorb_coefficient t B0 _ (zero_lt_one.trans_le ht1) hB0)
  have hbound := sourceLinkFailureBound_power_le k j s N cap R 1 (R*(3*j)*s+decay+1) (decay+1)
    t C beta y kappa ht1 hkappa (by exact_mod_cast hN) (by simpa only [pow_one] using hcap)
    hbeta' (by dsimp only [s]; omega) (by omega)
  exact hbound.trans (inverse_power_absorb_coefficient t coefficient decay (zero_lt_one.trans_le ht1) hcoef)

end Erdos207
