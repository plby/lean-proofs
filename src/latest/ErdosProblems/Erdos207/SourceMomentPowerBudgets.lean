/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceLeftCapsProbability
import ErdosProblems.Erdos207.FutureQuasiSourceProbability
import ErdosProblems.Erdos207.ReserveOverlapPowerBudgets

/-! # Explicit source left and quasi tails with the full incoming error coefficient -/

namespace Erdos207

open scoped NNReal

theorem two_term_moment_power_le
    (t main errorFactor beta A P B0 : ℝ≥0) (a d s B decay : ℕ)
    (ht : 1 ≤ t) (hmain : main ≤ A/t^a) (hfactor : errorFactor ≤ P*t^d)
    (hbeta : beta ≤ B0/t^B) (hmainGap : decay ≤ a*s) (herrorGap : d*s+decay ≤ B) :
    main^s+beta*errorFactor^s ≤ (A^s+B0*P^s)/t^decay := by
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hm : main^s ≤ A^s/t^decay := by
    calc
      _ ≤ (A/t^a)^s := pow_le_pow_left' hmain s
      _ = A^s/t^(a*s) := by rw [div_pow, pow_mul]
      _ ≤ _ := div_le_div_of_nonneg_left zero_le (pow_pos ht0 _) (pow_le_pow_right₀ ht hmainGap)
  rw [add_div]
  exact add_le_add hm (finite_moment_error_power_decay_with_coefficient t beta errorFactor P B0
    B d s decay ht hbeta hfactor herrorGap)

theorem sourceLeftFailureBound_power_le
    (k j s N R b reserveExp B decay : ℕ) (t p r C beta y epsilon epsilon0 n B0 : ℝ≥0)
    (ht : 1 ≤ t) (hepsilon0 : 0 < epsilon0) (hepsilon : epsilon0 ≤ epsilon)
    (hp : 1/t^b ≤ p) (hpUpper : p ≤ 2/t^b) (hr : 1/t^reserveExp ≤ r)
    (hN : (N : ℝ≥0) ≤ t^R) (hn : 1 ≤ n) (hbeta : beta ≤ B0/t^B)
    (hmainGap : decay ≤ b*s) (herrorGap : (R*(3*j)+2*b+2*reserveExp)*s+decay ≤ B) :
    let K : ℝ≥0 := (C^2)^(j-1)*(boundedIntersectionMomentCoefficient (j-1) s : ℝ≥0)*
      2^(j-2)*(k+3 : ℕ)*(j^k : ℕ)*y
    let P : ℝ≥0 := (C^2)^(j-1)*2^(j-2)*2^(3*j)/epsilon0
    sourceLeftFailureBound k j s N p r C beta y epsilon n ≤
      ((2*K/epsilon0)^s+B0*P^s)/t^decay := by
  dsimp only
  let K : ℝ≥0 := (C^2)^(j-1)*(boundedIntersectionMomentCoefficient (j-1) s : ℝ≥0)*
    2^(j-2)*(k+3 : ℕ)*(j^k : ℕ)*y
  let P : ℝ≥0 := (C^2)^(j-1)*2^(j-2)*2^(3*j)/epsilon0
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hmain : K*p/epsilon ≤ (2*K/epsilon0)/t^b := by
    calc
      _ ≤ K*(2/t^b)/epsilon0 := by gcongr
      _ = _ := by ring
  have hNplus : (N+1 : ℝ≥0) ≤ 2*t^R := by
    calc
      _ ≤ t^R+t^R := add_le_add hN (one_le_pow₀ ht)
      _ = _ := by ring
  have hfactor : (C^2)^(j-1)*(2^(j-2)*(N+1 : ℝ≥0)^(3*j))/(epsilon*p^2*r^2*n) ≤
      P*t^(R*(3*j)+2*b+2*reserveExp) := by
    calc
      _ ≤ (C^2)^(j-1)*(2^(j-2)*(2*t^R)^(3*j))/
          (epsilon0*(1/t^b)^2*(1/t^reserveExp)^2*1) := by gcongr
      _ = _ := by
        dsimp only [P]
        simp only [pow_add, pow_mul, mul_pow, div_pow, one_pow, mul_one]
        field_simp
        ring
  have hb := two_term_moment_power_le t (K*p/epsilon) _ beta (2*K/epsilon0) P B0
    b (R*(3*j)+2*b+2*reserveExp) s B decay ht hmain hfactor hbeta hmainGap herrorGap
  simpa only [sourceLeftFailureBound, K, P, mul_assoc] using hb

theorem sourceQuasiUniformFailureBound_power_le
    (k j s h N R b B decay : ℕ) (t p C beta y epsilon epsilon0 eta eta0 n B0 : ℝ≥0)
    (ht : 1 ≤ t) (hepsilon0 : 0 < epsilon0) (heta0 : 0 < eta0)
    (hepsilon : epsilon0/t ≤ epsilon) (heta : eta0 ≤ eta)
    (hp : 1/t^b ≤ p) (hpUpper : p ≤ 2/t^b) (hb : 2 ≤ b)
    (hN : (N : ℝ≥0) ≤ t^R) (hn : 1 ≤ n) (hbeta : beta ≤ B0/t^B)
    (hmainGap : decay ≤ s) (herrorGap : (R*(3*j)+b*h+1)*s+decay ≤ B) :
    let K : ℝ≥0 := C^(j-3+h)*(boundedIntersectionMomentCoefficient (j-3+h) s : ℝ≥0)*
      2^(j-2)*(k+3 : ℕ)*(j^k : ℕ)*y
    let P : ℝ≥0 := C^(j-3+h)*2^(j-2)*2^(3*j)/(epsilon0*eta0^(h^2))
    sourceQuasiUniformFailureBound k j s h N p C beta y epsilon eta n ≤
      ((2*K/(epsilon0*eta0^(h^2)))^s+B0*P^s)/t^decay := by
  dsimp only
  let K : ℝ≥0 := C^(j-3+h)*(boundedIntersectionMomentCoefficient (j-3+h) s : ℝ≥0)*
    2^(j-2)*(k+3 : ℕ)*(j^k : ℕ)*y
  let P : ℝ≥0 := C^(j-3+h)*2^(j-2)*2^(3*j)/(epsilon0*eta0^(h^2))
  have hmain : K*p/(epsilon*eta^(h^2)) ≤ (2*K/(epsilon0*eta0^(h^2)))/t^1 :=
    future_quasi_normalized_main_power_decay t K p epsilon eta epsilon0 eta0 b 1 (h^2) 1
      ht hepsilon0 heta0 hpUpper (by simpa only [pow_one] using hepsilon) heta hb
  have hfactor : C^(j-3+h)*(2^(j-2)*(N+1 : ℝ≥0)^(3*j))/(epsilon*p^h*eta^(h^2)*n) ≤
      P*t^(R*(3*j)+b*h+1) :=
    future_quasi_error_factor_power_le t N n (C^(j-3+h)) (2^(j-2)) p epsilon eta epsilon0 eta0
      R b 1 h (3*j) ht hN hn hp hepsilon0 heta0 (by simpa only [pow_one] using hepsilon) heta
  have hbound := two_term_moment_power_le t (K*p/(epsilon*eta^(h^2))) _ beta
    (2*K/(epsilon0*eta0^(h^2))) P B0 1 (R*(3*j)+b*h+1) s B decay ht hmain hfactor hbeta
      (by simpa only [one_mul] using hmainGap) herrorGap
  simpa only [sourceQuasiUniformFailureBound, K, P, mul_assoc] using hbound

end Erdos207
