/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.EventualSourceMomentBudgets
import ErdosProblems.Erdos207.SourcePrefixCoefficients

/-! # One fixed moment works simultaneously for every prefix and forbidden order -/

namespace Erdos207

open Finset
open scoped NNReal

theorem eventually_uniform_source_left_moments
    (q ell R b reserveExp decay : ℕ) (C epsilon0 B0 : ℝ≥0)
    (hb : 1 ≤ b) (hepsilon0 : 0 < epsilon0) :
    ∃ B T : ℕ, 1 ≤ B ∧ 1 ≤ T ∧ ∀ t : ℕ, T ≤ t →
      ∀ k ≤ ell, ∀ j ≤ q, ∀ (N : ℕ) (p r beta epsilon n : ℝ≥0),
        N ≤ t^R → 1 ≤ n → 1/(t : ℝ≥0)^b ≤ p → p ≤ 2/(t : ℝ≥0)^b →
        1/(t : ℝ≥0)^reserveExp ≤ r → epsilon0 ≤ epsilon → beta ≤ B0/(t : ℝ≥0)^B →
        sourceLeftFailureBound k j (decay+1) N p r C beta (sourcePrefixY q k) epsilon n ≤
          1/(t : ℝ≥0)^decay := by
  let s := decay+1
  let B := (R*(3*q)+2*b+2*reserveExp)*s+decay+1
  let K := fun k j ↦ (C^2)^(j-1)*(boundedIntersectionMomentCoefficient (j-1) s : ℝ≥0)*
    2^(j-2)*(k+3 : ℕ)*(j^k : ℕ)*sourcePrefixY q k
  let P := fun j ↦ (C^2)^(j-1)*2^(j-2)*2^(3*j)/epsilon0
  let coefficient := fun (k : Fin (ell+1)) (j : Fin (q+1)) ↦
    (2*K k.val j.val/epsilon0)^s+B0*(P j.val)^s
  let total := ∑ k, ∑ j, coefficient k j
  let T := max 1 ⌈total⌉₊
  refine ⟨B, T, by dsimp only [B]; omega, le_max_left _ _, ?_⟩
  intro t ht k hk j hj N p r beta epsilon n hN hn hp hpUpper hr hepsilon hbeta
  have ht1 : (1 : ℝ≥0) ≤ t := by exact_mod_cast (le_max_left 1 ⌈total⌉₊).trans ht
  have htotal : total ≤ (t : ℝ≥0) := (Nat.le_ceil _).trans
    (by exact_mod_cast (le_max_right 1 ⌈total⌉₊).trans ht)
  have hcoefficient : (2*K k j/epsilon0)^s+B0*(P j)^s ≤ (t : ℝ≥0) := by
    apply le_trans _ htotal
    let k' : Fin (ell+1) := ⟨k, by omega⟩
    let j' : Fin (q+1) := ⟨j, by omega⟩
    change coefficient k' j' ≤ total
    calc
      coefficient k' j' ≤ ∑ j, coefficient k' j := single_le_sum (fun _ _ ↦ zero_le) (mem_univ j')
      _ ≤ total := single_le_sum (f := fun k ↦ ∑ j, coefficient k j) (fun _ _ ↦ zero_le) (mem_univ k')
  have hmain : decay+1 ≤ b*s := by
    dsimp only [s]
    simpa only [one_mul] using Nat.mul_le_mul_right (decay+1) hb
  have herrorGap : (R*(3*j)+2*b+2*reserveExp)*s+(decay+1) ≤ B := by
    have hj' : (R*(3*j)+2*b+2*reserveExp)*s ≤ (R*(3*q)+2*b+2*reserveExp)*s := by gcongr
    dsimp only [B]
    omega
  have hbound := sourceLeftFailureBound_power_le k j s N R b reserveExp B (decay+1)
    t p r C beta (sourcePrefixY q k) epsilon epsilon0 n B0 ht1 hepsilon0 hepsilon hp hpUpper hr
    (by exact_mod_cast hN) hn hbeta hmain herrorGap
  exact hbound.trans (inverse_power_absorb_coefficient t _ decay (zero_lt_one.trans_le ht1) hcoefficient)

theorem eventually_uniform_source_quasi_moments
    (q ell h R b decay : ℕ) (C epsilon0 eta0 B0 : ℝ≥0)
    (hb : 2 ≤ b) (hepsilon0 : 0 < epsilon0) (heta0 : 0 < eta0) :
    ∃ B T : ℕ, 1 ≤ B ∧ 1 ≤ T ∧ ∀ t : ℕ, T ≤ t →
      ∀ k ≤ ell, ∀ j ≤ q, ∀ (N : ℕ) (p beta epsilon eta n : ℝ≥0),
        N ≤ t^R → 1 ≤ n → 1/(t : ℝ≥0)^b ≤ p → p ≤ 2/(t : ℝ≥0)^b →
        epsilon0/t ≤ epsilon → eta0 ≤ eta → beta ≤ B0/(t : ℝ≥0)^B →
        sourceQuasiUniformFailureBound k j (decay+1) h N p C beta (sourcePrefixY q k) epsilon eta n ≤
          1/(t : ℝ≥0)^decay := by
  let s := decay+1
  let B := (R*(3*q)+b*h+1)*s+decay+1
  let K := fun k j ↦ C^(j-3+h)*(boundedIntersectionMomentCoefficient (j-3+h) s : ℝ≥0)*
    2^(j-2)*(k+3 : ℕ)*(j^k : ℕ)*sourcePrefixY q k
  let P := fun j ↦ C^(j-3+h)*2^(j-2)*2^(3*j)/(epsilon0*eta0^(h^2))
  let coefficient := fun (k : Fin (ell+1)) (j : Fin (q+1)) ↦
    (2*K k.val j.val/(epsilon0*eta0^(h^2)))^s+B0*(P j.val)^s
  let total := ∑ k, ∑ j, coefficient k j
  let T := max 1 ⌈total⌉₊
  refine ⟨B, T, by dsimp only [B]; omega, le_max_left _ _, ?_⟩
  intro t ht k hk j hj N p beta epsilon eta n hN hn hp hpUpper hepsilon heta hbeta
  have ht1 : (1 : ℝ≥0) ≤ t := by exact_mod_cast (le_max_left 1 ⌈total⌉₊).trans ht
  have htotal : total ≤ (t : ℝ≥0) := (Nat.le_ceil _).trans
    (by exact_mod_cast (le_max_right 1 ⌈total⌉₊).trans ht)
  have hcoefficient : (2*K k j/(epsilon0*eta0^(h^2)))^s+B0*(P j)^s ≤ (t : ℝ≥0) := by
    apply le_trans _ htotal
    let k' : Fin (ell+1) := ⟨k, by omega⟩
    let j' : Fin (q+1) := ⟨j, by omega⟩
    change coefficient k' j' ≤ total
    calc
      coefficient k' j' ≤ ∑ j, coefficient k' j := single_le_sum (fun _ _ ↦ zero_le) (mem_univ j')
      _ ≤ total := single_le_sum (f := fun k ↦ ∑ j, coefficient k j) (fun _ _ ↦ zero_le) (mem_univ k')
  have herrorGap : (R*(3*j)+b*h+1)*s+(decay+1) ≤ B := by
    have hj' : (R*(3*j)+b*h+1)*s ≤ (R*(3*q)+b*h+1)*s := by gcongr
    dsimp only [B]
    omega
  have hbound := sourceQuasiUniformFailureBound_power_le k j s h N R b B (decay+1)
    t p C beta (sourcePrefixY q k) epsilon epsilon0 eta eta0 n B0 ht1 hepsilon0 heta0 hepsilon heta hp hpUpper hb
    (by exact_mod_cast hN) hn hbeta le_rfl herrorGap
  exact hbound.trans (inverse_power_absorb_coefficient t _ decay (zero_lt_one.trans_le ht1) hcoefficient)

theorem eventually_uniform_source_link_moments
    (q ell R decay : ℕ) (C kappa B0 : ℝ≥0) (hkappa : 0 < kappa) :
    ∃ B T : ℕ, 1 ≤ B ∧ 1 ≤ T ∧ ∀ t : ℕ, T ≤ t →
      ∀ k ≤ ell, ∀ j ≤ q, ∀ (N cap : ℕ) (beta : ℝ≥0),
        N ≤ t^R → kappa*t ≤ cap+1 → beta ≤ B0/(t : ℝ≥0)^B →
        sourceLinkFailureBound k j (decay+1) N cap C beta (sourcePrefixY q k) ≤ 1/(t : ℝ≥0)^decay := by
  let s := decay+1
  let B := R*(3*q)*s+decay+2
  let coefficient := fun (k : Fin (ell+1)) (j : Fin (q+1)) ↦
    (sourceLinkMomentMainCoefficient k.val j.val s C (sourcePrefixY q k.val)/kappa)^s+
      (sourceLinkMomentErrorCoefficient j.val C*2^(3*j.val))^s
  let total := ∑ k, ∑ j, coefficient k j
  let T := max 1 (max ⌈total⌉₊ ⌈B0⌉₊)
  refine ⟨B, T, by dsimp only [B]; omega, le_max_left _ _, ?_⟩
  intro t ht k hk j hj N cap beta hN hcap hbeta
  have ht1 : (1 : ℝ≥0) ≤ t := by exact_mod_cast (le_max_left 1 _).trans ht
  have htotal : total ≤ (t : ℝ≥0) := (Nat.le_ceil _).trans
    (by exact_mod_cast (le_max_left ⌈total⌉₊ ⌈B0⌉₊).trans ((le_max_right 1 _).trans ht))
  have hcoefficient : (sourceLinkMomentMainCoefficient k j s C (sourcePrefixY q k)/kappa)^s+
      (sourceLinkMomentErrorCoefficient j C*2^(3*j))^s ≤ (t : ℝ≥0) := by
    apply le_trans _ htotal
    let k' : Fin (ell+1) := ⟨k, by omega⟩
    let j' : Fin (q+1) := ⟨j, by omega⟩
    change coefficient k' j' ≤ total
    calc
      coefficient k' j' ≤ ∑ j, coefficient k' j := single_le_sum (fun _ _ ↦ zero_le) (mem_univ j')
      _ ≤ total := single_le_sum (f := fun k ↦ ∑ j, coefficient k j) (fun _ _ ↦ zero_le) (mem_univ k')
  have hB0 : B0 ≤ (t : ℝ≥0) := (Nat.le_ceil _).trans
    (by exact_mod_cast (le_max_right ⌈total⌉₊ ⌈B0⌉₊).trans ((le_max_right 1 _).trans ht))
  have hbeta' : beta ≤ 1/(t : ℝ≥0)^(R*(3*q)*s+decay+1) :=
    hbeta.trans (inverse_power_absorb_coefficient t B0 _ (zero_lt_one.trans_le ht1) hB0)
  have herrorGap : R*(3*j)*s+(decay+1) ≤ R*(3*q)*s+decay+1 := by
    have hj' : R*(3*j)*s ≤ R*(3*q)*s := by gcongr
    omega
  have hbound := sourceLinkFailureBound_power_le k j s N cap R 1 (R*(3*q)*s+decay+1) (decay+1)
    t C beta (sourcePrefixY q k) kappa ht1 hkappa (by exact_mod_cast hN)
    (by simpa only [pow_one] using hcap) hbeta' (by dsimp only [s]; omega) herrorGap
  exact hbound.trans (inverse_power_absorb_coefficient t _ decay (zero_lt_one.trans_le ht1) hcoefficient)

end Erdos207
