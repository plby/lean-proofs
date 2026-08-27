/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.CenteredHallScalars

/-! # Uniform reference-scale Hall coefficients, with empty links allowed -/

namespace Erdos207

open Finset
open scoped NNReal

theorem exists_centeredHall_reference_parameters
    (M N c t : ℕ) (reference rho xi : ℝ)
    (_href : 0 ≤ reference) (hrho : 0 ≤ rho) (hrho1 : rho ≤ 1)
    (hxi : 0 ≤ xi) (hxiSmall : xi ≤ 1/65536)
    (hsize : M ≤ N) (hlower : reference/2 ≤ M)
    (hlarge : (18*(65537+4*t) : ℕ) ≤ rho*reference)
    (hc : (c : ℝ) ≤ rho*reference/40)
    (htail : (N : ℝ≥0)*(2*(1/2 : ℝ≥0)^t) < 1) :
    ∃ m d : ℕ, ∃ error : ℝ, 0 ≤ error ∧
      (m : ℝ) ≤ (1-xi)*rho*M ∧
      2*rho*M+3*xi*rho^2*(M : ℝ)^2 ≤ error^2 ∧
      (c : ℝ)+rho*((M/2+1)/2 : ℕ)+error ≤ d ∧
      (M : ℝ≥0)*(2*(2 : ℝ≥0)^d*(3/4 : ℝ≥0)^(m-2)) < 1 := by
  have hsizeR := mul_le_mul_of_nonneg_left hlower hrho
  have hlarge' : (9*65537 : ℝ) ≤ rho*M := by
    push_cast at hlarge
    nlinarith only [hsizeR, hlarge, (show (0 : ℝ) ≤ t by positivity)]
  obtain ⟨u, hu, _huLower, huUpper, hm, hbudget, hscalar, hcHalf⟩ :=
    exists_centeredHall_block_parameters M rho xi hrho hrho1 hxi hxiSmall hlarge'
  have hut : 4*t ≤ u := by
    have hreal : (4 : ℝ)*t ≤ u := by
      push_cast at hlarge
      nlinarith only [hsizeR, hlarge, huUpper]
    exact_mod_cast hreal
  have hcHalf' : (c : ℝ) ≤ (u/2 : ℕ) := by
    have hcM : (c : ℝ) ≤ rho*M/20 := by nlinarith only [hc, hsizeR]
    exact hcM.trans hcHalf
  refine ⟨8*u+2, 3*u, rho*M/64, by positivity, hm, hbudget, ?_, ?_⟩
  · linarith only [hcHalf', hscalar]
  · rw [sharp_paired_tail_eighth_blocks]
    calc
      _ ≤ (M : ℝ≥0)*(2*(1/2 : ℝ≥0)^t) :=
        mul_le_mul_of_nonneg_left (sharp_paired_tail_le_dyadic t u hut) zero_le
      _ ≤ (N : ℝ≥0)*(2*(1/2 : ℝ≥0)^t) := by
        apply mul_le_mul_of_nonneg_right _ zero_le
        exact_mod_cast hsize
      _ < 1 := htail

theorem exists_centeredHall_reference_parameters_or_empty
    (M N c t : ℕ) (reference rho xi : ℝ)
    (href : 0 ≤ reference) (hrho : 0 ≤ rho) (hrho1 : rho ≤ 1)
    (hxi : 0 ≤ xi) (hxiSmall : xi ≤ 1/65536)
    (hsize : M ≤ N) (hlower : M = 0 ∨ reference/2 ≤ M)
    (hlarge : (18*(65537+4*t) : ℕ) ≤ rho*reference)
    (hc : (c : ℝ) ≤ rho*reference/40)
    (htail : (N : ℝ≥0)*(2*(1/2 : ℝ≥0)^t) < 1) :
    ∃ m d : ℕ, ∃ error : ℝ, 0 ≤ error ∧
      (m : ℝ) ≤ (1-xi)*rho*M ∧
      2*rho*M+3*xi*rho^2*(M : ℝ)^2 ≤ error^2 ∧
      (c : ℝ)+rho*((M/2+1)/2 : ℕ)+error ≤ d ∧
      (M : ℝ≥0)*(2*(2 : ℝ≥0)^d*(3/4 : ℝ≥0)^(m-2)) < 1 := by
  rcases hlower with rfl | hlower
  · exact ⟨0, c, 0, by norm_num⟩
  · exact exists_centeredHall_reference_parameters M N c t reference rho xi href hrho hrho1
      hxi hxiSmall hsize hlower hlarge hc htail

theorem floor_reference_hall_coefficient
    (reference rho : ℝ) (hlarge : 80 ≤ rho*reference) :
    let c := ⌊rho*reference/40⌋₊
    (c : ℝ) ≤ rho*reference/40 ∧ rho*reference/80 ≤ c := by
  dsimp only
  have hpos : 0 ≤ rho*reference/40 := by linarith only [hlarge]
  have hlo := Nat.floor_le hpos
  have hhi := Nat.lt_floor_add_one (rho*reference/40)
  exact ⟨hlo, by linarith only [hhi, hlarge]⟩

end Erdos207
