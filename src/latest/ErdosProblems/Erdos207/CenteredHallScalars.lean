/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.CenteredAvailableLink
import Mathlib.Algebra.Order.Floor.Ring

/-! # Nonvacuous fixed constants for the centered robust-matching interface -/

namespace Erdos207

open Finset

theorem centeredHall_block_scalars
    (M u : ℕ) (rho xi : ℝ) (hrho : 0 ≤ rho) (hrho1 : rho ≤ 1)
    (_hxi : 0 ≤ xi) (hxiSmall : xi ≤ 1/65536)
    (hu : 65536 ≤ u) (hlower : 9*(u : ℝ) ≤ rho*M) (hupper : rho*M ≤ 9*((u : ℝ)+1)) :
    (8*u+2 : ℕ) ≤ (1-xi)*rho*M ∧
      2*rho*M+3*xi*rho^2*(M : ℝ)^2 ≤ (rho*M/64)^2 ∧
      ((u/2 : ℕ) : ℝ)+rho*((M/2+1)/2 : ℕ)+rho*M/64 ≤ (3*u : ℕ) ∧
      rho*M/20 ≤ (u/2 : ℕ) := by
  have huR : (65536 : ℝ) ≤ u := by exact_mod_cast hu
  have hXpos : 0 ≤ rho*M := by positivity
  have hxiX : xi*(rho*M) ≤ (1/65536)*(rho*M) := mul_le_mul_of_nonneg_right hxiSmall hXpos
  have hxiX2 : xi*(rho*M)^2 ≤ (1/65536)*(rho*M)^2 := mul_le_mul_of_nonneg_right hxiSmall (sq_nonneg _)
  have hXlarge : (65536 : ℝ) ≤ rho*M := by linarith only [hlower, huR]
  have hlargeSq : 65536*(rho*M) ≤ (rho*M)^2 := by nlinarith only [hXlarge, hXpos]
  have hhalf : ((u/2 : ℕ) : ℝ) ≤ (u : ℝ)/2 := by
    have hnat : 2*(u/2) ≤ u := Nat.mul_div_le u 2
    have hreal : (2 : ℝ)*(u/2 : ℕ) ≤ u := by exact_mod_cast hnat
    linarith only [hreal]
  have hhalfLower : (u : ℝ) ≤ 2*(u/2 : ℕ)+1 := by
    have hnat : u ≤ 2*(u/2)+1 := by omega
    exact_mod_cast hnat
  have hquarter : (4 : ℝ)*((M/2+1)/2 : ℕ) ≤ M+2 := by
    have hnat : 4*((M/2+1)/2) ≤ M+2 := by omega
    exact_mod_cast hnat
  have hquarterRho := mul_le_mul_of_nonneg_left hquarter hrho
  refine ⟨?_, ?_, ?_, ?_⟩
  · push_cast
    nlinarith only [hxiX, hlower, hupper, huR]
  · nlinarith only [hxiX2, hlargeSq]
  · push_cast
    nlinarith only [hhalf, hquarterRho, hupper, huR, hrho1]
  · nlinarith only [hupper, hhalfLower, huR]

theorem exists_centeredHall_block_parameters
    (M : ℕ) (rho xi : ℝ) (hrho : 0 ≤ rho) (hrho1 : rho ≤ 1)
    (hxi : 0 ≤ xi) (hxiSmall : xi ≤ 1/65536) (hlarge : (9*65537 : ℝ) ≤ rho*M) :
    ∃ u : ℕ, 65536 ≤ u ∧ 9*(u : ℝ) ≤ rho*M ∧ rho*M ≤ 9*((u : ℝ)+1) ∧
      (8*u+2 : ℕ) ≤ (1-xi)*rho*M ∧
      2*rho*M+3*xi*rho^2*(M : ℝ)^2 ≤ (rho*M/64)^2 ∧
      ((u/2 : ℕ) : ℝ)+rho*((M/2+1)/2 : ℕ)+rho*M/64 ≤ (3*u : ℕ) ∧
      rho*M/20 ≤ (u/2 : ℕ) := by
  let u := ⌊rho*M/9⌋₊
  have hpos : 0 ≤ rho*M/9 := by positivity
  have hfloor : (u : ℝ) ≤ rho*M/9 := Nat.floor_le hpos
  have hceil : rho*M/9 < (u : ℝ)+1 := Nat.lt_floor_add_one (rho*M/9)
  have hu : 65536 ≤ u := by
    have huR : (65536 : ℝ) ≤ u := by linarith only [hceil, hlarge]
    exact_mod_cast huR
  have hlower : 9*(u : ℝ) ≤ rho*M := by linarith only [hfloor]
  have hupper : rho*M ≤ 9*((u : ℝ)+1) := by linarith only [hceil]
  exact ⟨u, hu, hlower, hupper, centeredHall_block_scalars M u rho xi hrho hrho1 hxi hxiSmall hu hlower hupper⟩

end Erdos207
