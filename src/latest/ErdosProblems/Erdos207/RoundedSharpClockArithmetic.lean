/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.KSSSWorkingGraphSupply
import ErdosProblems.Erdos207.CubicSurvivalCancellation

/-! # Rounding budgets for a nearly exact affine survival clock -/

namespace Erdos207

open scoped NNReal

noncomputable section

theorem rounded_pair_effective_lower
    (x e eps : ℝ) (K : ℕ) (hx : 0 ≤ x) (heps : eps ≤ 1 / 2)
    (he : e ≤ eps * x / 8) (hround : (K : ℝ) + 2 ≤ eps * x / 8) :
    (1 - eps / 4) * x ≤ ((⌊x - e⌋₊ - K : ℕ) : ℝ) := by
  have hfloor := Nat.lt_floor_add_one (x - e)
  have hsmall := mul_le_mul_of_nonneg_right heps hx
  have hKreal : (K : ℝ) ≤ (⌊x - e⌋₊ : ℝ) := by
    nlinarith only [hfloor, he, hround, hsmall, hx]
  have hK : K ≤ ⌊x - e⌋₊ := by exact_mod_cast hKreal
  rw [Nat.cast_sub hK]
  nlinarith only [hfloor, he, hround]

theorem rounded_availability_upper
    (L x e eps : ℝ) (hL : 6 ≤ L) (hx : 0 ≤ x) (he0 : 0 ≤ e)
    (he : e ≤ eps * x / 8) (hround : 2 ≤ eps * x / 8) :
    (⌈L * (x + e) / 3⌉₊ : ℝ) ≤ L * x * (1 + eps / 4) / 3 := by
  have hL0 : 0 ≤ L := by linarith
  have hceil := (Nat.ceil_lt_add_one (by positivity : 0 ≤ L * (x + e) / 3)).le
  have hLe := mul_le_mul_of_nonneg_left he hL0
  have hLround := mul_le_mul_of_nonneg_left hround hL0
  nlinarith only [hceil, hLe, hLround, hL]

theorem rounded_availability_lower
    (L x e : ℝ) (hL : 6 ≤ L) (hx : 32 ≤ x) (he : e ≤ x / 4) :
    L * x / 8 ≤ (⌊L * (x - e) / 3⌋₊ : ℝ) := by
  have hL0 : 0 ≤ L := by linarith
  have hLe := mul_le_mul_of_nonneg_left he hL0
  have hLx := mul_le_mul_of_nonneg_left hx hL0
  have hfloor := Nat.lt_floor_add_one (L * (x - e) / 3)
  nlinarith only [hfloor, hLe, hLx, hL]

theorem rounded_sharp_schedule_coherence
    (L x e : ℝ) (K : ℕ) (hL : 6 ≤ L) (hx : 0 < x) (he : 0 ≤ e) :
    0 < ⌈L * (x + e) / 3⌉₊ ∧
      ⌊x - e⌋₊ ≤ ⌈L * (x + e) / 3⌉₊ ∧
      ⌊x - e⌋₊ - K < ⌈L * (x + e) / 3⌉₊ ∧
      2 * (⌊x - e⌋₊ - K) ≤ ⌈L * (x + e) / 3⌉₊ := by
  have hL0 : 0 ≤ L := by linarith
  have hceil := Nat.le_ceil (L * (x + e) / 3)
  have hLe := mul_nonneg hL0 he
  have hLx := mul_le_mul_of_nonneg_right hL hx.le
  have hxM : 2 * x ≤ (⌈L * (x + e) / 3⌉₊ : ℝ) := by nlinarith only [hceil, hLe, hLx]
  have hfloor : (⌊x - e⌋₊ : ℝ) ≤ x := by
    by_cases hxe : 0 ≤ x - e
    · exact (Nat.floor_le hxe).trans (by linarith only [he])
    · rw [Nat.floor_eq_zero.mpr (show x - e < 1 by linarith only [hxe])]
      simpa only [Nat.cast_zero] using hx.le
  have hsub : ((⌊x - e⌋₊ - K : ℕ) : ℝ) ≤ (⌊x - e⌋₊ : ℝ) := by
    exact_mod_cast Nat.sub_le ⌊x - e⌋₊ K
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact_mod_cast (show (0 : ℝ) < ⌈L * (x + e) / 3⌉₊ by linarith only [hxM, hx])
  · exact_mod_cast (show (⌊x - e⌋₊ : ℝ) ≤ ⌈L * (x + e) / 3⌉₊ by linarith only [hxM, hfloor, hx])
  · exact_mod_cast (show ((⌊x - e⌋₊ - K : ℕ) : ℝ) < ⌈L * (x + e) / 3⌉₊ by
      linarith only [hxM, hfloor, hsub, hx])
  · exact_mod_cast (show (2 : ℝ) * ((⌊x - e⌋₊ - K : ℕ) : ℝ) ≤ ⌈L * (x + e) / 3⌉₊ by
      linarith only [hxM, hfloor, hsub])

theorem rounded_sharp_affine_loss
    (L x e eps : ℝ) (K : ℕ) (hL : 6 ≤ L) (hx : 0 ≤ x)
    (he0 : 0 ≤ e) (heps0 : 0 ≤ eps) (heps : eps ≤ 1 / 2)
    (he : e ≤ eps * x / 8) (hround : (K : ℝ) + 2 ≤ eps * x / 8) :
    3 * (1 - eps) * (⌈L * (x + e) / 3⌉₊ : ℝ) ≤
      L * ((⌊x - e⌋₊ - K : ℕ) : ℝ) := by
  have hL0 : 0 ≤ L := by linarith
  have hupper := rounded_availability_upper L x e eps hL hx he0 he
    (by have hK := Nat.cast_nonneg (α := ℝ) K; linarith only [hround, hK])
  have hlower := rounded_pair_effective_lower x e eps K hx heps he hround
  have hcoef : (1 - eps) * (1 + eps / 4) ≤ 1 - eps / 4 := by nlinarith only [sq_nonneg eps, heps0]
  calc
    _ ≤ 3 * (1 - eps) * (L * x * (1 + eps / 4) / 3) :=
      mul_le_mul_of_nonneg_left hupper (by linarith only [heps])
    _ = L * x * ((1 - eps) * (1 + eps / 4)) := by ring
    _ ≤ L * x * (1 - eps / 4) := mul_le_mul_of_nonneg_left hcoef (mul_nonneg hL0 hx)
    _ = L * ((1 - eps / 4) * x) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hlower hL0

end

end Erdos207
