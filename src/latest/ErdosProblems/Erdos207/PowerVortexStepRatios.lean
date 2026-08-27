/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.PowerVortexLevelBounds

/-! # Exact power-vortex ratios before the terminal jump -/

namespace Erdos207

open Finset

noncomputable section

theorem InitialPowerVortexPackage.positiveLevel_card_power_bounds
    {q h n ell t rootPower step : ℕ}
    (P : InitialPowerVortexPackage q h n ell t rootPower step)
    (i : Fin (ell + 1)) (hi : i ≠ 0) (hilast : i ≠ Fin.last ell)
    (hroot : rootPower ≤ step * (ell - i.val)) :
    t ^ (step * (ell - i.val)) ≤ (P.W.U i).card ∧
      (P.W.U i).card ≤ 2 * t ^ (step * (ell - i.val)) := by
  rw [P.levelCard i hi, powerFreeSize_of_ne_last t step ell i hilast]
  have hp := Nat.pow_le_pow_right (Nat.zero_lt_one.trans_le P.base_ge_one) hroot
  constructor <;> omega

theorem InitialPowerVortexPackage.consecutive_positiveLevel_scale_bounds
    {q h n ell t rootPower step : ℕ}
    (P : InitialPowerVortexPackage q h n ell t rootPower step)
    (i j : Fin (ell + 1)) (hi : i ≠ 0) (hj : j.val = i.val + 1)
    (hjlast : j ≠ Fin.last ell) (hroot : rootPower ≤ step * (ell - j.val)) :
    t ^ step * (P.W.U j).card ≤ 2 * (P.W.U i).card ∧
      (P.W.U i).card ≤ 2 * t ^ step * (P.W.U j).card := by
  have hjzero : j ≠ 0 := by
    intro hz
    have hval : j.val = 0 := by rw [hz]; rfl
    omega
  have hilast : i ≠ Fin.last ell := by
    intro hilast
    have hval := congrArg Fin.val hilast
    have := j.isLt
    simp only [Fin.val_last] at hval
    omega
  have hdiff : ell - i.val = (ell - j.val) + 1 := by have := j.isLt; omega
  have hexp : step * (ell - i.val) = step * (ell - j.val) + step := by
    rw [hdiff, Nat.mul_add, Nat.mul_one]
  have hrooti : rootPower ≤ step * (ell - i.val) := by omega
  obtain ⟨hilo, hihi⟩ := P.positiveLevel_card_power_bounds i hi hilast hrooti
  obtain ⟨hjlo, hjhi⟩ := P.positiveLevel_card_power_bounds j hjzero hjlast hroot
  have hp : t ^ (step * (ell - i.val)) = t ^ step * t ^ (step * (ell - j.val)) := by
    rw [hexp, pow_add, Nat.mul_comm]
  constructor
  · calc
      _ ≤ t ^ step * (2 * t ^ (step * (ell - j.val))) := Nat.mul_le_mul_left _ hjhi
      _ = 2 * t ^ (step * (ell - i.val)) := by rw [hp]; ring
      _ ≤ _ := Nat.mul_le_mul_left 2 hilo
  · calc
      _ ≤ 2 * t ^ (step * (ell - i.val)) := hihi
      _ = 2 * t ^ step * t ^ (step * (ell - j.val)) := by rw [hp, Nat.mul_assoc]
      _ ≤ _ := Nat.mul_le_mul_left _ hjlo

theorem InitialPowerVortexPackage.terminalJump_scale_bounds
    {q h n ell t rootPower step lo hi : ℕ}
    (P : InitialPowerVortexPackage q h n ell t rootPower step)
    (i : Fin (ell + 1)) (hi0 : i ≠ 0) (hilast : i ≠ Fin.last ell)
    (hlo : rootPower + lo ≤ step * (ell - i.val))
    (hhi : step * (ell - i.val) ≤ rootPower + hi) :
    t ^ lo * (P.W.U (Fin.last ell)).card ≤ (P.W.U i).card ∧
      (P.W.U i).card ≤ 2 * t ^ hi * (P.W.U (Fin.last ell)).card := by
  rw [P.terminal, P.rootCard]
  have ht := Nat.zero_lt_one.trans_le P.base_ge_one
  obtain ⟨hlower, hupper⟩ := P.positiveLevel_card_power_bounds i hi0 hilast (by omega)
  constructor
  · calc
      _ = t ^ (rootPower + lo) := by rw [pow_add]; ring
      _ ≤ t ^ (step * (ell - i.val)) := Nat.pow_le_pow_right ht hlo
      _ ≤ _ := hlower
  · calc
      _ ≤ 2 * t ^ (step * (ell - i.val)) := hupper
      _ ≤ 2 * t ^ (rootPower + hi) := Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right ht hhi)
      _ = _ := by rw [pow_add]; ring

theorem InitialPowerVortexPackage.ambient_positiveLevel_scale_bounds
    {q h n ell t rootPower step R K : ℕ}
    (P : InitialPowerVortexPackage q h n ell t rootPower step)
    (i : Fin (ell + 1)) (hi : i ≠ 0) (hilast : i ≠ Fin.last ell)
    (hroot : rootPower ≤ step * (ell - i.val)) (hexp : step * (ell - i.val) ≤ R)
    (hnlo : t ^ R ≤ n) (hnhi : n ≤ K * t ^ R) :
    t ^ (R - step * (ell - i.val)) * (P.W.U i).card ≤ 2 * n ∧
      n ≤ K * t ^ (R - step * (ell - i.val)) * (P.W.U i).card := by
  obtain ⟨hlo, hhi⟩ := P.positiveLevel_card_power_bounds i hi hilast hroot
  have hp : t ^ R = t ^ (R - step * (ell - i.val)) * t ^ (step * (ell - i.val)) := by
    rw [← pow_add, Nat.sub_add_cancel hexp]
  constructor
  · calc
      _ ≤ t ^ (R - step * (ell - i.val)) * (2 * t ^ (step * (ell - i.val))) :=
        Nat.mul_le_mul_left _ hhi
      _ = 2 * t ^ R := by rw [hp]; ring
      _ ≤ _ := Nat.mul_le_mul_left 2 hnlo
  · calc
      _ ≤ K * t ^ R := hnhi
      _ = K * t ^ (R - step * (ell - i.val)) * t ^ (step * (ell - i.val)) := by
        rw [hp, Nat.mul_assoc]
      _ ≤ _ := Nat.mul_le_mul_left _ hlo

end

end Erdos207
