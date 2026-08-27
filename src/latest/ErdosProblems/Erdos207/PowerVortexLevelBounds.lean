/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.PowerLocalizedMasterExtension

/-!
# Cardinal bounds for packaged power vortices

The scalar hierarchy repeatedly replaces exact positive-level cardinalities
by one power of the common base.  These lemmas collect those reductions and
also expose the exact terminal and ambient cardinalities.
-/

namespace Erdos207

open Finset

noncomputable section

@[simp]
theorem InitialPowerVortexPackage.rootLevel_card
    {q h n ell t rootPower step : ℕ}
    (P : InitialPowerVortexPackage q h n ell t rootPower step) :
    (P.W.U 0).card = n := by
  rw [P.W.root, card_univ, Fintype.card_fin]

@[simp]
theorem InitialPowerVortexPackage.terminalSize_eq
    {q h n ell t rootPower step : ℕ}
    (P : InitialPowerVortexPackage q h n ell t rootPower step) :
    P.W.terminalSize = t ^ rootPower := by
  rw [Vortex.terminalSize, P.terminal, P.rootCard]

theorem InitialPowerVortexPackage.positiveLevel_card_ge_root
    {q h n ell t rootPower step : ℕ}
    (P : InitialPowerVortexPackage q h n ell t rootPower step)
    (i : Fin (ell + 1)) (hi : i ≠ 0) :
    t ^ rootPower ≤ (P.W.U i).card := by
  rw [P.levelCard i hi]
  exact Nat.le_add_right _ _

theorem InitialPowerVortexPackage.positiveLevel_card_le_two_mul_power
    {q h n ell t rootPower step : ℕ}
    (P : InitialPowerVortexPackage q h n ell t rootPower step)
    (i : Fin (ell + 1)) (hi : i ≠ 0) :
    (P.W.U i).card ≤
      2 * t ^ max rootPower (step * (ell - i.val)) := by
  rw [P.levelCard i hi]
  have htpos : 0 < t := Nat.zero_lt_one.trans_le P.base_ge_one
  have hroot : t ^ rootPower ≤
      t ^ max rootPower (step * (ell - i.val)) :=
    Nat.pow_le_pow_right htpos (le_max_left _ _)
  have hfree : powerFreeSize t step ell i ≤
      t ^ max rootPower (step * (ell - i.val)) := by
    by_cases hilast : i = Fin.last ell
    · simp [hilast]
    rw [powerFreeSize_of_ne_last t step ell i hilast]
    exact Nat.pow_le_pow_right htpos (le_max_right _ _)
  omega

theorem InitialPowerVortexPackage.positiveLevel_card_le_two_mul_topPower
    {q h n ell t rootPower step : ℕ}
    (P : InitialPowerVortexPackage q h n ell t rootPower step)
    (i : Fin (ell + 1)) (hi : i ≠ 0) :
    (P.W.U i).card ≤ 2 * t ^ max rootPower (step * ell) := by
  refine (P.positiveLevel_card_le_two_mul_power i hi).trans ?_
  apply Nat.mul_le_mul_left
  apply Nat.pow_le_pow_right (Nat.zero_lt_one.trans_le P.base_ge_one)
  exact max_le_max_left rootPower
    (Nat.mul_le_mul_left step (Nat.sub_le ell i.val))

theorem InitialPowerVortexPackage.terminal_card_pos
    {q h n ell t rootPower step : ℕ}
    (P : InitialPowerVortexPackage q h n ell t rootPower step) :
    0 < P.W.terminalSize := by
  rw [P.terminalSize_eq]
  exact pow_pos (Nat.zero_lt_one.trans_le P.base_ge_one) _

end

end Erdos207
