/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.TerminalJumpChain
import ErdosProblems.Erdos207.PowerVortexStepRatios

/-! # The power vortex's retained chain has quantitative shrinking at every positive stage -/

namespace Erdos207

open Finset

noncomputable section

theorem powerTerminalCutoff_bounds (rootPower step : ℕ) (hstep : 0 < step) :
    rootPower < step * (rootPower / step + 1) ∧
      step * (rootPower / step + 1) ≤ rootPower + step := by
  have hlo : rootPower < (rootPower / step + 1) * step :=
    (Nat.div_lt_iff_lt_mul hstep).mp (Nat.lt_succ_self _)
  have hhi := Nat.div_mul_le_self rootPower step
  constructor
  · simpa only [Nat.mul_comm] using hlo
  · rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm step (rootPower / step)]
    omega

theorem InitialPowerVortexPackage.positive_terminalJump_chain_scale_bounds
    {q h n ell t rootPower step length m : ℕ}
    (P : InitialPowerVortexPackage q h n ell t rootPower step)
    (hsplit : length + m = ell) (hroot : rootPower ≤ step * m)
    (hrootUpper : step * m ≤ rootPower + step) (i : Fin length) (hi : 0 < i.val) :
    let stage := terminalJumpStage ell length (by omega)
    t ^ step * (P.W.U (stage i.succ)).card ≤ 2 * (P.W.U (stage i.castSucc)).card ∧
      (P.W.U (stage i.castSucc)).card ≤ 2 * t ^ (2 * step) * (P.W.U (stage i.succ)).card := by
  dsimp only
  rw [terminalJumpStage_castSucc]
  let current : Fin (ell + 1) := ⟨i.val, by have := i.isLt; omega⟩
  have hcurrent0 : current ≠ 0 := by
    intro hz
    have hval : current.val = 0 := by rw [hz]; rfl
    change i.val = 0 at hval
    omega
  by_cases hnext : i.val + 1 < length
  · let next : Fin (ell + 1) := ⟨i.val + 1, by omega⟩
    have hnextEq : terminalJumpStage ell length (by omega) i.succ = next := by
      simp only [terminalJumpStage, Fin.val_succ, dif_pos hnext, next]
    rw [hnextEq]
    have hnextLast : next ≠ Fin.last ell := by
      intro hlast
      have hval := congrArg Fin.val hlast
      change i.val + 1 = ell at hval
      omega
    have hrootNext : rootPower ≤ step * (ell - next.val) :=
      hroot.trans (Nat.mul_le_mul_left step (by dsimp only [next]; omega))
    obtain ⟨hlower, hupper⟩ := P.consecutive_positiveLevel_scale_bounds current next
      hcurrent0 rfl hnextLast hrootNext
    refine ⟨hlower, hupper.trans ?_⟩
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2
      (Nat.pow_le_pow_right (Nat.zero_lt_one.trans_le P.base_ge_one) (by omega)))
  · have hnextEq : terminalJumpStage ell length (by omega) i.succ = Fin.last ell := by
      simp only [terminalJumpStage, Fin.val_succ, dif_neg hnext]
    rw [hnextEq]
    have hcurrentLast : current ≠ Fin.last ell := by
      intro hlast
      have hval := congrArg Fin.val hlast
      change i.val = ell at hval
      have := i.isLt
      omega
    have hexp : step * (ell - current.val) = step * m + step := by
      have hdiff : ell - current.val = m + 1 := by
        change ell - i.val = m + 1
        have := i.isLt
        omega
      rw [hdiff, Nat.mul_add, Nat.mul_one]
    obtain ⟨hlower, hupper⟩ := P.terminalJump_scale_bounds (lo := step) (hi := 2 * step)
      current hcurrent0 hcurrentLast (by omega) (by omega)
    have htwice : (P.W.U current).card ≤ 2 * (P.W.U current).card := by omega
    exact ⟨hlower.trans htwice, hupper⟩

end

end Erdos207
