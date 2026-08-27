/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.PowerTerminalJumpChain
import ErdosProblems.Erdos207.InitialRetainedVortexLaw

/-! # Retained power vortices and a noncircular choice of their length -/

namespace Erdos207

open Finset

noncomputable section

def InitialPowerVortexPackage.retainedVortex
    {q h n ell t rootPower step : ℕ}
    (P : InitialPowerVortexPackage q h n ell t rootPower step)
    (length : ℕ) (hfit : length ≤ ell) (hlength : 0 < length) : Vortex (Fin n) length :=
  P.W.reindex (terminalJumpStage ell length hfit)
    (terminalJumpStage_strictMono ell length hfit).monotone
    (terminalJumpStage_zero ell length hfit hlength)

theorem InitialPowerVortexPackage.retainedVortex_terminal
    {q h n ell t rootPower step length : ℕ}
    (P : InitialPowerVortexPackage q h n ell t rootPower step)
    (hfit : length ≤ ell) (hlength : 0 < length) :
    (P.retainedVortex length hfit hlength).U (Fin.last length) = P.X := by
  change P.W.U (terminalJumpStage ell length hfit (Fin.last length)) = P.X
  rw [terminalJumpStage_last, P.terminal]

theorem InitialPowerVortexPackage.retainedVortex_level_card_lower
    {q h n ell t rootPower step length : ℕ}
    (P : InitialPowerVortexPackage q h n ell t rootPower step)
    (hfit : length ≤ ell) (hlength : 0 < length) (i : Fin (length + 1)) :
    t ^ rootPower ≤ ((P.retainedVortex length hfit hlength).U i).card :=
  P.level_card_lower _

theorem InitialPowerVortexPackage.retainedVortex_positive_scale_bounds
    {q h n ell t rootPower step length m : ℕ}
    (P : InitialPowerVortexPackage q h n ell t rootPower step)
    (hsplit : length + m = ell) (hlength : 0 < length)
    (hroot : rootPower ≤ step * m) (hrootUpper : step * m ≤ rootPower + step)
    (i : Fin length) (hi : 0 < i.val) :
    let W := P.retainedVortex length (by omega) hlength
    t ^ step * (W.U i.succ).card ≤ 2 * (W.U i.castSucc).card ∧
      (W.U i.castSucc).card ≤ 2 * t ^ (2 * step) * (W.U i.succ).card :=
  P.positive_terminalJump_chain_scale_bounds hsplit hroot hrootUpper i hi

theorem exists_retained_power_vortex_length (rootPower step Rfixed K : ℕ) (hstep : 0 < step) :
    ∃ ell length m : ℕ, 2 ≤ length ∧ length + m = ell ∧
      rootPower < step * m ∧ step * m ≤ rootPower + step ∧
      K * (Rfixed + step + 1) ≤ Rfixed + step * ell := by
  let m := rootPower / step + 1
  let length := K * (Rfixed + step + 1) + 2
  obtain ⟨hlo, hhi⟩ := powerTerminalCutoff_bounds rootPower step hstep
  refine ⟨length + m, length, m, by dsimp only [length]; omega, rfl, hlo, hhi, ?_⟩
  have hmul : length + m ≤ step * (length + m) :=
    Nat.le_mul_of_pos_left _ hstep
  calc
    K * (Rfixed + step + 1) ≤ length := by dsimp only [length]; omega
    _ ≤ length + m := Nat.le_add_right _ _
    _ ≤ step * (length + m) := hmul
    _ ≤ Rfixed + step * (length + m) := Nat.le_add_left _ _

end

end Erdos207
