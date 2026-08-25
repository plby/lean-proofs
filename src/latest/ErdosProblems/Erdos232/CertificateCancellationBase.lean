/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.FiniteDual

namespace Erdos232

def maskMass (a : AtomIndex → ℝ) (m : Nat) : ℝ :=
  ∑ s, if natMaskSubset m s.val then a s else 0

def weightedMaskMass (a : AtomIndex → ℝ) (m : Nat) (w : Int) : ℝ :=
  ∑ s, a s * ((if natMaskSubset m s.val then w else 0 : Int) : ℝ)

theorem weightedMaskMass_eq (a : AtomIndex → ℝ) (m : Nat) (w : Int) :
    weightedMaskMass a m w = (w : ℝ) * maskMass a m := by
  rw [weightedMaskMass, maskMass, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  split <;> simp_all [mul_comm]

end Erdos232
