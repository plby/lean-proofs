/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- This file has been modified for Lean/Mathlib 4.33.0. -/
/-
Erdős Problem 330, positive upper density formulation.
Informal authors: GPT-5.5 Pro, David Turturean.
Formal authors: Codex, GPT-5.5 Pro, Allen Graham Hart.
Source: https://www.erdosproblems.com/forum/thread/330#post-6271
https://github.com/AllenGrahamHart/FormalConjectures-Bench/tree/6160036caab0dcee80395ba3beb7b6ef2731604e/formalizations/erdos330
Original Lean/Mathlib version: 4.27.0.
-/
import ErdosProblems.Erdos330.Scheduler
import ErdosProblems.Erdos330.Iteration

namespace Erdos330

theorem erdos_330 :
    ∃ A : Set ℕ, IsAsymptoticBasisTwo A ∧ 0 < A.upperDensity ∧
      ∀ a ∈ A, 0 < (privateSet A a).upperDensity := by
  exact mainTarget_iff.mp erdos330_mainTarget

#print axioms erdos_330
-- 'Erdos330.erdos_330' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos330
