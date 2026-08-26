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
import Mathlib.NumberTheory.LSeries.PrimesInAP
import ErdosProblems.Erdos330.UpperDensity

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Prime supply for Erdős Problem 330

The roadmap suggests an elementary Euclid-style proof for primes `3 mod 4`.
For now we use Mathlib's formalized Dirichlet theorem in arithmetic
progressions as a reliable supply lemma.
-/

namespace Erdos330

theorem exists_prime_three_mod_four_ge (N : ℕ) :
    ∃ p ≥ N, Nat.Prime p ∧ p % 4 = 3 := by
  obtain ⟨p, hpgt, hpprime, hpmod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq N (q := 4) (a := 3)
      (by decide) (by decide : Nat.Coprime 3 4)
  exact ⟨p, hpgt.le, hpprime, by simpa [Nat.ModEq] using hpmod⟩

theorem exists_prime_three_mod_four_gt (N : ℕ) :
    ∃ p > N, Nat.Prime p ∧ p % 4 = 3 := by
  obtain ⟨p, hpge, hpprime, hpmod⟩ := exists_prime_three_mod_four_ge (N + 1)
  exact ⟨p, Nat.succ_le_iff.mp hpge, hpprime, hpmod⟩

end Erdos330
