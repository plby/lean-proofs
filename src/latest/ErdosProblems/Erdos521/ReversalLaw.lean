/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Finite coefficient reversal preserves the law of the single infinite iid sequence.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.Model

namespace Erdos521

open MeasureTheory

def finiteReverseIndex (n k : ℕ) : ℕ := if k ≤ n then n - k else k

theorem finiteReverseIndex_involutive (n : ℕ) : Function.Involutive (finiteReverseIndex n) := by
  intro k
  by_cases hk : k ≤ n
  · simp [finiteReverseIndex, hk, Nat.sub_sub_self hk]
  · simp [finiteReverseIndex, hk]

def reversedCoefficients (n : ℕ) (ε : ℕ → ℝ) (k : ℕ) : ℝ := ε (finiteReverseIndex n k)

theorem measurable_reversedCoefficients (n : ℕ) : Measurable (reversedCoefficients n) := by
  fun_prop [reversedCoefficients]

theorem measurePreserving_reversedCoefficients (n : ℕ) :
    MeasurePreserving (reversedCoefficients n) sequenceLaw sequenceLaw := by
  refine ⟨measurable_reversedCoefficients n, ?_⟩
  exact Measure.map_infinitePi_infinitePi_of_inj (finiteReverseIndex_involutive n).injective

theorem reversedCoefficients_zero (n : ℕ) (ε : ℕ → ℝ) : reversedCoefficients n ε 0 = ε n := by
  simp [reversedCoefficients, finiteReverseIndex]

theorem powerSum_reversedCoefficients (n : ℕ) (ε : ℕ → ℝ) (x : ℝ) :
    powerSum (reversedCoefficients n ε) (n + 1) x = powerSum (fun k ↦ ε (n - k)) (n + 1) x := by
  apply Finset.sum_congr rfl
  intro k hk
  simp [reversedCoefficients, finiteReverseIndex, Nat.le_of_lt_succ (Finset.mem_range.mp hk)]

theorem mem_realRoots_reversedCoefficients_inv (n : ℕ) (ε : ℕ → ℝ)
    (hε₀ : ε 0 ≠ 0) (hεn : ε n ≠ 0) (x : ℝ) (hx : x ≠ 0) :
    x⁻¹ ∈ realRoots (reversedCoefficients n ε) n ↔ x ∈ realRoots ε n := by
  have hrev : reversedCoefficients n ε 0 ≠ 0 := by rwa [reversedCoefficients_zero]
  rw [mem_realRoots _ _ hrev, mem_realRoots _ _ hε₀, powerSum_reversedCoefficients,
    ← reverse_powerSum_mul ε n x hx, mul_eq_zero, or_iff_left (pow_ne_zero n hx)]

end Erdos521
