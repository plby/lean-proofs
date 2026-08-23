/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 121.
https://www.erdosproblems.com/forum/thread/121

Informal authors:
- Terence Tao

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos121.md
-/
import ErdosProblems.Erdos121.Core
import ErdosProblems.Erdos121.Padding

/-!
# Erdős Problem 121

The exact extremal function is defined in `ErdosProblems.Erdos121.Core`.
This file records the final resolution: for every fixed `k ≥ 4`, and in
particular for `k = 5`, the extremal size has a fixed positive density gap
below `N`.
-/

open Filter

namespace Erdos121

set_option autoImplicit false

noncomputable section

theorem exists_denseSquareTupleBound_of_four_step :
    ∀ j : ℕ, ∃ c : ℝ, 0 < c ∧ DenseSquareTupleBound (4 + 2 * j) c := by
  intro j
  induction j with
  | zero =>
      exact ⟨1 / 100, by norm_num, by simpa using denseSquareTupleBound_four⟩
  | succ j ih =>
      obtain ⟨c, hc, hbound⟩ := ih
      obtain ⟨c', hc', hbound'⟩ := denseSquareTupleBound_add_two hc hbound
      refine ⟨c', hc', ?_⟩
      convert hbound' using 1 <;> omega

theorem exists_denseSquareTupleBound_of_five_step :
    ∀ j : ℕ, ∃ c : ℝ, 0 < c ∧ DenseSquareTupleBound (5 + 2 * j) c := by
  intro j
  induction j with
  | zero =>
      exact ⟨k5DensityConstant, k5DensityConstant_pos,
        by simpa using denseSquareTupleBound_five⟩
  | succ j ih =>
      obtain ⟨c, hc, hbound⟩ := ih
      obtain ⟨c', hc', hbound'⟩ := denseSquareTupleBound_add_two hc hbound
      refine ⟨c', hc', ?_⟩
      convert hbound' using 1 <;> omega

theorem exists_denseSquareTupleBound (k : ℕ) (hk : 4 ≤ k) :
    ∃ c : ℝ, 0 < c ∧ DenseSquareTupleBound k c := by
  by_cases heven : Even k
  · obtain ⟨j, rfl⟩ := heven
    have hj2 : 2 ≤ j := by omega
    obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hj2
    simpa [two_mul, add_assoc, add_left_comm, add_comm] using
      exists_denseSquareTupleBound_of_four_step r
  · have hodd : Odd k := Nat.not_even_iff_odd.mp heven
    obtain ⟨j, rfl⟩ := hodd
    have hj2 : 2 ≤ j := by omega
    obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hj2
    simpa [two_mul, add_assoc, add_left_comm, add_comm] using
      exists_denseSquareTupleBound_of_five_step r

/-- The negative answer to the original five-element question. -/
theorem erdos_121_five :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop,
      (extremalSize 5 N : ℝ) ≤ (1 - c) * N := by
  refine ⟨k5DensityConstant, k5DensityConstant_pos, ?_⟩
  exact extremal_bound_of_denseSquareTupleBound (by norm_num)
    denseSquareTupleBound_five

/-- Tao's complete resolution: every fixed `k ≥ 4` has a positive density
gap.  Thus neither `F₅(N)` nor any `F₂ₖ₊₁(N)` with `2k+1 ≥ 5` is
asymptotic to `N`. -/
theorem erdos_121 :
    ∀ k : ℕ, 4 ≤ k → ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop,
      (extremalSize k N : ℝ) ≤ (1 - c) * N := by
  intro k hk
  obtain ⟨c, hc, hbound⟩ := exists_denseSquareTupleBound k hk
  exact ⟨c, hc, extremal_bound_of_denseSquareTupleBound (by omega) hbound⟩

#print axioms erdos_121

end

end Erdos121
