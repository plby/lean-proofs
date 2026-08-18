/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos984.Basic

/-!
# Eventual-to-global bounds for Erdős Problem 984

Hunter's quantitative theorem is naturally stated only for sufficiently
large finite intervals.  This file absorbs the finite initial segment into
the implicit constant required by `OffDiagonalData.subpower`.
-/

namespace Erdos984

/-- A finite off-diagonal family with an eventual subpower estimate. -/
structure EventualOffDiagonalData where
  H : ℕ → ℕ
  three_le_H : ∀ N, 3 ≤ H N
  coloring : ℕ → ℕ → Bool
  good : ∀ N, GoodOffDiagonal (coloring N) N (H N)
  eventually_subpower : ∀ ε : ℝ, 0 < ε →
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → 0 < N →
      (H N : ℝ) ≤ (N : ℝ) ^ ε

/-- A finite initial segment of a nonnegative sequence is bounded by its
sum.  This deliberately loose bound avoids choosing a finite maximum. -/
lemma term_le_initial_sum (H : ℕ → ℕ) {N N₀ : ℕ} (hN : N < N₀) :
    (H N : ℝ) ≤ ∑ n ∈ Finset.range N₀, (H n : ℝ) := by
  exact Finset.single_le_sum (s := Finset.range N₀)
    (f := fun n => (H n : ℝ)) (fun i hi => by positivity) (by simpa using hN)

/-- Turn an eventual coefficient-one subpower estimate into the global
estimate with an epsilon-dependent positive coefficient. -/
lemma global_subpower_of_eventual (H : ℕ → ℕ)
    (hevent : ∀ ε : ℝ, 0 < ε →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → 0 < N →
        (H N : ℝ) ≤ (N : ℝ) ^ ε) :
    ∀ ε : ℝ, 0 < ε →
      ∃ B : ℝ, 0 < B ∧ ∀ N : ℕ, 0 < N →
        (H N : ℝ) ≤ B * (N : ℝ) ^ ε := by
  intro ε hε
  obtain ⟨N₀, hlarge⟩ := hevent ε hε
  let S : ℝ := ∑ n ∈ Finset.range N₀, (H n : ℝ)
  let B : ℝ := 1 + S
  have hSnonneg : 0 ≤ S := by
    dsimp [S]
    positivity
  have hBpos : 0 < B := by
    dsimp [B]
    positivity
  refine ⟨B, hBpos, ?_⟩
  intro N hNpos
  have hNone : (1 : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast hNpos
  have hpow_one : (1 : ℝ) ≤ (N : ℝ) ^ ε :=
    Real.one_le_rpow hNone hε.le
  by_cases hNlarge : N₀ ≤ N
  · calc
      (H N : ℝ) ≤ (N : ℝ) ^ ε := hlarge N hNlarge hNpos
      _ ≤ B * (N : ℝ) ^ ε :=
        le_mul_of_one_le_left (by positivity) (by
          dsimp [B]
          linarith)
  · have hterm : (H N : ℝ) ≤ S := by
      exact term_le_initial_sum H (by omega)
    calc
      (H N : ℝ) ≤ S := hterm
      _ ≤ B := by
        dsimp [B]
        linarith
      _ ≤ B * (N : ℝ) ^ ε :=
        le_mul_of_one_le_right hBpos.le hpow_one

/-- Forget the threshold in an eventual off-diagonal family. -/
def EventualOffDiagonalData.toOffDiagonalData
    (D : EventualOffDiagonalData) : OffDiagonalData where
  H := D.H
  three_le_H := D.three_le_H
  coloring := D.coloring
  good := D.good
  subpower := global_subpower_of_eventual D.H D.eventually_subpower

end Erdos984
