/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Finset

namespace Erdos866b

def HasPairwiseSums (A : Finset ℤ) (k : ℕ) : Prop :=
  ∃ b : Fin k → ℤ, Function.Injective b ∧ ∀ i j : Fin k, i < j → b i + b j ∈ A

def HasPosPairwiseSums (A : Finset ℤ) (k : ℕ) : Prop :=
  ∃ b : Fin k → ℤ, Function.Injective b ∧ (∀ i : Fin k, 0 < b i) ∧
    ∀ i j : Fin k, i < j → b i + b j ∈ A

noncomputable def gFun (k n : ℕ) : ℕ :=
  sInf {m : ℕ | ∀ (A : Finset ℤ), A ⊆ Icc (1 : ℤ) (2 * ↑n) →
    n + m ≤ A.card → HasPairwiseSums A k}

noncomputable def hFun (k n : ℕ) : ℕ :=
  sInf {m : ℕ | ∀ (A : Finset ℤ), A ⊆ Icc (1 : ℤ) (2 * ↑n) →
    n + m ≤ A.card → HasPosPairwiseSums A k}

theorem g3 (n : ℕ) (hn : 3 ≤ n) : gFun 3 n = 1 := by
  sorry

theorem h3 (n : ℕ) (hn : 4 ≤ n) : hFun 3 n = 2 := by
  sorry

theorem g4 (n : ℕ) (hn : 2 ≤ n) : gFun 4 n = 3 := by
  sorry

theorem h4upper (n : ℕ) (hn : 0 < n) : hFun 4 n ≤ 2270 := by
  sorry

theorem g5upper (n : ℕ) : gFun 5 n < 120000000 := by
  sorry

theorem erdos_866 (k : ℕ) (hk : 3 ≤ k) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      gFun k n ≤ hFun k n ∧
      (hFun k n : ℝ) < 4 * (↑n : ℝ) ^ ((1:ℝ) - 1 / 2 ^ ((k:ℝ) - 2)) := by
  sorry

end Erdos866b
