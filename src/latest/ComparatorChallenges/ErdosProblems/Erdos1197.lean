import Mathlib

namespace Erdos1197

open MeasureTheory Set
open scoped ENNReal

def Phi (A : Set ℝ) : Set ℝ :=
  Ico (1/2 : ℝ) 1 ∩ {x | ∃ m : ℕ, 0 < m ∧ ((m : ℝ) * x) ∈ A}

def I_inf : Set ℝ := Icc (16/25 : ℝ) (2/3)

axiom bm_approx_data :
    ∃ K₀ : ℕ, ∀ k, K₀ ≤ k →
      ∃ N_k : ℕ, ∀ ν, N_k ≤ ν →
        ∃ q : ℕ, 0 < q ∧
          (∀ y ∈ I_inf, ∃ m : ℕ, 0 < m ∧
            (m : ℝ) * y ∈ Ioo ((8 : ℝ) / 9 * 2 ^ ν) ((2 : ℝ) ^ ν) ∧
            ∃ n : ℤ, |Real.logb 2 ((m : ℝ) * y) - (n : ℝ) / (q : ℝ)| <
              1 / ((q : ℝ) * 2 ^ k)) ∧
          (∀ n : ℕ, (n : ℝ) ∈ Ioo ((7 : ℝ) / 8 * 2 ^ ν) ((9 : ℝ) / 8 * 2 ^ ν) →
            ∃ m : ℤ, |Real.logb 2 (n : ℝ) - (m : ℝ) / (q : ℝ)| <
              1 / (4 * (q : ℝ) * 2 ^ k))

end Erdos1197

open Erdos1197

attribute [local instance] Classical.propDecidable

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1197

theorem negative_answer :
    ∃ E : Set ℝ, MeasurableSet E ∧ E ⊆ Ioi 0 ∧ 0 < volume E ∧
      ∀ x ∈ I_inf,
        {n : ℕ | 0 < n ∧ ∀ r : ℕ, 0 < r →
          ¬∃ e ∈ E, x = ((r : ℝ) / (n : ℝ)) * e}.Infinite := by
  sorry

end Erdos1197
