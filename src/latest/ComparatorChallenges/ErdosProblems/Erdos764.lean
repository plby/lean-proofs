/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Finset

namespace Erdos764

def addConv (f g : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, f p.1 * g p.2

open scoped Classical in
noncomputable def indicator (A : Set ℕ) (n : ℕ) : ℕ :=
  if n ∈ A then 1 else 0

noncomputable def tripleConv (A : Set ℕ) (n : ℕ) : ℕ :=
  addConv (addConv (indicator A) (indicator A)) (indicator A) n

noncomputable def summatory (A : Set ℕ) (N : ℕ) : ℕ :=
  ∑ n ∈ range (N + 1), tripleConv A n

noncomputable def remainder (A : Set ℕ) (c : ℝ) (N : ℕ) : ℝ :=
  (summatory A N : ℝ) - c * N

theorem not_erdos_764 :
    ¬ ∃ A : Set ℕ, ∃ c : ℝ, 0 < c ∧
      remainder A c =O[Filter.atTop] (fun _ : ℕ ↦ (1 : ℝ)) := by
  sorry

end Erdos764
