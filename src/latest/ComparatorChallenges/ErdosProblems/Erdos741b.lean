/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open scoped Pointwise

namespace Erdos741b

open scoped Classical in
noncomputable def countIn (S : Set ℕ) (N : ℕ) : ℕ :=
  (Finset.range N).filter (· ∈ S) |>.card

noncomputable def upperDensity (S : Set ℕ) : ℝ :=
  Filter.limsup (fun N => (countIn S N : ℝ) / N) Filter.atTop

def HasNatDensity (S : Set ℕ) (d : ℝ) : Prop :=
  Filter.Tendsto (fun N => (countIn S (N + 1) : ℝ) / (N + 1)) Filter.atTop (nhds d)

structure BiPartition (A : Set ℕ) where
  left : Set ℕ
  right : Set ℕ
  disj : Disjoint left right
  cover : left ∪ right = A

theorem erdos_741 (A : Set ℕ) (hA : upperDensity (A + A) > 0) :
    ∃ P : BiPartition A,
      upperDensity (P.left + P.left) > 0 ∧ upperDensity (P.right + P.right) > 0 := by
  sorry

theorem not_erdos_741_natural_density :
    ∃ A : Set ℕ, HasNatDensity (A + A) 1 ∧
      ∀ P : BiPartition A, ¬(∃ d₁ > 0, ∃ d₂ > 0,
        HasNatDensity (P.left + P.left) d₁ ∧ HasNatDensity (P.right + P.right) d₂) := by
  sorry

end Erdos741b
