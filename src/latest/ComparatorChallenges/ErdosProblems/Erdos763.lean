/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter

namespace Erdos763

/-- The `ℕ`-valued indicator of a subset of the natural numbers. -/
noncomputable def indicator (A : Set ℕ) (n : ℕ) : ℕ :=
  open scoped Classical in
  if n ∈ A then 1 else 0

/-- The ordered representation function `(1_A * 1_A)(n)`. -/
noncomputable def representationCount (A : Set ℕ) (n : ℕ) : ℕ :=
  ∑ a ∈ Finset.range (n + 1), indicator A a * indicator A (n - a)

/-- The summatory ordered representation function through `N`, inclusive. -/
noncomputable def summatoryRepresentationCount (A : Set ℕ) (N : ℕ) : ℕ :=
  ∑ n ∈ Finset.range (N + 1), representationCount A n

/-! ## Bounded power series and Parseval on a circle -/

theorem not_erdos_763 :
    ¬ ∃ (A : Set ℕ) (c : ℝ), 0 < c ∧
      (fun N : ℕ ↦ (summatoryRepresentationCount A N : ℝ) - c * N) =O[atTop]
        (fun _N : ℕ ↦ (1 : ℝ)) := by
  sorry

end Erdos763
