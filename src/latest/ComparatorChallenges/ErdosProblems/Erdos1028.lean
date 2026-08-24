/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter

namespace Erdos1028

def inducedSum (n : ℕ) (f : Sym2 (Fin n) → ℤ) (X : Finset (Fin n)) : ℤ :=
  ∑ e ∈ X.sym2.filter (fun e => ¬e.IsDiag), f e
def coloringToInt {n : ℕ} (c : Sym2 (Fin n) → Bool) (e : Sym2 (Fin n)) : ℤ :=
  if c e then 1 else -1
noncomputable def H (n : ℕ) : ℤ :=
  let colorings := (Finset.univ : Finset (Sym2 (Fin n) → Bool))
  let subsets := (Finset.univ : Finset (Finset (Fin n)))
  let max_induced (c : Sym2 (Fin n) → Bool) : ℤ :=
    subsets.image (fun X => abs (inducedSum n (coloringToInt c) X)) |>.max' (by

    simp [subsets])
  colorings.image max_induced |>.min' (by
  bound)

theorem erdos_1028 : ∃ c C : ℝ, 0 < c ∧ c < C ∧ ∀ᶠ n : ℕ in atTop, c * (n : ℝ)^(3/2 : ℝ) ≤ (H n : ℝ) ∧ (H n : ℝ) ≤ C * (n : ℝ)^(3/2 : ℝ) := by
  sorry

end Erdos1028
