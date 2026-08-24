/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter

namespace Erdos605

abbrev E3 := EuclideanSpace ℝ (Fin 3)

noncomputable def pairDistance {n : ℕ} (x : Fin n → E3) : Sym2 (Fin n) → ℝ :=
  Sym2.lift ⟨fun i j ↦ dist (x i) (x j), fun _ _ ↦ dist_comm _ _⟩

theorem erdos_605 :
    ∃ f : ℕ → ℝ, Tendsto f atTop atTop ∧
      ∃ center : E3, ∃ radius : ℝ, 0 < radius ∧ ∀ n : ℕ,
        ∃ x : Fin n → E3, ∃ d : ℝ, ∃ E : Finset (Sym2 (Fin n)),
          Function.Injective x ∧
          (∀ i, dist (x i) center = radius) ∧
          0 < d ∧
          (∀ e ∈ E, ¬ e.IsDiag ∧ pairDistance x e = d) ∧
          f n * (n : ℝ) ≤ (E.card : ℝ) := by
  sorry

end Erdos605
