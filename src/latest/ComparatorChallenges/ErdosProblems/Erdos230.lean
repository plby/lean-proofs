import Mathlib

noncomputable section

attribute [local instance] Classical.propDecidable

namespace Erdos230

def IsUnimodular {n : ℕ} (a : Fin n → ℂ) : Prop :=
  ∀ i, ‖a i‖ = 1

end Erdos230

namespace Erdos230

def phasePoly {n : ℕ} (a : Fin n → ℂ) : Polynomial ℂ :=
  ∑ i : Fin n, Polynomial.monomial (i.1 + 1) (a i)

end Erdos230

namespace Erdos230

def circleValues {n : ℕ} (a : Fin n → ℂ) : Set ℝ :=
  {x | ∃ z : ℂ, ‖z‖ = 1 ∧ x = ‖(phasePoly a).eval z‖}

end Erdos230

namespace Erdos230

noncomputable def circleMaximum {n : ℕ} (a : Fin n → ℂ) : ℝ :=
  sSup (circleValues a)

end Erdos230

namespace Erdos230

def ErdosNewmanClaim : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ n : ℕ, 2 ≤ n →
      ∀ a : Fin n → ℂ, IsUnimodular a →
        (1 + c) * Real.sqrt n ≤ circleMaximum a

end Erdos230

namespace Erdos230

theorem erdos_230 : ¬ ErdosNewmanClaim := by
  sorry

end Erdos230

end
