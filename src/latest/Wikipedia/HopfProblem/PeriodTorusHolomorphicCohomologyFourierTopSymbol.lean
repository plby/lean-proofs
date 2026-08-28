import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationFourierDbarInverseAlgebra

/-!
# A right inverse for the top Dolbeault symbol

Division through the actual maximal-norm symbol coordinate gives a
two-component primitive for every scalar top-degree coefficient. Each
component has norm at most the scalar norm divided by the symbol norm.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomology.FourierTop

open PeriodTorusLineBundleClassification

/-- A right inverse of the two-component alternating symbol, using the
existing controlled division through a maximal-norm coordinate. -/
def symbolRightInverse (s : Fin 2 → ℂ) (c : ℂ) : Fin 2 → ℂ :=
  ![-symbolDivide s ![0, c], symbolDivide s ![c, 0]]

/-- Every scalar top-degree coefficient is solved at a nonzero symbol. -/
theorem symbolRightInverse_equation (s : Fin 2 → ℂ) (c : ℂ) (hs : s ≠ 0) :
    s 0 * symbolRightInverse s c 1 - s 1 * symbolRightInverse s c 0 = c := by
  have hmax := symbolMaxCoordinate_ne_zero hs
  unfold symbolRightInverse symbolDivide
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  generalize hj : symbolMaxCoordinate s = j at hmax ⊢
  fin_cases j
  · change s 0 * (c / s 0) - s 1 * -(0 / s 0) = c
    simp only [zero_div, neg_zero, mul_zero, sub_zero]
    exact mul_div_cancel₀ c hmax
  · change s 0 * (0 / s 1) - s 1 * -(c / s 1) = c
    simp only [zero_div, mul_zero, mul_neg, zero_sub, neg_neg]
    exact mul_div_cancel₀ c hmax

/-- Componentwise control, including the totalized zero-symbol quotient. -/
theorem symbolRightInverse_norm_le (s : Fin 2 → ℂ) (c : ℂ) (i : Fin 2) :
    ‖symbolRightInverse s c i‖ ≤ ‖c‖ / ‖s‖ := by
  fin_cases i
  · change ‖-symbolDivide s ![0, c]‖ ≤ ‖c‖ / ‖s‖
    rw [norm_neg]
    simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, norm_zero, zero_add] using
      symbolDivide_norm_le s ![0, c]
  · change ‖symbolDivide s ![c, 0]‖ ≤ ‖c‖ / ‖s‖
    simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, norm_zero, add_zero] using
      symbolDivide_norm_le s ![c, 0]

end Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomology.FourierTop
