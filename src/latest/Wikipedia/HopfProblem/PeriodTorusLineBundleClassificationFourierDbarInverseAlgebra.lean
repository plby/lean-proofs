import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationFourierSymbol

/-!
# Division by a nonzero two-component Dolbeault symbol

The selected coordinate has maximal norm in the actual finite-product norm.
Division through that coordinate is therefore quantitatively controlled,
without any assumed componentwise lower bound.
-/

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassification

/-- A coordinate attaining the norm of a two-component complex symbol. -/
noncomputable def symbolMaxCoordinate (s : Fin 2 → ℂ) : Fin 2 :=
  if ‖s 0‖ ≤ ‖s 1‖ then 1 else 0

theorem norm_symbolMaxCoordinate (s : Fin 2 → ℂ) :
    ‖s (symbolMaxCoordinate s)‖ = ‖s‖ := by
  refine le_antisymm (norm_le_pi_norm s (symbolMaxCoordinate s)) ?_
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro i
  by_cases h : ‖s 0‖ ≤ ‖s 1‖
  · simp only [symbolMaxCoordinate, if_pos h]
    fin_cases i
    · exact h
    · exact le_rfl
  · simp only [symbolMaxCoordinate, if_neg h]
    fin_cases i
    · exact le_rfl
    · exact (lt_of_not_ge h).le

theorem symbolMaxCoordinate_ne_zero {s : Fin 2 → ℂ} (hs : s ≠ 0) :
    s (symbolMaxCoordinate s) ≠ 0 := by
  intro h
  apply hs
  apply norm_eq_zero.mp
  rw [← norm_symbolMaxCoordinate, h, norm_zero]

/-- Explicit division through a maximal-norm coordinate of the symbol. -/
noncomputable def symbolDivide (s a : Fin 2 → ℂ) : ℂ :=
  a (symbolMaxCoordinate s) / s (symbolMaxCoordinate s)

/-- Pair compatibility makes division through the selected nonzero coordinate
solve both symbol equations. -/
theorem symbolDivide_mul (s a : Fin 2 → ℂ) (hs : s ≠ 0)
    (hc : s 0 * a 1 = s 1 * a 0) (i : Fin 2) :
    s i * symbolDivide s a = a i := by
  have hdivision (j : Fin 2) (hj : s j ≠ 0) :
      ∀ i : Fin 2, s i * (a j / s j) = a i := by
    intro i
    rw [← mul_div_assoc, div_eq_iff hj]
    fin_cases i <;> fin_cases j
    · exact mul_comm _ _
    · exact hc.trans (mul_comm _ _)
    · exact hc.symm.trans (mul_comm _ _)
    · exact mul_comm _ _
  exact hdivision (symbolMaxCoordinate s) (symbolMaxCoordinate_ne_zero hs) i

/-- The division bound is valid even for the totalized zero-symbol quotient. -/
theorem symbolDivide_norm_le (s a : Fin 2 → ℂ) :
    ‖symbolDivide s a‖ ≤ (‖a 0‖ + ‖a 1‖) / ‖s‖ := by
  have hA (j : Fin 2) : ‖a j‖ ≤ ‖a 0‖ + ‖a 1‖ := by
    fin_cases j
    · exact le_add_of_nonneg_right (norm_nonneg _)
    · exact le_add_of_nonneg_left (norm_nonneg _)
  rw [symbolDivide, norm_div, norm_symbolMaxCoordinate]
  exact div_le_div_of_nonneg_right (hA _) (norm_nonneg s)

theorem exists_symbol_solution (s a : Fin 2 → ℂ) (hs : s ≠ 0)
    (hc : s 0 * a 1 = s 1 * a 0) :
    ∃ b : ℂ, (∀ i : Fin 2, s i * b = a i) ∧
      ‖b‖ ≤ (‖a 0‖ + ‖a 1‖) / ‖s‖ :=
  ⟨symbolDivide s a, symbolDivide_mul s a hs hc, symbolDivide_norm_le s a⟩

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassification
