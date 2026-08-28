import Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomologyFourierTopSymbol
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationFourierDbarBasic

/-!
# Rapid inverse-symbol coefficients for top Dolbeault forms

The constructed two-component potential removes exactly the constant
mode. The actual integer-frequency Dolbeault symbol gap gives a uniform
bound, which proves rapid decay of each component from rapid input data.
No compatibility equation or existence of a solver is assumed.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomology.FourierTop

open PeriodTorusLineBundleClassification

/-- The explicit primitive coefficients, normalized to have zero constant mode. -/
def potentialCoefficients (p : PeriodDomain) (h : (Fin 4 → ℤ) → ℂ)
    (i : Fin 2) (k : Fin 4 → ℤ) : ℂ :=
  if k = 0 then 0 else symbolRightInverse (dolbeaultSymbol p (integerFrequency k)) (h k) i

@[simp] theorem potentialCoefficients_zero (p : PeriodDomain) (h : (Fin 4 → ℤ) → ℂ)
    (i : Fin 2) : potentialCoefficients p h i 0 = 0 := by
  simp [potentialCoefficients]

/-- The top symbol equation holds at every frequency, with only the mean removed. -/
theorem potentialCoefficients_equation (p : PeriodDomain) (h : (Fin 4 → ℤ) → ℂ)
    (k : Fin 4 → ℤ) :
    dolbeaultSymbol p (integerFrequency k) 0 * potentialCoefficients p h 1 k -
      dolbeaultSymbol p (integerFrequency k) 1 * potentialCoefficients p h 0 k =
        h k - (if k = 0 then h 0 else 0) := by
  by_cases hk : k = 0
  · subst k
    simp
  · simp only [potentialCoefficients, if_neg hk, sub_zero]
    exact symbolRightInverse_equation _ _ (dolbeaultSymbol_integer_ne_zero p hk)

theorem potentialCoefficients_norm_le (p : PeriodDomain) (h : (Fin 4 → ℤ) → ℂ)
    (i : Fin 2) (k : Fin 4 → ℤ) :
    ‖potentialCoefficients p h i k‖ ≤ ‖h k‖ / ‖dolbeaultSymbol p (integerFrequency k)‖ := by
  by_cases hk : k = 0
  · subst k
    simp only [potentialCoefficients_zero, norm_zero, integerFrequency_zero,
      map_zero, div_zero, le_refl]
  · rw [potentialCoefficients, if_neg hk]
    exact symbolRightInverse_norm_le _ _ i

/-- The uniform constant comes from the proved nonzero integer-frequency symbol gap. -/
theorem potentialCoefficients_exists_uniform_norm_bound (p : PeriodDomain) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (h : (Fin 4 → ℤ) → ℂ) (i : Fin 2) (k : Fin 4 → ℤ),
      ‖potentialCoefficients p h i k‖ ≤ C * ‖h k‖ := by
  obtain ⟨c, hc, hgap⟩ := dolbeaultSymbol_integer_exists_pos_gap p
  refine ⟨1 / c, one_div_nonneg.mpr hc.le, ?_⟩
  intro h i k
  by_cases hk : k = 0
  · subst k
    rw [potentialCoefficients_zero, norm_zero]
    exact mul_nonneg (one_div_nonneg.mpr hc.le) (norm_nonneg _)
  · calc
      ‖potentialCoefficients p h i k‖ ≤ ‖h k‖ / ‖dolbeaultSymbol p (integerFrequency k)‖ :=
        potentialCoefficients_norm_le p h i k
      _ ≤ ‖h k‖ / c := div_le_div_of_nonneg_left (norm_nonneg _) hc (hgap k hk)
      _ = (1 / c) * ‖h k‖ := by ring

/-- Every constructed component is rapid; no potential summability is an input. -/
theorem potentialCoefficients_rapid (p : PeriodDomain) (h : (Fin 4 → ℤ) → ℂ)
    (hh : RapidFourierCoefficients h) (i : Fin 2) :
    RapidFourierCoefficients (potentialCoefficients p h i) := by
  obtain ⟨C, _, hbound⟩ := potentialCoefficients_exists_uniform_norm_bound p
  apply rapidFourierCoefficients_of_norm_le_add hh rapidFourierCoefficients_zero C
  intro k
  simpa only [norm_zero, add_zero] using hbound h i k

end Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomology.FourierTop
