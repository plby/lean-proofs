import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationFourierDbarBasic
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationFourierDbarInverseAlgebra

/-!
# Constructed inverse-symbol Fourier coefficients

The potential coefficients vanish at zero frequency and divide the actual
Dolbeault symbol at every nonzero frequency. Its proved spectral gap gives
a uniform bound, and hence weighted absolute summability of every order for
rapid input data.
-/

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassification

/-- Explicit normalized potential coefficients, with zero constant term. -/
noncomputable def dolbeaultPotentialCoefficients (p : PeriodDomain)
    (a : Fin 2 → (Fin 4 → ℤ) → ℂ) (k : Fin 4 → ℤ) : ℂ :=
  if k = 0 then 0 else
    symbolDivide (dolbeaultSymbol p (integerFrequency k)) (fun i => a i k)

@[simp]
theorem dolbeaultPotentialCoefficients_zero (p : PeriodDomain)
    (a : Fin 2 → (Fin 4 → ℤ) → ℂ) : dolbeaultPotentialCoefficients p a 0 = 0 := by
  simp [dolbeaultPotentialCoefficients]

/-- The symbol equation holds at every frequency, with precisely the constant
coefficient removed. Compatibility is required only of the given input data. -/
theorem dolbeaultPotentialCoefficients_mul (p : PeriodDomain)
    (a : Fin 2 → (Fin 4 → ℤ) → ℂ)
    (hcompat : ∀ k : Fin 4 → ℤ,
      dolbeaultSymbol p (integerFrequency k) 0 * a 1 k =
        dolbeaultSymbol p (integerFrequency k) 1 * a 0 k)
    (i : Fin 2) (k : Fin 4 → ℤ) :
    dolbeaultSymbol p (integerFrequency k) i * dolbeaultPotentialCoefficients p a k =
      a i k - (if k = 0 then a i 0 else 0) := by
  by_cases hk : k = 0
  · subst k
    simp
  · simp only [dolbeaultPotentialCoefficients, if_neg hk, sub_zero]
    exact symbolDivide_mul _ _ (dolbeaultSymbol_integer_ne_zero p hk) (hcompat k) i

theorem dolbeaultPotentialCoefficients_norm_le (p : PeriodDomain)
    (a : Fin 2 → (Fin 4 → ℤ) → ℂ) (k : Fin 4 → ℤ) :
    ‖dolbeaultPotentialCoefficients p a k‖ ≤
      (‖a 0 k‖ + ‖a 1 k‖) / ‖dolbeaultSymbol p (integerFrequency k)‖ := by
  by_cases hk : k = 0
  · subst k
    simp only [dolbeaultPotentialCoefficients_zero, norm_zero, integerFrequency_zero,
      map_zero, div_zero, le_refl]
  · rw [dolbeaultPotentialCoefficients, if_neg hk]
    exact symbolDivide_norm_le _ _

/-- The bound is uniform in both the coefficient data and the frequency.
Its constant is supplied by the genuine nonzero-frequency symbol gap. -/
theorem dolbeaultPotentialCoefficients_exists_uniform_norm_bound (p : PeriodDomain) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : Fin 2 → (Fin 4 → ℤ) → ℂ) (k : Fin 4 → ℤ),
      ‖dolbeaultPotentialCoefficients p a k‖ ≤ C * (‖a 0 k‖ + ‖a 1 k‖) := by
  obtain ⟨c, hc, hgap⟩ := dolbeaultSymbol_integer_exists_pos_gap p
  refine ⟨1 / c, one_div_nonneg.mpr hc.le, ?_⟩
  intro a k
  by_cases hk : k = 0
  · subst k
    rw [dolbeaultPotentialCoefficients_zero, norm_zero]
    exact mul_nonneg (one_div_nonneg.mpr hc.le)
      (add_nonneg (norm_nonneg _) (norm_nonneg _))
  · calc
      ‖dolbeaultPotentialCoefficients p a k‖ ≤
          (‖a 0 k‖ + ‖a 1 k‖) / ‖dolbeaultSymbol p (integerFrequency k)‖ :=
        dolbeaultPotentialCoefficients_norm_le p a k
      _ ≤ (‖a 0 k‖ + ‖a 1 k‖) / c :=
        div_le_div_of_nonneg_left (add_nonneg (norm_nonneg _) (norm_nonneg _))
          hc (hgap k hk)
      _ = (1 / c) * (‖a 0 k‖ + ‖a 1 k‖) := by ring

/-- The explicitly constructed coefficients are rapid whenever both input
components are rapid; no summability of the potential is assumed. -/
theorem dolbeaultPotentialCoefficients_rapid (p : PeriodDomain)
    (a : Fin 2 → (Fin 4 → ℤ) → ℂ)
    (h₀ : RapidFourierCoefficients (a 0)) (h₁ : RapidFourierCoefficients (a 1)) :
    RapidFourierCoefficients (dolbeaultPotentialCoefficients p a) := by
  obtain ⟨C, _, hbound⟩ := dolbeaultPotentialCoefficients_exists_uniform_norm_bound p
  exact rapidFourierCoefficients_of_norm_le_add h₀ h₁ C (hbound a)

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassification
