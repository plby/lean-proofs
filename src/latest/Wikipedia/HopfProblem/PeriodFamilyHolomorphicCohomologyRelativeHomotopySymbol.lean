import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyRelativeHomotopySelection

/-!
# The original nonzero-mode homotopy equations

The inverse chosen at the fixed centre solves both original symbol
equations for a closed coefficient pair. Its genuine zero mode is zero,
so the all-frequency identity removes exactly the original zero Fourier
coefficient. No inverse equation or closedness is built into a definition.
-/

noncomputable section

open TopologicalSpace

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.RelativeHomotopy

open FourierSynthesis RelativeFourier MarkedLinear PeriodTorusLineBundleClassification

/-- Delete just the original zero-frequency coefficient. -/
def removeZeroCoefficients (c : Coefficients) : Coefficients :=
  fun k z => if k = 0 then 0 else c k z

@[simp] theorem removeZeroCoefficients_zero (c : Coefficients) (z : ℂ) :
    removeZeroCoefficients c 0 z = 0 := if_pos rfl

theorem removeZeroCoefficients_of_ne_zero (c : Coefficients) {k : Frequency}
    (hk : k ≠ 0) (z : ℂ) : removeZeroCoefficients c k z = c k z := if_neg hk

/-- Removing the zero mode preserves every proved rapid coefficient bound. -/
theorem removeZeroCoefficients_rapid {U : Opens ℂ} {c : Coefficients}
    (hc : SmoothRapidCoefficients U c) : SmoothRapidCoefficients U (removeZeroCoefficients c) := by
  have h := hc.frequency_mul (fun k => if k = 0 then (0 : ℂ) else 1)
    (show (0 : ℝ) ≤ 1 by norm_num) 0 (by
      intro k
      by_cases hk : k = 0 <;> simp only [hk, if_true, if_false, norm_zero, norm_one,
        pow_zero, mul_one, zero_le_one, le_refl])
  convert h using 1
  funext k z
  by_cases hk : k = 0 <;> simp only [removeZeroCoefficients, hk, if_true, if_false,
    zero_mul, one_mul]

/-- Division through any actual invertible selected component solves a
closed two-component scalar symbol system. -/
theorem selected_inverse_solves_pair (s a : Fin 2 → ℂ) (j : Fin 2) (m : ℂ)
    (hm : s j * m = 1) (hc : s 0 * a 1 = s 1 * a 0) (i : Fin 2) :
    s i * (m * a j) = a i := by
  have hcross : s i * a j = s j * a i := by
    fin_cases i <;> fin_cases j
    · rfl
    · exact hc
    · exact hc.symm
    · rfl
  calc
    s i * (m * a j) = m * (s i * a j) := by ring
    _ = m * (s j * a i) := by rw [hcross]
    _ = (s j * m) * a i := by ring
    _ = a i := by rw [hm, one_mul]

/-- The literal original potential solves every original relative
symbol equation where the proved selected inverse equation holds. -/
theorem potentialCoefficients_symbol {U : Opens ℂ} (P : HolomorphicPeriodMap ℂ U)
    (p₀ : PeriodDomain) (a : Fin 2 → Coefficients) (b : U) (k : Frequency)
    (hinverse : centreCoefficient p₀ (P.point b) (integerFrequency k) *
      ambientInverse P p₀ k (b : ℂ) = 1)
    (hclosed : relativeSymbol (P.point b) (integerFrequency k) 0 * a 1 k (b : ℂ) =
      relativeSymbol (P.point b) (integerFrequency k) 1 * a 0 k (b : ℂ)) (i : Fin 2) :
    relativeSymbol (P.point b) (integerFrequency k) i *
      potentialCoefficients P p₀ a k (b : ℂ) = a i k (b : ℂ) :=
  selected_inverse_solves_pair (relativeSymbol (P.point b) (integerFrequency k))
    (fun j => a j k (b : ℂ)) (centreCoordinate p₀ (integerFrequency k))
    (ambientInverse P p₀ k (b : ℂ)) hinverse hclosed i

/-- The all-frequency equation deletes exactly the genuine zero mode. -/
theorem potentialCoefficients_symbol_removeZero {U : Opens ℂ}
    (P : HolomorphicPeriodMap ℂ U) (p₀ : PeriodDomain) (a : Fin 2 → Coefficients) (b : U)
    (hinverse : ∀ k : Frequency, k ≠ 0 →
      centreCoefficient p₀ (P.point b) (integerFrequency k) *
        ambientInverse P p₀ k (b : ℂ) = 1)
    (hclosed : ∀ k : Frequency,
      relativeSymbol (P.point b) (integerFrequency k) 0 * a 1 k (b : ℂ) =
        relativeSymbol (P.point b) (integerFrequency k) 1 * a 0 k (b : ℂ))
    (i : Fin 2) (k : Frequency) :
    relativeSymbol (P.point b) (integerFrequency k) i *
      potentialCoefficients P p₀ a k (b : ℂ) = removeZeroCoefficients (a i) k (b : ℂ) := by
  by_cases hk : k = 0
  · subst k
    rw [potentialCoefficients_zero, mul_zero, removeZeroCoefficients_zero]
  · rw [removeZeroCoefficients_of_ne_zero _ hk]
    exact potentialCoefficients_symbol P p₀ a b k (hinverse k hk) (hclosed k) i

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.RelativeHomotopy
