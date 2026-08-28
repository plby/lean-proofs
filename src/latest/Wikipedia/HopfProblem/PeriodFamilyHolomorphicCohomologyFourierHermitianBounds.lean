import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyFourierHermitianBasic

/-!
# Quantitative bounds for the Hermitian symbol inverses

The norm is the original finite-product norm on `ComplexPlane₂`. The estimates
hold for the totalized zero-symbol formulas too. No coordinate selection is
used in either the definitions or the estimates.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.FourierHermitian

open Complex
open scoped ComplexConjugate

theorem energy_eq_norm_sq_add (s : ComplexPlane₂) :
    energy s = ‖s 0‖ ^ 2 + ‖s 1‖ ^ 2 := by
  simp only [energy, Complex.normSq_eq_norm_sq]

/-- The Hermitian energy dominates the square of the actual product norm. -/
theorem norm_sq_le_energy (s : ComplexPlane₂) : ‖s‖ ^ 2 ≤ energy s := by
  have hnorm : ‖s‖ ≤ Real.sqrt (energy s) := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
    intro i
    apply Real.le_sqrt_of_sq_le
    rw [energy_eq_norm_sq_add]
    fin_cases i
    · exact le_add_of_nonneg_right (sq_nonneg _)
    · exact le_add_of_nonneg_left (sq_nonneg _)
  have hsq := Real.sq_sqrt (energy_nonneg s)
  nlinarith [norm_nonneg s, Real.sqrt_nonneg (energy s)]

/-- Conversely, two coordinates cost at most the factor two. -/
theorem energy_le_two_mul_norm_sq (s : ComplexPlane₂) :
    energy s ≤ 2 * ‖s‖ ^ 2 := by
  rw [energy_eq_norm_sq_add]
  have h₀ := sq_le_sq₀ (norm_nonneg (s 0)) (norm_nonneg s) |>.mpr
    (norm_le_pi_norm s 0)
  have h₁ := sq_le_sq₀ (norm_nonneg (s 1)) (norm_nonneg s) |>.mpr
    (norm_le_pi_norm s 1)
  linarith

/-- Each conjugate coefficient divided by the energy has order minus one. -/
theorem norm_conj_div_energy_le (s : ComplexPlane₂) (i : Fin 2) :
    ‖conj (s i) / (energy s : ℂ)‖ ≤ 1 / ‖s‖ := by
  by_cases hs : s = 0
  · simp [hs]
  have hD := (energy_pos_iff s).mpr hs
  have hS := norm_pos_iff.mpr hs
  rw [norm_div, Complex.norm_conj, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (energy_nonneg s)]
  apply (div_le_div_iff₀ hD hS).mpr
  calc
    ‖s i‖ * ‖s‖ ≤ ‖s‖ * ‖s‖ :=
      mul_le_mul_of_nonneg_right (norm_le_pi_norm s i) (norm_nonneg s)
    _ ≤ 1 * energy s := by simpa only [one_mul, pow_two] using norm_sq_le_energy s

/-- The primitive is a sum of two explicit order-minus-one multipliers. -/
theorem potential_eq_sum (s a : ComplexPlane₂) :
    potential s a = (conj (s 0) / (energy s : ℂ)) * a 0 +
      (conj (s 1) / (energy s : ℂ)) * a 1 := by
  simp only [potential, div_eq_mul_inv]
  ring

/-- A coefficientwise bound valid without a closedness assumption. -/
theorem potential_norm_le (s a : ComplexPlane₂) :
    ‖potential s a‖ ≤ (‖a 0‖ + ‖a 1‖) / ‖s‖ := by
  rw [potential_eq_sum]
  calc
    ‖conj (s 0) / (energy s : ℂ) * a 0 + conj (s 1) / (energy s : ℂ) * a 1‖ ≤
        ‖conj (s 0) / (energy s : ℂ) * a 0‖ +
          ‖conj (s 1) / (energy s : ℂ) * a 1‖ := norm_add_le _ _
    _ = ‖conj (s 0) / (energy s : ℂ)‖ * ‖a 0‖ +
        ‖conj (s 1) / (energy s : ℂ)‖ * ‖a 1‖ := by rw [norm_mul, norm_mul]
    _ ≤ (1 / ‖s‖) * ‖a 0‖ + (1 / ‖s‖) * ‖a 1‖ :=
      add_le_add
        (mul_le_mul_of_nonneg_right (norm_conj_div_energy_le s 0) (norm_nonneg _))
        (mul_le_mul_of_nonneg_right (norm_conj_div_energy_le s 1) (norm_nonneg _))
    _ = (‖a 0‖ + ‖a 1‖) / ‖s‖ := by ring

/-- An operator bound expressed entirely in the original product norms. -/
theorem potential_norm_le_two (s a : ComplexPlane₂) :
    ‖potential s a‖ ≤ 2 * ‖a‖ / ‖s‖ := by
  apply (potential_norm_le s a).trans
  apply div_le_div_of_nonneg_right _ (norm_nonneg s)
  have h₀ := norm_le_pi_norm a 0
  have h₁ := norm_le_pi_norm a 1
  linarith

/-- Each component of the top-degree inverse has order minus one. -/
theorem topInverse_component_norm_le (s : ComplexPlane₂) (h : ℂ) (i : Fin 2) :
    ‖topInverse s h i‖ ≤ ‖h‖ / ‖s‖ := by
  have hbound (j : Fin 2) :
      ‖(conj (s j) / (energy s : ℂ)) * h‖ ≤ ‖h‖ / ‖s‖ := by
    rw [norm_mul]
    calc
      ‖conj (s j) / (energy s : ℂ)‖ * ‖h‖ ≤ (1 / ‖s‖) * ‖h‖ :=
        mul_le_mul_of_nonneg_right (norm_conj_div_energy_le s j) (norm_nonneg h)
      _ = ‖h‖ / ‖s‖ := by ring
  fin_cases i
  · change ‖topInverse s h 0‖ ≤ ‖h‖ / ‖s‖
    have heq : topInverse s h 0 = -((conj (s 1) / (energy s : ℂ)) * h) := by
      simp only [topInverse, Matrix.cons_val_zero, div_eq_mul_inv]
      ring
    rw [heq, norm_neg]
    exact hbound 1
  · change ‖topInverse s h 1‖ ≤ ‖h‖ / ‖s‖
    have heq : topInverse s h 1 = (conj (s 0) / (energy s : ℂ)) * h := by
      simp only [topInverse, Matrix.cons_val_one, Matrix.cons_val_zero, div_eq_mul_inv]
      ring
    rw [heq]
    exact hbound 0

/-- The top-degree inverse has the same bound in the product norm. -/
theorem topInverse_norm_le (s : ComplexPlane₂) (h : ℂ) :
    ‖topInverse s h‖ ≤ ‖h‖ / ‖s‖ :=
  (pi_norm_le_iff_of_nonneg (div_nonneg (norm_nonneg h) (norm_nonneg s))).mpr
    (topInverse_component_norm_le s h)

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.FourierHermitian
