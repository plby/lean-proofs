import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyFourierHermitianBounds

/-!
# The Hermitian contraction of the two-component symbol complex

The same explicit formulas give complex-linear operators and a contracting
homotopy at every nonzero symbol. These identities apply to arbitrary
coefficients, not just to closed pairs.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.FourierHermitian

open Complex
open scoped ComplexConjugate

theorem potential_add (s a b : ComplexPlane₂) :
    potential s (a + b) = potential s a + potential s b := by
  simp only [potential, Pi.add_apply, div_eq_mul_inv]
  ring

theorem potential_smul (s : ComplexPlane₂) (c : ℂ) (a : ComplexPlane₂) :
    potential s (c • a) = c * potential s a := by
  simp only [potential, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv]
  ring

theorem topInverse_add (s : ComplexPlane₂) (h k : ℂ) :
    topInverse s (h + k) = topInverse s h + topInverse s k := by
  ext i
  fin_cases i
  · change -conj (s 1) * (h + k) / (energy s : ℂ) =
      -conj (s 1) * h / (energy s : ℂ) + -conj (s 1) * k / (energy s : ℂ)
    ring
  · change conj (s 0) * (h + k) / (energy s : ℂ) =
      conj (s 0) * h / (energy s : ℂ) + conj (s 0) * k / (energy s : ℂ)
    ring

theorem topInverse_smul (s : ComplexPlane₂) (c h : ℂ) :
    topInverse s (c * h) = c • topInverse s h := by
  ext i
  fin_cases i
  · change -conj (s 1) * (c * h) / (energy s : ℂ) =
      c * (-conj (s 1) * h / (energy s : ℂ))
    ring
  · change conj (s 0) * (c * h) / (energy s : ℂ) =
      c * (conj (s 0) * h / (energy s : ℂ))
    ring

/-- The middle-degree contracting homotopy, with the original alternating sign. -/
theorem symbol_homotopy (s a : ComplexPlane₂) (hs : s ≠ 0) (i : Fin 2) :
    s i * potential s a + topInverse s (s 0 * a 1 - s 1 * a 0) i = a i := by
  fin_cases i
  · change s 0 * potential s a +
      (-conj (s 1) * (s 0 * a 1 - s 1 * a 0) / (energy s : ℂ)) = a 0
    rw [potential, ← mul_div_assoc, ← add_div,
      div_eq_iff (energy_coe_ne_zero hs), energy_coe]
    ring
  · change s 1 * potential s a +
      (conj (s 0) * (s 0 * a 1 - s 1 * a 0) / (energy s : ℂ)) = a 1
    rw [potential, ← mul_div_assoc, ← add_div,
      div_eq_iff (energy_coe_ne_zero hs), energy_coe]
    ring

/-- The degree-zero contraction is a genuine inverse on symbol multiples. -/
theorem potential_smul_symbol (s : ComplexPlane₂) (c : ℂ) (hs : s ≠ 0) :
    potential s (c • s) = c := by
  simp only [potential, Pi.smul_apply, smul_eq_mul]
  rw [div_eq_iff (energy_coe_ne_zero hs), energy_coe]
  ring

/-- The two inverse operators compose to zero, even at the zero symbol. -/
theorem potential_topInverse (s : ComplexPlane₂) (h : ℂ) :
    potential s (topInverse s h) = 0 := by
  simp only [potential, topInverse, Matrix.cons_val_zero, Matrix.cons_val_one,
    div_eq_mul_inv]
  ring

/-- The actual degree-one Hermitian inverse as a complex-linear map. -/
def potentialLinearMap (s : ComplexPlane₂) : ComplexPlane₂ →ₗ[ℂ] ℂ where
  toFun := potential s
  map_add' := potential_add s
  map_smul' c a := by
    simpa only [RingHom.id_apply, smul_eq_mul] using potential_smul s c a

/-- The actual degree-two Hermitian inverse as a complex-linear map. -/
def topInverseLinearMap (s : ComplexPlane₂) : ℂ →ₗ[ℂ] ComplexPlane₂ where
  toFun := topInverse s
  map_add' := topInverse_add s
  map_smul' c h := by
    simpa only [RingHom.id_apply, smul_eq_mul] using topInverse_smul s c h

@[simp]
theorem potentialLinearMap_apply (s a : ComplexPlane₂) :
    potentialLinearMap s a = potential s a := rfl

@[simp]
theorem topInverseLinearMap_apply (s : ComplexPlane₂) (h : ℂ) :
    topInverseLinearMap s h = topInverse s h := rfl

/-- Finite-dimensional continuity of the original degree-one formula. -/
def potentialCLM (s : ComplexPlane₂) : ComplexPlane₂ →L[ℂ] ℂ :=
  (potentialLinearMap s).toContinuousLinearMap

/-- Finite-dimensional continuity of the original degree-two formula. -/
def topInverseCLM (s : ComplexPlane₂) : ℂ →L[ℂ] ComplexPlane₂ :=
  (topInverseLinearMap s).toContinuousLinearMap

@[simp]
theorem potentialCLM_apply (s a : ComplexPlane₂) :
    potentialCLM s a = potential s a := rfl

@[simp]
theorem topInverseCLM_apply (s : ComplexPlane₂) (h : ℂ) :
    topInverseCLM s h = topInverse s h := rfl

/-- The primitive operator has a uniform order-minus-one operator norm bound. -/
theorem potentialCLM_norm_le (s : ComplexPlane₂) :
    ‖potentialCLM s‖ ≤ 2 / ‖s‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (div_nonneg (by norm_num) (norm_nonneg s))
  intro a
  calc
    ‖potentialCLM s a‖ = ‖potential s a‖ := rfl
    _ ≤ 2 * ‖a‖ / ‖s‖ := potential_norm_le_two s a
    _ = (2 / ‖s‖) * ‖a‖ := by ring

/-- The top-degree operator has an order-minus-one operator norm bound. -/
theorem topInverseCLM_norm_le (s : ComplexPlane₂) :
    ‖topInverseCLM s‖ ≤ 1 / ‖s‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (div_nonneg zero_le_one (norm_nonneg s))
  intro h
  calc
    ‖topInverseCLM s h‖ = ‖topInverse s h‖ := rfl
    _ ≤ ‖h‖ / ‖s‖ := topInverse_norm_le s h
    _ = (1 / ‖s‖) * ‖h‖ := by ring

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.FourierHermitian
