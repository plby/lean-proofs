import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationFourierSymbol

/-!
# Hermitian inverses of the two-component Dolbeault symbol

The denominator is the sum of the two squared complex norms. These explicit
formulas do not select a coordinate and therefore remain suitable for varying
periods. All maps use the original `ComplexPlane₂` and are totalized at zero.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.FourierHermitian

open Complex
open scoped ComplexConjugate

/-- The positive Hermitian energy of a nonzero two-component symbol. -/
def energy (s : ComplexPlane₂) : ℝ := normSq (s 0) + normSq (s 1)

theorem energy_nonneg (s : ComplexPlane₂) : 0 ≤ energy s :=
  add_nonneg (normSq_nonneg _) (normSq_nonneg _)

@[simp]
theorem energy_zero : energy 0 = 0 := by simp [energy]

@[simp]
theorem energy_eq_zero (s : ComplexPlane₂) : energy s = 0 ↔ s = 0 := by
  constructor
  · intro h
    have h₀ : normSq (s 0) = 0 := by
      have := normSq_nonneg (s 1)
      have := normSq_nonneg (s 0)
      change normSq (s 0) + normSq (s 1) = 0 at h
      linarith
    have h₁ : normSq (s 1) = 0 := by
      have := normSq_nonneg (s 1)
      have := normSq_nonneg (s 0)
      change normSq (s 0) + normSq (s 1) = 0 at h
      linarith
    ext i
    fin_cases i
    · exact normSq_eq_zero.mp h₀
    · exact normSq_eq_zero.mp h₁
  · rintro rfl
    exact energy_zero

theorem energy_pos_iff (s : ComplexPlane₂) : 0 < energy s ↔ s ≠ 0 := by
  constructor
  · intro h hs
    simp [hs] at h
  · intro hs
    exact lt_of_le_of_ne (energy_nonneg s)
      (fun h => hs ((energy_eq_zero s).mp h.symm))

theorem energy_coe_ne_zero {s : ComplexPlane₂} (hs : s ≠ 0) :
    (energy s : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (ne_of_gt ((energy_pos_iff s).mpr hs))

/-- The same energy is the Hermitian quadratic polynomial after coercion. -/
theorem energy_coe (s : ComplexPlane₂) :
    (energy s : ℂ) = s 0 * conj (s 0) + s 1 * conj (s 1) := by
  simp only [energy, Complex.ofReal_add, Complex.mul_conj]

/-- A scalar primitive for a compatible two-component symbol coefficient. -/
def potential (s a : ComplexPlane₂) : ℂ :=
  (conj (s 0) * a 0 + conj (s 1) * a 1) / (energy s : ℂ)

/-- A right inverse for the alternating top-degree symbol. -/
def topInverse (s : ComplexPlane₂) (h : ℂ) : ComplexPlane₂ :=
  ![-conj (s 1) * h / (energy s : ℂ), conj (s 0) * h / (energy s : ℂ)]

@[simp]
theorem potential_zero_symbol (a : ComplexPlane₂) : potential 0 a = 0 := by
  simp [potential]

@[simp]
theorem potential_zero (s : ComplexPlane₂) : potential s 0 = 0 := by
  simp [potential]

@[simp]
theorem topInverse_zero_symbol (h : ℂ) : topInverse 0 h = 0 := by
  ext i
  fin_cases i <;> simp [topInverse]

@[simp]
theorem topInverse_zero (s : ComplexPlane₂) : topInverse s 0 = 0 := by
  ext i
  fin_cases i <;> simp [topInverse]

/-- Compatibility makes the Hermitian primitive solve both component equations. -/
theorem potential_mul (s a : ComplexPlane₂) (hs : s ≠ 0)
    (hc : s 0 * a 1 = s 1 * a 0) (i : Fin 2) :
    s i * potential s a = a i := by
  rw [potential, ← mul_div_assoc, div_eq_iff (energy_coe_ne_zero hs), energy_coe]
  fin_cases i
  · calc
      s 0 * (conj (s 0) * a 0 + conj (s 1) * a 1) =
          a 0 * (s 0 * conj (s 0)) + conj (s 1) * (s 0 * a 1) := by ring
      _ = a 0 * (s 0 * conj (s 0)) + conj (s 1) * (s 1 * a 0) := by rw [hc]
      _ = a 0 * (s 0 * conj (s 0) + s 1 * conj (s 1)) := by ring
  · calc
      s 1 * (conj (s 0) * a 0 + conj (s 1) * a 1) =
          conj (s 0) * (s 1 * a 0) + a 1 * (s 1 * conj (s 1)) := by ring
      _ = conj (s 0) * (s 0 * a 1) + a 1 * (s 1 * conj (s 1)) := by rw [← hc]
      _ = a 1 * (s 0 * conj (s 0) + s 1 * conj (s 1)) := by ring

/-- Every top-degree coefficient is solved at every nonzero symbol. -/
theorem topInverse_equation (s : ComplexPlane₂) (h : ℂ) (hs : s ≠ 0) :
    s 0 * topInverse s h 1 - s 1 * topInverse s h 0 = h := by
  change s 0 * (conj (s 0) * h / (energy s : ℂ)) -
    s 1 * (-conj (s 1) * h / (energy s : ℂ)) = h
  rw [← mul_div_assoc, ← mul_div_assoc, ← sub_div,
    div_eq_iff (energy_coe_ne_zero hs), energy_coe]
  ring

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.FourierHermitian
