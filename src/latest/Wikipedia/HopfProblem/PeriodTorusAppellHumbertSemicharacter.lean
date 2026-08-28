import Wikipedia.HopfProblem.PeriodTorusTypeOneOneIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# The canonical semicharacter on the genuine period lattice

The ordered six coefficients determine an integral quadratic refinement
of the alternating coordinate form modulo two. Its exponential gives a
unit-norm semicharacter on the actual period lattice. Both signs of the
integral phase agree, which is useful in the factor-of-automorphy cocycle.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusAppellHumbert

open PeriodTorusTypeOneOne

/-- The quadratic refinement in the source order `01, 02, 03, 12, 13, 23`. -/
def coordinateQuadratic (E : Fin 6 → ℤ) (c : Lattice) : ℤ :=
  E 0 * c 0 * c 1 + E 1 * c 0 * c 2 + E 2 * c 0 * c 3 +
  E 3 * c 1 * c 2 + E 4 * c 1 * c 3 + E 5 * c 2 * c 3

@[simp] theorem coordinateQuadratic_zero (E : Fin 6 → ℤ) :
    coordinateQuadratic E 0 = 0 := by simp [coordinateQuadratic]

@[simp] theorem coordinateQuadratic_neg (E : Fin 6 → ℤ) (c : Lattice) :
    coordinateQuadratic E (-c) = coordinateQuadratic E c := by
  simp [coordinateQuadratic]

/-- The cross term is the alternating pairing modulo an even integer. -/
theorem coordinateQuadratic_add_mod_two (E : Fin 6 → ℤ) (c d : Lattice) :
    ∃ n : ℤ, coordinateQuadratic E (c + d) =
      coordinateQuadratic E c + coordinateQuadratic E d + coordinateForm E c d + 2 * n := by
  refine ⟨E 0 * c 1 * d 0 + E 1 * c 2 * d 0 + E 2 * c 3 * d 0 +
    E 3 * c 2 * d 1 + E 4 * c 3 * d 1 + E 5 * c 3 * d 2, ?_⟩
  simp only [coordinateQuadratic, coordinateForm_apply, coordinateValue, Pi.add_apply]
  ring

/-- Exponentiating an integral multiple of `π I` is independent of its sign. -/
theorem exp_pi_mul_I_int_neg (n : ℤ) :
    Complex.exp (-((Real.pi : ℂ) * Complex.I * (n : ℂ))) =
      Complex.exp ((Real.pi : ℂ) * Complex.I * (n : ℂ)) := by
  calc
    Complex.exp (-((Real.pi : ℂ) * Complex.I * (n : ℂ))) =
        Complex.exp ((Real.pi : ℂ) * Complex.I * (n : ℂ) +
          ((-n : ℤ) : ℂ) * (2 * Real.pi * Complex.I)) := by
      congr 1
      push_cast
      ring
    _ = Complex.exp ((Real.pi : ℂ) * Complex.I * (n : ℂ)) := by
      rw [Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- The marked-lattice semicharacter, as an actual complex scalar. -/
def coordinateSemicharacter (E : Fin 6 → ℤ) (c : Lattice) : ℂ :=
  Complex.exp ((Real.pi : ℂ) * Complex.I * (coordinateQuadratic E c : ℂ))

@[simp] theorem coordinateSemicharacter_zero (E : Fin 6 → ℤ) :
    coordinateSemicharacter E 0 = 1 := by
  simp [coordinateSemicharacter]

@[simp] theorem coordinateSemicharacter_norm (E : Fin 6 → ℤ) (c : Lattice) :
    ‖coordinateSemicharacter E c‖ = 1 := by
  simp [coordinateSemicharacter, Complex.norm_exp, Complex.mul_re, Complex.mul_im]

theorem coordinateSemicharacter_ne_zero (E : Fin 6 → ℤ) (c : Lattice) :
    coordinateSemicharacter E c ≠ 0 := Complex.exp_ne_zero _

@[simp] theorem coordinateSemicharacter_neg (E : Fin 6 → ℤ) (c : Lattice) :
    coordinateSemicharacter E (-c) = coordinateSemicharacter E c := by
  simp [coordinateSemicharacter]

/-- The genuine semicharacter law for the integral alternating coordinate form. -/
theorem coordinateSemicharacter_add (E : Fin 6 → ℤ) (c d : Lattice) :
    coordinateSemicharacter E (c + d) =
      coordinateSemicharacter E c * coordinateSemicharacter E d *
        Complex.exp ((Real.pi : ℂ) * Complex.I * (coordinateForm E c d : ℂ)) := by
  obtain ⟨n, hn⟩ := coordinateQuadratic_add_mod_two E c d
  have hexp : (Real.pi : ℂ) * Complex.I * (coordinateQuadratic E (c + d) : ℂ) =
      (Real.pi : ℂ) * Complex.I * (coordinateQuadratic E c : ℂ) +
      (Real.pi : ℂ) * Complex.I * (coordinateQuadratic E d : ℂ) +
      (Real.pi : ℂ) * Complex.I * (coordinateForm E c d : ℂ) +
      (n : ℂ) * (2 * Real.pi * Complex.I) := by
    rw [hn]
    push_cast
    ring
  simp only [coordinateSemicharacter, hexp, Complex.exp_add,
    Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- The same semicharacter law with the negative phase. -/
theorem coordinateSemicharacter_add_neg (E : Fin 6 → ℤ) (c d : Lattice) :
    coordinateSemicharacter E (c + d) =
      coordinateSemicharacter E c * coordinateSemicharacter E d *
        Complex.exp (-((Real.pi : ℂ) * Complex.I * (coordinateForm E c d : ℂ))) := by
  rw [exp_pi_mul_I_int_neg]
  exact coordinateSemicharacter_add E c d

theorem coordinateQuadratic_add_coefficients (E F : Fin 6 → ℤ) (c : Lattice) :
    coordinateQuadratic (E + F) c = coordinateQuadratic E c + coordinateQuadratic F c := by
  simp only [coordinateQuadratic, Pi.add_apply]
  ring

theorem coordinateQuadratic_zsmul (n : ℤ) (E : Fin 6 → ℤ) (c : Lattice) :
    coordinateQuadratic (n • E) c = n * coordinateQuadratic E c := by
  simp only [coordinateQuadratic, Pi.smul_apply, smul_eq_mul]
  ring

@[simp] theorem coordinateSemicharacter_zero_coefficients (c : Lattice) :
    coordinateSemicharacter 0 c = 1 := by
  simp [coordinateSemicharacter, coordinateQuadratic]

/-- Addition of integral forms multiplies their canonical semicharacters. -/
theorem coordinateSemicharacter_add_coefficients (E F : Fin 6 → ℤ) (c : Lattice) :
    coordinateSemicharacter (E + F) c =
      coordinateSemicharacter E c * coordinateSemicharacter F c := by
  simp only [coordinateSemicharacter, coordinateQuadratic_add_coefficients,
    Int.cast_add, mul_add, Complex.exp_add]

/-- Integer scaling of a form takes the corresponding integer power. -/
theorem coordinateSemicharacter_zsmul (n : ℤ) (E : Fin 6 → ℤ) (c : Lattice) :
    coordinateSemicharacter (n • E) c = coordinateSemicharacter E c ^ n := by
  simp only [coordinateSemicharacter, coordinateQuadratic_zsmul, Int.cast_mul]
  rw [← Complex.exp_int_mul]
  congr 1
  ring

/-- The actual period lattice is marked by its actual integral period coordinates. -/
def latticeSemicharacter (p : PeriodDomain) (E : Fin 6 → ℤ) (l : p.lattice) : ℂ :=
  coordinateSemicharacter E (p.latticeEquiv l)

@[simp] theorem latticeSemicharacter_zero (p : PeriodDomain) (E : Fin 6 → ℤ) :
    latticeSemicharacter p E 0 = 1 := by
  simp [latticeSemicharacter]

@[simp] theorem latticeSemicharacter_norm (p : PeriodDomain) (E : Fin 6 → ℤ)
    (l : p.lattice) : ‖latticeSemicharacter p E l‖ = 1 :=
  coordinateSemicharacter_norm E _

theorem latticeSemicharacter_ne_zero (p : PeriodDomain) (E : Fin 6 → ℤ)
    (l : p.lattice) : latticeSemicharacter p E l ≠ 0 :=
  coordinateSemicharacter_ne_zero E _

@[simp] theorem latticeSemicharacter_neg (p : PeriodDomain) (E : Fin 6 → ℤ)
    (l : p.lattice) : latticeSemicharacter p E (-l) = latticeSemicharacter p E l := by
  simp [latticeSemicharacter]

/-- The positive-phase law on the genuine period lattice. -/
theorem latticeSemicharacter_add (p : PeriodDomain) (E : Fin 6 → ℤ)
    (l m : p.lattice) :
    latticeSemicharacter p E (l + m) =
      latticeSemicharacter p E l * latticeSemicharacter p E m *
        Complex.exp ((Real.pi : ℂ) * Complex.I *
          (coordinateForm E (p.latticeEquiv l) (p.latticeEquiv m) : ℂ)) := by
  simpa only [latticeSemicharacter, map_add] using
    coordinateSemicharacter_add E (p.latticeEquiv l) (p.latticeEquiv m)

/-- The negative-phase law on the genuine period lattice. -/
theorem latticeSemicharacter_add_neg (p : PeriodDomain) (E : Fin 6 → ℤ)
    (l m : p.lattice) :
    latticeSemicharacter p E (l + m) =
      latticeSemicharacter p E l * latticeSemicharacter p E m *
        Complex.exp (-((Real.pi : ℂ) * Complex.I *
          (coordinateForm E (p.latticeEquiv l) (p.latticeEquiv m) : ℂ))) := by
  simpa only [latticeSemicharacter, map_add] using
    coordinateSemicharacter_add_neg E (p.latticeEquiv l) (p.latticeEquiv m)

@[simp] theorem latticeSemicharacter_zero_coefficients (p : PeriodDomain) (l : p.lattice) :
    latticeSemicharacter p 0 l = 1 := coordinateSemicharacter_zero_coefficients _

theorem latticeSemicharacter_add_coefficients (p : PeriodDomain) (E F : Fin 6 → ℤ)
    (l : p.lattice) :
    latticeSemicharacter p (E + F) l =
      latticeSemicharacter p E l * latticeSemicharacter p F l :=
  coordinateSemicharacter_add_coefficients E F _

theorem latticeSemicharacter_zsmul (p : PeriodDomain) (n : ℤ) (E : Fin 6 → ℤ)
    (l : p.lattice) :
    latticeSemicharacter p (n • E) l = latticeSemicharacter p E l ^ n :=
  coordinateSemicharacter_zsmul n E _

end Wikipedia.HopfProblem.PeriodTorusAppellHumbert
