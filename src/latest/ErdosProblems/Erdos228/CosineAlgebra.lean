import Mathlib

/-!
# The four-derivative algebra in the Rudin--Shapiro cosine construction

For fixed complex numbers `A` and `B`, the rapidly oscillating part of the
`k`-th derivative of

`H(x) = exp (I*x) * alpha(x) + exp (2*I*x) * beta(x)`

is `I^k A + (2*I)^k B`.  This file proves the finite-dimensional fact used in
the construction: if `‖A‖^2 + ‖B‖^2 = 1` and the true first four derivatives
are within `1/8` of these leading terms, then one of their real parts has
absolute value at least `1/4`.
-/

namespace Erdos228.CosineAlgebra

/-- The leading two-frequency term in the `k`-th derivative. -/
def leadingDerivative (k : ℕ) (A B : ℂ) : ℂ :=
  Complex.I ^ k * A + ((2 : ℂ) * Complex.I) ^ k * B

/-- The real part of the leading two-frequency derivative. -/
def leadingReal (k : ℕ) (A B : ℂ) : ℝ :=
  (leadingDerivative k A B).re

/-! ## The explicit four rows and their inverse -/

@[simp] theorem leadingReal_zero (A B : ℂ) :
    leadingReal 0 A B = A.re + B.re := by
  simp [leadingReal, leadingDerivative]

@[simp] theorem leadingReal_one (A B : ℂ) :
    leadingReal 1 A B = -A.im - 2 * B.im := by
  simp [leadingReal, leadingDerivative]
  ring

@[simp] theorem leadingReal_two (A B : ℂ) :
    leadingReal 2 A B = -A.re - 4 * B.re := by
  norm_num [leadingReal, leadingDerivative, pow_succ]
  ring

@[simp] theorem leadingReal_three (A B : ℂ) :
    leadingReal 3 A B = A.im + 8 * B.im := by
  norm_num [leadingReal, leadingDerivative, pow_succ]

/-- Inversion of the real-coordinate half of the four-by-four system. -/
theorem leadingReal_inversion_re (A B : ℂ) :
    A.re = (4 * leadingReal 0 A B + leadingReal 2 A B) / 3 ∧
    B.re = -(leadingReal 0 A B + leadingReal 2 A B) / 3 := by
  simp only [leadingReal_zero, leadingReal_two]
  constructor <;> ring

/-- Inversion of the imaginary-coordinate half of the four-by-four system. -/
theorem leadingReal_inversion_im (A B : ℂ) :
    A.im = -(4 * leadingReal 1 A B + leadingReal 3 A B) / 3 ∧
    B.im = (leadingReal 1 A B + leadingReal 3 A B) / 6 := by
  simp only [leadingReal_one, leadingReal_three]
  constructor <;> ring

/-! ## Quantitative inversion -/

/-- If all four rows of the system are bounded by `epsilon`, then the two
complex coordinates have energy at most `(55/9) * epsilon^2`. -/
theorem energy_le_of_leadingReal_le {A B : ℂ} {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon)
    (h0 : |leadingReal 0 A B| ≤ epsilon)
    (h1 : |leadingReal 1 A B| ≤ epsilon)
    (h2 : |leadingReal 2 A B| ≤ epsilon)
    (h3 : |leadingReal 3 A B| ≤ epsilon) :
    ‖A‖ ^ 2 + ‖B‖ ^ 2 ≤ (55 / 9 : ℝ) * epsilon ^ 2 := by
  have h0' := abs_le.mp h0
  have h1' := abs_le.mp h1
  have h2' := abs_le.mp h2
  have h3' := abs_le.mp h3
  have hAre : |A.re| ≤ (5 / 3 : ℝ) * epsilon := by
    rw [abs_le]
    simp only [leadingReal_zero, leadingReal_two] at h0' h2'
    constructor <;> nlinarith
  have hAim : |A.im| ≤ (5 / 3 : ℝ) * epsilon := by
    rw [abs_le]
    simp only [leadingReal_one, leadingReal_three] at h1' h3'
    constructor <;> nlinarith
  have hBre : |B.re| ≤ (2 / 3 : ℝ) * epsilon := by
    rw [abs_le]
    simp only [leadingReal_zero, leadingReal_two] at h0' h2'
    constructor <;> nlinarith
  have hBim : |B.im| ≤ (1 / 3 : ℝ) * epsilon := by
    rw [abs_le]
    simp only [leadingReal_one, leadingReal_three] at h1' h3'
    constructor <;> nlinarith
  have hAreSq : A.re ^ 2 ≤ ((5 / 3 : ℝ) * epsilon) ^ 2 := by
    rw [← sq_abs]
    exact (sq_le_sq₀ (abs_nonneg A.re) (mul_nonneg (by norm_num) hepsilon)).2 hAre
  have hAimSq : A.im ^ 2 ≤ ((5 / 3 : ℝ) * epsilon) ^ 2 := by
    rw [← sq_abs]
    exact (sq_le_sq₀ (abs_nonneg A.im) (mul_nonneg (by norm_num) hepsilon)).2 hAim
  have hBreSq : B.re ^ 2 ≤ ((2 / 3 : ℝ) * epsilon) ^ 2 := by
    rw [← sq_abs]
    exact (sq_le_sq₀ (abs_nonneg B.re) (mul_nonneg (by norm_num) hepsilon)).2 hBre
  have hBimSq : B.im ^ 2 ≤ ((1 / 3 : ℝ) * epsilon) ^ 2 := by
    rw [← sq_abs]
    exact (sq_le_sq₀ (abs_nonneg B.im) (mul_nonneg (by norm_num) hepsilon)).2 hBim
  rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
  nlinarith

/-- The numerical instance used in the paper: four leading rows bounded by
`3/8` force energy at most `55/64`. -/
theorem energy_le_fiftyFive_div_sixtyFour {A B : ℂ}
    (h : ∀ k : Fin 4, |leadingReal k A B| ≤ 3 / 8) :
    ‖A‖ ^ 2 + ‖B‖ ^ 2 ≤ (55 / 64 : ℝ) := by
  have hbound := energy_le_of_leadingReal_le (A := A) (B := B)
    (epsilon := (3 / 8 : ℝ)) (by norm_num)
    (by simpa using h ⟨0, by omega⟩)
    (by simpa using h ⟨1, by omega⟩)
    (by simpa using h ⟨2, by omega⟩)
    (by simpa using h ⟨3, by omega⟩)
  norm_num at hbound ⊢
  exact hbound

/-! ## Perturbing the leading rows by the slow derivative terms -/

/-- Real version of the no-simultaneous-small-derivatives assertion. -/
theorem exists_large_of_real_error {A B : ℂ} (D : Fin 4 → ℝ)
    (henergy : ‖A‖ ^ 2 + ‖B‖ ^ 2 = 1)
    (herror : ∀ k : Fin 4, |D k - leadingReal k A B| ≤ 1 / 8) :
    ∃ k : Fin 4, 1 / 4 ≤ |D k| := by
  by_contra hlarge
  push_neg at hlarge
  have hleading : ∀ k : Fin 4, |leadingReal k A B| ≤ 3 / 8 := by
    intro k
    calc
      |leadingReal k A B| = |D k - (D k - leadingReal k A B)| := by ring_nf
      _ ≤ |D k| + |D k - leadingReal k A B| := abs_sub _ _
      _ ≤ 3 / 8 := by
        have hk := herror k
        have hk' := hlarge k
        linarith
  have hsmall := energy_le_fiftyFive_div_sixtyFour hleading
  rw [henergy] at hsmall
  norm_num at hsmall

/-- Complex derivative-error version.  Bounding the complex error bounds its
real coordinate, so the same `1/4` conclusion follows. -/
theorem exists_large_re_of_complex_error {A B : ℂ} (D : Fin 4 → ℂ)
    (henergy : ‖A‖ ^ 2 + ‖B‖ ^ 2 = 1)
    (herror : ∀ k : Fin 4, ‖D k - leadingDerivative k A B‖ ≤ 1 / 8) :
    ∃ k : Fin 4, 1 / 4 ≤ |(D k).re| := by
  apply exists_large_of_real_error (fun k ↦ (D k).re) henergy
  intro k
  have hre :
      |(D k - leadingDerivative k A B).re| ≤
        ‖D k - leadingDerivative k A B‖ :=
    Complex.abs_re_le_norm _
  have hid :
      (D k - leadingDerivative k A B).re =
        (D k).re - leadingReal k A B := by
    rfl
  rw [hid] at hre
  exact hre.trans (herror k)

/-- Multiplication by unit phases preserves the normalized Rudin--Shapiro
energy of `alpha` and `beta`. -/
theorem phase_energy {u v alpha beta : ℂ}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (henergy : ‖alpha‖ ^ 2 + ‖beta‖ ^ 2 = 1) :
    ‖u * alpha‖ ^ 2 + ‖v * beta‖ ^ 2 = 1 := by
  rw [norm_mul, norm_mul, hu, hv, one_mul, one_mul]
  exact henergy

/-- The normalized statement in the form obtained by setting
`A = exp(I*x) * alpha` and `B = exp(2*I*x) * beta`. -/
theorem exists_large_re_of_normalized_modes {u v alpha beta : ℂ}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (henergy : ‖alpha‖ ^ 2 + ‖beta‖ ^ 2 = 1)
    (D : Fin 4 → ℂ)
    (herror : ∀ k : Fin 4,
      ‖D k - leadingDerivative k (u * alpha) (v * beta)‖ ≤ 1 / 8) :
    ∃ k : Fin 4, 1 / 4 ≤ |(D k).re| :=
  exists_large_re_of_complex_error D (phase_energy hu hv henergy) herror

/-! ## Scaling back to the unnormalized cosine sum -/

/-- If `D k` is the normalized derivative and the unnormalized derivative is
`scale * frequency^k * D k`, the `1/4` lower bound scales exactly as expected. -/
theorem scaled_derivative_lower_bound {scale frequency value : ℝ} {k : ℕ}
    (hscale : 0 ≤ scale) (hfrequency : 0 ≤ frequency)
    (hvalue : 1 / 4 ≤ |value|) :
    scale * frequency ^ k / 4 ≤ |scale * frequency ^ k * value| := by
  rw [abs_mul, abs_of_nonneg (mul_nonneg hscale (pow_nonneg hfrequency k))]
  nlinarith [mul_nonneg (mul_nonneg hscale (pow_nonneg hfrequency k))
    (sub_nonneg.mpr hvalue)]

/-- Consequently one of four scaled derivatives inherits the normalized
`1/4` lower bound. -/
theorem exists_large_scaled_derivative {scale frequency : ℝ}
    (hscale : 0 ≤ scale) (hfrequency : 0 ≤ frequency)
    (D : Fin 4 → ℝ) (hD : ∃ k : Fin 4, 1 / 4 ≤ |D k|) :
    ∃ k : Fin 4,
      scale * frequency ^ (k : ℕ) / 4 ≤
        |scale * frequency ^ (k : ℕ) * D k| := by
  obtain ⟨k, hk⟩ := hD
  exact ⟨k, scaled_derivative_lower_bound hscale hfrequency hk⟩

end Erdos228.CosineAlgebra
