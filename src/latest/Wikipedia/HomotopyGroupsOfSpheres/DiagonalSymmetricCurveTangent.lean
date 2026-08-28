import Wikipedia.HomotopyGroupsOfSpheres.SymmetricIdentityCurveTangent

/-!
# Normalizing actual tangent curves at a diagonal symmetric unitary matrix

A diagonal unitary square root moves the base matrix to identity by
congruence. Imaginary parts then give the real symmetric trace-zero tangent
model, with an exact reconstruction formula for the original derivative.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices

open ComplexCrossProductUnitary ImaginarySymmetricMatrices RealSymmetricMixing

def phaseDiagonal (q : Fin 3 → unitary ℂ) : unitary (Matrix (Fin 3) (Fin 3) ℂ) :=
  ⟨Matrix.diagonal (fun r ↦ (q r).val), by
    constructor
    · change (Matrix.diagonal (fun r ↦ (q r).val)).conjTranspose *
        Matrix.diagonal (fun r ↦ (q r).val) = 1
      rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
      ext r s
      by_cases h : r = s
      · subst s
        simpa using (q r).property.1
      · simp [h]
    · change Matrix.diagonal (fun r ↦ (q r).val) *
        (Matrix.diagonal (fun r ↦ (q r).val)).conjTranspose = 1
      rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
      ext r s
      by_cases h : r = s
      · subst s
        simpa using (q r).property.2
      · simp [h]⟩

def normalizeDiagonal (q : Fin 3 → unitary ℂ) (B : Space (Fin 3)) : Space (Fin 3) :=
  congruence (phaseDiagonal (fun r ↦ star (q r))) B

theorem normalizeDiagonal_entry (q : Fin 3 → unitary ℂ) (B : Space (Fin 3)) (r s : Fin 3) :
    (normalizeDiagonal q B).val.val r s = star (q r).val * B.val.val r s * star (q s).val := by
  change (Matrix.diagonal (fun r ↦ star (q r).val) * B.val.val *
    (Matrix.diagonal (fun r ↦ star (q r).val)).transpose) r s = _
  rw [Matrix.diagonal_transpose, Matrix.mul_diagonal, Matrix.diagonal_mul]

def normalizeVariation (q : Fin 3 → unitary ℂ) :
    Matrix (Fin 3) (Fin 3) ℂ →ₗ[ℝ] Matrix (Fin 3) (Fin 3) ℂ where
  toFun D r s := star (q r).val * D r s * star (q s).val
  map_add' D E := by
    ext r s
    change star (q r).val * (D r s + E r s) * star (q s).val =
      star (q r).val * D r s * star (q s).val + star (q r).val * E r s * star (q s).val
    ring
  map_smul' c D := by
    ext r s
    change star (q r).val * (c • D r s) * star (q s).val =
      c • (star (q r).val * D r s * star (q s).val)
    rw [mul_smul_comm, smul_mul_assoc]

def diagonalTangentCoordinates (q : Fin 3 → unitary ℂ) :
    Matrix (Fin 3) (Fin 3) ℂ →ₗ[ℝ] Matrix (Fin 3) (Fin 3) ℝ :=
  LocalLogarithm.imaginaryPart.comp (normalizeVariation q)

theorem normalizeDiagonal_at_square (q : Fin 3 → unitary ℂ) (B : Space (Fin 3))
    (hB : B.val.val = Matrix.diagonal (fun r ↦ (q r).val ^ 2)) :
    (normalizeDiagonal q B).val.val = 1 := by
  ext r s
  rw [normalizeDiagonal_entry, hB]
  by_cases h : r = s
  · subst s
    simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
    calc
      star (q r).val * (q r).val ^ 2 * star (q r).val =
          (star (q r).val * (q r).val) * ((q r).val * star (q r).val) := by ring
      _ = 1 := by rw [(q r).property.1, (q r).property.2, one_mul]
  · simp [h]

theorem hasDerivAt_normalizeDiagonal_entry (q : Fin 3 → unitary ℂ)
    (B : ℝ → Space (Fin 3)) (D : Matrix (Fin 3) (Fin 3) ℂ) (x : ℝ)
    (hB : ∀ r s, HasDerivAt (fun t ↦ (B t).val.val r s) (D r s) x) (r s : Fin 3) :
    HasDerivAt (fun t ↦ (normalizeDiagonal q (B t)).val.val r s)
      (normalizeVariation q D r s) x := by
  simp only [normalizeDiagonal_entry]
  exact ((hB r s).const_mul (star (q r).val)).mul_const (star (q s).val)

theorem diagonal_curve_coordinates_mem (q : Fin 3 → unitary ℂ)
    (B : ℝ → Space (Fin 3)) (D : Matrix (Fin 3) (Fin 3) ℂ) (x : ℝ)
    (hB : ∀ r s, HasDerivAt (fun t ↦ (B t).val.val r s) (D r s) x)
    (hBx : (B x).val.val = Matrix.diagonal (fun r ↦ (q r).val ^ 2))
    (c : ℂ) (hdet : ∀ t, (B t).val.val.det = c) :
    diagonalTangentCoordinates q D ∈ symmetricTraceZero (Fin 3) := by
  apply identity_curve_imaginaryPart_mem (fun t ↦ normalizeDiagonal q (B t))
    (normalizeVariation q D) x (hasDerivAt_normalizeDiagonal_entry q B D x hB)
    (normalizeDiagonal_at_square q (B x) hBx)
    ((phaseDiagonal (fun r ↦ star (q r))).val.det ^ 2 * c)
  intro t
  rw [normalizeDiagonal, congruence_det, hdet]

theorem diagonal_curve_reconstruction (q : Fin 3 → unitary ℂ)
    (B : ℝ → Space (Fin 3)) (D : Matrix (Fin 3) (Fin 3) ℂ) (x : ℝ)
    (hB : ∀ r s, HasDerivAt (fun t ↦ (B t).val.val r s) (D r s) x)
    (hBx : (B x).val.val = Matrix.diagonal (fun r ↦ (q r).val ^ 2)) (r s : Fin 3) :
    D r s = (q r).val * (Complex.I * ((diagonalTangentCoordinates q D r s : ℝ) : ℂ)) *
      (q s).val := by
  have he := identity_curve_imaginary_reconstruction (fun t ↦ normalizeDiagonal q (B t))
    (normalizeVariation q D) x (hasDerivAt_normalizeDiagonal_entry q B D x hB)
    (normalizeDiagonal_at_square q (B x) hBx)
  have hc := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℂ ↦ (q r).val * M r s * (q s).val) he
  change (q r).val * (star (q r).val * D r s * star (q s).val) * (q s).val = _ at hc
  have hleft : (q r).val * (star (q r).val * D r s * star (q s).val) * (q s).val = D r s := by
    calc
      _ = ((q r).val * star (q r).val) * D r s * (star (q s).val * (q s).val) := by ring
      _ = _ := by rw [(q r).property.2, (q s).property.1, one_mul, mul_one]
  rw [hleft] at hc
  exact hc

theorem diagonal_curve_coordinates_kernel (q : Fin 3 → unitary ℂ)
    (B : ℝ → Space (Fin 3)) (D : Matrix (Fin 3) (Fin 3) ℂ) (x : ℝ)
    (hB : ∀ r s, HasDerivAt (fun t ↦ (B t).val.val r s) (D r s) x)
    (hBx : (B x).val.val = Matrix.diagonal (fun r ↦ (q r).val ^ 2))
    (hD : diagonalTangentCoordinates q D = 0) : D = 0 := by
  ext r s
  rw [diagonal_curve_reconstruction q B D x hB hBx r s, hD]
  simp

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices
