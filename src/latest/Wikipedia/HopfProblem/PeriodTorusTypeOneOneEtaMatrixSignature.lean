import Wikipedia.HopfProblem.PeriodTorusTypeOneOneEtaMatrix

/-!
# An explicit positive/negative basis for the Hermitian form of η

Completion of the square is implemented by an actual complex-linear
equivalence.  In the resulting basis the form is diagonal with entries
`1 / Im τ > 0` and `6 * Im τ / etaDenom < 0`.  Thus the signature assertion
uses a full complex basis, not just the sign of a determinant.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.PeriodTorusTypeOneOne

/-- The complex-linear shear which diagonalizes the actual Hermitian form. -/
def etaDiagonalizingEquiv (p : PeriodDomain) : ComplexPlane₂ ≃ₗ[ℂ] ComplexPlane₂ where
  toFun x := ![x 0, (p.val.μ.im / p.val.τ.im : ℝ) * x 0 + x 1]
  invFun x := ![x 0, x 1 - (p.val.μ.im / p.val.τ.im : ℝ) * x 0]
  left_inv x := by ext i; fin_cases i <;> simp
  right_inv x := by ext i; fin_cases i <;> simp
  map_add' x y := by
    ext i
    fin_cases i
    · simp
    · simp [mul_add]
      ring
  map_smul' c x := by
    ext i
    fin_cases i
    · simp
    · simp [mul_add]
      ring

theorem etaDiagonalizingEquiv_apply (p : PeriodDomain) (x : ComplexPlane₂) :
    etaDiagonalizingEquiv p x =
      ![x 0, (p.val.μ.im / p.val.τ.im : ℝ) * x 0 + x 1] := rfl

/-- The full sesquilinear congruence, with one positive and one negative entry. -/
theorem etaMatrixForm_diagonalized (p : PeriodDomain) (x y : ComplexPlane₂) :
    etaMatrixForm p (etaDiagonalizingEquiv p x) (etaDiagonalizingEquiv p y) =
      ((1 / p.val.τ.im : ℝ) : ℂ) * x 0 * star (y 0) +
        ((6 * p.val.τ.im / etaDenom p : ℝ) : ℂ) * x 1 * star (y 1) := by
  have hT : (p.val.τ.im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (etaTau_ne_zero p)
  have hd : (etaDenom p : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (etaDenom_ne_zero p)
  simp [etaMatrixForm, etaHermitianMatrix, etaDiagonalizingEquiv, Fin.sum_univ_two]
  field_simp [hT, hd]
  simp only [etaDenom, Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_pow,
    Complex.ofReal_ofNat]
  ring

/-- The explicit full complex basis supplied by completion of the square. -/
def etaSignatureBasis (p : PeriodDomain) : Module.Basis (Fin 2) ℂ ComplexPlane₂ :=
  (Pi.basisFun ℂ (Fin 2)).map (etaDiagonalizingEquiv p)

theorem etaSignatureBasis_zero (p : PeriodDomain) :
    etaSignatureBasis p 0 = ![1, ((p.val.μ.im / p.val.τ.im : ℝ) : ℂ)] := by
  ext i
  fin_cases i <;> simp [etaSignatureBasis, etaDiagonalizingEquiv, Pi.basisFun_apply]

theorem etaSignatureBasis_one (p : PeriodDomain) :
    etaSignatureBasis p 1 = ![0, 1] := by
  ext i
  fin_cases i <;> simp [etaSignatureBasis, etaDiagonalizingEquiv, Pi.basisFun_apply]

theorem etaSignatureBasis_pairing (p : PeriodDomain) (i j : Fin 2) :
    etaMatrixForm p (etaSignatureBasis p i) (etaSignatureBasis p j) =
      if i = j then
        if i = 0 then ((1 / p.val.τ.im : ℝ) : ℂ)
        else ((6 * p.val.τ.im / etaDenom p : ℝ) : ℂ)
      else 0 := by
  simp only [etaSignatureBasis, Module.Basis.map_apply]
  rw [etaMatrixForm_diagonalized]
  fin_cases i <;> fin_cases j <;> simp [Pi.basisFun_apply]

theorem etaSignatureBasis_positive (p : PeriodDomain) :
    0 < (etaMatrixForm p (etaSignatureBasis p 0) (etaSignatureBasis p 0)).re := by
  rw [etaSignatureBasis_pairing]
  change 0 < 1 / p.val.τ.im
  exact one_div_pos.mpr (etaTau_pos p)

theorem etaSignatureBasis_negative (p : PeriodDomain) :
    (etaMatrixForm p (etaSignatureBasis p 1) (etaSignatureBasis p 1)).re < 0 := by
  rw [etaSignatureBasis_pairing]
  change 6 * p.val.τ.im / etaDenom p < 0
  exact div_neg_of_pos_of_neg (mul_pos (by norm_num) (etaTau_pos p)) (etaDenom_neg p)

/-- Signature `(1,1)` witnessed by a complete orthogonal complex basis. -/
theorem etaMatrixForm_signature_one_one (p : PeriodDomain) :
    ∃ b : Module.Basis (Fin 2) ℂ ComplexPlane₂,
      0 < (etaMatrixForm p (b 0) (b 0)).re ∧
      (etaMatrixForm p (b 1) (b 1)).re < 0 ∧
      etaMatrixForm p (b 0) (b 1) = 0 ∧
      etaMatrixForm p (b 1) (b 0) = 0 := by
  refine ⟨etaSignatureBasis p, etaSignatureBasis_positive p, etaSignatureBasis_negative p, ?_, ?_⟩
  · simp [etaSignatureBasis_pairing]
  · simp [etaSignatureBasis_pairing]

/-- No nonzero vector is orthogonal to the entire space. -/
theorem etaMatrixForm_separatingLeft (p : PeriodDomain) (x : ComplexPlane₂)
    (hx : ∀ y, etaMatrixForm p x y = 0) : x = 0 := by
  let z := (etaDiagonalizingEquiv p).symm x
  have hdiag (y : ComplexPlane₂) :
      ((1 / p.val.τ.im : ℝ) : ℂ) * z 0 * star (y 0) +
        ((6 * p.val.τ.im / etaDenom p : ℝ) : ℂ) * z 1 * star (y 1) = 0 := by
    rw [← etaMatrixForm_diagonalized]
    simpa [z] using hx (etaDiagonalizingEquiv p y)
  have h0 : ((1 / p.val.τ.im : ℝ) : ℂ) * z 0 = 0 := by
    simpa using hdiag ![1, 0]
  have h1 : ((6 * p.val.τ.im / etaDenom p : ℝ) : ℂ) * z 1 = 0 := by
    simpa using hdiag ![0, 1]
  have c0 : ((1 / p.val.τ.im : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (one_div_pos.mpr (etaTau_pos p)))
  have c1 : ((6 * p.val.τ.im / etaDenom p : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_lt
      (div_neg_of_pos_of_neg (mul_pos (by norm_num) (etaTau_pos p)) (etaDenom_neg p)))
  have hz : z = 0 := by
    ext i
    fin_cases i
    · exact (mul_eq_zero.mp h0).resolve_left c0
    · exact (mul_eq_zero.mp h1).resolve_left c1
  calc
    x = etaDiagonalizingEquiv p z := ((etaDiagonalizingEquiv p).apply_symm_apply x).symm
    _ = 0 := by rw [hz, map_zero]

/-- Nondegeneracy of the actual complex sesquilinear form, in both arguments. -/
theorem etaMatrixSesquilinear_nondegenerate (p : PeriodDomain) :
    (etaMatrixSesquilinear p).Nondegenerate := by
  constructor
  · intro x hx
    apply etaMatrixForm_separatingLeft p x
    intro y
    rw [← etaMatrixSesquilinear_apply, hx]
  · intro x hx
    apply etaMatrixForm_separatingLeft p x
    intro y
    rw [← etaMatrixForm_conj_symm p y x, ← etaMatrixSesquilinear_apply, hx, star_zero]

end Wikipedia.HopfProblem.PeriodTorusTypeOneOne
