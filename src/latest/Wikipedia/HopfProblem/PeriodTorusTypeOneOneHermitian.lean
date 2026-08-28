import Wikipedia.HopfProblem.PeriodTorusTypeOneOneHermitianBasic

/-!
# The Hermitian form associated to an alternating real form of type `(1,1)`

All scalar laws are proved for the actual value
`E (I • x) y + I * E x y`. In particular, the construction is not a
postulated Hermitian form or an assumption about its imaginary part.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusTypeOneOne

open Complex

theorem hermitianValue_add_left (E : RealForm) (x x' y : ComplexPlane₂) :
    hermitianValue E (x + x') y = hermitianValue E x y + hermitianValue E x' y := by
  simp [hermitianValue, smul_add, map_add, mul_add]
  ring

theorem hermitianValue_add_right (E : RealForm) (x y y' : ComplexPlane₂) :
    hermitianValue E x (y + y') = hermitianValue E x y + hermitianValue E x y' := by
  simp [hermitianValue, map_add, mul_add]
  ring

theorem hermitianValue_real_smul_left (E : RealForm) (r : ℝ) (x y : ComplexPlane₂) :
    hermitianValue E (r • x) y = r • hermitianValue E x y := by
  apply Complex.ext <;>
    simp [hermitianValue, smul_comm I r, map_smul, LinearMap.smul_apply]

theorem hermitianValue_real_smul_right (E : RealForm) (r : ℝ) (x y : ComplexPlane₂) :
    hermitianValue E x (r • y) = r • hermitianValue E x y := by
  apply Complex.ext <;> simp [hermitianValue, map_smul]

theorem hermitianValue_I_smul_left (E : RealForm) (x y : ComplexPlane₂) :
    hermitianValue E (I • x) y = I * hermitianValue E x y := by
  apply Complex.ext <;> simp [hermitianValue]

theorem hermitianValue_I_smul_right (E : RealForm) (hE : IsTypeOneOne E)
    (x y : ComplexPlane₂) :
    hermitianValue E x (I • y) = -I * hermitianValue E x y := by
  apply Complex.ext <;> simp [hermitianValue, hE x y, hE.right_I E x y]

theorem hermitianValue_smul_left (E : RealForm) (c : ℂ) (x y : ComplexPlane₂) :
    hermitianValue E (c • x) y = c * hermitianValue E x y := by
  rw [complex_smul_decomposition, hermitianValue_add_left,
    hermitianValue_real_smul_left, hermitianValue_real_smul_left,
    hermitianValue_I_smul_left]
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

theorem hermitianValue_smul_right (E : RealForm) (hE : IsTypeOneOne E)
    (c : ℂ) (x y : ComplexPlane₂) :
    hermitianValue E x (c • y) = star c * hermitianValue E x y := by
  rw [complex_smul_decomposition, hermitianValue_add_right,
    hermitianValue_real_smul_right, hermitianValue_real_smul_right,
    hermitianValue_I_smul_right E hE]
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

/-- The associated form, bundled with complex linearity in the first variable
and conjugate linearity in the second. -/
def associatedSesquilinear (E : RealForm) (hE : IsTypeOneOne E) :
    ComplexPlane₂ →ₗ[ℂ] ComplexPlane₂ →ₗ⋆[ℂ] ℂ where
  toFun x :=
    { toFun := hermitianValue E x
      map_add' := hermitianValue_add_right E x
      map_smul' := by
        intro c y
        exact hermitianValue_smul_right E hE c x y }
  map_add' x x' := by
    ext y
    exact hermitianValue_add_left E x x' y
  map_smul' c x := by
    ext y
    exact hermitianValue_smul_left E c x y

@[simp]
theorem associatedSesquilinear_apply (E : RealForm) (hE : IsTypeOneOne E)
    (x y : ComplexPlane₂) :
    associatedSesquilinear E hE x y = hermitianValue E x y := rfl

@[simp]
theorem associatedSesquilinear_re (E : RealForm) (hE : IsTypeOneOne E)
    (x y : ComplexPlane₂) :
    (associatedSesquilinear E hE x y).re = E (I • x) y :=
  hermitianValue_re E x y

@[simp]
theorem associatedSesquilinear_im (E : RealForm) (hE : IsTypeOneOne E)
    (x y : ComplexPlane₂) :
    (associatedSesquilinear E hE x y).im = E x y :=
  hermitianValue_im E x y

theorem associatedSesquilinear_conj_symm (E : RealForm) (hE : IsTypeOneOne E)
    (hAlt : ∀ x, E x x = 0) (x y : ComplexPlane₂) :
    associatedSesquilinear E hE y x = star (associatedSesquilinear E hE x y) := by
  apply Complex.ext
  · simp only [associatedSesquilinear_re, Complex.star_def, Complex.conj_re]
    rw [realForm_skew E hAlt x (I • y), hE.right_I E x y, neg_neg]
  · simp only [associatedSesquilinear_im, Complex.star_def, Complex.conj_im]
    exact realForm_skew E hAlt x y

/-- Mathlib's symmetric sesquilinear convention is conjugate-linear first,
so symmetry is bundled on the flipped associated form. -/
theorem associatedSesquilinear_flip_isSymm (E : RealForm) (hE : IsTypeOneOne E)
    (hAlt : ∀ x, E x x = 0) : (associatedSesquilinear E hE).flip.IsSymm := by
  constructor
  intro x y
  exact (associatedSesquilinear_conj_symm E hE hAlt y x).symm

/-- The imaginary part determines a first-linear sesquilinear form uniquely. -/
theorem eq_associatedSesquilinear_of_im (E : RealForm) (hE : IsTypeOneOne E)
    (H : ComplexPlane₂ →ₗ[ℂ] ComplexPlane₂ →ₗ⋆[ℂ] ℂ)
    (hIm : ∀ x y, (H x y).im = E x y) : H = associatedSesquilinear E hE := by
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  apply Complex.ext
  · rw [associatedSesquilinear_re]
    have h := hIm (I • x) y
    simpa [map_smul, LinearMap.smul_apply, smul_eq_mul, Complex.mul_im] using h
  · rw [associatedSesquilinear_im]
    exact hIm x y

theorem existsUnique_sesquilinear_im (E : RealForm) (hE : IsTypeOneOne E) :
    ∃! H : ComplexPlane₂ →ₗ[ℂ] ComplexPlane₂ →ₗ⋆[ℂ] ℂ,
      ∀ x y, (H x y).im = E x y := by
  refine ⟨associatedSesquilinear E hE, associatedSesquilinear_im E hE, ?_⟩
  intro H hH
  exact eq_associatedSesquilinear_of_im E hE H hH

end Wikipedia.HopfProblem.PeriodTorusTypeOneOne
