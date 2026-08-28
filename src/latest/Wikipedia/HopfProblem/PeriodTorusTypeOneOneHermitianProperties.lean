import Wikipedia.HopfProblem.PeriodTorusTypeOneOneHermitian

/-!
# Scaling, uniqueness, and nondegeneracy of the associated Hermitian form

The left and right radicals agree with those of the original real form.
Thus nondegeneracy is preserved by the actual Hermitian construction.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusTypeOneOne

open Complex

theorem IsTypeOneOne.zsmul (E : RealForm) (hE : IsTypeOneOne E) (n : ℤ) :
    IsTypeOneOne (n • E) := by
  intro x y
  simpa only [LinearMap.smul_apply] using congrArg (n • ·) (hE x y)

theorem associatedSesquilinear_real_smul (E : RealForm) (hE : IsTypeOneOne E)
    (r : ℝ) :
    associatedSesquilinear (r • E) (hE.smul E r) = r • associatedSesquilinear E hE := by
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  apply Complex.ext <;> simp [LinearMap.smul_apply]

theorem associatedSesquilinear_zsmul (E : RealForm) (hE : IsTypeOneOne E)
    (n : ℤ) :
    associatedSesquilinear (n • E) (hE.zsmul E n) = n • associatedSesquilinear E hE := by
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  apply Complex.ext <;> simp [LinearMap.smul_apply]

/-- A vector is in the left radical exactly when its Hermitian pairing vanishes. -/
theorem associatedSesquilinear_left_radical_iff (E : RealForm) (hE : IsTypeOneOne E)
    (x : ComplexPlane₂) :
    (∀ y, associatedSesquilinear E hE x y = 0) ↔ ∀ y, E x y = 0 := by
  constructor
  · intro h y
    have h' := congrArg Complex.im (h y)
    simpa only [associatedSesquilinear_im, Complex.zero_im] using h'
  · intro h y
    apply Complex.ext
    · simp only [associatedSesquilinear_re, Complex.zero_re]
      have h' := h (I • y)
      rw [hE.right_I E x y] at h'
      exact neg_eq_zero.mp h'
    · simpa only [associatedSesquilinear_im, Complex.zero_im] using h y

theorem associatedSesquilinear_right_radical_iff (E : RealForm) (hE : IsTypeOneOne E)
    (y : ComplexPlane₂) :
    (∀ x, associatedSesquilinear E hE x y = 0) ↔ ∀ x, E x y = 0 := by
  constructor
  · intro h x
    have h' := congrArg Complex.im (h x)
    simpa only [associatedSesquilinear_im, Complex.zero_im] using h'
  · intro h x
    apply Complex.ext
    · simpa only [associatedSesquilinear_re, Complex.zero_re] using h (I • x)
    · simpa only [associatedSesquilinear_im, Complex.zero_im] using h x

theorem associatedSesquilinear_nondegenerate_iff (E : RealForm) (hE : IsTypeOneOne E) :
    (associatedSesquilinear E hE).Nondegenerate ↔ E.Nondegenerate := by
  simp only [LinearMap.Nondegenerate, LinearMap.SeparatingLeft, LinearMap.SeparatingRight,
    associatedSesquilinear_left_radical_iff, associatedSesquilinear_right_radical_iff]

/-- Existence and uniqueness include conjugate symmetry, not merely the scalar laws. -/
theorem existsUnique_hermitian_im (E : RealForm) (hE : IsTypeOneOne E)
    (hAlt : ∀ x, E x x = 0) :
    ∃! H : ComplexPlane₂ →ₗ[ℂ] ComplexPlane₂ →ₗ⋆[ℂ] ℂ,
      (∀ x y, H y x = star (H x y)) ∧ (∀ x y, (H x y).im = E x y) := by
  refine ⟨associatedSesquilinear E hE,
    ⟨associatedSesquilinear_conj_symm E hE hAlt, associatedSesquilinear_im E hE⟩, ?_⟩
  intro H hH
  exact eq_associatedSesquilinear_of_im E hE H hH.2

/-- The imaginary part of any first-linear sesquilinear form satisfies the type condition. -/
theorem isTypeOneOne_of_sesquilinear_im (E : RealForm)
    (H : ComplexPlane₂ →ₗ[ℂ] ComplexPlane₂ →ₗ⋆[ℂ] ℂ)
    (hIm : ∀ x y, (H x y).im = E x y) : IsTypeOneOne E := by
  intro x y
  rw [← hIm, ← hIm]
  simp [map_smul, LinearMap.map_smulₛₗ₂, LinearMap.smul_apply, smul_eq_mul,
    mul_assoc]

theorem isTypeOneOne_iff_exists_sesquilinear_im (E : RealForm) :
    IsTypeOneOne E ↔ ∃ H : ComplexPlane₂ →ₗ[ℂ] ComplexPlane₂ →ₗ⋆[ℂ] ℂ,
      ∀ x y, (H x y).im = E x y := by
  constructor
  · intro hE
    exact ⟨associatedSesquilinear E hE, associatedSesquilinear_im E hE⟩
  · rintro ⟨H, hH⟩
    exact isTypeOneOne_of_sesquilinear_im E H hH

end Wikipedia.HopfProblem.PeriodTorusTypeOneOne
