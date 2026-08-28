import Wikipedia.HopfProblem.PeriodTorusTypeOneOneHermitianBasic

/-!
# Complex-linear functionals with prescribed real part

A real-linear functional on the period plane is the real part of a unique
complex-linear functional. The extension below is the explicit value
`ν z - I * ν (I • z)`.
-/

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassification

open Complex

/-- The complex-linear functional whose real part is the given real-linear
functional. -/
noncomputable def complexLinearOfReal (ν : ComplexPlane₂ →ₗ[ℝ] ℝ) :
    ComplexPlane₂ →ₗ[ℂ] ℂ where
  toFun z := (ν z : ℂ) - I * (ν (I • z) : ℂ)
  map_add' x y := by
    simp [smul_add, map_add, mul_add]
    ring
  map_smul' c z := by
    change (ν (c • z) : ℂ) - I * (ν (I • (c • z)) : ℂ) =
      c * ((ν z : ℂ) - I * (ν (I • z) : ℂ))
    rw [PeriodTorusTypeOneOne.complex_smul_decomposition c z]
    apply Complex.ext <;>
      simp [smul_add, smul_comm I c.re, smul_comm I c.im, map_add, map_smul,
        PeriodTorusTypeOneOne.I_smul_I_smul, Complex.mul_re, Complex.mul_im, add_comm]

@[simp]
theorem complexLinearOfReal_apply (ν : ComplexPlane₂ →ₗ[ℝ] ℝ) (z : ComplexPlane₂) :
    complexLinearOfReal ν z = (ν z : ℂ) - I * (ν (I • z) : ℂ) := rfl

@[simp]
theorem complexLinearOfReal_re (ν : ComplexPlane₂ →ₗ[ℝ] ℝ) (z : ComplexPlane₂) :
    (complexLinearOfReal ν z).re = ν z := by
  simp [complexLinearOfReal_apply]

@[simp]
theorem complexLinearOfReal_im (ν : ComplexPlane₂ →ₗ[ℝ] ℝ) (z : ComplexPlane₂) :
    (complexLinearOfReal ν z).im = -ν (I • z) := by
  simp [complexLinearOfReal_apply]

/-- The actual real-linear real part of a complex-linear functional. -/
noncomputable def realPartLinear (ℓ : ComplexPlane₂ →ₗ[ℂ] ℂ) :
    ComplexPlane₂ →ₗ[ℝ] ℝ :=
  Complex.reLm.comp (ℓ.restrictScalars ℝ)

@[simp]
theorem realPartLinear_apply (ℓ : ComplexPlane₂ →ₗ[ℂ] ℂ) (z : ComplexPlane₂) :
    realPartLinear ℓ z = (ℓ z).re := rfl

/-- Complex-linear functionals are determined by their real parts. -/
theorem complexLinear_ext_realPart (ℓ₁ ℓ₂ : ComplexPlane₂ →ₗ[ℂ] ℂ)
    (h : ∀ z, (ℓ₁ z).re = (ℓ₂ z).re) : ℓ₁ = ℓ₂ := by
  apply LinearMap.ext
  intro z
  apply Complex.ext
  · exact h z
  · have hI := h (I • z)
    simpa [map_smul, smul_eq_mul, Complex.mul_re] using hI

/-- Any complex-linear functional with real part `ν` is the explicit extension. -/
theorem complexLinearOfReal_unique (ν : ComplexPlane₂ →ₗ[ℝ] ℝ)
    (ℓ : ComplexPlane₂ →ₗ[ℂ] ℂ) (h : ∀ z, (ℓ z).re = ν z) :
    ℓ = complexLinearOfReal ν := by
  apply complexLinear_ext_realPart
  intro z
  simpa only [complexLinearOfReal_re] using h z

@[simp]
theorem realPartLinear_complexLinearOfReal (ν : ComplexPlane₂ →ₗ[ℝ] ℝ) :
    realPartLinear (complexLinearOfReal ν) = ν := by
  apply LinearMap.ext
  intro z
  exact complexLinearOfReal_re ν z

@[simp]
theorem complexLinearOfReal_realPartLinear (ℓ : ComplexPlane₂ →ₗ[ℂ] ℂ) :
    complexLinearOfReal (realPartLinear ℓ) = ℓ :=
  (complexLinearOfReal_unique (realPartLinear ℓ) ℓ (fun _ => rfl)).symm

theorem existsUnique_complexLinear_realPart (ν : ComplexPlane₂ →ₗ[ℝ] ℝ) :
    ∃! ℓ : ComplexPlane₂ →ₗ[ℂ] ℂ, ∀ z, (ℓ z).re = ν z := by
  refine ⟨complexLinearOfReal ν, complexLinearOfReal_re ν, ?_⟩
  intro ℓ h
  exact complexLinearOfReal_unique ν ℓ h

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassification
