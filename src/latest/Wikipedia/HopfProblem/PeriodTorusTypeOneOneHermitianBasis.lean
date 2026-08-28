import Wikipedia.HopfProblem.PeriodTorusTypeOneOneHermitianBasic

/-!
# A two-equation criterion for type `(1,1)`

For an alternating real bilinear form on `ℂ²`, invariance under the complex
structure is determined by two equations between the four real basis vectors.
The criterion is unchanged by a complex-linear change of coordinates.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusTypeOneOne

open Complex
open scoped Matrix

/-- The real basis `e0, I • e0, e1, I • e1` of the complex plane of periods. -/
def standardRealBasis : Module.Basis (Fin 4) ℝ ComplexPlane₂ :=
  (Pi.basisFun ℝ (Fin 4)).map complexCoordinates

@[simp]
theorem standardRealBasis_zero : standardRealBasis 0 = e0 := by
  ext j
  fin_cases j <;> apply Complex.ext <;>
    simp [standardRealBasis, complexCoordinates, e0]

@[simp]
theorem standardRealBasis_one : standardRealBasis 1 = I • e0 := by
  ext j
  fin_cases j <;> apply Complex.ext <;>
    simp [standardRealBasis, complexCoordinates, e0]

@[simp]
theorem standardRealBasis_two : standardRealBasis 2 = e1 := by
  ext j
  fin_cases j <;> apply Complex.ext <;>
    simp [standardRealBasis, complexCoordinates, e1]

@[simp]
theorem standardRealBasis_three : standardRealBasis 3 = I • e1 := by
  ext j
  fin_cases j <;> apply Complex.ext <;>
    simp [standardRealBasis, complexCoordinates, e1]

/-- The actual type `(1,1)` condition for an alternating form is equivalent to
two equations in the standard complex basis. -/
theorem isTypeOneOne_iff_basis (E : RealForm) (hAlt : ∀ x, E x x = 0) :
    IsTypeOneOne E ↔
      E e0 e1 = E (I • e0) (I • e1) ∧
      E e0 (I • e1) + E (I • e0) e1 = 0 := by
  constructor
  · intro hE
    refine ⟨(hE e0 e1).symm, ?_⟩
    rw [hE.right_I E e0 e1]
    exact neg_add_cancel _
  · rintro ⟨h01, hCross⟩
    have h12 : E (I • e0) e1 = -E e0 (I • e1) := by
      linarith only [hCross]
    have h10 := realForm_skew E hAlt e0 (I • e0)
    have h20 := realForm_skew E hAlt e0 e1
    have h30 := realForm_skew E hAlt e0 (I • e1)
    have h21 := realForm_skew E hAlt (I • e0) e1
    have h31 := realForm_skew E hAlt (I • e0) (I • e1)
    have h32 := realForm_skew E hAlt e1 (I • e1)
    let J : ComplexPlane₂ →ₗ[ℝ] ComplexPlane₂ :=
      (LinearMap.lsmul ℂ ComplexPlane₂ I).restrictScalars ℝ
    have hEqual : E.compl₁₂ J J = E := by
      apply LinearMap.BilinForm.ext_basis standardRealBasis
      intro i j
      change E (I • standardRealBasis i) (I • standardRealBasis j) =
        E (standardRealBasis i) (standardRealBasis j)
      fin_cases i <;> fin_cases j <;>
        simp [I_smul_I_smul, LinearMap.BilinForm.neg_right,
          hAlt, h10, h20, h30, h21, h31, h32,
          h01, h12]
    intro x y
    exact LinearMap.congr_fun (LinearMap.congr_fun hEqual x) y

/-- The same criterion in any complex basis obtained by a complex-linear
equivalence of `ℂ²`. -/
theorem isTypeOneOne_iff_basis_equiv (E : RealForm) (hAlt : ∀ x, E x x = 0)
    (e : ComplexPlane₂ ≃ₗ[ℂ] ComplexPlane₂) :
    IsTypeOneOne E ↔
      E (e e0) (e e1) = E (I • e e0) (I • e e1) ∧
      E (e e0) (I • e e1) + E (I • e e0) (e e1) = 0 := by
  let f : ComplexPlane₂ →ₗ[ℝ] ComplexPlane₂ := e.toLinearMap.restrictScalars ℝ
  let F : RealForm := E.compl₁₂ f f
  have hFAlt : ∀ x, F x x = 0 := fun x => hAlt (e x)
  have hType : IsTypeOneOne E ↔ IsTypeOneOne F := by
    constructor
    · intro hE x y
      change E (e (I • x)) (e (I • y)) = E (e x) (e y)
      simpa only [map_smul] using hE (e x) (e y)
    · intro hF x y
      obtain ⟨u, rfl⟩ := e.surjective x
      obtain ⟨v, rfl⟩ := e.surjective y
      have h := hF u v
      change E (e (I • u)) (e (I • v)) = E (e u) (e v) at h
      simpa only [map_smul] using h
  rw [hType, isTypeOneOne_iff_basis F hFAlt]
  change
    (E (e e0) (e e1) = E (e (I • e0)) (e (I • e1)) ∧
      E (e e0) (e (I • e1)) + E (e (I • e0)) (e e1) = 0) ↔ _
  simp only [map_smul]

end Wikipedia.HopfProblem.PeriodTorusTypeOneOne
