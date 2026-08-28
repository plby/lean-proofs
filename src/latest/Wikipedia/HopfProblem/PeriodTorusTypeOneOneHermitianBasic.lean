import Wikipedia.HopfProblem.PeriodTori
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.SesquilinearForm.Star

/-!
# Real forms of type `(1,1)` on the complex plane of periods

The type condition is the actual invariance under multiplication by `I` in
both variables. The Hermitian convention used below is linear in the first
variable and conjugate-linear in the second.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusTypeOneOne

open Complex
open scoped Matrix

abbrev RealForm := LinearMap.BilinForm ℝ ComplexPlane₂

/-- Invariance of a real bilinear form under the complex structure. -/
def IsTypeOneOne (E : RealForm) : Prop :=
  ∀ x y, E (I • x) (I • y) = E x y

/-- The first standard complex vector. -/
def e0 : ComplexPlane₂ := ![1, 0]

/-- The second standard complex vector. -/
def e1 : ComplexPlane₂ := ![0, 1]

@[simp]
theorem I_smul_I_smul (x : ComplexPlane₂) : I • (I • x) = -x := by
  simp [smul_smul]

theorem complex_smul_decomposition (c : ℂ) (x : ComplexPlane₂) :
    c • x = c.re • x + c.im • (I • x) := by
  ext j
  apply Complex.ext <;>
    simp [Complex.mul_re, Complex.mul_im] <;> ring

theorem realForm_skew (E : RealForm) (hAlt : ∀ x, E x x = 0)
    (x y : ComplexPlane₂) : E y x = -E x y :=
  (LinearMap.IsAlt.neg hAlt x y).symm

theorem IsTypeOneOne.right_I (E : RealForm) (hE : IsTypeOneOne E)
    (x y : ComplexPlane₂) : E x (I • y) = -E (I • x) y := by
  have h := hE x (I • y)
  simpa only [I_smul_I_smul, map_neg] using h.symm

theorem IsTypeOneOne.smul (E : RealForm) (hE : IsTypeOneOne E) (r : ℝ) :
    IsTypeOneOne (r • E) := by
  intro x y
  simpa only [LinearMap.smul_apply] using congrArg (r • ·) (hE x y)

/-- The uniquely possible first-linear Hermitian value with imaginary part `E`. -/
def hermitianValue (E : RealForm) (x y : ComplexPlane₂) : ℂ :=
  (E (I • x) y : ℂ) + I * (E x y : ℂ)

@[simp]
theorem hermitianValue_re (E : RealForm) (x y : ComplexPlane₂) :
    (hermitianValue E x y).re = E (I • x) y := by
  simp [hermitianValue]

@[simp]
theorem hermitianValue_im (E : RealForm) (x y : ComplexPlane₂) :
    (hermitianValue E x y).im = E x y := by
  simp [hermitianValue]

end Wikipedia.HopfProblem.PeriodTorusTypeOneOne
