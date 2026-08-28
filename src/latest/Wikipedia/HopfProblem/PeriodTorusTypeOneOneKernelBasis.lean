import Wikipedia.HopfProblem.PeriodTorusTypeOneOneTangent
import Wikipedia.HopfProblem.PeriodTorusTypeOneOneHermitianBasic

/-!
# A genuine complex basis coming from the period-kernel vectors

The two complex kernel vectors of `[Z | I]` are
`(1,0,-6μ,-β)` and `(0,1,-τ,-μ)`. Their real parts map under the real
period isomorphism to a complex basis of `ℂ²`, and their imaginary parts
map to `I` times that basis. Nondegeneracy follows from the proved strict
negativity of the actual real period determinant.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusTypeOneOne

open Complex
open scoped Matrix

def kernelRealFirst (p : PeriodPoint) : Fin 4 → ℝ := ![1, 0, -6 * p.μ.re, -p.β.re]

def kernelImagFirst (p : PeriodPoint) : Fin 4 → ℝ := ![0, 0, -6 * p.μ.im, -p.β.im]

def kernelRealSecond (p : PeriodPoint) : Fin 4 → ℝ := ![0, 1, -p.τ.re, -p.μ.re]

def kernelImagSecond (p : PeriodPoint) : Fin 4 → ℝ := ![0, 0, -p.τ.im, -p.μ.im]

/-- The actual images of the two real kernel vectors, as columns of a complex matrix. -/
def kernelBasisMatrix (p : PeriodPoint) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![I * (6 * p.μ.im), I * p.τ.im; I * p.β.im, I * p.μ.im]

theorem kernelBasisMatrix_det (p : PeriodPoint) :
    (kernelBasisMatrix p).det = (p.realMatrix.det : ℂ) := by
  rw [Matrix.det_fin_two, PeriodPoint.det_realMatrix]
  change (I * (6 * (p.μ.im : ℂ))) * (I * (p.μ.im : ℂ)) -
    (I * (p.τ.im : ℂ)) * (I * (p.β.im : ℂ)) = _
  push_cast
  calc
    _ = I ^ 2 * (6 * (p.μ.im : ℂ) ^ 2 - (p.τ.im : ℂ) * (p.β.im : ℂ)) := by ring
    _ = _ := by rw [I_sq]; ring

theorem kernelBasisMatrix_det_ne_zero (p : PeriodDomain) : (kernelBasisMatrix p.val).det ≠ 0 := by
  rw [kernelBasisMatrix_det]
  exact_mod_cast ne_of_lt (p.val.det_realMatrix_neg p.property)

/-- An actual complex-linear basis change; its two columns are not assumed independent. -/
def kernelBasisEquiv (p : PeriodDomain) : ComplexPlane₂ ≃ₗ[ℂ] ComplexPlane₂ :=
  Matrix.toLinearEquiv (Pi.basisFun ℂ (Fin 2)) (kernelBasisMatrix p.val)
    (isUnit_iff_ne_zero.mpr (kernelBasisMatrix_det_ne_zero p))

theorem kernelBasisEquiv_apply (p : PeriodDomain) (x : ComplexPlane₂) :
    kernelBasisEquiv p x = kernelBasisMatrix p.val *ᵥ x := by
  simp [kernelBasisEquiv, Matrix.toLin_eq_toLin', Matrix.toLin'_apply]

theorem kernelBasisEquiv_e0 (p : PeriodDomain) :
    kernelBasisEquiv p e0 = ![I * (6 * p.val.μ.im), I * p.val.β.im] := by
  rw [kernelBasisEquiv_apply]
  ext i
  fin_cases i <;> simp [kernelBasisMatrix, e0, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem kernelBasisEquiv_e1 (p : PeriodDomain) :
    kernelBasisEquiv p e1 = ![I * p.val.τ.im, I * p.val.μ.im] := by
  rw [kernelBasisEquiv_apply]
  ext i
  fin_cases i <;> simp [kernelBasisMatrix, e1, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem periodEquiv_kernelRealFirst (p : PeriodDomain) :
    periodEquiv p (kernelRealFirst p.val) = kernelBasisEquiv p e0 := by
  rw [periodEquiv_coordinates, kernelBasisEquiv_e0]
  ext i
  fin_cases i <;> apply Complex.ext <;>
    simp [kernelRealFirst, Complex.mul_re, Complex.mul_im]

theorem periodEquiv_kernelImagFirst (p : PeriodDomain) :
    periodEquiv p (kernelImagFirst p.val) = I • kernelBasisEquiv p e0 := by
  rw [periodEquiv_coordinates, kernelBasisEquiv_e0]
  ext i
  fin_cases i <;> apply Complex.ext <;>
    simp [kernelImagFirst, Complex.mul_re, Complex.mul_im]

theorem periodEquiv_kernelRealSecond (p : PeriodDomain) :
    periodEquiv p (kernelRealSecond p.val) = kernelBasisEquiv p e1 := by
  rw [periodEquiv_coordinates, kernelBasisEquiv_e1]
  ext i
  fin_cases i <;> apply Complex.ext <;>
    simp [kernelRealSecond, Complex.mul_re, Complex.mul_im]

theorem periodEquiv_kernelImagSecond (p : PeriodDomain) :
    periodEquiv p (kernelImagSecond p.val) = I • kernelBasisEquiv p e1 := by
  rw [periodEquiv_coordinates, kernelBasisEquiv_e1]
  ext i
  fin_cases i <;> apply Complex.ext <;>
    simp [kernelImagSecond, Complex.mul_re, Complex.mul_im]

end Wikipedia.HopfProblem.PeriodTorusTypeOneOne
