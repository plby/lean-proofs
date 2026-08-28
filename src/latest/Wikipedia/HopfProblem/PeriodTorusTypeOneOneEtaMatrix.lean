import Wikipedia.HopfProblem.PeriodTori
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The explicit Hermitian matrix of the distinguished alternating form

For an actual point of the period domain, this file constructs the real
Gram matrix in Lemma 9.4 and its twice-inverse Hermitian matrix.  The
associated form is linear in its first argument and conjugate-linear in
its second argument, as in the source.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.PeriodTorusTypeOneOne

/-- The nonzero determinant factor of the actual real period matrix. -/
def etaDenom (p : PeriodDomain) : ℝ :=
  p.val.τ.im * p.val.β.im - 6 * p.val.μ.im ^ 2

theorem etaDenom_eq_discriminant (p : PeriodDomain) :
    etaDenom p = p.val.τ.im * p.val.discriminant := by
  unfold etaDenom
  rw [← p.val.det_realMatrix, p.val.det_realMatrix_eq_discriminant (ne_of_gt p.property.1)]

theorem etaDenom_neg (p : PeriodDomain) : etaDenom p < 0 := by
  rw [etaDenom_eq_discriminant]
  exact mul_neg_of_pos_of_neg p.property.1 p.property.2

theorem etaDenom_ne_zero (p : PeriodDomain) : etaDenom p ≠ 0 := ne_of_lt (etaDenom_neg p)

theorem etaTau_pos (p : PeriodDomain) : 0 < p.val.τ.im := p.property.1

theorem etaTau_ne_zero (p : PeriodDomain) : p.val.τ.im ≠ 0 := ne_of_gt (etaTau_pos p)

/-- The real Gram matrix `Gη` of the inverse alternating form. -/
def etaGram (p : PeriodDomain) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![2 * p.val.τ.im, 2 * p.val.μ.im; 2 * p.val.μ.im, p.val.β.im / 3]

/-- The explicit matrix `Hη = 2 Gη⁻¹`. -/
def etaHermitianMatrix (p : PeriodDomain) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![p.val.β.im / etaDenom p, -6 * p.val.μ.im / etaDenom p;
     -6 * p.val.μ.im / etaDenom p, 6 * p.val.τ.im / etaDenom p]

theorem etaGram_det (p : PeriodDomain) : (etaGram p).det = (2 / 3 : ℝ) * etaDenom p := by
  rw [Matrix.det_fin_two]
  change (2 * p.val.τ.im) * (p.val.β.im / 3) - (2 * p.val.μ.im) * (2 * p.val.μ.im) = _
  unfold etaDenom
  ring

theorem etaGram_det_eq_discriminant (p : PeriodDomain) :
    (etaGram p).det = (2 / 3 : ℝ) * p.val.τ.im * p.val.discriminant := by
  rw [etaGram_det, etaDenom_eq_discriminant, mul_assoc]

theorem etaGram_det_neg (p : PeriodDomain) : (etaGram p).det < 0 := by
  rw [etaGram_det]
  exact mul_neg_of_pos_of_neg (by norm_num) (etaDenom_neg p)

theorem etaGram_isHermitian (p : PeriodDomain) : (etaGram p).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [etaGram]

theorem etaHermitianMatrix_isHermitian (p : PeriodDomain) :
    (etaHermitianMatrix p).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [etaHermitianMatrix]

theorem etaHermitianMatrix_mul_etaGram (p : PeriodDomain) :
    etaHermitianMatrix p * etaGram p = (2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [etaHermitianMatrix, etaGram, Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp [etaDenom_ne_zero p] <;> unfold etaDenom <;> ring

theorem etaHermitianMatrix_eq_twice_inv (p : PeriodDomain) :
    etaHermitianMatrix p = (2 : ℝ) • (etaGram p)⁻¹ := by
  have hleft : ((1 / 2 : ℝ) • etaHermitianMatrix p) * etaGram p = 1 := by
    rw [Matrix.smul_mul, etaHermitianMatrix_mul_etaGram, smul_smul]
    norm_num
  rw [Matrix.inv_eq_left_inv hleft, smul_smul]
  norm_num

theorem etaHermitianMatrix_det (p : PeriodDomain) :
    (etaHermitianMatrix p).det = 6 / etaDenom p := by
  simp [etaHermitianMatrix, Matrix.det_fin_two]
  field_simp [etaDenom_ne_zero p]
  unfold etaDenom
  ring

theorem etaHermitianMatrix_det_neg (p : PeriodDomain) :
    (etaHermitianMatrix p).det < 0 := by
  rw [etaHermitianMatrix_det]
  exact div_neg_of_pos_of_neg (by norm_num) (etaDenom_neg p)

theorem etaGram_nondegenerate (p : PeriodDomain) : (etaGram p).Nondegenerate :=
  Matrix.Nondegenerate.of_det_ne_zero (ne_of_lt (etaGram_det_neg p))

theorem etaHermitianMatrix_nondegenerate (p : PeriodDomain) :
    (etaHermitianMatrix p).Nondegenerate :=
  Matrix.Nondegenerate.of_det_ne_zero (ne_of_lt (etaHermitianMatrix_det_neg p))

/-- The same matrix regarded over the complex numbers. -/
def etaComplexMatrix (p : PeriodDomain) : Matrix (Fin 2) (Fin 2) ℂ :=
  (etaHermitianMatrix p).map Complex.ofReal

theorem etaComplexMatrix_isHermitian (p : PeriodDomain) :
    (etaComplexMatrix p).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [etaComplexMatrix, etaHermitianMatrix]

/-- The source's linear-first Hermitian form, written directly as a finite sum. -/
def etaMatrixForm (p : PeriodDomain) (x y : ComplexPlane₂) : ℂ :=
  ∑ i, ∑ j, (etaHermitianMatrix p i j : ℂ) * x i * star (y j)

/-- The explicit form is genuinely complex-linear/conjugate-linear. -/
def etaMatrixSesquilinear (p : PeriodDomain) :
    ComplexPlane₂ →ₗ[ℂ] ComplexPlane₂ →ₗ⋆[ℂ] ℂ :=
  Matrix.toLinearMapₛₗ₂' ℂ (RingHom.id ℂ) (starRingEnd ℂ) (etaComplexMatrix p)

theorem etaMatrixSesquilinear_apply (p : PeriodDomain) (x y : ComplexPlane₂) :
    etaMatrixSesquilinear p x y = etaMatrixForm p x y := by
  rw [etaMatrixSesquilinear, Matrix.toLinearMapₛₗ₂'_apply]
  unfold etaMatrixForm etaComplexMatrix
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  simp only [RingHom.id_apply, starRingEnd_apply, smul_eq_mul, Matrix.map_apply]
  ring

theorem etaMatrixForm_conj_symm (p : PeriodDomain) (x y : ComplexPlane₂) :
    star (etaMatrixForm p x y) = etaMatrixForm p y x := by
  simp [etaMatrixForm, Fin.sum_univ_two, etaHermitianMatrix]
  ring

end Wikipedia.HopfProblem.PeriodTorusTypeOneOne
