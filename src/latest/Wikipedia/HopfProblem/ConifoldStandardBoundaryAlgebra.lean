import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Explicit matrix algebra for the standard conifold boundary

The involution `adjointAdjugate M = adjugate (conjTranspose M)` is real-linear
on two-by-two complex matrices.  Its deformation sends suitable nonzero
determinant-zero level sets to determinant-one level sets.  These are literal
matrix identities, independent of any sphere-recognition theorem.
-/

noncomputable section

open scoped ComplexConjugate

namespace Wikipedia.HopfProblem.ConifoldStandardBoundary

/-- The original two-by-two complex matrix model, with its usual product topology. -/
abbrev MatrixSpace := Matrix (Fin 2) (Fin 2) ℂ

/-- Squared Frobenius norm, using all four complex matrix entries. -/
def frobeniusSq (M : MatrixSpace) : ℝ :=
  ∑ i, ∑ j, Complex.normSq (M i j)

/-- The adjugate of the conjugate transpose, not the conjugate transpose alone. -/
def adjointAdjugate (M : MatrixSpace) : MatrixSpace :=
  M.conjTranspose.adjugate

/-- The real-linear conifold deformation with real coefficient `a`. -/
def deform (a : ℝ) (M : MatrixSpace) : MatrixSpace :=
  M + (a : ℂ) • adjointAdjugate M

theorem frobeniusSq_entries (M : MatrixSpace) :
    frobeniusSq M = Complex.normSq (M 0 0) + Complex.normSq (M 0 1) +
      (Complex.normSq (M 1 0) + Complex.normSq (M 1 1)) := by
  simp only [frobeniusSq, Fin.sum_univ_two]

theorem adjointAdjugate_entries (M : MatrixSpace) :
    adjointAdjugate M = !![conj (M 1 1), -conj (M 1 0);
      -conj (M 0 1), conj (M 0 0)] := by
  simp [adjointAdjugate, Matrix.adjugate_fin_two, Matrix.conjTranspose_apply]

@[simp] theorem adjointAdjugate_involutive (M : MatrixSpace) :
    adjointAdjugate (adjointAdjugate M) = M := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [adjointAdjugate_entries]

theorem adjointAdjugate_add (M N : MatrixSpace) :
    adjointAdjugate (M + N) = adjointAdjugate M + adjointAdjugate N := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [adjointAdjugate_entries, add_comm]

theorem adjointAdjugate_smul (a : ℝ) (M : MatrixSpace) :
    adjointAdjugate ((a : ℂ) • M) = (a : ℂ) • adjointAdjugate M := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [adjointAdjugate_entries]

theorem adjointAdjugate_deform (a : ℝ) (M : MatrixSpace) :
    adjointAdjugate (deform a M) = adjointAdjugate M + (a : ℂ) • M := by
  rw [deform, adjointAdjugate_add, adjointAdjugate_smul,
    adjointAdjugate_involutive]

theorem deform_deform_neg (a : ℝ) (M : MatrixSpace) :
    deform (-a) (deform a M) = ((1 - a ^ 2 : ℝ) : ℂ) • M := by
  rw [deform, adjointAdjugate_deform]
  ext i j
  simp only [deform, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    Complex.ofReal_neg, Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_pow]
  ring

theorem deform_neg_deform (a : ℝ) (M : MatrixSpace) :
    deform a (deform (-a) M) = ((1 - a ^ 2 : ℝ) : ℂ) • M := by
  simpa only [neg_neg, neg_sq] using deform_deform_neg (-a) M

theorem deform_smul (a b : ℝ) (M : MatrixSpace) :
    deform a ((b : ℂ) • M) = (b : ℂ) • deform a M := by
  rw [deform, adjointAdjugate_smul]
  ext i j
  simp only [deform, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

theorem det_adjointAdjugate (M : MatrixSpace) :
    (adjointAdjugate M).det = conj M.det := by
  simp [Matrix.det_fin_two, adjointAdjugate_entries]
  ring

theorem frobeniusSq_smul (a : ℝ) (M : MatrixSpace) :
    frobeniusSq ((a : ℂ) • M) = a ^ 2 * frobeniusSq M := by
  simp only [frobeniusSq_entries, Matrix.smul_apply, smul_eq_mul,
    Complex.normSq_mul, Complex.normSq_ofReal]
  ring

theorem frobeniusSq_adjointAdjugate (M : MatrixSpace) :
    frobeniusSq (adjointAdjugate M) = frobeniusSq M := by
  simp [frobeniusSq_entries, adjointAdjugate_entries]
  ring

theorem det_deform (a : ℝ) (M : MatrixSpace) :
    (deform a M).det = M.det + (a : ℂ) * (frobeniusSq M : ℂ) +
      (a : ℂ) ^ 2 * conj M.det := by
  apply Complex.ext <;>
    simp [Matrix.det_fin_two, deform, adjointAdjugate_entries,
      frobeniusSq_entries, Complex.normSq_apply, pow_two] <;> ring

theorem frobeniusSq_deform (a : ℝ) (M : MatrixSpace) :
    frobeniusSq (deform a M) =
      (1 + a ^ 2) * frobeniusSq M + 4 * a * M.det.re := by
  simp [frobeniusSq_entries, deform, adjointAdjugate_entries,
    Matrix.det_fin_two, Complex.normSq_apply]
  ring

end Wikipedia.HopfProblem.ConifoldStandardBoundary
