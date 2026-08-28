import Wikipedia.HomotopyGroupsOfSpheres.RealUnitaryMatrices
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# The compact orthogonal orbit of a balanced real involution

The matrix `diag(1ₙ,-1ₙ)` has equally sized positive and negative eigenspaces.
Its actual orthogonal conjugacy orbit is a matrix model for the balanced real
Grassmannian. The topology here is the original matrix subspace topology.
-/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.BalancedRealInvolutions

open RealUnitaryMatrices

abbrev Index (n : ℕ) := Fin n ⊕ Fin n

def sign (n : ℕ) : Index n → ℝ := Sum.elim (fun _ ↦ 1) (fun _ ↦ -1)

def standardMatrix (n : ℕ) : Matrix (Index n) (Index n) ℝ := Matrix.diagonal (sign n)

theorem standardMatrix_transpose (n : ℕ) : (standardMatrix n).transpose = standardMatrix n :=
  Matrix.diagonal_transpose _

theorem standardMatrix_square (n : ℕ) : standardMatrix n * standardMatrix n = 1 := by
  rw [standardMatrix, Matrix.diagonal_mul_diagonal]
  have hs : (fun a : Index n ↦ sign n a * sign n a) = fun _ ↦ (1 : ℝ) := by
    funext a
    cases a <;> simp [sign]
  rw [hs, Matrix.diagonal_one]

theorem standardMatrix_trace (n : ℕ) : (standardMatrix n).trace = 0 := by
  simp [standardMatrix, Matrix.trace_diagonal, Fintype.sum_sum_type, sign]

def orbitMatrix (n : ℕ) (U : unitary (Matrix (Index n) (Index n) ℝ)) :
    Matrix (Index n) (Index n) ℝ := U.val * standardMatrix n * U.val.transpose

theorem orbitMatrix_transpose (n : ℕ) (U : unitary (Matrix (Index n) (Index n) ℝ)) :
    (orbitMatrix n U).transpose = orbitMatrix n U := by
  rw [orbitMatrix, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.transpose_mul, standardMatrix_transpose]
  exact (mul_assoc _ _ _).symm

theorem orbitMatrix_square (n : ℕ) (U : unitary (Matrix (Index n) (Index n) ℝ)) :
    orbitMatrix n U * orbitMatrix n U = 1 := by
  have hU : U.val.transpose * U.val = 1 := by
    rw [← star_eq_transpose]
    exact Unitary.star_mul_self_of_mem U.property
  have hU' : U.val * U.val.transpose = 1 := by
    rw [← star_eq_transpose]
    exact Unitary.mul_star_self_of_mem U.property
  calc
    orbitMatrix n U * orbitMatrix n U =
        U.val * (standardMatrix n * (U.val.transpose * U.val) * standardMatrix n) *
          U.val.transpose := by simp only [orbitMatrix, mul_assoc]
    _ = 1 := by rw [hU, mul_one, standardMatrix_square, mul_one, hU']

theorem orbitMatrix_trace (n : ℕ) (U : unitary (Matrix (Index n) (Index n) ℝ)) :
    (orbitMatrix n U).trace = 0 := by
  have hU : U.val.transpose * U.val = 1 := by
    rw [← star_eq_transpose]
    exact Unitary.star_mul_self_of_mem U.property
  rw [orbitMatrix, Matrix.trace_mul_comm, ← mul_assoc, hU, one_mul, standardMatrix_trace]

theorem continuous_orbitMatrix (n : ℕ) : Continuous (orbitMatrix n) :=
  (continuous_subtype_val.matrix_mul continuous_const).matrix_mul
    continuous_subtype_val.matrix_transpose

def locus (n : ℕ) : Set (Matrix (Index n) (Index n) ℝ) := Set.range (orbitMatrix n)

abbrev Space (n : ℕ) := locus n

def standard (n : ℕ) : Space n :=
  ⟨standardMatrix n, ⟨1, by simp [orbitMatrix]⟩⟩

instance compactSpace (n : ℕ) : CompactSpace (Space n) :=
  isCompact_iff_compactSpace.mp (isCompact_range (continuous_orbitMatrix n))

theorem transpose_eq {n : ℕ} (J : Space n) : J.val.transpose = J.val := by
  obtain ⟨U, hU⟩ := J.property
  rw [← hU]
  exact orbitMatrix_transpose n U

theorem square_eq {n : ℕ} (J : Space n) : J.val * J.val = 1 := by
  obtain ⟨U, hU⟩ := J.property
  rw [← hU]
  exact orbitMatrix_square n U

theorem trace_eq_zero {n : ℕ} (J : Space n) : J.val.trace = 0 := by
  obtain ⟨U, hU⟩ := J.property
  rw [← hU]
  exact orbitMatrix_trace n U

def toOrthogonal {n : ℕ} (J : Space n) : unitary (Matrix (Index n) (Index n) ℝ) :=
  ⟨J.val, by
    constructor <;> rw [star_eq_transpose, transpose_eq, square_eq]⟩

end Wikipedia.HomotopyGroupsOfSpheres.BalancedRealInvolutions
