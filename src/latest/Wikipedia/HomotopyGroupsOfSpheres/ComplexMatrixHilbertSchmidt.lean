import Wikipedia.HomotopyGroupsOfSpheres.ComplexMatrixRealRepresentation
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicHilbertSchmidt
import Wikipedia.NoExoticSixSphere.OrthogonalCommutator

/-!
# The real Hilbert--Schmidt norm of a complex matrix

Each complex coordinate contributes two real orthonormal directions.
Consequently the squared Hilbert--Schmidt norm of the real action is
twice the sum of squared complex entry norms. The same factor applies
to the actual operator commutator.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HomotopyGroupsOfSpheres.ComplexMatrixRealRepresentation

open NoExoticSixSphere.HilbertSchmidt

variable {N : Type*} [Fintype N] [DecidableEq N]

def scalarBasis : OrthonormalBasis (Fin 2) ℝ ℂ :=
  (stdOrthonormalBasis ℝ ℂ).reindex (finCongr Complex.finrank_real_complex)

def vectorBasis (N : Type*) [Fintype N] :
    OrthonormalBasis ((_a : N) × Fin 2) ℝ (ComplexSpace N) :=
  Pi.orthonormalBasis (fun _ : N ↦ scalarBasis)

def realBasis (N : Type*) [Fintype N] :
    OrthonormalBasis ((_a : N) × Fin 2) ℝ (RealSpace N) :=
  (vectorBasis N).map (coordinates N)

theorem action_toLp (A : Matrix N N ℂ) (v : N → ℂ) :
    action A (coordinates N (WithLp.toLp 2 v)) =
      coordinates N (WithLp.toLp 2 (A *ᵥ v)) := by
  rw [action_apply, (coordinates N).symm_apply_apply, Matrix.toEuclideanCLM_toLp]

theorem action_basis_norm_sq (A : Matrix N N ℂ) (a : N) (k : Fin 2) :
    ‖action A (realBasis N ⟨a, k⟩)‖ ^ 2 = ∑ b, ‖A b a‖ ^ 2 := by
  simp only [realBasis, OrthonormalBasis.map_apply, vectorBasis, Pi.orthonormalBasis_apply]
  change ‖action A (coordinates N (WithLp.toLp 2 (Pi.single a (scalarBasis k))))‖ ^ 2 = _
  rw [action_toLp, (coordinates N).norm_map, PiLp.norm_sq_eq_of_L2, Matrix.mulVec_single]
  apply Finset.sum_congr rfl
  intro b _
  change ‖A b a * scalarBasis k‖ ^ 2 = ‖A b a‖ ^ 2
  rw [norm_mul, scalarBasis.orthonormal.norm_eq_one k, mul_one]

theorem squareNorm_action (A : Matrix N N ℂ) :
    squareNorm (action A) = 2 * ImaginarySymmetricMatrices.squareNorm A := by
  rw [QuaternionicColumns.squareNorm_eq_sum_basis (realBasis N), Fintype.sum_sigma]
  simp_rw [action_basis_norm_sq]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    ← Finset.mul_sum, Complex.sq_norm]
  rw [ImaginarySymmetricMatrices.squareNorm, Finset.sum_comm]
  norm_num

theorem action_commutator (A B : Matrix N N ℂ) :
    NoExoticSixSphere.OrthogonalCommutator.commutator (action A) (action B) =
      action (ImaginarySymmetricMatrices.commutator A B) := by
  change representation A * representation B - representation B * representation A =
    representation (A * B - B * A)
  rw [map_sub, map_mul, map_mul]

theorem squareNorm_action_commutator (A B : Matrix N N ℂ) :
    squareNorm (NoExoticSixSphere.OrthogonalCommutator.commutator (action A) (action B)) =
      2 * ImaginarySymmetricMatrices.squareNorm (ImaginarySymmetricMatrices.commutator A B) := by
  rw [action_commutator, squareNorm_action]

theorem squareNorm_action_imaginary (A : Matrix N N ℝ) :
    squareNorm (action (ImaginarySymmetricMatrices.imaginary A)) =
      2 * RealMatrixSquareNorm.squareNorm A := by
  rw [squareNorm_action, ImaginarySymmetricMatrices.squareNorm_imaginary]

end Wikipedia.HomotopyGroupsOfSpheres.ComplexMatrixRealRepresentation
