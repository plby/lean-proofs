import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicRealRepresentation
import Wikipedia.NoExoticSixSphere.HilbertSchmidt

/-!
# The real Hilbert–Schmidt norm of a quaternionic matrix

The faithful real representation has squared Hilbert–Schmidt norm equal to
four times the sum of squared quaternionic entry norms. The factor four is
proved by using the actual four-dimensional orthonormal basis of each
quaternionic coordinate.
-/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns

open NoExoticSixSphere.GLOrthonormalization NoExoticSixSphere.HilbertSchmidt

local notation "ℍ" => Quaternion ℝ

theorem squareNorm_eq_sum_basis {d : ℕ} {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (Vector d)) (A : Vector d →L[ℝ] Vector d) :
    squareNorm A = ∑ i, ‖A (b i)‖ ^ 2 := by
  rw [squareNorm, innerForm_eq_trace, LinearMap.trace_eq_sum_inner _ b]
  apply Finset.sum_congr rfl
  intro i _
  change inner ℝ (b i) (A.adjoint (A (b i))) = ‖A (b i)‖ ^ 2
  rw [ContinuousLinearMap.adjoint_inner_right, real_inner_self_eq_norm_sq]

def quaternionScalarBasis : OrthonormalBasis (Fin 4) ℝ ℍ :=
  (EuclideanSpace.basisFun (Fin 4) ℝ).map Quaternion.linearIsometryEquivTuple.symm

def quaternionVectorBasis (n : ℕ) :
    OrthonormalBasis ((_a : Fin (n + 1)) × Fin 4) ℝ (QuaternionSpace n) :=
  Pi.orthonormalBasis (fun _ : Fin (n + 1) => quaternionScalarBasis)

def quaternionRealBasis (n : ℕ) :
    OrthonormalBasis ((_a : Fin (n + 1)) × Fin 4) ℝ (Vector (4 * n + 4)) :=
  (quaternionVectorBasis n).map (quaternionCoordinates n)

theorem realAction_basis_norm_sq (n : ℕ)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℍ) (a : Fin (n + 1)) (k : Fin 4) :
    ‖realAction n A (quaternionRealBasis n ⟨a, k⟩)‖ ^ 2 = ∑ b, ‖A b a‖ ^ 2 := by
  simp only [quaternionRealBasis, OrthonormalBasis.map_apply, realAction_apply,
    (quaternionCoordinates n).symm_apply_apply, (quaternionCoordinates n).norm_map,
    quaternionVectorBasis, Pi.orthonormalBasis_apply, PiLp.ofLp_single, Matrix.mulVec_single,
    PiLp.norm_sq_eq_of_L2]
  apply Finset.sum_congr rfl
  intro b _
  change ‖A b a * quaternionScalarBasis k‖ ^ 2 = ‖A b a‖ ^ 2
  rw [norm_mul, quaternionScalarBasis.orthonormal.norm_eq_one k, mul_one]

/-- The four real directions in each quaternionic column account for the factor four. -/
theorem squareNorm_realAction (n : ℕ)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℍ) :
    squareNorm (realAction n A) = 4 * ∑ a, ∑ b, ‖A b a‖ ^ 2 := by
  rw [squareNorm_eq_sum_basis (quaternionRealBasis n)]
  rw [Fintype.sum_sigma]
  simp_rw [realAction_basis_norm_sq]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    ← Finset.mul_sum]
  norm_num

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns
