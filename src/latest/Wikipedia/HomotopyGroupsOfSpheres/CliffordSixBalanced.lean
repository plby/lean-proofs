import Wikipedia.HomotopyGroupsOfSpheres.CliffordFiveHermitian
import Wikipedia.HomotopyGroupsOfSpheres.BalancedRealConjugation
import Wikipedia.HomotopyGroupsOfSpheres.MatrixBorder

/-!
# The actual rank-six balanced family from the Clifford involution

Adding one constant complex positive and one negative direction gives six
positive and six negative real directions. A fixed orthogonal change of
coordinates puts the pole at the standard involution used by the Bott map.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HomotopyGroupsOfSpheres.CliffordFiveHermitian

abbrev UnitSphere := Metric.sphere (0 : EuclideanSpace ℝ (Fin 5)) 1

theorem matrix_square_unit (v : UnitSphere) : matrix v.val * matrix v.val = 1 := by
  have hn : ∑ k, v.val k ^ 2 = 1 := by
    rw [← EuclideanSpace.real_norm_sq_eq, mem_sphere_zero_iff_norm.mp v.property]
    norm_num
  rw [matrix_square, hn, Complex.ofReal_one, one_smul]

def paddedMatrix (v : Coordinates) : Matrix (Fin 6) (Fin 6) ℂ :=
  MatrixBorder.border (-1) (MatrixBorder.border 1 (matrix v))

theorem paddedMatrix_hermitian (v : Coordinates) : (paddedMatrix v)ᴴ = paddedMatrix v := by
  have h : star (matrix v) = matrix v := matrix_hermitian v
  change star (paddedMatrix v) = paddedMatrix v
  simp only [paddedMatrix, MatrixBorder.star_border, star_neg, star_one, h]

theorem paddedMatrix_square (v : UnitSphere) : paddedMatrix v.val * paddedMatrix v.val = 1 := by
  rw [paddedMatrix, ← MatrixBorder.border_mul, ← MatrixBorder.border_mul, matrix_square_unit]
  norm_num [MatrixBorder.border_one]

theorem paddedMatrix_trace (v : Coordinates) : (paddedMatrix v).trace = 0 := by
  simp [paddedMatrix, MatrixBorder.border, Matrix.trace, Fin.sum_univ_succ, matrix]

theorem continuous_paddedMatrix : Continuous paddedMatrix :=
  (MatrixBorder.continuous_border (-1 : ℂ)).comp
    ((MatrixBorder.continuous_border (1 : ℂ)).comp continuous_matrix)

def rawBalanced : C(UnitSphere, BalancedRealInvolutions.Space 6) where
  toFun v := BalancedRealInvolutions.ofRelations 6
    (ComplexMatrixRealification.matrix (paddedMatrix v.val))
    (ComplexMatrixRealification.matrix_symmetric _ (paddedMatrix_hermitian v.val))
    (ComplexMatrixRealification.matrix_square _ (paddedMatrix_square v))
    (by rw [ComplexMatrixRealification.matrix_trace, paddedMatrix_trace]; simp)
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact ComplexMatrixRealification.continuous_matrix.comp
      (continuous_paddedMatrix.comp
        ((PiLp.continuous_ofLp 2 (fun _ : Fin 5 ↦ ℝ)).comp continuous_subtype_val))

theorem rawBalanced_val (v : UnitSphere) :
    (rawBalanced v).val = ComplexMatrixRealification.matrix (paddedMatrix v.val) := rfl

def pole : UnitSphere :=
  ⟨EuclideanSpace.basisFun (Fin 5) ℝ 0, mem_sphere_zero_iff_norm.mpr
    ((EuclideanSpace.basisFun (Fin 5) ℝ).orthonormal.1 0)⟩

theorem pole_val : (fun i ↦ pole.val i) = ![1, 0, 0, 0, 0] := by
  funext i
  fin_cases i <;> simp [pole, EuclideanSpace.basisFun_apply]

def poleFrame :
    unitary (Matrix (BalancedRealInvolutions.Index 6) (BalancedRealInvolutions.Index 6) ℝ) :=
  Classical.choose (rawBalanced pole).property

theorem poleFrame_conjugate :
    BalancedRealInvolutions.conjugate poleFrame (BalancedRealInvolutions.standard 6) =
      rawBalanced pole := by
  apply Subtype.ext
  exact Classical.choose_spec (rawBalanced pole).property

def balancedMap : C(UnitSphere, BalancedRealInvolutions.Space 6) :=
  (BalancedRealInvolutions.conjugationHomeomorph poleFrame⁻¹ : C(_, _)).comp rawBalanced

theorem balancedMap_pole : balancedMap pole = BalancedRealInvolutions.standard 6 := by
  change BalancedRealInvolutions.conjugate poleFrame⁻¹ (rawBalanced pole) = _
  rw [← poleFrame_conjugate, BalancedRealInvolutions.conjugate_inv_cancel]

theorem balancedMap_val (v : UnitSphere) :
    (balancedMap v).val = poleFrame⁻¹.val *
      ComplexMatrixRealification.matrix (paddedMatrix v.val) * poleFrame⁻¹.val.transpose := rfl

end Wikipedia.HomotopyGroupsOfSpheres.CliffordFiveHermitian
