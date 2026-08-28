import Wikipedia.HomotopyGroupsOfSpheres.CliffordSixBalanced
import Wikipedia.HomotopyGroupsOfSpheres.ComplexUnitaryRotation

/-! # The explicit unitary off-diagonal Clifford block and its frame endpoint -/

noncomputable section

open scoped Matrix

namespace Wikipedia.HomotopyGroupsOfSpheres.CliffordFiveHermitian

abbrev EquatorCoordinates := Fin 4 → ℝ

abbrev EquatorSphere := Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1

def offDiagonal (q : EquatorCoordinates) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(q 1 : ℂ) + (q 0 : ℂ) * Complex.I, (q 3 : ℂ) + (q 2 : ℂ) * Complex.I;
     (q 3 : ℂ) - (q 2 : ℂ) * Complex.I, -(q 1 : ℂ) + (q 0 : ℂ) * Complex.I]

theorem offDiagonal_star_mul (q : EquatorCoordinates) :
    (offDiagonal q)ᴴ * offDiagonal q =
      ((∑ k, q k ^ 2 : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  have h3 : (2 : Fin 3).succ = (3 : Fin 4) := rfl
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    norm_num [offDiagonal, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three,
      pow_two, Complex.mul_re, Complex.mul_im, h3] <;> ring

theorem offDiagonal_mul_star (q : EquatorCoordinates) :
    offDiagonal q * (offDiagonal q)ᴴ =
      ((∑ k, q k ^ 2 : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  have h3 : (2 : Fin 3).succ = (3 : Fin 4) := rfl
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    norm_num [offDiagonal, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three,
      pow_two, Complex.mul_re, Complex.mul_im, h3] <;> ring

theorem offDiagonal_unitary (q : EquatorSphere) :
    offDiagonal q.val ∈ unitary (Matrix (Fin 2) (Fin 2) ℂ) := by
  have hq : ∑ k, q.val k ^ 2 = 1 := by
    rw [← EuclideanSpace.real_norm_sq_eq, mem_sphere_zero_iff_norm.mp q.property]
    norm_num
  constructor
  · change (offDiagonal q.val)ᴴ * offDiagonal q.val = 1
    rw [offDiagonal_star_mul, hq, Complex.ofReal_one, one_smul]
  · change offDiagonal q.val * (offDiagonal q.val)ᴴ = 1
    rw [offDiagonal_mul_star, hq, Complex.ofReal_one, one_smul]

def offDiagonalUnitary (q : EquatorSphere) : unitary (Matrix (Fin 2) (Fin 2) ℂ) :=
  ⟨offDiagonal q.val, offDiagonal_unitary q⟩

theorem continuous_offDiagonal : Continuous offDiagonal := by
  apply _root_.continuous_matrix
  intro i j
  fin_cases i <;> fin_cases j <;> simp only [offDiagonal] <;> fun_prop

theorem continuous_offDiagonalUnitary : Continuous offDiagonalUnitary := by
  apply Continuous.subtype_mk
  exact continuous_offDiagonal.comp
    ((PiLp.continuous_ofLp 2 (fun _ : Fin 4 ↦ ℝ)).comp continuous_subtype_val)

def equatorPole : EquatorSphere :=
  ⟨EuclideanSpace.basisFun (Fin 4) ℝ 0, mem_sphere_zero_iff_norm.mpr
    ((EuclideanSpace.basisFun (Fin 4) ℝ).orthonormal.1 0)⟩

theorem offDiagonal_equatorPole :
    offDiagonal equatorPole.val = Complex.I • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    norm_num [offDiagonal, equatorPole, EuclideanSpace.basisFun_apply,
      Complex.mul_re, Complex.mul_im] <;> decide

def boundaryUnitary (q : EquatorSphere) : unitary (Matrix (Fin 2) (Fin 2) ℂ) :=
  offDiagonalUnitary equatorPole * (offDiagonalUnitary q)⁻¹

theorem boundaryUnitary_val (q : EquatorSphere) :
    (boundaryUnitary q).val =
      !![(q.val 0 : ℂ) + (q.val 1 : ℂ) * Complex.I,
          -(q.val 2 : ℂ) + (q.val 3 : ℂ) * Complex.I;
         (q.val 2 : ℂ) + (q.val 3 : ℂ) * Complex.I,
          (q.val 0 : ℂ) - (q.val 1 : ℂ) * Complex.I] := by
  change offDiagonal equatorPole.val * (offDiagonal q.val)ᴴ = _
  rw [offDiagonal_equatorPole, smul_mul_assoc, one_mul]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    norm_num [offDiagonal, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im]

theorem boundaryUnitary_equatorPole : boundaryUnitary equatorPole = 1 :=
  mul_inv_cancel _

theorem boundaryUnitary_det (q : EquatorSphere) : (boundaryUnitary q).val.det = 1 := by
  have hq : ∑ k, q.val k ^ 2 = 1 := by
    rw [← EuclideanSpace.real_norm_sq_eq, mem_sphere_zero_iff_norm.mp q.property]
    norm_num
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hq
  change q.val 0 ^ 2 + (q.val 1 ^ 2 + (q.val 2 ^ 2 + q.val 3 ^ 2)) = 1 at hq
  rw [boundaryUnitary_val]
  apply Complex.ext <;>
    norm_num [Matrix.det_fin_two, Complex.mul_re, Complex.mul_im] <;> nlinarith [hq]

theorem continuous_boundaryUnitary : Continuous boundaryUnitary :=
  continuous_const.mul continuous_offDiagonalUnitary.inv

end Wikipedia.HomotopyGroupsOfSpheres.CliffordFiveHermitian
