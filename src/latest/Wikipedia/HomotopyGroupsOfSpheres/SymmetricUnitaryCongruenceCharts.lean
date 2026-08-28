import Wikipedia.HomotopyGroupsOfSpheres.SymmetricUnitaryFactorization
import Wikipedia.HomotopyGroupsOfSpheres.SymmetricUnitaryLocalLogarithm

/-! # Exponential charts at every symmetric determinant-one unitary matrix -/

noncomputable section

open scoped Matrix.Norms.Frobenius ContDiff
open Set

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices

variable {N : Type*} [Fintype N] [DecidableEq N]

theorem inverse_det_square (U : unitary (Matrix N N ℂ)) (hU : U.val.det ^ 2 = 1) :
    (U⁻¹).val.det ^ 2 = 1 := by
  have hm : (U⁻¹).val.det * U.val.det = 1 := by
    rw [← Matrix.det_mul]
    have h : (U⁻¹).val * U.val = 1 := congrArg Subtype.val (inv_mul_cancel U)
    rw [h, Matrix.det_one]
  calc
    (U⁻¹).val.det ^ 2 = (U⁻¹).val.det ^ 2 * U.val.det ^ 2 := by rw [hU, mul_one]
    _ = ((U⁻¹).val.det * U.val.det) ^ 2 := (mul_pow _ _ _).symm
    _ = 1 := by rw [hm, one_pow]

def congruenceHomeomorph (U : unitary (Matrix N N ℂ)) (hU : U.val.det ^ 2 = 1) :
    SpecialSpace N ≃ₜ SpecialSpace N where
  toFun := congruenceSpecial U hU
  invFun := congruenceSpecial U⁻¹ (inverse_det_square U hU)
  left_inv B := Subtype.ext (congruence_inv_cancel U B.val)
  right_inv B := by
    apply Subtype.ext
    change congruence U (congruence U⁻¹ B.val) = B.val
    rw [congruence_mul, mul_inv_cancel, congruence_one]
  continuous_toFun := continuous_congruenceSpecial (fun _ ↦ U) (fun _ ↦ hU) id
    continuous_const continuous_id
  continuous_invFun := continuous_congruenceSpecial (fun _ ↦ U⁻¹)
    (fun _ ↦ inverse_det_square U hU) id continuous_const continuous_id

namespace LocalLogarithm

open RealSymmetricMixing ImaginarySymmetricMatrices

abbrev Frame (N : Type*) [Fintype N] [DecidableEq N] :=
  {U : unitary (Matrix N N ℂ) // U.val.det ^ 2 = 1}

theorem exists_frame (B : SpecialSpace N) :
    ∃ U : Frame N, congruenceHomeomorph U.val U.property specialIdentity = B := by
  obtain ⟨U, hU, he⟩ := exists_special_unitary_congruence B
  exact ⟨⟨U, hU⟩, he⟩

def frame (B : SpecialSpace N) : Frame N := Classical.choose (exists_frame B)

theorem frame_center (B : SpecialSpace N) :
    congruenceHomeomorph (frame B).val (frame B).property specialIdentity = B :=
  Classical.choose_spec (exists_frame B)

def translation (B : SpecialSpace N) : SpecialSpace N ≃ₜ SpecialSpace N :=
  congruenceHomeomorph (frame B).val (frame B).property

theorem translation_identity (B : SpecialSpace N) : translation B specialIdentity = B :=
  frame_center B

theorem translation_symm_self (B : SpecialSpace N) :
    (translation B).symm B = specialIdentity := by
  calc
    (translation B).symm B = (translation B).symm (translation B specialIdentity) :=
      congrArg (translation B).symm (translation_identity B).symm
    _ = specialIdentity := (translation B).symm_apply_apply _

def atPoint (B : SpecialSpace N) : OpenPartialHomeomorph (SpecialSpace N) (DirectionSpace N) :=
  (translation B).symm.toOpenPartialHomeomorph.trans (chart N)

theorem mem_atPoint_source (B : SpecialSpace N) : B ∈ (atPoint B).source := by
  refine ⟨mem_univ B, ?_⟩
  change (translation B).symm B ∈ (chart N).source
  rw [translation_symm_self]
  exact identity_mem_source

theorem atPoint_apply (B C : SpecialSpace N) :
    atPoint B C = coordinates (matrix ((translation B).symm C)) := rfl

theorem atPoint_symm_apply (B : SpecialSpace N) (A : DirectionSpace N) :
    (atPoint B).symm A = translation B (exponential A) := rfl

theorem atPoint_self (B : SpecialSpace N) : atPoint B B = 0 := by
  change chart N ((translation B).symm B) = 0
  rw [translation_symm_self, chart_identity]

theorem zero_mem_atPoint_target (B : SpecialSpace N) :
    (0 : DirectionSpace N) ∈ (atPoint B).target := by
  refine ⟨zero_mem_target, mem_univ _⟩

theorem contDiff_exponential_matrix :
    ContDiff ℝ ∞ (fun A : DirectionSpace N ↦ matrix (exponential A)) := by
  have hi : ContDiff ℝ ∞ (fun A : DirectionSpace N ↦ imaginary A.val) :=
    finiteLinearMap_contDiff (directionMap (N := N))
  exact ComplexMatrixLocalLogarithm.contDiff_exp.comp hi

def transitionMatrix (B C : SpecialSpace N) (A : DirectionSpace N) : Matrix N N ℂ :=
  matrix ((translation C).symm (translation B (exponential A)))

theorem contDiff_transitionMatrix (B C : SpecialSpace N) :
    ContDiff ℝ ∞ (transitionMatrix B C) := by
  let U := (frame B).val.val
  let V := ((frame C).val⁻¹).val
  change ContDiff ℝ ∞ (fun A : DirectionSpace N ↦
    V * (U * matrix (exponential A) * U.transpose) * V.transpose)
  exact (contDiff_const.mul ((contDiff_const.mul contDiff_exponential_matrix).mul
    contDiff_const)).mul contDiff_const

theorem transition_mem_logarithm_target (B C : SpecialSpace N) (A : DirectionSpace N)
    (hA : A ∈ ((atPoint B).symm.trans (atPoint C)).source) :
    transitionMatrix B C A ∈ (ComplexMatrixLocalLogarithm.exponentialChart N).target := by
  have h := hA.2.2
  change matrix ((translation C).symm (translation B (exponential A))) ∈
    ComplexMatrixLocalLogarithm.domain N at h
  exact h.1

theorem contDiffOn_transition (B C : SpecialSpace N) :
    ContDiffOn ℝ ∞ ((atPoint B).symm.trans (atPoint C))
      ((atPoint B).symm.trans (atPoint C)).source := by
  have h : ContDiffOn ℝ ∞ (fun A ↦ coordinates (transitionMatrix B C A))
      ((atPoint B).symm.trans (atPoint C)).source :=
    (contDiffOn_coordinates (N := N)).comp (contDiff_transitionMatrix B C).contDiffOn
      (transition_mem_logarithm_target B C)
  exact h

end LocalLogarithm

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices
