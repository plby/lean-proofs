import Wikipedia.HomotopyGroupsOfSpheres.ComplexMatrixRealification
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! # Explicit unitary rotations between two equal complex coordinate blocks -/

noncomputable section

open scoped Matrix

namespace Wikipedia.HomotopyGroupsOfSpheres.ComplexUnitaryRotation

variable {N : Type*} [Fintype N] [DecidableEq N]

def matrix (U : unitary (Matrix N N ℂ)) (t : ℝ) : Matrix (N ⊕ N) (N ⊕ N) ℂ :=
  Matrix.fromBlocks ((Real.cos t : ℂ) • 1) (-(Real.sin t : ℂ) • U.val)
    ((Real.sin t : ℂ) • U.valᴴ) ((Real.cos t : ℂ) • 1)

theorem matrix_zero (U : unitary (Matrix N N ℂ)) : matrix U 0 = 1 := by
  simp [matrix, Matrix.fromBlocks_one]

theorem matrix_star (U : unitary (Matrix N N ℂ)) (t : ℝ) :
    (matrix U t)ᴴ = matrix U (-t) := by
  simp [matrix, Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_smul,
    -Complex.ofReal_cos, -Complex.ofReal_sin]

theorem matrix_mul (U : unitary (Matrix N N ℂ)) (t s : ℝ) :
    matrix U t * matrix U s = matrix U (t + s) := by
  have h₁ : U.valᴴ * U.val = 1 := U.property.1
  have h₂ : U.val * U.valᴴ = 1 := U.property.2
  simp only [matrix, Matrix.fromBlocks_multiply, smul_mul_assoc, mul_smul_comm,
    one_mul, mul_one, h₁, h₂, smul_smul, Real.cos_add, Real.sin_add,
    Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_mul]
  apply Matrix.fromBlocks_inj.mpr
  refine ⟨?_, ?_, ?_, ?_⟩ <;> module

theorem matrix_unitary (U : unitary (Matrix N N ℂ)) (t : ℝ) :
    matrix U t ∈ unitary (Matrix (N ⊕ N) (N ⊕ N) ℂ) := by
  constructor
  · change (matrix U t)ᴴ * matrix U t = 1
    rw [matrix_star, matrix_mul, neg_add_cancel, matrix_zero]
  · change matrix U t * (matrix U t)ᴴ = 1
    rw [matrix_star, matrix_mul, add_neg_cancel, matrix_zero]

def unitaryMap (U : unitary (Matrix N N ℂ)) (t : ℝ) :
    unitary (Matrix (N ⊕ N) (N ⊕ N) ℂ) :=
  ⟨matrix U t, matrix_unitary U t⟩

theorem continuous_matrix :
    Continuous (fun p : unitary (Matrix N N ℂ) × ℝ ↦ matrix p.1 p.2) := by
  have hU : Continuous (fun p : unitary (Matrix N N ℂ) × ℝ ↦ p.1.val) :=
    continuous_subtype_val.comp continuous_fst
  have hc : Continuous (fun p : unitary (Matrix N N ℂ) × ℝ ↦ (Real.cos p.2 : ℂ)) :=
    Complex.continuous_ofReal.comp (Real.continuous_cos.comp continuous_snd)
  have hs : Continuous (fun p : unitary (Matrix N N ℂ) × ℝ ↦ (Real.sin p.2 : ℂ)) :=
    Complex.continuous_ofReal.comp (Real.continuous_sin.comp continuous_snd)
  exact (hc.smul continuous_const).matrix_fromBlocks (hs.neg.smul hU)
    (hs.smul hU.matrix_conjTranspose) (hc.smul continuous_const)

theorem continuous_unitaryMap :
    Continuous (fun p : unitary (Matrix N N ℂ) × ℝ ↦ unitaryMap p.1 p.2) :=
  continuous_matrix.subtype_mk _

theorem unitaryMap_zero (U : unitary (Matrix N N ℂ)) : unitaryMap U 0 = 1 :=
  Subtype.ext (matrix_zero U)

theorem matrix_half_pi (U : unitary (Matrix N N ℂ)) :
    matrix U (Real.pi / 2) = Matrix.fromBlocks 0 (-U.val) U.valᴴ 0 := by
  simp [matrix]

theorem reference_endpoint (U V : unitary (Matrix N N ℂ)) :
    (matrix U (Real.pi / 2))ᴴ * matrix V (Real.pi / 2) =
      Matrix.fromBlocks (U.val * V.valᴴ) 0 0 (U.valᴴ * V.val) := by
  rw [matrix_half_pi, matrix_half_pi, Matrix.fromBlocks_conjTranspose,
    Matrix.fromBlocks_multiply]
  simp

end Wikipedia.HomotopyGroupsOfSpheres.ComplexUnitaryRotation
