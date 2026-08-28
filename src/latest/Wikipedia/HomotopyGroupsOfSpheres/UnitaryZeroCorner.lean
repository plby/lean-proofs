import Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary
import Mathlib.Data.Matrix.Block
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Explicit reduction of a unitary matrix with a zero corner block

For a unitary block matrix `[A B; C 0]`, the matrices
`[A - sin(t) BC, cos(t) B; cos(t) C, sin(t) 1]` remain unitary.
At a quarter turn this gives the actual reduced matrix `A - BC`.
-/

noncomputable section

open scoped Matrix unitInterval

namespace Wikipedia.HomotopyGroupsOfSpheres.UnitaryZeroCorner

variable {N M : Type*} [Fintype N] [DecidableEq N] [Fintype M] [DecidableEq M]

def deformation (A : Matrix N N ℂ) (B : Matrix N M ℂ) (C : Matrix M N ℂ)
    (s t : ℝ) : Matrix (N ⊕ M) (N ⊕ M) ℂ :=
  Matrix.fromBlocks (A - s • (B * C)) (t • B) (t • C) (s • 1)

theorem deformation_mul_star (A : Matrix N N ℂ) (B : Matrix N M ℂ)
    (C : Matrix M N ℂ) (hA : A * Aᴴ + B * Bᴴ = 1)
    (hAC : A * Cᴴ = 0) (hCA : C * Aᴴ = 0) (hC : C * Cᴴ = 1)
    (s t : ℝ) (hst : s ^ 2 + t ^ 2 = 1) :
    deformation A B C s t * star (deformation A B C s t) = 1 := by
  have hACB : A * (Cᴴ * Bᴴ) = 0 := by
    rw [← Matrix.mul_assoc, hAC, Matrix.zero_mul]
  have hCCB : C * (Cᴴ * Bᴴ) = Bᴴ := by
    rw [← Matrix.mul_assoc, hC, Matrix.one_mul]
  have hst' : s * s + t * t = 1 := by simpa only [pow_two] using hst
  change deformation A B C s t * (deformation A B C s t)ᴴ = 1
  rw [deformation, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
    ← Matrix.fromBlocks_one]
  apply Matrix.fromBlocks_inj.mpr
  simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, star_trivial,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_one]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, Matrix.mul_assoc, hACB, hCA, hCCB, Matrix.mul_zero, smul_zero,
      sub_zero, zero_sub, smul_neg, sub_neg_eq_add]
    rw [add_assoc, ← add_smul, hst', one_smul]
    exact hA
  · simp only [Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul,
      Matrix.mul_assoc, hAC, hC, Matrix.mul_one]
    rw [mul_comm s t]
    module
  · simp only [Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      ← Matrix.mul_assoc, hCA, hC, Matrix.one_mul, smul_zero]
    rw [mul_comm s t]
    module
  · simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hC, Matrix.mul_one]
    rw [← add_smul]
    have hts : t * t + s * s = 1 := by nlinarith [hst]
    rw [hts, one_smul]

theorem deformation_unitary (A : Matrix N N ℂ) (B : Matrix N M ℂ)
    (C : Matrix M N ℂ)
    (hU : Matrix.fromBlocks A B C 0 ∈ unitary (Matrix (N ⊕ M) (N ⊕ M) ℂ))
    (s t : ℝ) (hst : s ^ 2 + t ^ 2 = 1) :
    deformation A B C s t ∈ unitary (Matrix (N ⊕ M) (N ⊕ M) ℂ) := by
  have h := Unitary.mul_star_self_of_mem hU
  change Matrix.fromBlocks A B C 0 * (Matrix.fromBlocks A B C 0)ᴴ = 1 at h
  rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
    ← Matrix.fromBlocks_one] at h
  simp only [Matrix.conjTranspose_zero, Matrix.mul_zero, Matrix.zero_mul, add_zero] at h
  obtain ⟨hA, hAC, hCA, hC⟩ := Matrix.fromBlocks_inj.mp h
  have hr := deformation_mul_star A B C hA hAC hCA hC s t hst
  exact ⟨mul_eq_one_comm.mp hr, hr⟩

end Wikipedia.HomotopyGroupsOfSpheres.UnitaryZeroCorner
