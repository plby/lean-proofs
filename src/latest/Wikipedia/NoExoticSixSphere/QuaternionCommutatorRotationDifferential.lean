import Wikipedia.NoExoticSixSphere.QuaternionCommutatorColumnDifferential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.Module

/-!
# Derivatives of the actual conjugated diagonal block at the quarter-turn midpoint
-/

noncomputable section

namespace NoExoticSixSphere.QuaternionCommutatorRotationDifferential

open QuaternionCommutatorColumns

local notation "ℍ" => Quaternion ℝ

theorem cos_sq_mid : Real.cos (Real.pi / 4) ^ 2 = 1 / 2 := by
  rw [Real.cos_pi_div_four, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

theorem sin_sq_mid : Real.sin (Real.pi / 4) ^ 2 = 1 / 2 := by
  rw [Real.sin_pi_div_four, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

theorem cos_sin_mid : Real.cos (Real.pi / 4) * Real.sin (Real.pi / 4) = 1 / 2 := by
  rw [Real.sin_pi_div_four, ← Real.cos_pi_div_four, ← pow_two, cos_sq_mid]

theorem hasDerivAt_cos_sq_mid :
    HasDerivAt (fun θ : ℝ ↦ Real.cos θ ^ 2) (-1) (Real.pi / 4) := by
  convert! (Real.hasDerivAt_cos (Real.pi / 4)).pow 2 using 1
  norm_num
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

theorem hasDerivAt_sin_sq_mid :
    HasDerivAt (fun θ : ℝ ↦ Real.sin θ ^ 2) 1 (Real.pi / 4) := by
  convert! (Real.hasDerivAt_sin (Real.pi / 4)).pow 2 using 1
  norm_num
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

theorem hasDerivAt_cos_sin_mid :
    HasDerivAt (fun θ : ℝ ↦ Real.cos θ * Real.sin θ) 0 (Real.pi / 4) := by
  convert! (Real.hasDerivAt_cos (Real.pi / 4)).mul
    (Real.hasDerivAt_sin (Real.pi / 4)) using 1
  nlinarith [cos_sq_mid, sin_sq_mid]

theorem diagonalZero_smul (c s : ℝ) (r : ℍ) :
    diagonalZero c s r = (c ^ 2) • (1 : ℍ) + (s ^ 2) • r := by
  simp only [diagonalZero, ← Quaternion.coe_mul_eq_smul, mul_one]

theorem offDiagonal_smul (c s : ℝ) (r : ℍ) :
    offDiagonal c s r = (c * s) • (1 - r) := Quaternion.coe_mul_eq_smul _ _

theorem diagonalOne_smul (c s : ℝ) (r : ℍ) :
    diagonalOne c s r = (s ^ 2) • (1 : ℍ) + (c ^ 2) • r := by
  simp only [diagonalOne, ← Quaternion.coe_mul_eq_smul, mul_one]

theorem midpoint_entries :
    diagonalZero (Real.cos (Real.pi / 4)) (Real.sin (Real.pi / 4)) (-1) = 0 ∧
    offDiagonal (Real.cos (Real.pi / 4)) (Real.sin (Real.pi / 4)) (-1) = 1 ∧
    diagonalOne (Real.cos (Real.pi / 4)) (Real.sin (Real.pi / 4)) (-1) = 0 := by
  rw [diagonalZero_smul, offDiagonal_smul, diagonalOne_smul,
    cos_sq_mid, sin_sq_mid, cos_sin_mid]
  constructor
  · simp
  constructor
  · simp only [sub_neg_eq_add, smul_add, ← add_smul]
    norm_num
  · simp

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {θ : E → ℝ} {r : E → ℍ} {θ' : E →L[ℝ] ℝ} {r' : E →L[ℝ] ℍ} {x : E}

theorem hasFDerivAt_diagonalZero (hθ : HasFDerivAt θ θ' x) (hr : HasFDerivAt r r' x)
    (hθ₀ : θ x = Real.pi / 4) (hr₀ : r x = -1) :
    HasFDerivAt (fun y ↦ diagonalZero (Real.cos (θ y)) (Real.sin (θ y)) (r y))
      (((-2 : ℝ) • θ').smulRight (1 : ℍ) + (1 / 2 : ℝ) • r') x := by
  have hc := hasDerivAt_cos_sq_mid.comp_hasFDerivAt_of_eq x hθ hθ₀.symm
  have hs := hasDerivAt_sin_sq_mid.comp_hasFDerivAt_of_eq x hθ hθ₀.symm
  have h := (hc.smul_const (1 : ℍ)).add (hs.smul hr)
  simp only [Function.comp_apply, hθ₀, hr₀, sin_sq_mid] at h
  simp only [diagonalZero_smul]
  convert! h using 1 <;> try rfl
  ext v : 1
  simp
  module

theorem hasFDerivAt_offDiagonal (hθ : HasFDerivAt θ θ' x) (hr : HasFDerivAt r r' x)
    (hθ₀ : θ x = Real.pi / 4) (hr₀ : r x = -1) :
    HasFDerivAt (fun y ↦ offDiagonal (Real.cos (θ y)) (Real.sin (θ y)) (r y))
      ((-1 / 2 : ℝ) • r') x := by
  have hc := hasDerivAt_cos_sin_mid.comp_hasFDerivAt_of_eq x hθ hθ₀.symm
  have h := hc.smul ((hasFDerivAt_const (1 : ℍ) x).sub hr)
  simp only [Function.comp_apply, hθ₀, hr₀, cos_sin_mid] at h
  simp only [offDiagonal_smul]
  convert! h using 1 <;> try rfl
  ext v : 1
  simp
  module

theorem hasFDerivAt_diagonalOne (hθ : HasFDerivAt θ θ' x) (hr : HasFDerivAt r r' x)
    (hθ₀ : θ x = Real.pi / 4) (hr₀ : r x = -1) :
    HasFDerivAt (fun y ↦ diagonalOne (Real.cos (θ y)) (Real.sin (θ y)) (r y))
      (((2 : ℝ) • θ').smulRight (1 : ℍ) + (1 / 2 : ℝ) • r') x := by
  have hc := hasDerivAt_cos_sq_mid.comp_hasFDerivAt_of_eq x hθ hθ₀.symm
  have hs := hasDerivAt_sin_sq_mid.comp_hasFDerivAt_of_eq x hθ hθ₀.symm
  have h := (hs.smul_const (1 : ℍ)).add (hc.smul hr)
  simp only [Function.comp_apply, hθ₀, hr₀, cos_sq_mid] at h
  simp only [diagonalOne_smul]
  convert! h using 1 <;> try rfl
  ext v : 1
  simp
  module

end NoExoticSixSphere.QuaternionCommutatorRotationDifferential
