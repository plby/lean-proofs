import Wikipedia.HopfProblem.EllipticHigherHomologyNormData
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyExteriorLatticeMatrices

/-!
# Exact integral lattices for the third-homology Wang columns

These are integer calculations for the two columns obtained from the
finite-cover comparison.  The parameter `c` records the actual shear of
the existing surface marking when this file is applied to singular
homology.  No parity or vanishing of that parameter is imposed here.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.EllipticCapKernelWang

open Elliptic PeriodTorusHigherHomologyExterior

/-- The two third-homology columns, including the retained surface shear. -/
def topWangMatrix : Kind → ℤ → Matrix (Fin 4) (Fin 2) ℤ
  | .three, c => !![0, 3; 0, -1; 0, 2; 3, -3 * c]
  | .four, c => !![0, -2; 0, 1; 0, -1; 4, -2 * c]

theorem topWangMatrix_mulVec_three (c : ℤ) (a : Fin 2 → ℤ) :
    topWangMatrix .three c *ᵥ a =
      ![3 * a 1, -a 1, 2 * a 1, 3 * a 0 - 3 * c * a 1] := by
  ext i
  fin_cases i <;> simp [topWangMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  ring

theorem topWangMatrix_mulVec_four (c : ℤ) (a : Fin 2 → ℤ) :
    topWangMatrix .four c *ᵥ a =
      ![-2 * a 1, a 1, -a 1, 4 * a 0 - 2 * c * a 1] := by
  ext i
  fin_cases i <;> simp [topWangMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  ring

/-- The two columns are independent over the integers for either value of the shear. -/
theorem topWangMatrix_injective (j : Kind) (c : ℤ) :
    Function.Injective (topWangMatrix j c).mulVecLin := by
  intro a b hab
  change topWangMatrix j c *ᵥ a = topWangMatrix j c *ᵥ b at hab
  cases j with
  | three =>
    rw [topWangMatrix_mulVec_three, topWangMatrix_mulVec_three] at hab
    have h₁ := congrFun hab (1 : Fin 4)
    change -a 1 = -b 1 at h₁
    have h₁ := neg_injective h₁
    have h₃ := congrFun hab (3 : Fin 4)
    change 3 * a 0 - 3 * c * a 1 = 3 * b 0 - 3 * c * b 1 at h₃
    rw [h₁] at h₃
    ext i
    fin_cases i
    · change a 0 = b 0
      linarith only [h₃]
    · exact h₁
  | four =>
    rw [topWangMatrix_mulVec_four, topWangMatrix_mulVec_four] at hab
    have h₁ := congrFun hab (1 : Fin 4)
    change a 1 = b 1 at h₁
    have h₃ := congrFun hab (3 : Fin 4)
    change 4 * a 0 - 2 * c * a 1 = 4 * b 0 - 2 * c * b 1 at h₃
    rw [h₁] at h₃
    ext i
    fin_cases i
    · change a 0 = b 0
      linarith only [h₃]
    · exact h₁

/-- Exact membership in the order-three image, with its integral divisibility condition. -/
theorem topWangMatrix_mem_range_three (c : ℤ) (v : Lattice) :
    v ∈ LinearMap.range (topWangMatrix .three c).mulVecLin ↔
      v 0 = -3 * v 1 ∧ v 2 = -2 * v 1 ∧ (3 : ℤ) ∣ v 3 := by
  constructor
  · rintro ⟨a, rfl⟩
    change (topWangMatrix .three c *ᵥ a) 0 = -3 * (topWangMatrix .three c *ᵥ a) 1 ∧
      (topWangMatrix .three c *ᵥ a) 2 = -2 * (topWangMatrix .three c *ᵥ a) 1 ∧
      (3 : ℤ) ∣ (topWangMatrix .three c *ᵥ a) 3
    rw [topWangMatrix_mulVec_three]
    change 3 * a 1 = -3 * -a 1 ∧ 2 * a 1 = -2 * -a 1 ∧
      (3 : ℤ) ∣ 3 * a 0 - 3 * c * a 1
    refine ⟨by ring, by ring, a 0 - c * a 1, ?_⟩
    ring
  · rintro ⟨h₀, h₂, k, h₃⟩
    refine ⟨![k - c * v 1, -v 1], ?_⟩
    change topWangMatrix .three c *ᵥ ![k - c * v 1, -v 1] = v
    rw [topWangMatrix_mulVec_three]
    ext i
    fin_cases i
    · change 3 * -v 1 = v 0
      linarith only [h₀]
    · change - -v 1 = v 1
      exact neg_neg _
    · change 2 * -v 1 = v 2
      linarith only [h₂]
    · change 3 * (k - c * v 1) - 3 * c * -v 1 = v 3
      linear_combination -h₃

/-- The order-four image keeps the genuine parity-sensitive shear correction. -/
theorem topWangMatrix_mem_range_four (c : ℤ) (v : Lattice) :
    v ∈ LinearMap.range (topWangMatrix .four c).mulVecLin ↔
      v 0 = -2 * v 1 ∧ v 2 = -v 1 ∧ (4 : ℤ) ∣ v 3 + 2 * c * v 1 := by
  constructor
  · rintro ⟨a, rfl⟩
    change (topWangMatrix .four c *ᵥ a) 0 = -2 * (topWangMatrix .four c *ᵥ a) 1 ∧
      (topWangMatrix .four c *ᵥ a) 2 = -(topWangMatrix .four c *ᵥ a) 1 ∧
      (4 : ℤ) ∣ (topWangMatrix .four c *ᵥ a) 3 + 2 * c * (topWangMatrix .four c *ᵥ a) 1
    rw [topWangMatrix_mulVec_four]
    change -2 * a 1 = -2 * a 1 ∧ -a 1 = -a 1 ∧
      (4 : ℤ) ∣ (4 * a 0 - 2 * c * a 1) + 2 * c * a 1
    refine ⟨rfl, rfl, a 0, ?_⟩
    ring
  · rintro ⟨h₀, h₂, k, h₃⟩
    refine ⟨![k, v 1], ?_⟩
    change topWangMatrix .four c *ᵥ ![k, v 1] = v
    rw [topWangMatrix_mulVec_four]
    ext i
    fin_cases i
    · exact h₀.symm
    · rfl
    · exact h₂.symm
    · change 4 * k - 2 * c * v 1 = v 3
      linear_combination -h₃

/-- The complete integral invariant lattice of the original order-three cube. -/
theorem cubeA₁_fixed_iff (v : Lattice) :
    cubeA₁ *ᵥ v = v ↔ v 0 = -3 * v 1 ∧ v 2 = -2 * v 1 := by
  constructor
  · intro h
    have h₁ := congrFun h (1 : Fin 4)
    have h₂ := congrFun h (2 : Fin 4)
    simp [cubeA₁_eq, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h₁ h₂
    constructor <;> omega
  · rintro ⟨h₀, h₂⟩
    ext i
    fin_cases i <;>
      simp [cubeA₁_eq, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, h₀, h₂] <;> ring

/-- The complete integral invariant lattice of the original order-four cube. -/
theorem cubeA₂_fixed_iff (v : Lattice) :
    cubeA₂ *ᵥ v = v ↔ v 0 = -2 * v 1 ∧ v 2 = -v 1 := by
  constructor
  · intro h
    have h₁ := congrFun h (1 : Fin 4)
    have h₂ := congrFun h (2 : Fin 4)
    simp [cubeA₂_eq, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h₁ h₂
    constructor <;> omega
  · rintro ⟨h₀, h₂⟩
    ext i
    fin_cases i <;>
      simp [cubeA₂_eq, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, h₀, h₂] <;> ring

/-- In order three the image is the invariant lattice with top coordinate divisible by three. -/
theorem topWangMatrix_mem_range_three_iff_fixed (c : ℤ) (v : Lattice) :
    v ∈ LinearMap.range (topWangMatrix .three c).mulVecLin ↔
      cubeA₁ *ᵥ v = v ∧ (3 : ℤ) ∣ v 3 := by
  rw [topWangMatrix_mem_range_three, cubeA₁_fixed_iff, and_assoc]

/-- In order four the precise sheared residue is imposed on the invariant lattice. -/
theorem topWangMatrix_mem_range_four_iff_fixed (c : ℤ) (v : Lattice) :
    v ∈ LinearMap.range (topWangMatrix .four c).mulVecLin ↔
      cubeA₂ *ᵥ v = v ∧ (4 : ℤ) ∣ v 3 + 2 * c * v 1 := by
  rw [topWangMatrix_mem_range_four, cubeA₂_fixed_iff, and_assoc]

end Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.EllipticCapKernelWang
