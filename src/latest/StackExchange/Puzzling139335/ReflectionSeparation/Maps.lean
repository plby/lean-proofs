import StackExchange.Puzzling139335.SquareSymmetry.Basic

/-!
# The four reflections of the square

Each reflection is an affine isometry equivalence of the Euclidean plane.
The coordinate and fixed-line lemmas make these maps usable in separation
arguments without unfolding their constructions.
-/

open Set

namespace Puzzling139335.ReflectionSeparation

noncomputable section

/-- Reflection across the horizontal line through the square center. -/
def horizontal : Plane ≃ᵃⁱ[ℝ] Plane := SquareSymmetry.cornerFlip 3

/-- Reflection across the vertical line through the square center. -/
def vertical : Plane ≃ᵃⁱ[ℝ] Plane := SquareSymmetry.cornerFlip 1

private def diagonalPoint (p : Plane) : Plane := !₂[p 1, p 0]

private theorem diagonalPoint_involutive : Function.Involutive diagonalPoint := by
  intro p
  ext i
  fin_cases i <;> rfl

private theorem diagonalPoint_isometry : Isometry diagonalPoint := by
  apply isometry_iff_dist_eq.mpr
  intro p q
  apply (sq_eq_sq₀ dist_nonneg dist_nonneg).mp
  simp only [plane_dist_sq, diagonalPoint, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- Reflection across the diagonal `p 0 = p 1`. -/
def diagonal : Plane ≃ᵃⁱ[ℝ] Plane :=
  ({ toFun := diagonalPoint
     invFun := diagonalPoint
     left_inv := diagonalPoint_involutive
     right_inv := diagonalPoint_involutive
     isometry_toFun := diagonalPoint_isometry } : Plane ≃ᵢ Plane).toRealAffineIsometryEquiv

/-- Reflection across the diagonal `p 0 + p 1 = 1`. -/
def antiDiagonal : Plane ≃ᵃⁱ[ℝ] Plane :=
  diagonal.trans (SquareSymmetry.cornerFlip 2)

@[simp] theorem horizontal_apply_zero (p : Plane) : horizontal p 0 = p 0 := by
  norm_num [horizontal, SquareSymmetry.cornerFlipPoint, corner, Fin.ext_iff]

@[simp] theorem horizontal_apply_one (p : Plane) : horizontal p 1 = 1 - p 1 := by
  norm_num [horizontal, SquareSymmetry.cornerFlipPoint, corner, Fin.ext_iff]

@[simp] theorem vertical_apply_zero (p : Plane) : vertical p 0 = 1 - p 0 := by
  norm_num [vertical, SquareSymmetry.cornerFlipPoint, corner, Fin.ext_iff]

@[simp] theorem vertical_apply_one (p : Plane) : vertical p 1 = p 1 := by
  norm_num [vertical, SquareSymmetry.cornerFlipPoint, corner, Fin.ext_iff]

@[simp] theorem diagonal_apply_zero (p : Plane) : diagonal p 0 = p 1 := rfl

@[simp] theorem diagonal_apply_one (p : Plane) : diagonal p 1 = p 0 := rfl

@[simp] theorem antiDiagonal_apply_zero (p : Plane) : antiDiagonal p 0 = 1 - p 1 := by
  norm_num [antiDiagonal, SquareSymmetry.cornerFlipPoint, corner, Fin.ext_iff]

@[simp] theorem antiDiagonal_apply_one (p : Plane) : antiDiagonal p 1 = 1 - p 0 := by
  norm_num [antiDiagonal, SquareSymmetry.cornerFlipPoint, corner, Fin.ext_iff]

@[simp] theorem horizontal_involutive (p : Plane) : horizontal (horizontal p) = p :=
  SquareSymmetry.cornerFlip_involutive 3 p

@[simp] theorem vertical_involutive (p : Plane) : vertical (vertical p) = p :=
  SquareSymmetry.cornerFlip_involutive 1 p

@[simp] theorem diagonal_involutive (p : Plane) : diagonal (diagonal p) = p :=
  diagonalPoint_involutive p

@[simp] theorem antiDiagonal_involutive (p : Plane) : antiDiagonal (antiDiagonal p) = p := by
  ext i
  fin_cases i <;> simp

theorem horizontal_fixed {p : Plane} (hp : p 1 = (1 / 2 : ℝ)) : horizontal p = p := by
  ext i
  fin_cases i <;> norm_num [hp]

theorem vertical_fixed {p : Plane} (hp : p 0 = (1 / 2 : ℝ)) : vertical p = p := by
  ext i
  fin_cases i <;> norm_num [hp]

theorem diagonal_fixed {p : Plane} (hp : p 0 = p 1) : diagonal p = p := by
  ext i
  fin_cases i <;> simp [hp]

theorem antiDiagonal_fixed {p : Plane} (hp : p 0 + p 1 = 1) : antiDiagonal p = p := by
  ext i
  fin_cases i <;> simp <;> linarith

@[simp] theorem horizontal_center : horizontal squareCenter = squareCenter :=
  SquareSymmetry.cornerFlip_center 3

@[simp] theorem vertical_center : vertical squareCenter = squareCenter :=
  SquareSymmetry.cornerFlip_center 1

@[simp] theorem diagonal_center : diagonal squareCenter = squareCenter :=
  diagonal_fixed rfl

@[simp] theorem antiDiagonal_center : antiDiagonal squareCenter = squareCenter := by
  apply antiDiagonal_fixed
  norm_num [squareCenter]

@[simp] theorem horizontal_mem_unitSquare {p : Plane} :
    horizontal p ∈ unitSquare ↔ p ∈ unitSquare :=
  SquareSymmetry.cornerFlip_mem_unitSquare 3

@[simp] theorem vertical_mem_unitSquare {p : Plane} :
    vertical p ∈ unitSquare ↔ p ∈ unitSquare :=
  SquareSymmetry.cornerFlip_mem_unitSquare 1

@[simp] theorem diagonal_mem_unitSquare {p : Plane} :
    diagonal p ∈ unitSquare ↔ p ∈ unitSquare := by
  change (p 1 ∈ Icc (0 : ℝ) 1 ∧ p 0 ∈ Icc (0 : ℝ) 1) ↔
    (p 0 ∈ Icc (0 : ℝ) 1 ∧ p 1 ∈ Icc (0 : ℝ) 1)
  exact and_comm

@[simp] theorem antiDiagonal_mem_unitSquare {p : Plane} :
    antiDiagonal p ∈ unitSquare ↔ p ∈ unitSquare := by
  change SquareSymmetry.cornerFlip 2 (diagonal p) ∈ unitSquare ↔ p ∈ unitSquare
  rw [SquareSymmetry.cornerFlip_mem_unitSquare, diagonal_mem_unitSquare]

theorem horizontal_image_unitSquare : horizontal '' unitSquare = unitSquare :=
  SquareSymmetry.cornerFlip_image_unitSquare 3

theorem vertical_image_unitSquare : vertical '' unitSquare = unitSquare :=
  SquareSymmetry.cornerFlip_image_unitSquare 1

theorem diagonal_image_unitSquare : diagonal '' unitSquare = unitSquare := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact diagonal_mem_unitSquare.mpr hq
  · intro hp
    exact ⟨diagonal p, diagonal_mem_unitSquare.mpr hp, diagonal_involutive p⟩

theorem antiDiagonal_image_unitSquare : antiDiagonal '' unitSquare = unitSquare := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact antiDiagonal_mem_unitSquare.mpr hq
  · intro hp
    exact ⟨antiDiagonal p, antiDiagonal_mem_unitSquare.mpr hp, antiDiagonal_involutive p⟩

end

end Puzzling139335.ReflectionSeparation
