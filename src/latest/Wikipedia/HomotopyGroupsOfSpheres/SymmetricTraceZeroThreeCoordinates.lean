import Wikipedia.HomotopyGroupsOfSpheres.RealSymmetricMixing
import Mathlib.LinearAlgebra.Determinant

/-!
# Five explicit coordinates for real symmetric trace-zero three-by-three matrices

The two free diagonal entries and three off-diagonal entries form an actual
linear equivalence with real five-space. This is the model space already
used by the symmetric special-unitary charts.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HomotopyGroupsOfSpheres.RealSymmetricMixing

def threeMatrix (x : Fin 5 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![x 0, x 2, x 3; x 2, x 1, x 4; x 3, x 4, -x 0 - x 1]

theorem threeMatrix_mem (x : Fin 5 → ℝ) : threeMatrix x ∈ symmetricTraceZero (Fin 3) := by
  constructor
  · ext r s
    fin_cases r <;> fin_cases s <;> rfl
  · simp [threeMatrix, Matrix.trace_fin_three]

def threeDirectionLinear : (Fin 5 → ℝ) →ₗ[ℝ] DirectionSpace (Fin 3) where
  toFun x := ⟨threeMatrix x, threeMatrix_mem x⟩
  map_add' x y := by
    apply Subtype.ext
    ext r s
    fin_cases r <;> fin_cases s <;>
      simp [threeMatrix, Matrix.cons_val_two]
    ring
  map_smul' c x := by
    apply Subtype.ext
    ext r s
    fin_cases r <;> fin_cases s <;>
      simp [threeMatrix, Matrix.cons_val_two, mul_sub]

def threeCoordinates (A : DirectionSpace (Fin 3)) : Fin 5 → ℝ :=
  ![A.val 0 0, A.val 1 1, A.val 0 1, A.val 0 2, A.val 1 2]

theorem threeCoordinates_direction (x : Fin 5 → ℝ) :
    threeCoordinates (threeDirectionLinear x) = x := by
  funext r
  fin_cases r <;> simp [threeCoordinates, threeDirectionLinear, threeMatrix, Matrix.cons_val_two]

theorem threeDirection_coordinates (A : DirectionSpace (Fin 3)) :
    threeDirectionLinear (threeCoordinates A) = A := by
  have hs (r s : Fin 3) : A.val s r = A.val r s :=
    congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ ↦ M r s) A.property.1
  have ht : A.val 2 2 = -A.val 0 0 - A.val 1 1 := by
    have h := A.property.2
    rw [Matrix.trace_fin_three] at h
    linarith
  apply Subtype.ext
  ext r s
  fin_cases r <;> fin_cases s <;>
    simp [threeDirectionLinear, threeMatrix, threeCoordinates, Matrix.cons_val_two,
      hs 0 1, hs 0 2, hs 1 2, ht]

def threeDirectionEquiv : (Fin 5 → ℝ) ≃ₗ[ℝ] DirectionSpace (Fin 3) where
  __ := threeDirectionLinear
  invFun := threeCoordinates
  left_inv := threeCoordinates_direction
  right_inv := threeDirection_coordinates

theorem directionSpace_three_finrank : Module.finrank ℝ (DirectionSpace (Fin 3)) = 5 := by
  rw [← threeDirectionEquiv.finrank_eq]
  simp

end Wikipedia.HomotopyGroupsOfSpheres.RealSymmetricMixing
