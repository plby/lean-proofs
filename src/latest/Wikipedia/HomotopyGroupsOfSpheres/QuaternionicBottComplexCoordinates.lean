import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSchurPivot
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicComplexPair

/-! # Complex coordinate formulas for the entire Bott parameter family -/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicBottMatrix

open QuaternionicComplexPlane QuaternionicSymmetricMatrices

local notation "ℍ" => Quaternion ℝ

theorem matrix_complex_split (a b c : ℝ) (B : Space (Fin 3)) (r s : Fin 3) :
    matrix a b c B r s = ((if r = s then (⟨a, b⟩ : ℂ) else 0) : ℍ) +
      embed (c • B.val.val r s) := by
  rw [matrix_apply]
  by_cases h : r = s
  · simp only [if_pos h, coeComplex_mk, embed_real_smul]
  · simp only [if_neg h, smul_zero, zero_add, embed_real_smul]

theorem complexPart_matrix (a b c : ℝ) (B : Space (Fin 3)) (r s : Fin 3) :
    complexPart (matrix a b c B r s) = if r = s then (⟨a, b⟩ : ℂ) else 0 := by
  rw [matrix_complex_split]
  by_cases h : r = s
  · simp only [if_pos h, complexPart_add, complexPart_coeComplex, complexPart_embed, add_zero]
  · simp only [if_neg h, complexPart_add, complexPart_embed, add_zero]
    rfl

theorem coordinate_matrix (a b c : ℝ) (B : Space (Fin 3)) (r s : Fin 3) :
    coordinate (matrix a b c B r s) = c • B.val.val r s := by
  rw [matrix_complex_split]
  by_cases h : r = s
  · simp only [if_pos h, coordinate_add, coordinate_coeComplex, coordinate_embed, zero_add]
  · simp only [if_neg h, coordinate_add, coordinate_embed]
    change 0 + c • B.val.val r s = c • B.val.val r s
    exact zero_add _

def angleComplex (s t : ℝ) : ℂ := ⟨Real.cos s, Real.sin s * Real.cos t⟩
def angleReal (s t : ℝ) : ℝ := Real.sin s * Real.sin t

theorem angle_norm (s t : ℝ) : Complex.normSq (angleComplex s t) + angleReal s t ^ 2 = 1 := by
  simp only [angleComplex, Complex.normSq_apply, angleReal]
  calc
    _ = Real.cos s ^ 2 + Real.sin s ^ 2 * (Real.cos t ^ 2 + Real.sin t ^ 2) := by ring
    _ = 1 := by rw [Real.cos_sq_add_sin_sq, mul_one, Real.cos_sq_add_sin_sq]

theorem complexPart_rotation (s t : ℝ) (B : Space (Fin 3)) (r q : Fin 3) :
    complexPart ((rotation s t B).val r q) = if r = q then angleComplex s t else 0 := by
  rw [rotation_val, complexPart_matrix]
  rfl

theorem coordinate_rotation (s t : ℝ) (B : Space (Fin 3)) (r q : Fin 3) :
    coordinate ((rotation s t B).val r q) = (angleReal s t : ℂ) * B.val.val r q := by
  rw [rotation_val, coordinate_matrix]
  exact Complex.real_smul

theorem scalarRotation_split (s t : ℝ) :
    scalarRotation s t = (angleComplex s t : ℍ) + embed (angleReal s t : ℂ) := by
  rw [angleComplex, coeComplex_mk, embed_ofReal]
  rfl

theorem scalarRotation_complexPart (s t : ℝ) :
    complexPart (scalarRotation s t) = angleComplex s t := by
  rw [scalarRotation_split, complexPart_add, complexPart_coeComplex, complexPart_embed, add_zero]

theorem scalarRotation_coordinate (s t : ℝ) :
    coordinate (scalarRotation s t) = (angleReal s t : ℂ) := by
  rw [scalarRotation_split, coordinate_add, coordinate_coeComplex, coordinate_embed, zero_add]

theorem referenceSquare_complexPart (s t : ℝ) : complexPart (referenceSquare s t) =
    (angleReal s t : ℂ) ^ 2 - angleComplex s t ^ 2 := by
  rw [referenceSquare, complexPart_neg, complexPart_mul,
    scalarRotation_complexPart, scalarRotation_coordinate]
  have hc : star (angleReal s t : ℂ) = (angleReal s t : ℂ) := by simp
  rw [hc]
  ring

theorem referenceSquare_coordinate (s t : ℝ) : coordinate (referenceSquare s t) =
    -(angleReal s t : ℂ) * (angleComplex s t + star (angleComplex s t)) := by
  rw [referenceSquare, coordinate_neg, coordinate_mul,
    scalarRotation_complexPart, scalarRotation_coordinate]
  ring

theorem referenceSquare_coordinate_real (s t : ℝ) : coordinate (referenceSquare s t) =
    ((-2 * Real.cos s * angleReal s t : ℝ) : ℂ) := by
  rw [referenceSquare_coordinate]
  apply Complex.ext <;>
    simp only [angleComplex, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
      Complex.add_re, Complex.add_im, Complex.star_def, Complex.conj_re, Complex.conj_im,
      Complex.ofReal_re, Complex.ofReal_im] <;> ring

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicBottMatrix
