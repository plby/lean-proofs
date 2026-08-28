import Wikipedia.HomotopyGroupsOfSpheres.ComplexMatrixRealExponential
import Wikipedia.NoExoticSixSphere.OrthogonalComplexStructures

/-! # Recovering a real symmetric involution from a minimum path's midpoint -/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres

namespace ImaginarySymmetricMatrices

variable {N : Type*} [Fintype N] [DecidableEq N]

theorem imaginary_map_im (B : Matrix N N ℂ) (hsym : B.transpose = B)
    (hskew : star B = -B) : imaginary (B.map Complex.im) = B := by
  apply Matrix.ext
  intro i j
  have hs : B j i = B i j := congrArg (fun C : Matrix N N ℂ ↦ C i j) hsym
  have hk : star (B j i) = -B i j := congrArg (fun C : Matrix N N ℂ ↦ C i j) hskew
  rw [hs] at hk
  have hr := congrArg Complex.re hk
  simp only [Complex.star_def, Complex.conj_re, Complex.neg_re] at hr
  have hz : (B i j).re = 0 := by linarith
  apply Complex.ext
  · simp [imaginary_apply, hz]
  · simp [imaginary_apply]

omit [Fintype N] [DecidableEq N] in
theorem map_im_transpose (B : Matrix N N ℂ) (hsym : B.transpose = B) :
    (B.map Complex.im).transpose = B.map Complex.im :=
  congrArg (fun C : Matrix N N ℂ ↦ C.map Complex.im) hsym

theorem map_im_square (B : Matrix N N ℂ) (hsym : B.transpose = B)
    (hskew : star B = -B) (hsq : B * B = -1) :
    B.map Complex.im * B.map Complex.im = 1 := by
  apply RealUnitaryMatrices.complexification_injective
  rw [map_one]
  apply neg_injective
  rw [← imaginary_mul, imaginary_map_im B hsym hskew]
  exact hsq

end ImaginarySymmetricMatrices

namespace ComplexMatrixRealRepresentation

open ImaginarySymmetricMatrices

variable {N : Type*} [Fintype N] [DecidableEq N]

theorem midpoint_skew (B : Matrix N N ℂ)
    (J : NoExoticSixSphere.OrthogonalComplexStructures.Space (2 * Fintype.card N))
    (hB : action B = J.val.val) : star B = -B := by
  apply action_injective
  have hn : action (-B) = -action B := representation.map_neg B
  rw [action_star, hn, hB]
  exact J.val.property

theorem midpoint_square (B : Matrix N N ℂ)
    (J : NoExoticSixSphere.OrthogonalComplexStructures.Space (2 * Fintype.card N))
    (hB : action B = J.val.val) : B * B = -1 := by
  apply action_injective
  have hn : action (-1 : Matrix N N ℂ) = -1 := by
    change representation (-1 : Matrix N N ℂ) = -(1 : RealSpace N →L[ℝ] RealSpace N)
    rw [map_neg, map_one]
  rw [action_mul, hn, hB]
  exact J.property

theorem recover_midpoint (B : QuaternionicSymmetricMatrices.Space N)
    (J : NoExoticSixSphere.OrthogonalComplexStructures.Space (2 * Fintype.card N))
    (hB : action B.val.val = J.val.val) :
    ∃ A : Matrix N N ℝ, A.transpose = A ∧ A * A = 1 ∧ imaginary A = B.val.val := by
  refine ⟨B.val.val.map Complex.im, map_im_transpose _ B.property, ?_, ?_⟩
  · exact map_im_square _ B.property (midpoint_skew _ J hB) (midpoint_square _ J hB)
  · exact imaginary_map_im _ B.property (midpoint_skew _ J hB)

end ComplexMatrixRealRepresentation

end Wikipedia.HomotopyGroupsOfSpheres
