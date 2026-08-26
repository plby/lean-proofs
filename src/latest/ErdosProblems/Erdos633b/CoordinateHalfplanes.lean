import ErdosProblems.Erdos633b.Barycentric
import Mathlib.Analysis.Normed.Operator.Banach

/-! Topological interiors of nonconstant affine-coordinate halfplanes. -/

namespace Erdos633b.Triangle

noncomputable def coordForm (T : Triangle) (a b : ℝ) : Plane →ᵃ[ℝ] ℝ :=
  a • T.coord 1 + b • T.coord 2

theorem coordForm_apply (T : Triangle) (a b : ℝ) (p : Plane) :
    T.coordForm a b p = a * T.coord 1 p + b * T.coord 2 p := rfl

theorem coordForm_surjective (T : Triangle) (a b : ℝ) (h : a ≠ 0 ∨ b ≠ 0) :
    Function.Surjective (T.coordForm a b) := by
  intro r
  have h1 : (1 : Fin 3) ≠ 0 := by decide
  have h2 : (2 : Fin 3) ≠ 0 := by decide
  rcases h with ha | hb
  · refine ⟨T.latticeShift (r / a) 0 + T.points 0, ?_⟩
    simp only [coordForm_apply, coord_shift_one, coord_shift_two, coord_vertex,
      h1, h2, if_false, add_zero, mul_zero]
    calc
      a * (r / a) = r * (a / a) := by ring
      _ = r := by rw [div_self ha, mul_one]
  · refine ⟨T.latticeShift 0 (r / b) + T.points 0, ?_⟩
    simp only [coordForm_apply, coord_shift_one, coord_shift_two, coord_vertex,
      h1, h2, if_false, add_zero, mul_zero, zero_add]
    calc
      b * (r / b) = r * (b / b) := by ring
      _ = r := by rw [div_self hb, mul_one]

theorem interior_coordForm_le (T : Triangle) (a b c : ℝ) (h : a ≠ 0 ∨ b ≠ 0) :
    interior {p | T.coordForm a b p ≤ c} = {p | T.coordForm a b p < c} := by
  let f := T.coordForm a b
  have hf : Continuous f := f.continuous_of_finiteDimensional
  have ho := f.isOpenMap hf (T.coordForm_surjective a b h)
  have hi := ho.preimage_interior_eq_interior_preimage hf (Set.Iic c)
  change interior (f ⁻¹' Set.Iic c) = f ⁻¹' Set.Iio c
  simpa only [interior_Iic] using hi.symm

theorem interior_coordForm_ge (T : Triangle) (a b c : ℝ) (h : a ≠ 0 ∨ b ≠ 0) :
    interior {p | c ≤ T.coordForm a b p} = {p | c < T.coordForm a b p} := by
  let f := T.coordForm a b
  have hf : Continuous f := f.continuous_of_finiteDimensional
  have ho := f.isOpenMap hf (T.coordForm_surjective a b h)
  have hi := ho.preimage_interior_eq_interior_preimage hf (Set.Ici c)
  change interior (f ⁻¹' Set.Ici c) = f ⁻¹' Set.Ioi c
  simpa only [interior_Ici] using hi.symm

end Erdos633b.Triangle
