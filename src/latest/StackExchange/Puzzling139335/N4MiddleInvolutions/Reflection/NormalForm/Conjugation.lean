import StackExchange.Puzzling139335.N4MiddleInvolutions.Reflection.NormalForm

/-!
# Transporting a reflection normal through an affine isometry

Conjugation by any affine isometry preserves the unit-normal reflection
formula.  The normal is transported by the inverse linear isometry, and
the offset is adjusted by the translation of the conjugating map.
-/

namespace Puzzling139335.N4MiddleInvolutions.Reflection

noncomputable section

open PlaneIsometries

/-- The real plane inner product is the coordinate dot product. -/
theorem inner_eq_coordinate_dot (p q : Plane) :
    inner ℝ p q = p 0 * q 0 + p 1 * q 1 := by
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_two, mul_comm]

/-- The normal of a reflection after conjugation by `f`. -/
def conjugateNormal (f : Plane ≃ᵃⁱ[ℝ] Plane) (ν : Plane) : Plane :=
  f.linearIsometryEquiv.symm ν

/-- The offset of a reflection after conjugation by `f`. -/
def conjugateOffset (f : Plane ≃ᵃⁱ[ℝ] Plane) (ν : Plane) (k : ℝ) : ℝ :=
  k - (ν 0 * (f 0) 0 + ν 1 * (f 0) 1)

/-- Inverse linear transport preserves the unit length of a normal. -/
theorem conjugateNormal_unit (f : Plane ≃ᵃⁱ[ℝ] Plane) (ν : Plane)
    (hunit : ν 0 ^ 2 + ν 1 ^ 2 = 1) :
    conjugateNormal f ν 0 ^ 2 + conjugateNormal f ν 1 ^ 2 = 1 := by
  have h := f.linearIsometryEquiv.symm.inner_map_map ν ν
  simp only [inner_eq_coordinate_dot, ← pow_two] at h
  exact h.trans hunit

/-- The normal coordinate relative to the axis is unchanged by the
corresponding inverse transport of normal and offset. -/
theorem conjugate_normal_coordinate (f : Plane ≃ᵃⁱ[ℝ] Plane)
    (ν : Plane) (k : ℝ) (p : Plane) :
    ν 0 * (f p) 0 + ν 1 * (f p) 1 - k =
      conjugateNormal f ν 0 * p 0 + conjugateNormal f ν 1 * p 1 -
        conjugateOffset f ν k := by
  have h := f.linearIsometryEquiv.inner_map_map (conjugateNormal f ν) p
  simp only [conjugateNormal, LinearIsometryEquiv.apply_symm_apply,
    inner_eq_coordinate_dot] at h
  rw [affine_apply_eq_linear_add f p]
  simp only [PiLp.add_apply, conjugateNormal, conjugateOffset]
  linear_combination h

private theorem affine_map_sub_smul (f : Plane ≃ᵃⁱ[ℝ] Plane)
    (p v : Plane) (a : ℝ) :
    f (p - a • v) = f p - a • f.linearIsometryEquiv v := by
  rw [affine_apply_eq_linear_add f (p - a • v), map_sub, map_smul,
    affine_apply_eq_linear_add f p]
  abel

/-- An affine conjugate of a map in reflection normal form has the
transported normal and offset.  The coordinate identity itself does not
require the normal to have unit length. -/
theorem conjugate_normal_form (e f : Plane ≃ᵃⁱ[ℝ] Plane)
    (ν : Plane) (k : ℝ)
    (hform : ∀ p, e p = p - (2 * ((ν 0 * p 0 + ν 1 * p 1) - k)) • ν) :
    ∀ p, ((f.trans e).trans f.symm) p = p -
      (2 * ((conjugateNormal f ν 0 * p 0 + conjugateNormal f ν 1 * p 1) -
        conjugateOffset f ν k)) • conjugateNormal f ν := by
  intro p
  apply f.injective
  change f (f.symm (e (f p))) = _
  rw [f.apply_symm_apply, hform, affine_map_sub_smul]
  simp only [conjugateNormal, LinearIsometryEquiv.apply_symm_apply]
  rw [conjugate_normal_coordinate f ν k p]
  rfl

/-- Conjugation preserves the existence of a real unit-normal reflection
formula, without any orientation restriction on the conjugating map. -/
theorem exists_unit_normal_form_conjugate (e f : Plane ≃ᵃⁱ[ℝ] Plane)
    (ν : Plane) (k : ℝ) (hunit : ν 0 ^ 2 + ν 1 ^ 2 = 1)
    (hform : ∀ p, e p = p - (2 * ((ν 0 * p 0 + ν 1 * p 1) - k)) • ν) :
    ∃ (μ : Plane) (k' : ℝ), μ 0 ^ 2 + μ 1 ^ 2 = 1 ∧
      ∀ p, ((f.trans e).trans f.symm) p =
        p - (2 * ((μ 0 * p 0 + μ 1 * p 1) - k')) • μ := by
  exact ⟨conjugateNormal f ν, conjugateOffset f ν k, conjugateNormal_unit f ν hunit,
    conjugate_normal_form e f ν k hform⟩

/-- An ordinary reflection in complex axis form has a unit-normal formula
after conjugation by any affine isometry. -/
theorem exists_unit_normal_form_conjugate_of_axis_form
    (e f : Plane ≃ᵃⁱ[ℝ] Plane) (c : ℂ) (u : Circle)
    (hform : ∀ p, complexEquiv (e p) =
      c + (u : ℂ) * (starRingEnd ℂ) ((complexEquiv p - c) / (u : ℂ))) :
    ∃ (μ : Plane) (k : ℝ), μ 0 ^ 2 + μ 1 ^ 2 = 1 ∧
      ∀ p, ((f.trans e).trans f.symm) p =
        p - (2 * ((μ 0 * p 0 + μ 1 * p 1) - k)) • μ := by
  obtain ⟨ν, k, hunit, he⟩ := exists_unit_normal_form e c u hform
  exact exists_unit_normal_form_conjugate e f ν k hunit he

end

end Puzzling139335.N4MiddleInvolutions.Reflection
