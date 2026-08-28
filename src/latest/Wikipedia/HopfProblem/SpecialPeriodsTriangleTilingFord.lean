import Wikipedia.HopfProblem.SpecialPeriodsTriangleTilingCircularDouble
import Wikipedia.HopfProblem.SpecialPeriodsTriangleTilingFordCut

/-!
# Interior-disjointness of the actual Ford translates

The two halves of the strict Ford polygon are transferred to the
circularly doubled polygon.  A reduced word returning a generic point
can only be the identity or one of the two nonidentity powers of the
first generator; the explicit unit-circle inequalities exclude the
latter.  An open-set argument removes the temporary cut from the
statement.  Together with the previously proved covering theorem this
gives a genuine fundamental polygon for the actual triangle action.
-/

noncomputable section

open Set UpperHalfPlane
open scoped MatrixGroups Topology

namespace Wikipedia.HopfProblem.SpecialPeriods.Triangle

local instance : MulAction TriangleGroup ℍ := triangleGeometricAction

private theorem first_generator_inv_eq_sq : triangleGenerator₁⁻¹ = triangleGenerator₁ ^ 2 := by
  apply inv_eq_of_mul_eq_one_right
  simpa only [← pow_succ'] using triangleGenerator₁_cube

private theorem first_generator_inv_apply (z : ℍ) :
    triangleGeometricRepresentation triangleGenerator₁⁻¹ z = (generatorOneSL ^ 2) • z := by
  rw [first_generator_inv_eq_sq, map_pow, triangleGeometricRepresentation_generator₁,
    generatorOnePerm_pow_apply]

private theorem right_mem_circularDouble (z : ℍ) (hz : z ∈ fordInterior)
    (hx : -(1 / 2) < z.re) :
    triangleGeometricRepresentation triangleGenerator₁⁻¹ z ∈ circularDoubleInterior := by
  rw [first_generator_inv_apply]
  exact fordInterior_right_mem_circularDoubleInterior z hz hx

private theorem eq_one_of_fordInterior_mem_off_axis (g : TriangleGroup) {z : ℍ}
    (hz : z ∈ fordInterior) (hgz : triangleGeometricRepresentation g z ∈ fordInterior)
    (hx : z.re ≠ -(1 / 2))
    (hgx : (triangleGeometricRepresentation g z).re ≠ -(1 / 2)) : g = 1 := by
  rcases lt_or_gt_of_ne hx with hx | hx <;> rcases lt_or_gt_of_ne hgx with hgx | hgx
  · exact eq_one_of_circularDoubleInterior_mem g
      (fordInterior_left_mem_circularDoubleInterior z hz hx)
      (fordInterior_left_mem_circularDoubleInterior _ hgz hgx)
  · have hm : triangleGeometricRepresentation (triangleGenerator₁⁻¹ * g) z ∈
        circularDoubleInterior := by
      change (triangleGenerator₁⁻¹ * g) • z ∈ circularDoubleInterior
      simpa only [mul_smul, triangleGeometricAction_smul] using
        right_mem_circularDouble _ hgz hgx
    have he := eq_one_of_circularDoubleInterior_mem (triangleGenerator₁⁻¹ * g)
      (fordInterior_left_mem_circularDoubleInterior z hz hx) hm
    have hg : g = triangleGenerator₁ := (inv_mul_eq_one.mp he).symm
    rw [hg, triangleGeometricRepresentation_generator₁_apply] at hgz
    exact False.elim (generatorOne_not_mem_fordInterior z hz hgz)
  · have hm : triangleGeometricRepresentation (g * triangleGenerator₁)
        (triangleGeometricRepresentation triangleGenerator₁⁻¹ z) ∈ circularDoubleInterior := by
      change (g * triangleGenerator₁) • (triangleGenerator₁⁻¹ • z) ∈ circularDoubleInterior
      rw [mul_smul, smul_inv_smul, triangleGeometricAction_smul]
      exact fordInterior_left_mem_circularDoubleInterior _ hgz hgx
    have he := eq_one_of_circularDoubleInterior_mem (g * triangleGenerator₁)
      (right_mem_circularDouble z hz hx) hm
    have hg : g = triangleGenerator₁⁻¹ := eq_inv_of_mul_eq_one_left he
    apply False.elim
    apply generatorOne_sq_not_mem_fordInterior z hz
    rw [hg, first_generator_inv_apply] at hgz
    exact hgz
  · have hm : triangleGeometricRepresentation (triangleGenerator₁⁻¹ * g * triangleGenerator₁)
        (triangleGeometricRepresentation triangleGenerator₁⁻¹ z) ∈ circularDoubleInterior := by
      change (triangleGenerator₁⁻¹ * g * triangleGenerator₁) •
        (triangleGenerator₁⁻¹ • z) ∈ circularDoubleInterior
      rw [mul_smul, smul_inv_smul, mul_smul]
      simpa only [triangleGeometricAction_smul] using right_mem_circularDouble _ hgz hgx
    have he := eq_one_of_circularDoubleInterior_mem
      (triangleGenerator₁⁻¹ * g * triangleGenerator₁) (right_mem_circularDouble z hz hx) hm
    have he' := congrArg
      (fun h : TriangleGroup => triangleGenerator₁ * h * triangleGenerator₁⁻¹) he
    simpa only [mul_assoc, mul_inv_cancel, inv_mul_cancel, one_mul, mul_one,
      mul_inv_cancel_left] using he'

/-- An interior point of the actual Ford region can return to that
interior only under the identity triangle transformation. -/
theorem eq_one_of_fordInterior_mem (g : TriangleGroup) {z : ℍ}
    (hz : z ∈ fordInterior) (hgz : triangleGeometricRepresentation g z ∈ fordInterior) :
    g = 1 := by
  let U : Set ℍ := fordInterior ∩ (triangleGeometricRepresentation g) ⁻¹' fordInterior
  have hU : IsOpen U := fordInterior_isOpen.inter
    (fordInterior_isOpen.preimage (triangleGeometricBiholomorph g).continuous)
  have hne : U.Nonempty := ⟨z, hz, hgz⟩
  obtain ⟨w, hw, hx, hgx⟩ := exists_mem_open_ne_re_and_image_re
    (triangleGeometricBiholomorph g).toHomeomorph (-(1 / 2)) U hU hne
  exact eq_one_of_fordInterior_mem_off_axis g hw.1 hw.2 hx hgx

theorem eq_one_of_fordInterior_eq (g : TriangleGroup) {z w : ℍ}
    (hz : z ∈ fordInterior) (hw : w ∈ fordInterior)
    (hzw : triangleGeometricRepresentation g z = w) : g = 1 :=
  eq_one_of_fordInterior_mem g hz (hzw ▸ hw)

/-- The strict Ford translates are pairwise disjoint for the actual
faithful representation of `C₃ * C₄`. -/
theorem fordInterior_translates_pairwiseDisjoint :
    Pairwise fun g h : TriangleGroup =>
      Disjoint (triangleGeometricRepresentation g '' fordInterior)
        (triangleGeometricRepresentation h '' fordInterior) := by
  intro g h hgh
  apply Set.disjoint_left.mpr
  rintro w ⟨z, hz, rfl⟩ ⟨u, hu, he⟩
  have hreturn : triangleGeometricRepresentation (h⁻¹ * g) z = u := by
    rw [map_mul, map_inv]
    change (triangleGeometricRepresentation h).symm (triangleGeometricRepresentation g z) = u
    rw [← he]
    exact (triangleGeometricRepresentation h).symm_apply_apply u
  have hid := eq_one_of_fordInterior_eq (h⁻¹ * g) hz hu hreturn
  exact hgh ((inv_mul_eq_one.mp hid).symm)

theorem interior_fordRegion_translate (g : TriangleGroup) :
    interior (triangleGeometricRepresentation g '' fordRegion) =
      triangleGeometricRepresentation g '' fordInterior := by
  have h := (triangleGeometricBiholomorph g).toHomeomorph.image_interior fordRegion
  have hh : ((triangleGeometricBiholomorph g).toHomeomorph : ℍ → ℍ) =
      triangleGeometricRepresentation g := rfl
  rw [hh, interior_fordRegion] at h
  exact h.symm

/-- This statement concerns the topological interiors of the translates
of the original closed polygon, not merely a chosen smaller subset. -/
theorem fordRegion_translates_interiors_pairwiseDisjoint :
    Pairwise fun g h : TriangleGroup =>
      Disjoint (interior (triangleGeometricRepresentation g '' fordRegion))
        (interior (triangleGeometricRepresentation h '' fordRegion)) := by
  intro g h hgh
  rw [interior_fordRegion_translate, interior_fordRegion_translate]
  exact fordInterior_translates_pairwiseDisjoint hgh

/-- Covering and interior-disjointness for the actual Ford polygon. -/
theorem fordRegion_fundamental_polygon :
    (⋃ g : TriangleGroup, triangleGeometricRepresentation g '' fordRegion) = univ ∧
      Pairwise fun g h : TriangleGroup =>
        Disjoint (interior (triangleGeometricRepresentation g '' fordRegion))
          (interior (triangleGeometricRepresentation h '' fordRegion)) :=
  ⟨triangle_translates_fordRegion_cover, fordRegion_translates_interiors_pairwiseDisjoint⟩

end Wikipedia.HopfProblem.SpecialPeriods.Triangle
