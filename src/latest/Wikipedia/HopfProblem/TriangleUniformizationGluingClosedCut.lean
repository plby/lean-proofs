import Wikipedia.HopfProblem.TriangleUniformizationGluingClosedSectors
import Wikipedia.HopfProblem.TriangleUniformizationGluingClosedCutFirst
import Wikipedia.HopfProblem.TriangleUniformizationGluingClosedCutSecond
import Wikipedia.HopfProblem.TriangleUniformizationGluingClosedCutReflection

/-!
# The closed circular cut of the Ford polygon

The closed cyclic-sector polygon is the actual double of the half-Ford
triangle across its circular side.  This file also records how the two
closed halves of the Ford polygon move into that circular double.
Boundary return statements use the concrete circle reflection.
The supporting files prove that each of the five nonidentity elliptic
powers, whenever it returns a point to the closed double, has exactly
that reflected value.
-/

noncomputable section

open Set UpperHalfPlane
open scoped MatrixGroups Topology

namespace Wikipedia.HopfProblem.SpecialPeriods.Triangle

/-- The closed Ford polygon satisfies the closed order-four sector inequalities. -/
theorem fordRegion_subset_closedSecondSector : fordRegion ⊆ closedSecondSector := by
  intro z hz
  refine ⟨hz.1, ?_⟩
  have hn : 1 ≤ Complex.normSq ((z : ℂ) + 1) := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [hz.2.2.1]
  have hprod : 0 ≤ stripRight * (z.re - stripLeft) :=
    mul_nonneg stripRight_pos.le (sub_nonneg.mpr hz.1)
  have hs : stripRight ^ 2 ≤ ‖(z : ℂ) - (stripLeft : ℂ)‖ ^ 2 := by
    rw [Complex.sq_norm]
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.ofReal_re,
      Complex.sub_im, Complex.ofReal_im, sub_zero, Complex.add_re,
      Complex.one_re, Complex.add_im, Complex.one_im, add_zero,
      UpperHalfPlane.coe_re, UpperHalfPlane.coe_im] at hn ⊢
    have hleft : stripLeft = -1 - stripRight := by linarith [stripLeft_add_stripRight]
    rw [hleft] at hprod ⊢
    nlinarith [stripRight_sq]
  exact (sq_le_sq₀ stripRight_pos.le (norm_nonneg _)).mp hs

/-- The closed half-Ford triangle lies in the closed circular double. -/
theorem halfFordRegion_subset_circularDoubleRegion :
    halfFordRegion ⊆ circularDoubleRegion := by
  intro z hz
  exact ⟨⟨hz.2, hz.1.2.2.2⟩, fordRegion_subset_closedSecondSector hz.1⟩

/-- Outside the reflecting circle, the closed double is exactly the
original closed half-Ford triangle. -/
theorem circularDoubleRegion_and_norm_add_one_iff_halfFordRegion (z : ℍ) :
    z ∈ circularDoubleRegion ∧ 1 ≤ ‖(z : ℂ) + 1‖ ↔ z ∈ halfFordRegion := by
  constructor
  · rintro ⟨hz, hn⟩
    refine ⟨⟨hz.2.1, ?_, hn, hz.1.2⟩, hz.1.1⟩
    linarith [hz.1.1, stripRight_pos]
  · intro hz
    exact ⟨halfFordRegion_subset_circularDoubleRegion hz, hz.1.2.2.1⟩

theorem halfFordRegion_eq_circularDoubleRegion_inter :
    halfFordRegion = circularDoubleRegion ∩ {z | 1 ≤ ‖(z : ℂ) + 1‖} := by
  ext z
  exact (circularDoubleRegion_and_norm_add_one_iff_halfFordRegion z).symm

theorem fordRegion_left_mem_circularDoubleRegion (z : ℍ) (hz : z ∈ fordRegion)
    (hx : z.re ≤ -(1 / 2)) : z ∈ circularDoubleRegion :=
  halfFordRegion_subset_circularDoubleRegion ⟨hz, hx⟩

/-- The reflected half is precisely the inside-circle part of the
closed cyclic-sector polygon. -/
theorem circleReflection_image_halfFordRegion :
    circleReflection '' halfFordRegion =
      circularDoubleRegion ∩ {z | ‖(z : ℂ) + 1‖ ≤ 1} := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    refine ⟨circleReflection_mapsTo_circularDoubleRegion
      (halfFordRegion_subset_circularDoubleRegion hw), ?_⟩
    change ‖(circleReflection w : ℂ) + 1‖ ≤ 1
    rw [circleReflection_add_one_norm]
    exact (div_le_one (norm_pos_iff.mpr (denominatorOne_ne_zero w))).mpr hw.1.2.2.1
  · rintro ⟨hz, hn⟩
    refine ⟨circleReflection z, ?_, circleReflection_involutive z⟩
    apply (circularDoubleRegion_and_norm_add_one_iff_halfFordRegion (circleReflection z)).mp
    refine ⟨circleReflection_mapsTo_circularDoubleRegion hz, ?_⟩
    rw [circleReflection_add_one_norm]
    exact (one_le_div (norm_pos_iff.mpr (denominatorOne_ne_zero z))).mpr hn

/-- The actual closed double is obtained by reflecting the half-Ford
triangle in its circular side. -/
theorem circularDoubleRegion_eq_halfFordRegion_union_circle :
    circularDoubleRegion = halfFordRegion ∪ circleReflection '' halfFordRegion := by
  rw [circleReflection_image_halfFordRegion, halfFordRegion_eq_circularDoubleRegion_inter]
  ext z
  change z ∈ circularDoubleRegion ↔
    ((z ∈ circularDoubleRegion ∧ 1 ≤ ‖(z : ℂ) + 1‖) ∨
      (z ∈ circularDoubleRegion ∧ ‖(z : ℂ) + 1‖ ≤ 1))
  constructor
  · intro hz
    rcases le_total 1 ‖(z : ℂ) + 1‖ with hn | hn
    · exact Or.inl ⟨hz, hn⟩
    · exact Or.inr ⟨hz, hn⟩
  · rintro (hz | hz) <;> exact hz.1

/-- The two closed halves intersect exactly on their reflecting circle. -/
theorem halfFordRegion_inter_circleReflection_image :
    halfFordRegion ∩ circleReflection '' halfFordRegion =
      circularDoubleRegion ∩ {z | ‖(z : ℂ) + 1‖ = 1} := by
  rw [circleReflection_image_halfFordRegion, halfFordRegion_eq_circularDoubleRegion_inter]
  ext z
  change ((z ∈ circularDoubleRegion ∧ 1 ≤ ‖(z : ℂ) + 1‖) ∧
      (z ∈ circularDoubleRegion ∧ ‖(z : ℂ) + 1‖ ≤ 1)) ↔
    (z ∈ circularDoubleRegion ∧ ‖(z : ℂ) + 1‖ = 1)
  constructor
  · rintro ⟨⟨hz, hge⟩, ⟨_, hle⟩⟩
    exact ⟨hz, le_antisymm hle hge⟩
  · rintro ⟨hz, hn⟩
    exact ⟨⟨hz, hn.ge⟩, ⟨hz, hn.le⟩⟩

/-- If both a point and its circular reflection lie in the original
closed half, then the reflection fixes the point. -/
theorem circleReflection_eq_self_of_halfFordRegion_mem (z : ℍ)
    (hz : z ∈ halfFordRegion) (hcz : circleReflection z ∈ halfFordRegion) :
    circleReflection z = z := by
  have hn : 1 ≤ ‖(circleReflection z : ℂ) + 1‖ := hcz.1.2.2.1
  rw [circleReflection_add_one_norm] at hn
  have hle := (one_le_div (norm_pos_iff.mpr (denominatorOne_ne_zero z))).mp hn
  exact (circleReflection_fixed_iff z).mpr (le_antisymm hle hz.1.2.2.1)

theorem generatorOne_inv_reflections (z : ℍ) :
    generatorOneSL⁻¹ • z = circleReflection (rightReflection z) := by
  have h : generatorOneSL • circleReflection (rightReflection z) = z := by
    rw [generatorOne_reflections, circleReflection_involutive, rightReflection_involutive]
  simpa only [inv_smul_smul] using congrArg (fun w : ℍ => generatorOneSL⁻¹ • w) h.symm

theorem generatorOne_inv_smul_eq_sq (z : ℍ) :
    generatorOneSL⁻¹ • z = (generatorOneSL ^ 2) • z := by
  rw [generatorOne_inv_reflections, generatorOne_sq_reflections]

/-- The right closed half of the Ford polygon is moved into the
circular double by the square of the first generator. -/
theorem fordRegion_right_mem_circularDoubleRegion (z : ℍ) (hz : z ∈ fordRegion)
    (hx : -(1 / 2) ≤ z.re) :
    (generatorOneSL ^ 2) • z ∈ circularDoubleRegion := by
  rw [generatorOne_sq_reflections]
  apply circleReflection_mapsTo_circularDoubleRegion
  apply halfFordRegion_subset_circularDoubleRegion
  refine ⟨rightReflection_mapsTo_fordRegion hz, ?_⟩
  change (rightReflection z).re ≤ -(1 / 2)
  rw [rightReflection_re]
  linarith

theorem fordRegion_right_inv_mem_circularDoubleRegion (z : ℍ) (hz : z ∈ fordRegion)
    (hx : -(1 / 2) ≤ z.re) : generatorOneSL⁻¹ • z ∈ circularDoubleRegion := by
  rw [generatorOne_inv_smul_eq_sq]
  exact fordRegion_right_mem_circularDoubleRegion z hz hx

/-- Every closed Ford point is already in the double or is moved there
by the indicated side-pairing matrix. -/
theorem fordRegion_mem_or_sq_mem_circularDoubleRegion (z : ℍ) (hz : z ∈ fordRegion) :
    z ∈ circularDoubleRegion ∨ (generatorOneSL ^ 2) • z ∈ circularDoubleRegion := by
  rcases le_total z.re (-(1 / 2)) with hx | hx
  · exact Or.inl (fordRegion_left_mem_circularDoubleRegion z hz hx)
  · exact Or.inr (fordRegion_right_mem_circularDoubleRegion z hz hx)

end Wikipedia.HopfProblem.SpecialPeriods.Triangle
