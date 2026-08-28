import Wikipedia.HopfProblem.SpecialPeriodsTriangleTilingReflections
import Wikipedia.HopfProblem.SpecialPeriodsTriangleTilingFordGeometry
import Wikipedia.HopfProblem.SpecialPeriodsTriangleInterior

/-!
# The two concrete halves of the Ford polygon

The left closed half has the source's open triangle as its exact
topological interior.  The identity and the vertical reflection fold
this same half into the full Ford polygon, with a closed two-piece cover
and disjoint open halves.  All sets and maps are subsets and
homeomorphisms of the actual upper half-plane.
-/

noncomputable section

open Set UpperHalfPlane
open scoped Topology

namespace Wikipedia.HopfProblem.SpecialPeriods.Triangle

/-- The closed left half of the Ford polygon. -/
def halfFordRegion : Set ℍ := fordRegion ∩ {z | z.re ≤ -(1 / 2)}

/-- The strict left half of the Ford polygon. -/
def halfFordInterior : Set ℍ := fordInterior ∩ {z | z.re < -(1 / 2)}

theorem halfFordRegion_isClosed : IsClosed halfFordRegion :=
  fordRegion_closed.inter (isClosed_le continuous_re continuous_const)

theorem halfFordInterior_isOpen : IsOpen halfFordInterior :=
  fordInterior_isOpen.inter (isOpen_lt continuous_re continuous_const)

theorem halfFordRegion_subset_fordRegion : halfFordRegion ⊆ fordRegion :=
  inter_subset_left

theorem halfFordInterior_subset_fordInterior : halfFordInterior ⊆ fordInterior :=
  inter_subset_left

theorem halfFordInterior_subset_halfFordRegion : halfFordInterior ⊆ halfFordRegion := by
  intro z hz
  exact ⟨fordInterior_subset_fordRegion hz.1, (show z.re < -(1 / 2) from hz.2).le⟩

/-- The chosen strict half is precisely the topological interior. -/
theorem interior_halfFordRegion : interior halfFordRegion = halfFordInterior := by
  unfold halfFordRegion halfFordInterior
  rw [interior_inter, interior_fordRegion]
  have hcut : interior {z : ℍ | z.re ≤ -(1 / 2)} =
      {z : ℍ | z.re < -(1 / 2)} := by
    change interior (UpperHalfPlane.re ⁻¹' Iic (-(1 / 2))) =
      UpperHalfPlane.re ⁻¹' Iio (-(1 / 2))
    rw [← isOpenMap_re.preimage_interior_eq_interior_preimage continuous_re, interior_Iic]
  rw [hcut]

theorem norm_add_one_lt_norm_of_re_lt_neg_half (z : ℍ)
    (hzre : z.re < -(1 / 2)) : ‖(z : ℂ) + 1‖ < ‖(z : ℂ)‖ := by
  apply (sq_lt_sq₀ (norm_nonneg ((z : ℂ) + 1)) (norm_nonneg (z : ℂ))).mp
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.one_re,
    Complex.add_im, Complex.one_im, add_zero, UpperHalfPlane.coe_re,
    UpperHalfPlane.coe_im]
  nlinarith

theorem one_lt_norm_of_re_lt_neg_half (z : ℍ)
    (hzre : z.re < -(1 / 2)) (hn : 1 < ‖(z : ℂ) + 1‖) :
    1 < ‖(z : ℂ)‖ :=
  hn.trans (norm_add_one_lt_norm_of_re_lt_neg_half z hzre)

theorem strict_ford_left_half_iff_triangleInterior (z : ℍ) :
    ((stripLeft < z.re ∧ z.re < stripRight ∧
      1 < ‖(z : ℂ) + 1‖ ∧ 1 < ‖(z : ℂ)‖) ∧ z.re < -(1 / 2)) ↔
      (z : ℂ) ∈ triangleInterior := by
  change _ ↔ stripLeft < z.re ∧ z.re < -1 / 2 ∧
    0 < z.im ∧ 1 < ‖(z : ℂ) + 1‖
  constructor
  · rintro ⟨⟨hl, _, hn, _⟩, hm⟩
    exact ⟨hl, by linarith, z.im_pos, hn⟩
  · rintro ⟨hl, hm, _, hn⟩
    have hm' : z.re < -(1 / 2) := by linarith
    refine ⟨⟨hl, ?_, hn, one_lt_norm_of_re_lt_neg_half z hm' hn⟩, hm'⟩
    linarith [stripRight_pos]

/-- The half-Ford interior is exactly the source complex triangle,
viewed inside the upper half-plane. -/
theorem halfFordInterior_eq_preimage_triangleInterior :
    halfFordInterior = ((↑) : ℍ → ℂ) ⁻¹' triangleInterior :=
  Set.ext strict_ford_left_half_iff_triangleInterior

@[simp] theorem rightReflection_mem_fordInterior_iff (z : ℍ) :
    rightReflection z ∈ fordInterior ↔ z ∈ fordInterior := by
  simp only [fordInterior, mem_ofPred_eq, rightReflection_re,
    rightReflection_add_one_norm, rightReflection_norm]
  unfold stripLeft stripRight
  constructor
  · rintro ⟨hl, hr, hnorm, hadd⟩
    refine ⟨?_, ?_, hadd, hnorm⟩ <;> linarith
  · rintro ⟨hl, hr, hadd, hnorm⟩
    refine ⟨?_, ?_, hnorm, hadd⟩ <;> linarith

theorem rightReflection_mapsTo_fordInterior :
    MapsTo rightReflection fordInterior fordInterior :=
  fun z hz => (rightReflection_mem_fordInterior_iff z).mpr hz

theorem rightReflection_image_fordInterior :
    rightReflection '' fordInterior = fordInterior := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact rightReflection_mapsTo_fordInterior hw
  · intro hz
    exact ⟨rightReflection z, rightReflection_mapsTo_fordInterior hz,
      rightReflection_involutive z⟩

/-- The two actual folds used to recover the full Ford polygon. -/
def halfFold (b : Bool) : ℍ ≃ₜ ℍ :=
  if b then rightReflection else Homeomorph.refl ℍ

@[simp] theorem halfFold_false : halfFold false = Homeomorph.refl ℍ := rfl

@[simp] theorem halfFold_true : halfFold true = rightReflection := rfl

theorem halfFold_mapsTo_region (b : Bool) :
    MapsTo (halfFold b) halfFordRegion fordRegion := by
  cases b
  · intro z hz
    exact hz.1
  · intro z hz
    exact rightReflection_mapsTo_fordRegion hz.1

theorem halfFold_mapsTo_interior (b : Bool) :
    MapsTo (halfFold b) halfFordInterior fordInterior := by
  cases b
  · intro z hz
    exact hz.1
  · intro z hz
    exact rightReflection_mapsTo_fordInterior hz.1

theorem halfFold_image_region_subset (b : Bool) :
    halfFold b '' halfFordRegion ⊆ fordRegion := (halfFold_mapsTo_region b).image_subset

theorem halfFold_image_interior_subset (b : Bool) :
    halfFold b '' halfFordInterior ⊆ fordInterior := (halfFold_mapsTo_interior b).image_subset

/-- The reflected closed half is the other closed real-coordinate half. -/
theorem rightReflection_image_halfFordRegion :
    rightReflection '' halfFordRegion = fordRegion ∩ {z | -(1 / 2) ≤ z.re} := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    refine ⟨rightReflection_mapsTo_fordRegion hw.1, ?_⟩
    change -(1 / 2) ≤ (rightReflection w).re
    rw [rightReflection_re]
    have hcut : w.re ≤ -(1 / 2) := hw.2
    linarith
  · rintro ⟨hz, hr⟩
    refine ⟨rightReflection z, ⟨rightReflection_mapsTo_fordRegion hz, ?_⟩,
      rightReflection_involutive z⟩
    change (rightReflection z).re ≤ -(1 / 2)
    rw [rightReflection_re]
    change -(1 / 2) ≤ z.re at hr
    linarith

/-- The reflected open half is the other strict real-coordinate half. -/
theorem rightReflection_image_halfFordInterior :
    rightReflection '' halfFordInterior = fordInterior ∩ {z | -(1 / 2) < z.re} := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    refine ⟨rightReflection_mapsTo_fordInterior hw.1, ?_⟩
    change -(1 / 2) < (rightReflection w).re
    rw [rightReflection_re]
    have hcut : w.re < -(1 / 2) := hw.2
    linarith
  · rintro ⟨hz, hr⟩
    refine ⟨rightReflection z, ⟨rightReflection_mapsTo_fordInterior hz, ?_⟩,
      rightReflection_involutive z⟩
    change (rightReflection z).re < -(1 / 2)
    rw [rightReflection_re]
    change -(1 / 2) < z.re at hr
    linarith

/-- The two closed halves cover exactly the Ford region. -/
theorem halfFordRegion_union_reflection :
    halfFordRegion ∪ rightReflection '' halfFordRegion = fordRegion := by
  rw [rightReflection_image_halfFordRegion]
  ext z
  change ((z ∈ fordRegion ∧ z.re ≤ -(1 / 2)) ∨
    (z ∈ fordRegion ∧ -(1 / 2) ≤ z.re)) ↔ z ∈ fordRegion
  constructor
  · rintro (hz | hz) <;> exact hz.1
  · intro hz
    rcases le_total z.re (-(1 / 2)) with h | h
    · exact Or.inl ⟨hz, h⟩
    · exact Or.inr ⟨hz, h⟩

/-- The two open halves have no common point. -/
theorem halfFordInterior_disjoint_reflection :
    Disjoint halfFordInterior (rightReflection '' halfFordInterior) := by
  rw [rightReflection_image_halfFordInterior]
  apply Set.disjoint_left.mpr
  intro z hz hw
  exact lt_asymm (show z.re < -(1 / 2) from hz.2)
    (show -(1 / 2) < z.re from hw.2)

theorem halfFold_closed_cover :
    (⋃ b : Bool, halfFold b '' halfFordRegion) = fordRegion := by
  ext z
  rw [mem_iUnion]
  constructor
  · rintro ⟨b, hb⟩
    exact halfFold_image_region_subset b hb
  · intro hz
    rw [← halfFordRegion_union_reflection] at hz
    rcases hz with hz | hz
    · exact ⟨false, z, hz, rfl⟩
    · exact ⟨true, hz⟩

theorem halfFold_images_disjoint (b c : Bool) (h : b ≠ c) :
    Disjoint (halfFold b '' halfFordInterior) (halfFold c '' halfFordInterior) := by
  cases b <;> cases c
  · exact (h rfl).elim
  · change Disjoint (id '' halfFordInterior) (rightReflection '' halfFordInterior)
    simpa only [image_id] using
      halfFordInterior_disjoint_reflection
  · change Disjoint (rightReflection '' halfFordInterior) (id '' halfFordInterior)
    simpa only [image_id] using
      halfFordInterior_disjoint_reflection.symm
  · exact (h rfl).elim

end Wikipedia.HopfProblem.SpecialPeriods.Triangle
