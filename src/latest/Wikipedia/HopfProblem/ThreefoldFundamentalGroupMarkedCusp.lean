import Wikipedia.HopfProblem.ThreefoldFundamentalGroupMarkedInclusion
import Wikipedia.HopfProblem.ThreefoldFundamentalGroupCuspPeripheral

/-!
# The cusp relation in the actual source-marked threefold group

The finite-coordinate zero section and the original regular-family zero
section agree pointwise under the actual base homeomorphism.  Their
induced maps therefore agree after the proved basepoint equality.
Consequently the genuine cusp contraction gives the product relation
for exactly the same joint meridians that act by `A₁` and `A₂` on the
source-column lattice.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.PiOne

open Triangle TrianglePeriodFamily Meridians

attribute [local instance] triangleCompactifiedChartedSpace triangleRegularQuotientChartedSpace

local notation "Dsp" =>
  regularData specialPeriodMap specialPeriodMap_generator₁ specialPeriodMap_generator₂

/-- Pointwise agreement of the two actual descriptions of the regular zero section. -/
theorem planeSection_regularCoordinate (q : TriangleRegularQuotient) :
    CuspPeripheral.planeSection (triangleRegularPlaneHomeomorph q) =
      regularFamilyInclusionMap ((Dsp).zeroSection q) := by
  change inclusion none ((Dsp).zeroSection
      (regularBiholomorph.symm (regularBiholomorph
        (triangleRegularPlaneHomeomorph.symm (triangleRegularPlaneHomeomorph q))))) =
    inclusion none ((Dsp).zeroSection q)
  rw [triangleRegularPlaneHomeomorph.symm_apply_apply, regularBiholomorph.symm_apply_apply]

/-- The basepoint equality is proved from the actual normalized coordinate. -/
theorem planeSection_basepoint :
    CuspPeripheral.planeSectionMap meridianBasepoint = basepoint := by
  have h := planeSection_regularCoordinate
    (triangleRegularProject normalizedRegularMeridianBasepoint)
  rw [normalizedRegularMeridianBasepoint_coordinate] at h
  exact h

/-- The actual planar zero-section map with its target basepoint identified. -/
def pointedPlaneHom : FundamentalGroup TwicePuncturedPlane meridianBasepoint →* GlobalGroup :=
  FundamentalGroup.mapOfEq CuspPeripheral.planeSectionMap planeSection_basepoint

private theorem mapOfEq_eq_one_of_map_eq_one
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) {x : X} {y : Y} (e : f x = y)
    (g : FundamentalGroup X x) (h : FundamentalGroup.map f x g = 1) :
    FundamentalGroup.mapOfEq f e g = 1 := by
  subst y
  simpa only [FundamentalGroup.mapOfEq, CategoryTheory.eqToIso_refl,
    MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, CategoryTheory.Iso.refl_conj] using h

/-- Simultaneous orientation reversal still gives the same product relation
after the actual basepoint identification. -/
theorem pointedPlaneHom_oriented_product_eq_one (reverse : Bool) :
    pointedPlaneHom (FreeMeridianMarking.orientedClass reverse false) *
      pointedPlaneHom (FreeMeridianMarking.orientedClass reverse true) = 1 := by
  rw [← map_mul]
  apply mapOfEq_eq_one_of_map_eq_one
  rw [map_mul]
  exact CuspPeripheral.planeSection_oriented_meridian_product_eq_one reverse

/-- Naturality for the actual zero section and actual normalized base map,
proved on literal loop representatives rather than on a chosen free group. -/
theorem regularHom_section_eq_plane
    (g : FundamentalGroup TriangleRegularQuotient
      (triangleRegularProject normalizedRegularMeridianBasepoint)) :
    regularHom (specialRegularFamilyMarkedSectionHom g) =
      pointedPlaneHom (compatibleBasePlaneEquiv g) := by
  unfold pointedPlaneHom
  rw [compatibleBasePlaneEquiv_apply, FundamentalGroup.mapOfEq_apply,
    FundamentalGroup.mapOfEq_apply]
  obtain ⟨p⟩ := g
  apply congrArg Path.Homotopic.Quotient.mk
  ext t
  exact (planeSection_regularCoordinate (p t)).symm

/-- The exact joint meridian images, with the common geometric orientation
choice inherited from the actual normalization. -/
theorem meridian_eq_pointedPlane (b : Bool) :
    meridian b = pointedPlaneHom
      (FreeMeridianMarking.orientedClass normalizationReversesMeridians b) := by
  rw [meridian, specialRegularFamilyMarkedMeridianClass_eq_section,
    regularHom_section_eq_plane, compatibleBasePlaneEquiv_meridianClass]

/-- The genuine cusp relation for the actual marked threefold generators. -/
theorem meridian_product_eq_one : meridian false * meridian true = 1 := by
  rw [meridian_eq_pointedPlane, meridian_eq_pointedPlane]
  exact pointedPlaneHom_oriented_product_eq_one normalizationReversesMeridians

theorem meridian_second_eq_first_inv : meridian true = (meridian false)⁻¹ :=
  eq_inv_of_mul_eq_one_right meridian_product_eq_one

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.PiOne
