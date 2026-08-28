import Wikipedia.HopfProblem.ThreefoldFundamentalGroupCuspPeripheralBase
import Wikipedia.HopfProblem.SpecialPeriodsCuspAttachingHomotopy
import Wikipedia.HopfProblem.TrianglePeriodFamilyFundamentalGroupFreeInversion

/-!
# The actual joint peripheral relation in the threefold

The large explicit outer-circle core lies in the chosen cusp disc.  Its
regular zero section agrees there with the toric section extending across
the cusp, so the core contracts.  Concatenating with the original based
tail and its reverse gives a based contraction of the peripheral loop.
The independently proved exact free-word calculation then gives the
joint meridian relation in the actual threefold fundamental group.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.CuspPeripheral

open Triangle

/-- The actual regular zero section written in the normalized finite coordinate. -/
def planeSection : TwicePuncturedPlane → Space :=
  CuspAttaching.regularSection ∘ planeToRegularBase

theorem planeSection_continuous : Continuous planeSection :=
  CuspAttaching.regularSection_continuous.comp planeToRegularBase_continuous

/-- The corresponding genuine bundled continuous map into the constructed space. -/
def planeSectionMap : C(TwicePuncturedPlane, Space) :=
  ⟨planeSection, planeSection_continuous⟩

/-- The original core loop contracts through the genuine cusp filling. -/
theorem outerPositiveCircle_section_nullhomotopic :
    Path.Homotopic
      ((outerPositiveCircle outerRadius outerRadius_ge_two).map planeSection_continuous)
      (Path.refl (planeSection (outerCircleBasepoint outerRadius outerRadius_ge_two))) := by
  have h := CuspAttaching.regularSection_loop_nullhomotopic_of_mem
    outerRegularCircle outerRegularCircle_mem_cusp
  have heq : outerRegularCircle.map CuspAttaching.regularSection_continuous =
      (outerPositiveCircle outerRadius outerRadius_ge_two).map planeSection_continuous := by
    ext t
    rfl
  exact heq ▸ h

/-- The explicit original vertical tail is retained on both sides of the
core contraction; its own image need not lie in the cusp patch. -/
theorem positiveOuterMeridian_section_nullhomotopic :
    Path.Homotopic
      ((positiveOuterMeridian outerRadius outerRadius_ge_two).map planeSection_continuous)
      (Path.refl (planeSection meridianBasepoint)) := by
  let a := (outerMeridianTail outerRadius outerRadius_ge_two).map planeSection_continuous
  let b := (outerPositiveCircle outerRadius outerRadius_ge_two).map planeSection_continuous
  have hb : b.Homotopic (Path.refl (planeSection
      (outerCircleBasepoint outerRadius outerRadius_ge_two))) :=
    outerPositiveCircle_section_nullhomotopic
  have h₁ := ((Path.Homotopic.refl a).hcomp hb).hcomp (Path.Homotopic.refl a.symm)
  have h₂ := (Path.Homotopic.trans_refl a).hcomp (Path.Homotopic.refl a.symm)
  have h := h₁.trans (h₂.trans (Path.Homotopic.trans_symm a))
  simpa only [positiveOuterMeridian_eq_tail_circle_tail, Path.map_trans,
    ← Path.map_symm] using h

/-- The actual regular-section image of the positively oriented outer
peripheral class is trivial in the constructed threefold. -/
theorem planeSection_positiveOuterMeridian_eq_one :
    FundamentalGroup.map planeSectionMap meridianBasepoint
      (Path.Homotopic.Quotient.mk
        (positiveOuterMeridian outerRadius outerRadius_ge_two)) = 1 :=
  Path.Homotopic.Quotient.eq.mpr positiveOuterMeridian_section_nullhomotopic

/-- The two jointly based positive planar meridians satisfy the genuine
cusp relation after inclusion by the actual regular zero section. -/
theorem planeSection_meridian_product_eq_one :
    FundamentalGroup.map planeSectionMap meridianBasepoint (meridianClass false) *
      FundamentalGroup.map planeSectionMap meridianBasepoint (meridianClass true) = 1 := by
  rw [← map_mul, ← positiveOuterMeridian_class_eq outerRadius outerRadius_ge_two]
  exact planeSection_positiveOuterMeridian_eq_one

/-- Simultaneously reversing the two meridian orientations preserves
this product relation.  No orientation choice is made separately at the
two punctures. -/
theorem planeSection_oriented_meridian_product_eq_one (reverse : Bool) :
    FundamentalGroup.map planeSectionMap meridianBasepoint
        (FreeMeridianMarking.orientedClass reverse false) *
      FundamentalGroup.map planeSectionMap meridianBasepoint
        (FreeMeridianMarking.orientedClass reverse true) = 1 := by
  cases reverse with
  | false => exact planeSection_meridian_product_eq_one
  | true =>
    simp only [FreeMeridianMarking.orientedClass_true, map_inv]
    have h := planeSection_meridian_product_eq_one
    have hx := eq_inv_of_mul_eq_one_left h
    rw [hx, inv_inv, mul_inv_cancel]

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.CuspPeripheral
