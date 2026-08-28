import Wikipedia.HopfProblem.SpecialPeriodsEllipticAttachingMeridians
import Wikipedia.HopfProblem.SpecialPeriodsEllipticAttachingGlobal
import Wikipedia.HopfProblem.ThreefoldFundamentalGroupLattice

/-!
# The actual global elliptic power relations in the fixed marking

The proved geometric peripheral homotopy compares the actual logarithmic
attaching loop with the fixed compatible free generator. The actual
global group is already proved commutative independently of the elliptic
power relations, so the displayed geometric conjugator cancels.

The actual upstairs tail separately preserves the original lattice
column. Applying the checked local attaching power relation therefore
gives the global power relation for the original fixed generators, with
one common orientation choice. No attaching map, peripheral homotopy,
period-column identification, or group relation is an input.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.EllipticGeometry

open Elliptic TrianglePeriodFamily.Meridians CuspUniformization

/-- The section homomorphism uses exactly the original fixed meridian
marking in the native global fundamental group. -/
@[simp] theorem attachingBaseSectionHom_compatibleMeridian (b : Bool) :
    attachingBaseSectionHom (compatibleRegularMeridianClass b) = PiOne.meridian b := rfl

/-- The actual globally transported local meridian equals the original
marked generator with its proved common clockwise orientation. -/
theorem transportedAttachingClass_eq_oriented_meridian (j : Kind) (s₀ : ℂ)
    (hs₀ : 0 < s₀.im)
    (hr : ‖exponential s₀‖ ^ j.order < specialBaseCover.radius (some j))
    (hsmall : ‖exponential s₀‖ ^ j.order < attachingMeridianRadius j) :
    transportedAttachingClass j s₀ hs₀ hr =
      if normalizationReversesMeridians then PiOne.meridian (attachingMeridianIndex j)
      else (PiOne.meridian (attachingMeridianIndex j))⁻¹ := by
  rw [transportedAttachingClass_eq_baseImage]
  have h := attachingMeridian_map_whisker j s₀ hs₀ hr hsmall
    (attachingBaseTail j s₀ hs₀) attachingBaseSectionHom PiOne.all_commute
  simpa only [transportedAttachingBaseLoop, attachingBaseSectionHom_compatibleMeridian] using! h

/-- The selected actual small logarithmic parameters discharge every
radius and existence condition in the global meridian comparison. -/
theorem chosenTransportedAttachingClass_eq_oriented_meridian (j : Kind) :
    transportedAttachingClass j (chosenAttachingParameter j) (chosenAttachingParameter_im_pos j)
        (chosenAttachingParameter_filling_bound j) =
      if normalizationReversesMeridians then PiOne.meridian (attachingMeridianIndex j)
      else (PiOne.meridian (attachingMeridianIndex j))⁻¹ :=
  transportedAttachingClass_eq_oriented_meridian j (chosenAttachingParameter j)
    (chosenAttachingParameter_im_pos j) (chosenAttachingParameter_filling_bound j)
    (chosenAttachingParameter_bound j)

/-- A genuine local parameter and actual attaching map realize the
fixed clockwise global meridian, without any supplied parameter. -/
theorem exists_transportAttachingClass_eq_oriented_meridian (j : Kind) :
    ∃ s₀ : ℂ, ∃ hs₀ : 0 < s₀.im,
      ∃ hr : ‖exponential s₀‖ ^ j.order < specialBaseCover.radius (some j),
        transportedAttachingClass j s₀ hs₀ hr =
          if normalizationReversesMeridians then PiOne.meridian (attachingMeridianIndex j)
          else (PiOne.meridian (attachingMeridianIndex j))⁻¹ :=
  ⟨chosenAttachingParameter j, chosenAttachingParameter_im_pos j,
    chosenAttachingParameter_filling_bound j,
    chosenTransportedAttachingClass_eq_oriented_meridian j⟩

/-- The actual original free generators obey the attaching power laws,
with the same clockwise-orientation choice for both elliptic orders and
with the source's unchanged integral twist columns. -/
theorem clockwise_meridian_pow_order (j : Kind) :
    (if normalizationReversesMeridians then PiOne.meridian (attachingMeridianIndex j)
      else (PiOne.meridian (attachingMeridianIndex j))⁻¹) ^ j.order =
        PiOne.latticeHom (Multiplicative.ofAdd j.twist) := by
  have h := transportedAttachingClass_pow_order j (chosenAttachingParameter j)
    (chosenAttachingParameter_im_pos j) (chosenAttachingParameter_filling_bound j)
  rwa [chosenTransportedAttachingClass_eq_oriented_meridian] at h

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.EllipticGeometry
