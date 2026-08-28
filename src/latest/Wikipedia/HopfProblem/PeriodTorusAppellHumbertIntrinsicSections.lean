import Wikipedia.HopfProblem.PeriodTorusAppellHumbertIntrinsic
import Wikipedia.HopfProblem.PeriodTorusAppellHumbertCoreSections
import Wikipedia.HopfProblem.PeriodTorusThetaSpecial

/-!
# Vanishing of actual sections for nonzero intrinsic integral forms

Outside the proved exceptional set, a nonzero intrinsic integral
alternating form of type `(1,1)` has no nonzero holomorphic sections in
its constructed Appell--Humbert quotient.  The independently constructed
holomorphic vector bundle has the same conclusion through the proved
analytic section identification.  The sections are genuine right
inverses and Mathlib `ContMDiffSection` objects, respectively.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusAppellHumbert

open PeriodTorusTypeOneOne SpecialPeriods UpperHalfPlane

/-- Actual holomorphic quotient sections vanish for every nonzero intrinsic
integral type-`(1,1)` form away from the exceptional locus. -/
theorem intrinsic_quotientSection_eq_zero (z : ℍ) (hz : z ∉ exceptionalTypeOneOneSet)
    (B : RealForm) (hAlt : ∀ x, B x x = 0)
    (hInt : IntegralOnPeriodLattice (specialPeriodMap.point z) B)
    (hType : IsTypeOneOne B) (hB : B ≠ 0)
    (s : Section (intrinsicFactor (specialPeriodMap.point z) B hAlt hInt hType))
    (hs : s.IsHolomorphic (intrinsicFactor (specialPeriodMap.point z) B hAlt hInt hType)) :
    s = zeroSection (intrinsicFactor (specialPeriodMap.point z) B hAlt hInt hType) := by
  let F := intrinsicFactor (specialPeriodMap.point z) B hAlt hInt hType
  apply (Section.eq_zero_iff_pullback F s).mpr
  have hAuto : PeriodTorusTheta.AppellHumbertAutomorphy (specialPeriodMap.point z)
      (associatedSesquilinear B hType)
      (intrinsicMultiplier (specialPeriodMap.point z) B hAlt hInt) (s.pullback F) :=
    (intrinsicFactor_automorphy_iff (specialPeriodMap.point z) B hAlt hInt hType
      (s.pullback F)).mp (s.pullback_automorphic F)
  exact PeriodTorusTheta.theta_eq_zero_of_nonzero_integral_form z hz B hAlt hInt hType hB
    (intrinsicMultiplier (specialPeriodMap.point z) B hAlt hInt)
    (intrinsicMultiplier_norm (specialPeriodMap.point z) B hAlt hInt)
    (s.pullback F) ((s.pullback_contDiff F hs).differentiable (by simp)) hAuto

/-- Every actual Mathlib holomorphic section of the constructed line bundle
is zero, not only every scalar function satisfying a transformation law. -/
theorem intrinsic_holomorphicSection_eq_zero (z : ℍ) (hz : z ∉ exceptionalTypeOneOneSet)
    (B : RealForm) (hAlt : ∀ x, B x x = 0)
    (hInt : IntegralOnPeriodLattice (specialPeriodMap.point z) B)
    (hType : IsTypeOneOne B) (hB : B ≠ 0)
    (s : Core.HolomorphicSection
      (intrinsicFactor (specialPeriodMap.point z) B hAlt hInt hType)) : s = 0 := by
  let F := intrinsicFactor (specialPeriodMap.point z) B hAlt hInt hType
  apply Core.quotientSection_injective F
  rw [Core.quotientSection_zero]
  exact intrinsic_quotientSection_eq_zero z hz B hAlt hInt hType hB
    (Core.quotientSection F s) (Core.quotientSection_holomorphic F s)

end Wikipedia.HopfProblem.PeriodTorusAppellHumbert
