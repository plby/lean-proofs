import Wikipedia.HopfProblem.SpecialPeriodsCuspAttachingZeroCover
import Wikipedia.HopfProblem.SpecialPeriodsCuspGlobalOverlapPartial

/-!
# The genuine cusp comparison preserves the zero section

The logarithmic vector zero is the toric point `(t,1,1)`.  The actual
cyclic-to-regular-family map preserves its real torus coordinate, so the
whole-family comparison identifies the extended toric section with the
regular zero section.  These statements concern the already constructed
overlap, not a replacement map chosen to preserve sections.
-/

noncomputable section

open Set Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.CuspGlobalOverlap

open CuspFamily CuspUniformization ToricCharts

variable (C : CuspFamily.Data)
  (D : TrianglePeriodFamily.Data ℂ TriangleRegularPoint)
  (hrcap : C.radius ≤ Triangle.cuspRadius Triangle.width)

/-- The actual family comparison preserves zero in every real torus fibre. -/
theorem familyMap_iteratedCover_zero (s : LogBase C.radius) :
    familyMap C D hrcap (C.iteratedCover ⟨((s : ℂ), 0), s.property⟩) =
      D.zeroSection (D.baseQuotient (logBaseToRegular C.radius hrcap s)) := by
  rw [C.iteratedCover_zero, familyMap_quotient, D.zeroSection_baseQuotient]
  rfl

variable (hperiod : ∀ s : LogBase C.radius,
  D.periods.point (logBaseToRegular C.radius hrcap s) = C.periods.point s)

/-- On every actual logarithmic representative, the ambient cusp overlap
carries the toric section to the regular family's genuine zero section. -/
theorem cuspToRegularPartial_zeroSection_log (s : LogBase C.radius)
    (t : CuspQuotient.disc C.radius) (ht : (t : ℂ) = exponential s) :
    letI := CuspQuotient.chartedSpace C.correction C.radius C.radius_pos C.radius_lt_one
      C.holomorphic C.smallDrift
    letI := D.chartedSpace (familyCovering D)
    cuspToRegularPartial C D hrcap hperiod (CuspQuotient.zeroSection C.correction C.radius t) =
      D.zeroSection (D.baseQuotient (logBaseToRegular C.radius hrcap s)) := by
  let := CuspQuotient.chartedSpace C.correction C.radius C.radius_pos C.radius_lt_one
    C.holomorphic C.smallDrift
  let := D.chartedSpace (familyCovering D)
  have htne : (t : ℂ) ≠ 0 := by
    rw [ht]
    exact exponential_ne_zero s
  have hsource : CuspQuotient.zeroSection C.correction C.radius t ∈
      puncturedQuotientOpen C.correction C.radius := by
    change CuspQuotient.projection C.correction C.radius
      (CuspQuotient.zeroSection C.correction C.radius t) ≠ 0
    rw [CuspQuotient.projection_zeroSection]
    exact htne
  rw [cuspToRegularPartial_apply C D hrcap hperiod _ hsource]
  have he : (⟨CuspQuotient.zeroSection C.correction C.radius t, hsource⟩ :
      PuncturedQuotient C.correction C.radius) =
      puncturedCuspCover C.correction C.radius ⟨((s : ℂ), 0), s.property⟩ := by
    apply Subtype.ext
    exact (puncturedCuspCover_zero C.correction C.radius s t ht).symm
  rw [he, puncturedBiholomorph_cover C D hrcap hperiod]
  exact familyMap_iteratedCover_zero C D hrcap s

/-- The entire punctured section is carried to zero over its actual base
point; the assertion is independent of the chosen logarithmic lift. -/
theorem cuspToRegularPartial_zeroSection (t : CuspQuotient.disc C.radius)
    (ht : (t : ℂ) ≠ 0) :
    letI := CuspQuotient.chartedSpace C.correction C.radius C.radius_pos C.radius_lt_one
      C.holomorphic C.smallDrift
    letI := D.chartedSpace (familyCovering D)
    cuspToRegularPartial C D hrcap hperiod (CuspQuotient.zeroSection C.correction C.radius t) =
      D.zeroSection (D.projection
        (cuspToRegularPartial C D hrcap hperiod
          (CuspQuotient.zeroSection C.correction C.radius t))) := by
  let := CuspQuotient.chartedSpace C.correction C.radius C.radius_pos C.radius_lt_one
    C.holomorphic C.smallDrift
  let := D.chartedSpace (familyCovering D)
  obtain ⟨s, hs⟩ := baseExponential_surjective C.radius
    (⟨t, t.property, ht⟩ : puncturedDisc C.radius)
  have he : (t : ℂ) = exponential s := (congrArg Subtype.val hs).symm
  rw [cuspToRegularPartial_zeroSection_log C D hrcap hperiod s t he,
    D.projection_zeroSection]

end Wikipedia.HopfProblem.SpecialPeriods.CuspGlobalOverlap
