import Wikipedia.HopfProblem.CuspCoinvariantExtensionPuncturedBasic
import Wikipedia.HopfProblem.TrianglePeriodFamilyGammaZeroFamily
import Wikipedia.HopfProblem.SpecialPeriodsCuspAttachingSection

/-!
# The genuine punctured cusp gamma agrees with the regular gamma

The original whole-family cusp comparison keeps every real torus
coordinate. Consequently the continuous gamma on the entire punctured
cusp is the pullback of the original regular-family gamma by the actual
gluing overlap. The specialization uses the already chosen special
periods, correction, and restricted radius, and is compatible with the
unchanged inclusions into the glued threefold.
-/

noncomputable section

open Set Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.CuspCoinvariantExtension

open SpecialPeriods CuspFamily CuspUniformization CuspGlobalOverlap
open ThreefoldOverlapMappingTorus.Cusp TrianglePeriodFamily.GammaZero

variable (C : CuspFamily.Data)
  (D : TrianglePeriodFamily.Data ℂ TriangleRegularPoint)
  (hrcap : C.radius ≤ Triangle.cuspRadius Triangle.width)

/-- The actual cyclic-to-regular quotient comparison preserves the
original first circle coordinate on every fibre. -/
theorem familyGamma_familyMap (x : C.Space) :
    familyGamma D (familyMap C D hrcap x) = cuspFamilyGamma C x := by
  obtain ⟨y, rfl⟩ := C.quotient_surjective x
  rw [familyMap_quotient, familyGamma_quotient, cuspFamilyGamma_quotient]

variable (hperiod : ∀ s : LogBase C.radius,
  D.periods.point (logBaseToRegular C.radius hrcap s) = C.periods.point s)

/-- The already constructed whole punctured-cusp biholomorphism
identifies the two genuine gamma maps on its entire domain. -/
theorem familyGamma_puncturedBiholomorph
    (x : PuncturedQuotient C.correction C.radius) :
    letI := CuspQuotient.chartedSpace C.correction C.radius C.radius_pos C.radius_lt_one
      C.holomorphic C.smallDrift
    letI := D.chartedSpace (familyCovering D)
    familyGamma D (puncturedBiholomorph C D hrcap hperiod x) = puncturedGamma C x := by
  let := C.chartedSpace
  let := CuspQuotient.chartedSpace C.correction C.radius C.radius_pos C.radius_lt_one
    C.holomorphic C.smallDrift
  let := D.chartedSpace (familyCovering D)
  obtain ⟨y, rfl⟩ := (puncturedFamilyHomeomorph C).surjective x
  rw [puncturedGamma_family]
  change familyGamma D (familyMap C D hrcap
    (C.puncturedFamilyBiholomorph.symm (C.puncturedFamilyBiholomorph y))) = _
  rw [Diffeomorph.symm_apply_apply, familyGamma_familyMap]

/-- The original ambient cusp overlap has the same equality at every
point outside the central fibre, not only on a marked boundary. -/
theorem familyGamma_cuspToRegularPartial
    (x : CuspQuotient.QuotientSpace C.correction C.radius)
    (hx : CuspQuotient.projection C.correction C.radius x ≠ 0) :
    letI := CuspQuotient.chartedSpace C.correction C.radius C.radius_pos C.radius_lt_one
      C.holomorphic C.smallDrift
    letI := D.chartedSpace (familyCovering D)
    familyGamma D (cuspToRegularPartial C D hrcap hperiod x) =
      puncturedGamma C ⟨x, hx⟩ := by
  let := CuspQuotient.chartedSpace C.correction C.radius C.radius_pos C.radius_lt_one
    C.holomorphic C.smallDrift
  let := D.chartedSpace (familyCovering D)
  rw [cuspToRegularPartial_apply C D hrcap hperiod x hx]
  exact familyGamma_puncturedBiholomorph C D hrcap hperiod ⟨x, hx⟩

section Special

open SpecialPeriods.Threefold

attribute [local instance] triangleCompactifiedChartedSpace triangleRegularQuotientChartedSpace
  specialRegularFamilyChartedSpace specialCuspPieceChartedSpace

/-- The actual common-model gluing overlap pulls the original regular
gamma back to the genuine punctured gamma at the chosen cusp radius. -/
theorem familyGamma_specialCuspOverlap
    (x : PuncturedQuotient CuspAttaching.data.correction CuspAttaching.data.radius) :
    familyGamma CuspAttaching.regularData (specialCuspOverlap x.val) =
      puncturedGamma CuspAttaching.data x := by
  exact familyGamma_cuspToRegularPartial CuspAttaching.data CuspAttaching.regularData
    CuspAttaching.radius_le_cuspChart CuspAttaching.period_agreement x.val x.property

/-- The native cusp atlas gives literally the same full-overlap gamma equality. -/
theorem familyGamma_specialCuspNativeOverlap
    (x : PuncturedQuotient CuspAttaching.data.correction CuspAttaching.data.radius) :
    familyGamma CuspAttaching.regularData (specialCuspNativeOverlap x.val) =
      puncturedGamma CuspAttaching.data x :=
  familyGamma_specialCuspOverlap x

/-- Equality already holds on every actual original logarithmic
representative for the restricted special cusp data. -/
theorem familyGamma_specialCuspOverlap_realCoordinates
    (s : LogBase CuspAttaching.data.radius) (x : RealPlane₄) :
    familyGamma CuspAttaching.regularData
      (specialCuspOverlap (totalCuspCover CuspAttaching.data.correction
        CuspAttaching.data.radius
        ⟨((s : ℂ), CuspAttaching.data.periods.periodEquiv s x), s.property⟩)) =
      (x 0 : AddCircle (1 : ℝ)) :=
  (familyGamma_specialCuspOverlap (puncturedCuspCover CuspAttaching.data.correction
    CuspAttaching.data.radius
    ⟨((s : ℂ), CuspAttaching.data.periods.periodEquiv s x), s.property⟩)).trans
      (puncturedGamma_realCoordinates CuspAttaching.data s x)

/-- The two genuine gamma maps agree whenever their original cusp
and regular representatives are identified by the actual gluing inclusions. -/
theorem familyGamma_eq_puncturedGamma_of_inclusion_eq
    (x : PuncturedQuotient CuspAttaching.data.correction CuspAttaching.data.radius)
    (y : SpecialRegularFamily)
    (h : inclusion (some none) x.val = inclusion none y) :
    familyGamma CuspAttaching.regularData y = puncturedGamma CuspAttaching.data x := by
  have hy : specialCuspOverlap x.val = y :=
    ((gluingData.inclusion_eq_iff (some none) none x.val y).mp h).2
  rw [← hy]
  exact familyGamma_specialCuspOverlap x

end Special

end Wikipedia.HopfProblem.CuspCoinvariantExtension
