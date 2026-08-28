import Wikipedia.HopfProblem.SpecialPeriodsThreefoldVerticalActionCuspCoordinates
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldVerticalActionTriangle
import Wikipedia.HopfProblem.SpecialPeriodsCuspGlobalOverlapPartial

/-!
# The vertical-flow square on the genuine logarithmic cusp overlap

The existing cusp-to-regular biholomorphism agrees with the original
logarithmic exponential cover.  The proved equality of the actual period
points identifies its complex fibre coordinates with the regular vector
cover.  Thus both flows become the same translation by `s (0,1)` on
every representative of the full punctured cusp.
-/

noncomputable section

open Set Topology
open scoped ContDiff Matrix

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction.Cusp

open CuspFamily CuspGlobalOverlap CuspUniformization ToricCharts
open Wikipedia.HopfProblem.SpecialPeriods.Triangle (cuspRadius width)

local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)
local notation "I₃" => modelWithCornersSelf ℂ (CoordinateSpace 3)

variable (C : CuspFamily.Data)
  (D : TrianglePeriodFamily.Data ℂ TriangleRegularPoint)
  (hrcap : C.radius ≤ cuspRadius width)

/-- The actual regular vector-cover projection on a logarithmic cusp representative. -/
def overlapVectorCover (p : LogCover C.radius) : D.Space :=
  D.quotient (D.periods.quotientMap
    (logBaseToRegular C.radius hrcap ⟨p.val.1, p.property⟩, p.val.2))

/-- Translating the logarithmic fibre coordinates produces exactly the
already constructed regular triangle-family flow. -/
theorem overlapVectorCover_logFlow (s : ℂ) (p : LogCover C.radius) :
    overlapVectorCover C D hrcap (logFlow C.radius s p) =
      Triangle.flow D s (overlapVectorCover C D hrcap p) := by
  unfold overlapVectorCover
  rw [Triangle.flow_quotient, Period.flow_quotientMap]
  apply congrArg D.quotient
  apply congrArg D.periods.quotientMap
  change (logBaseToRegular C.radius hrcap ⟨p.val.1, p.property⟩,
      p.val.2 + s • (![0, 1] : ComplexPlane₂)) =
    (logBaseToRegular C.radius hrcap ⟨p.val.1, p.property⟩, p.val.2 + Period.vector s)
  rw [Period.vector_eq_smul]

variable (hperiod : ∀ s : LogBase C.radius,
  D.periods.point (logBaseToRegular C.radius hrcap s) = C.periods.point s)

include hperiod

/-- The real-coordinate family comparison is the literal vector-cover
comparison because its two actual period points agree. -/
theorem familyMap_iteratedCover_eq_vectorCover (p : LogCover C.radius) :
    familyMap C D hrcap (C.iteratedCover p) = overlapVectorCover C D hrcap p := by
  change D.quotient
      (HolomorphicPeriodMap.periodPullbackMap C.periods D.periods
        (logBaseToRegular C.radius hrcap)
        (C.periods.quotientMap (⟨p.val.1, p.property⟩, p.val.2))) = _
  exact congrArg D.quotient
    (HolomorphicPeriodMap.periodPullbackMap_quotientMap C.periods D.periods
      (logBaseToRegular C.radius hrcap) hperiod (⟨p.val.1, p.property⟩, p.val.2))

/-- The original ambient partial biholomorphism has the actual regular
vector-cover formula on every logarithmic cusp representative. -/
theorem cuspToRegularPartial_totalCuspCover (p : LogCover C.radius) :
    letI := CuspQuotient.chartedSpace C.correction C.radius C.radius_pos C.radius_lt_one
      C.holomorphic C.smallDrift
    letI := D.chartedSpace (familyCovering D)
    cuspToRegularPartial C D hrcap hperiod (totalCuspCover C.correction C.radius p) =
      overlapVectorCover C D hrcap p := by
  let := CuspQuotient.chartedSpace C.correction C.radius C.radius_pos C.radius_lt_one
    C.holomorphic C.smallDrift
  let := D.chartedSpace (familyCovering D)
  exact (cuspToRegularPartial_apply C D hrcap hperiod
    (totalCuspCover C.correction C.radius p)
    (puncturedCuspCover C.correction C.radius p).property).trans
      ((puncturedBiholomorph_cover C D hrcap hperiod p).trans
        (familyMap_iteratedCover_eq_vectorCover C D hrcap hperiod p))

/-- The genuine cusp overlap intertwines the two actual vertical flows
on its entire source.  Surjectivity of the original punctured exponential
cover supplies representatives for every point, not merely a dense set. -/
theorem cuspToRegularPartial_flow (s : ℂ)
    (x : CuspQuotient.QuotientSpace C.correction C.radius)
    (hx : CuspQuotient.projection C.correction C.radius x ≠ 0) :
    letI := CuspQuotient.chartedSpace C.correction C.radius C.radius_pos C.radius_lt_one
      C.holomorphic C.smallDrift
    letI := D.chartedSpace (familyCovering D)
    cuspToRegularPartial C D hrcap hperiod (flow C.correction C.radius s x) =
      Triangle.flow D s (cuspToRegularPartial C D hrcap hperiod x) := by
  let := CuspQuotient.chartedSpace C.correction C.radius C.radius_pos C.radius_lt_one
    C.holomorphic C.smallDrift
  let := D.chartedSpace (familyCovering D)
  obtain ⟨p, hp⟩ := puncturedCuspCover_surjective C.correction C.radius ⟨x, hx⟩
  have he : totalCuspCover C.correction C.radius p = x := congrArg Subtype.val hp
  rw [← he, flow_totalCuspCover,
    cuspToRegularPartial_totalCuspCover C D hrcap hperiod,
    cuspToRegularPartial_totalCuspCover C D hrcap hperiod]
  exact overlapVectorCover_logFlow C D hrcap s p

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction.Cusp
