import StackExchange.Puzzling139335.GeometricReduction
import StackExchange.Puzzling139335.N8

/-!
# Remaining incidence cases

The eight-incidence theorem applies with the now-proved intrinsic-type
bound. Therefore a putative counterexample can only have four, five, six,
or seven corner incidences. The remaining exclusions are separate proof
obligations, not assumptions of the dissection or of this reduction.
-/

namespace Puzzling139335.SquareDissection

/-- The full eight-incidence exclusion, with the intrinsic-type hypothesis
discharged by the rectangular-hull obstruction. -/
theorem not_hasProtectedCenter_of_eight_incidences (d : SquareDissection)
    (hN : d.cornerIncidenceCount = 8) : ¬ d.HasProtectedCenter := by
  intro hc
  exact d.not_hasProtectedCenter_of_eight_incidences_of_le_three_types hN
    (d.usedCornerTypes_card_le_three hc) hc

theorem cornerIncidenceCount_le_seven (d : SquareDissection)
    (hc : d.HasProtectedCenter) : d.cornerIncidenceCount ≤ 7 := by
  have hle := (d.cornerIncidenceCount_bounds hc).2
  have hne : d.cornerIncidenceCount ≠ 8 :=
    fun h => d.not_hasProtectedCenter_of_eight_incidences h hc
  omega

theorem remaining_incidence_cases (d : SquareDissection) (hc : d.HasProtectedCenter) :
    d.cornerIncidenceCount = 4 ∨ d.cornerIncidenceCount = 5 ∨
      d.cornerIncidenceCount = 6 ∨ d.cornerIncidenceCount = 7 := by
  have hlo := (d.cornerIncidenceCount_bounds hc).1
  have hhi := d.cornerIncidenceCount_le_seven hc
  omega

end Puzzling139335.SquareDissection
