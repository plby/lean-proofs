import StackExchange.Puzzling139335.GeometricReduction
import StackExchange.Puzzling139335.N7

/-!
# The seven-incidence case with the type bound discharged
-/

namespace Puzzling139335.SquareDissection

/-- No extra bound on intrinsic corner types is assumed: it follows from
the actual dissection and the hypothetical protected center. -/
theorem not_hasProtectedCenter_of_seven_incidences (d : SquareDissection)
    (hN : d.cornerIncidenceCount = 7) : ¬ d.HasProtectedCenter := by
  intro hc
  exact N7.impossible d hc hN (d.usedCornerTypes_card_le_three hc)

end Puzzling139335.SquareDissection
