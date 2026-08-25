import StackExchange.Puzzling139335.N4Dispatch
import StackExchange.Puzzling139335.N4OuterPairConclusion

/-!
# Four square-corner incidences exclude a protected center

The finite dispatch and all normalized geometric cases are discharged.
Only the actual dissection and its corner-incidence count are assumed.
-/

namespace Puzzling139335.SquareDissection

theorem not_hasProtectedCenter_of_four_incidences (d : SquareDissection)
    (hN : d.cornerIncidenceCount = 4) : ¬ d.HasProtectedCenter := by
  intro hc
  obtain ⟨D, hD, hcfg⟩ := N4Dispatch.exists_outerPair_of_four_incidences d hc hN
  exact hcfg.not_protectedCenter hD

end Puzzling139335.SquareDissection
