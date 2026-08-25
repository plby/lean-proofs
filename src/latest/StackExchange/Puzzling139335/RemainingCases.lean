import StackExchange.Puzzling139335.CaseReduction
import StackExchange.Puzzling139335.N4
import StackExchange.Puzzling139335.N7Reduction
import StackExchange.Puzzling139335.N6

/-!
# Reduction to five corner incidences

The initial incidence bounds and the complete four-, six-, seven-, and
eight-incidence obstructions leave only the five-incidence case.
-/

namespace Puzzling139335.SquareDissection

theorem remaining_incidence_cases_five_six (d : SquareDissection)
    (hc : d.HasProtectedCenter) : d.cornerIncidenceCount = 5 ∨ d.cornerIncidenceCount = 6 := by
  rcases d.remaining_incidence_cases hc with h4 | h5 | h6 | h7
  · exact (d.not_hasProtectedCenter_of_four_incidences h4 hc).elim
  · exact Or.inl h5
  · exact Or.inr h6
  · exact (d.not_hasProtectedCenter_of_seven_incidences h7 hc).elim

theorem remaining_incidence_case_five (d : SquareDissection)
    (hc : d.HasProtectedCenter) : d.cornerIncidenceCount = 5 :=
  (d.remaining_incidence_cases_five_six hc).resolve_right (d.cornerIncidenceCount_ne_six hc)

end Puzzling139335.SquareDissection
