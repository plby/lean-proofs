import StackExchange.Puzzling139335.N7.TwoTwoTwoOne
import StackExchange.Puzzling139335.N7.FullPairNormalization.AsNormalizedPair
import StackExchange.Puzzling139335.N7.NormalizedPair

/-!
# Seven square-corner incidences exclude a protected center

All finite type and placement reductions are derived from the actual
Jordan dissection. The two possible multiplicity patterns are excluded
without any polygonal, tangent-ray, or null-boundary assumption.
-/

namespace Puzzling139335.N7

/-- The complete seven-incidence case, with only the actual intrinsic
corner-type bound remaining as the preceding global reduction. -/
theorem not_hasProtectedCenter_of_seven_incidences (d : SquareDissection)
    (hN : d.cornerIncidenceCount = 7) (htypes : d.usedCornerTypes.card ≤ 3) :
    ¬ d.HasProtectedCenter := by
  classical
  intro hc
  obtain ⟨C⟩ := exists_pairConfiguration d hc hN htypes
  rcases corner_count_card_patterns d hc hN with hU | hU
  · exact C.not_one_unique_corner hc hU.1
  · have hfull : C.repeatedEnd ∈ N5.fullCornerTypes d := by
      rw [C.full_types_eq_repeatedEnd_of_unique_count_two hc hU.1]
      simp
    obtain ⟨D, _, ⟨N⟩⟩ := C.exists_normalizedPair_of_repeatedEnd_full hc hfull
    exact N.impossible

theorem impossible (d : SquareDissection) (hc : d.HasProtectedCenter)
    (hN : d.cornerIncidenceCount = 7) (htypes : d.usedCornerTypes.card ≤ 3) : False :=
  not_hasProtectedCenter_of_seven_incidences d hN htypes hc

end Puzzling139335.N7
