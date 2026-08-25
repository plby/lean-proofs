import StackExchange.Puzzling139335.N4Diagonal.FromDissection.OrderedModel
import StackExchange.Puzzling139335.N4Diagonal.FromDissection.DistinctTypes

/-!
# An actual repeated diagonal pair gives the normalized model

The model's full corner types, their distinctness, their ordered supporting
cones, and the location of the protected center are consequences of the
actual four-piece dissection.  No geometric case exclusion is assumed.
-/

open Set

namespace Puzzling139335.N4Diagonal

open FromDissection

/-- Normalize the two remaining actual placements around a repeated
anti-diagonal pair.  A protected center must belong to one of these two
placements, and all fields of the geometric model are derived internally. -/
theorem exists_model_of_actual_pair (d : SquareDissection)
    (hN : d.cornerIncidenceCount = 4)
    (hOwners : ∀ j : Fin 4, corner j ∈ d.piece j)
    (hH : ReflectionSeparation.antiDiagonal '' d.piece 0 = d.piece 2)
    (hc : d.HasProtectedCenter) :
    ∃ m : Model, m.P = d.piece 0 ∧
      (squareCenter ∈ interior (m.e '' m.P) ∨
        squareCenter ∈ interior (m.f '' m.P)) := by
  obtain ⟨e, he⟩ := d.congruent 0 1
  obtain ⟨f, hf⟩ := d.congruent 0 3
  obtain ⟨hp0, hq0, hpq⟩ :=
    corner_preimages_distinct d hN hOwners hH hc e f he hf
  exact exists_model_of_distinct_preimages d hN hOwners hH e f he hf hp0 hq0 hpq
    (center_mem_one_or_three d hH hc)

end Puzzling139335.N4Diagonal
