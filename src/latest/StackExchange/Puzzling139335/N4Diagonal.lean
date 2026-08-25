import StackExchange.Puzzling139335.N4Diagonal.Angles
import StackExchange.Puzzling139335.N4Diagonal.Endpoint
import StackExchange.Puzzling139335.N4Diagonal.FromDissection

/-!
# The one-corner diagonal-reflection case is impossible

Starting from an actual Jordan dissection, unique corner ownership supplies
full right-angle germs. The reflected pair confines its prototype to a
triangle. Ordered support frames, actual side coverage, and the endpoint
interlacing obstruction exclude a center neighborhood in every remaining
placement. No polygonal boundary or assumed tangent ordering is used.
-/

open Set

namespace Puzzling139335.N4Diagonal.Model

/-- Every tile in the normalized actual diagonal model misses the center
in its interior. -/
theorem center_not_mem_interior (m : Model) (i : Fin 4) :
    squareCenter ∉ interior (m.piece i) := by
  have hAngles := m.angles_are_endpoints
  have hθ : m.θ = 0 ∨ m.θ = Real.pi / 2 := by
    rcases hAngles with h | h | h
    · exact Or.inl h.1
    · exact Or.inl h.1
    · exact Or.inr h.1
  have hβ : m.β = 0 ∨ m.β = Real.pi / 2 := by
    rcases hAngles with h | h | h
    · exact Or.inl h.2
    · exact Or.inr h.2
    · exact Or.inr h.2
  exact m.center_not_mem_interior_of_endpoint_angles hθ hβ i

theorem singleton_centers_not_mem_interior (m : Model) :
    squareCenter ∉ interior (m.e '' m.P) ∧
      squareCenter ∉ interior (m.f '' m.P) := by
  constructor
  · simpa [piece, pieces] using m.center_not_mem_interior 1
  · simpa [piece, pieces] using m.center_not_mem_interior 3

end Puzzling139335.N4Diagonal.Model

namespace Puzzling139335.SquareDissection

/-- With one uniquely owned square corner per tile, an actual pair related
by the anti-diagonal reflection rules out a protected center. The indices
are normalized so that piece `j` owns corner `j`.

No bound on chosen intrinsic types is needed: the actual reflected pair
already repeats the origin type. -/
theorem not_hasProtectedCenter_of_one_corner_antiDiagonal_pair (d : SquareDissection)
    (hN : d.cornerIncidenceCount = 4)
    (hOwners : ∀ j : Fin 4, corner j ∈ d.piece j)
    (hH : ReflectionSeparation.antiDiagonal '' d.piece 0 = d.piece 2) :
    ¬ d.HasProtectedCenter := by
  intro hc
  obtain ⟨m, _, hcenter⟩ := N4Diagonal.exists_model_of_actual_pair d hN hOwners hH hc
  obtain ⟨he, hf⟩ := m.singleton_centers_not_mem_interior
  exact hcenter.elim he hf

end Puzzling139335.SquareDissection
