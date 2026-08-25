import StackExchange.Puzzling139335.N4Diagonal.Endpoint.OuterModel
import StackExchange.Puzzling139335.N4Diagonal.Endpoint.Claims

/-!
# Endpoint angles in the diagonal-reflection model

The two outer endpoint pairs are excluded by the triangle containing the
prototype. In the mixed pair, an actual center-containing placement forces
two long rectangle sides. One of the first singleton tile's actual side
contacts then interlaces with the prototype or its reflected copy.

All four actual placements, both assignments of the singleton corner types,
and both orientation parities are retained in the conclusion.
-/

open Set

namespace Puzzling139335.N4Diagonal.Endpoint

open ThreeCorners ReflectionSeparation

/-- The mixed endpoint pair excludes both actual singleton placements,
using their actual center preimages and Jordan side interlacing. -/
theorem mixed_singleton_centers_not_mem_interior (m : Model)
    (hθ : m.θ = 0) (hβ : m.β = Real.pi / 2) :
    squareCenter ∉ interior (m.e '' m.P) ∧
      squareCenter ∉ interior (m.f '' m.P) := by
  have hcontra (hc : squareCenter ∈ interior (m.e '' m.P) ∨
      squareCenter ∈ interior (m.f '' m.P)) : False := by
    obtain ⟨hu, hv⟩ := mixed_center_forces_large_sides m hθ hβ hc
    obtain ⟨hu1, hv1⟩ := mixed_side_lengths_lt_one m hθ hβ
    obtain ⟨hp, hq⟩ := mixed_vertex_coordinates m hθ hβ
    have hj : m.firstCorner = 1 ∨ m.firstCorner = 3 := by
      rcases m.corner_order with h | h
      · exact Or.inl h.1
      · exact Or.inr h.1
    have hecorner : m.e !₂[m.p 0, 0] = corner m.firstCorner := by
      rw [← hp]
      exact m.first_corner
    have hecenter :
        m.e (!₂[m.p 0, 0] +
          (1 / 2 : ℝ) • (ray (Real.pi / 2) + perpRay (Real.pi / 2))) =
          squareCenter := by
      rw [← hp]
      have hpre : m.e.symm squareCenter =
          m.p + (1 / 2 : ℝ) • (ray (Real.pi / 2) + perpRay (Real.pi / 2)) := by
        rw [m.first_center]
        ext i
        fin_cases i <;> norm_num [hθ, ray, perpRay, sub_eq_add_neg]
      rw [← hpre, m.e.apply_symm_apply]
    have hdisP : Disjoint (interior m.P) (interior (m.e '' m.P)) := by
      simpa [pieces] using m.disjoint (by decide : (0 : Fin 4) ≠ 1)
    have hdisH : Disjoint (interior (m.e '' m.P))
        (interior (antiDiagonal '' m.P)) := by
      simpa [pieces] using m.disjoint (by decide : (1 : Fin 4) ≠ 2)
    exact mixed_endpoint_placement_impossible m.jordan m.subset_square m.origin_mem
      (hp ▸ m.p_mem) (hq ▸ m.q_mem) hu hu1 hv hv1 m.e m.first_subset
      hdisP hdisH m.firstCorner hj hecorner hecenter
  exact ⟨fun hc => hcontra (Or.inl hc), fun hc => hcontra (Or.inr hc)⟩

end Puzzling139335.N4Diagonal.Endpoint

namespace Puzzling139335.N4Diagonal.Model

/-- No actual tile contains the center when both ordered parameters are
endpoint angles. The ordering excludes the fourth, reversed endpoint pair. -/
theorem center_not_mem_interior_of_endpoint_angles (m : Model)
    (hθ : m.θ = 0 ∨ m.θ = Real.pi / 2)
    (hβ : m.β = 0 ∨ m.β = Real.pi / 2) (i : Fin 4) :
    squareCenter ∉ interior (m.piece i) := by
  obtain ⟨hzero, htwo⟩ := Endpoint.repeated_centers_not_mem_interior m
  have hsingle : squareCenter ∉ interior (m.e '' m.P) ∧
      squareCenter ∉ interior (m.f '' m.P) := by
    rcases hθ with hθ | hθ <;> rcases hβ with hβ | hβ
    · exact Endpoint.low_singleton_centers_not_mem_interior m hθ hβ
    · exact Endpoint.mixed_singleton_centers_not_mem_interior m hθ hβ
    · have horder := m.beta_bounds.1
      rw [hθ, hβ] at horder
      exfalso
      linarith [Real.pi_pos]
    · exact Endpoint.high_singleton_centers_not_mem_interior m hθ hβ
  fin_cases i
  · simpa [piece, pieces] using hzero
  · simpa [piece, pieces] using hsingle.1
  · simpa [piece, pieces] using htwo
  · simpa [piece, pieces] using hsingle.2

/-- The entire endpoint-angle model has no protected center. -/
theorem no_protected_center_of_endpoint_angles (m : Model)
    (hθ : m.θ = 0 ∨ m.θ = Real.pi / 2)
    (hβ : m.β = 0 ∨ m.β = Real.pi / 2) :
    ¬ ∃ i : Fin 4, squareCenter ∈ interior (m.piece i) := by
  rintro ⟨i, hi⟩
  exact m.center_not_mem_interior_of_endpoint_angles hθ hβ i hi

end Puzzling139335.N4Diagonal.Model
