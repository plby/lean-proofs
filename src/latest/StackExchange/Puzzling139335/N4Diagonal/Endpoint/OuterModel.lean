import StackExchange.Puzzling139335.N4Diagonal.Endpoint.MixedGeometry
import StackExchange.Puzzling139335.N4Diagonal.Endpoint.Outer

/-!
# The outer endpoint exclusions for actual placements

The support inequalities and the intrinsic center formulas of the normalized
model instantiate the two coordinate-triangle obstructions. The reflected
pair cannot contain the center because the center is fixed by the reflection.
-/

open Set

namespace Puzzling139335.N4Diagonal.Endpoint

open ThreeCorners ReflectionSeparation

/-- Neither of the two actual reflected pieces contains the fixed center
in its interior. -/
theorem repeated_centers_not_mem_interior (m : Model) :
    squareCenter ∉ interior m.P ∧
      squareCenter ∉ interior (antiDiagonal '' m.P) := by
  have hdis : Disjoint (interior m.P) (interior (antiDiagonal '' m.P)) := by
    simpa [pieces] using m.disjoint (by decide : (0 : Fin 4) ≠ 2)
  have hsymm : antiDiagonal.symm squareCenter = squareCenter := by
    calc
      antiDiagonal.symm squareCenter =
          antiDiagonal.symm (antiDiagonal squareCenter) := by rw [antiDiagonal_center]
      _ = squareCenter := antiDiagonal.symm_apply_apply squareCenter
  have hforward (hc : squareCenter ∈ interior m.P) :
      squareCenter ∈ interior (antiDiagonal '' m.P) := by
    have himage : antiDiagonal '' interior m.P = interior (antiDiagonal '' m.P) :=
      antiDiagonal.toHomeomorph.image_interior m.P
    rw [← himage]
    exact ⟨squareCenter, hc, antiDiagonal_center⟩
  have hbackward (hc : squareCenter ∈ interior (antiDiagonal '' m.P)) :
      squareCenter ∈ interior m.P := by
    simpa only [hsymm] using symm_mem_interior_of_mem_interior_image antiDiagonal hc
  exact ⟨fun hc => Set.disjoint_left.mp hdis hc (hforward hc),
    fun hc => Set.disjoint_left.mp hdis (hbackward hc) hc⟩

/-- The low endpoint pair excludes both actual singleton placements. -/
theorem low_singleton_centers_not_mem_interior (m : Model)
    (hθ : m.θ = 0) (hβ : m.β = 0) :
    squareCenter ∉ interior (m.e '' m.P) ∧
      squareCenter ∉ interior (m.f '' m.P) := by
  have hConeP : m.P ⊆ supportCone m.p (Real.pi / 2) := by
    intro x hx
    simpa [hθ, supportCone, ray, perpRay, Schoenflies.Plane.inner_eq,
      sub_nonneg, sub_nonpos] using m.first_support x hx
  have hConeQ : m.P ⊆ supportCone m.q Real.pi := by
    intro x hx
    simpa [hβ, supportCone, ray, perpRay, Schoenflies.Plane.inner_eq,
      sub_nonneg, sub_nonpos] using m.last_support x hx
  obtain ⟨hfirst, hlast⟩ := outer_low_frameCenters_not_mem_interior
    (fun _ hx => m.triangle hx) m.origin_mem m.p_mem m.q_mem hConeP hConeQ
  have hepre : m.e.symm squareCenter =
      m.p + (1 / 2 : ℝ) • (ray (Real.pi / 2) + perpRay (Real.pi / 2)) := by
    rw [m.first_center]
    ext i
    fin_cases i <;> norm_num [hθ, ray, perpRay, sub_eq_add_neg]
  have hfpre : m.f.symm squareCenter =
      m.q + (1 / 2 : ℝ) • (ray Real.pi + perpRay Real.pi) := by
    rw [m.last_center]
    ext i
    fin_cases i <;> norm_num [hβ, ray, perpRay, sub_eq_add_neg]
  constructor
  · intro hc
    apply hfirst
    rw [← hepre]
    exact symm_mem_interior_of_mem_interior_image m.e hc
  · intro hc
    apply hlast
    rw [← hfpre]
    exact symm_mem_interior_of_mem_interior_image m.f hc

/-- The high endpoint pair excludes both actual singleton placements. -/
theorem high_singleton_centers_not_mem_interior (m : Model)
    (hθ : m.θ = Real.pi / 2) (hβ : m.β = Real.pi / 2) :
    squareCenter ∉ interior (m.e '' m.P) ∧
      squareCenter ∉ interior (m.f '' m.P) := by
  have hang : (3 * Real.pi / 2 : ℝ) = Real.pi + Real.pi / 2 := by ring
  have hConeP : m.P ⊆ supportCone m.p Real.pi := by
    intro x hx
    simpa [hθ, supportCone, ray, perpRay, Schoenflies.Plane.inner_eq,
      sub_nonneg, sub_nonpos] using m.first_support x hx
  have hConeQ : m.P ⊆ supportCone m.q (3 * Real.pi / 2) := by
    intro x hx
    simpa [hβ, supportCone, ray, perpRay, Schoenflies.Plane.inner_eq, hang,
      Real.cos_add_pi_div_two, Real.sin_add_pi_div_two, sub_nonneg, sub_nonpos]
      using m.last_support x hx
  obtain ⟨hfirst, hlast⟩ := outer_high_frameCenters_not_mem_interior
    (fun _ hx => m.triangle hx) m.origin_mem m.p_mem m.q_mem hConeP hConeQ
  have hepre : m.e.symm squareCenter =
      m.p + (1 / 2 : ℝ) • (ray Real.pi + perpRay Real.pi) := by
    rw [m.first_center]
    ext i
    fin_cases i <;> norm_num [hθ, ray, perpRay, sub_eq_add_neg]
  have hfpre : m.f.symm squareCenter =
      m.q + (1 / 2 : ℝ) •
        (ray (3 * Real.pi / 2) + perpRay (3 * Real.pi / 2)) := by
    rw [m.last_center]
    ext i
    fin_cases i <;> norm_num [hβ, ray, perpRay, hang, Real.cos_add_pi_div_two,
      Real.sin_add_pi_div_two, sub_eq_add_neg]
  constructor
  · intro hc
    apply hfirst
    rw [← hepre]
    exact symm_mem_interior_of_mem_interior_image m.e hc
  · intro hc
    apply hlast
    rw [← hfpre]
    exact symm_mem_interior_of_mem_interior_image m.f hc

end Puzzling139335.N4Diagonal.Endpoint
