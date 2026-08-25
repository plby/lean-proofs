import StackExchange.Puzzling139335.N4Dispatch.TwoOneOne.Reflection

/-!
# The square maps of a normalized repeated corner

Once the source corner is the origin, a second corner at the bottom right
allows only vertical reflection or a quarter-turn.  A second corner at the
top right allows only the central half-turn or anti-diagonal reflection.
These alternatives are consequences of the exhaustive square-isometry
classification.
-/

open Set

namespace Puzzling139335.N4Dispatch.OneCorner

open SquareSymmetry ReflectionSeparation

theorem bottom_corner_map_forms (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (hS : e '' unitSquare ⊆ unitSquare)
    (hcorner : e (corner 0) = corner 1) :
    (∀ p, e p = vertical p) ∨ (∀ p, e p = vertical (diagonal p)) := by
  have hx := congrArg (fun p : Plane => p 0) hcorner
  have hy := congrArg (fun p : Plane => p 1) hcorner
  obtain ⟨b, hform | hform⟩ := coordinate_forms_of_maps_square_into_square e hS
  · fin_cases b
    · exfalso
      norm_num [hform, cornerFlipPoint, corner, Fin.ext_iff] at hx
    · exact Or.inl hform
    · exfalso
      norm_num [hform, cornerFlipPoint, corner, Fin.ext_iff] at hy
    · exfalso
      norm_num [hform, cornerFlipPoint, corner, Fin.ext_iff] at hx
  · fin_cases b
    · exfalso
      norm_num [hform, cornerFlipPoint, corner, Fin.ext_iff] at hx
    · exact Or.inr hform
    · exfalso
      norm_num [hform, cornerFlipPoint, corner, Fin.ext_iff] at hy
    · exfalso
      norm_num [hform, cornerFlipPoint, corner, Fin.ext_iff] at hx

theorem vertical_of_bottom_corner_pair (d : SquareDissection)
    (hc : d.HasProtectedCenter) {i j : Fin 4} (hij : i ≠ j)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he : e '' d.piece i = d.piece j)
    (hS : e '' unitSquare ⊆ unitSquare)
    (hcorner : e (corner 0) = corner 1) : e = vertical := by
  rcases bottom_corner_map_forms e hS hcorner with hreflection | hquarter
  · exact AffineIsometryEquiv.ext hreflection
  · exact (d.not_hasProtectedCenter_of_quarterTurn_pair hij e
      (TwoOneOne.quarterTurn_of_top_corner_swap e hquarter) hS he hc).elim

theorem opposite_corner_map_forms (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (hS : e '' unitSquare ⊆ unitSquare)
    (hcorner : e (corner 0) = corner 2) :
    e = AffineIsometryEquiv.pointReflection ℝ squareCenter ∨ e = antiDiagonal := by
  have hx := congrArg (fun p : Plane => p 0) hcorner
  have hy := congrArg (fun p : Plane => p 1) hcorner
  obtain ⟨b, hform | hform⟩ := coordinate_forms_of_maps_square_into_square e hS
  · fin_cases b
    · exfalso
      norm_num [hform, cornerFlipPoint, corner, Fin.ext_iff] at hx
    · exfalso
      norm_num [hform, cornerFlipPoint, corner, Fin.ext_iff] at hy
    · left
      apply AffineIsometryEquiv.ext
      intro p
      rw [hform]
      ext i
      fin_cases i <;>
        simp [cornerFlipPoint, corner, Fin.ext_iff,
          AffineIsometryEquiv.pointReflection_apply, squareCenter,
          vsub_eq_sub, vadd_eq_add] <;> ring
    · exfalso
      norm_num [hform, cornerFlipPoint, corner, Fin.ext_iff] at hx
  · fin_cases b
    · exfalso
      norm_num [hform, cornerFlipPoint, corner, Fin.ext_iff] at hx
    · exfalso
      norm_num [hform, cornerFlipPoint, corner, Fin.ext_iff] at hy
    · right
      apply AffineIsometryEquiv.ext
      intro p
      rw [hform]
      ext i
      fin_cases i <;> simp [cornerFlipPoint, corner, Fin.ext_iff]
    · exfalso
      norm_num [hform, cornerFlipPoint, corner, Fin.ext_iff] at hx

end Puzzling139335.N4Dispatch.OneCorner
