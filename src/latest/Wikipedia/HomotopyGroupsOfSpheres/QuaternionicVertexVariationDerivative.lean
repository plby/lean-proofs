import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicPolygonStationarity
import Wikipedia.NoExoticSixSphere.OrthogonalVertexVariationDerivative

/-! # First variation along a symplectic vertex curve at every parameter -/

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.Polygon

open VertexSpace NoExoticSixSphere.HilbertSchmidt

variable {n m : ℕ}

theorem hasDerivAt_energy_vertexVariation_at (a b : symplecticSubgroup n)
    (τ : Fin (m + 2) → ℝ) (v : Space n m) (W : Model n m) (s : ℝ)
    (hs : vertexVariation v W s ∈ admissible a b m) :
    HasDerivAt (fun r => energy a b τ (vertexVariation v W r))
      (2 * ∑ j : Fin m, innerForm (velocityJump a b τ (vertexVariation v W s) j).val (W j).val)
      s := by
  have hsO := admissible_forget a b hs
  rw [forget_vertexVariation] at hsO
  have h := NoExoticSixSphere.OrthogonalPolygon.hasDerivAt_energy_vertexVariation_at
    a.val b.val τ (forget v) (fun j => toOrthogonalSkew n (W j)) s hsO
  have hfun : (fun r => energy a b τ (vertexVariation v W r)) =
      (fun r => NoExoticSixSphere.OrthogonalPolygon.energy a.val b.val τ
        (NoExoticSixSphere.OrthogonalPolygon.vertexVariation
          (forget v) (fun j => toOrthogonalSkew n (W j)) r)) := by
    funext r
    rw [energy, forget_vertexVariation]
  rw [hfun]
  have hj (j : Fin m) := velocityJump_forget a b τ hs j
  rw [forget_vertexVariation] at hj
  simp_rw [hj] at h
  simpa only [toOrthogonalSkew, LinearMap.coe_mk, AddHom.coe_mk] using h

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.Polygon
