import Wikipedia.SmoothSixDPoincare.SmoothBoundaryBody
import Wikipedia.SmoothSixDPoincare.SphereLinearDiffeomorph

/-!
# A smooth-boundary body with exact disk coordinates

Both the whole body and its boundary have genuine disk and sphere
coordinates. Their compatibility is the ordinary sphere-to-disk inclusion.
In positive dimension the boundary also has a native smooth standard-sphere
parametrization. This data is constructed for native Morse births; it is
not inferred from a homeomorphism of boundaries.
-/

noncomputable section

open Set Topology Metric
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare

variable {G H : Type} [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
  (J : ModelWithCorners ℝ G H) (N : Type) [NormedAddCommGroup N] [NormedSpace ℝ N]

structure SmoothBoundaryDisk where
  space : SmoothBoundaryBody J
  bodyCoordinates : space.body ≃ₜ MorseHandle.UnitDisk N
  boundaryCoordinates : space.boundary ≃ₜ PuncturedHandle.UnitSphere N
  boundary_point : ∀ x : space.boundary,
    (bodyCoordinates (space.inclusion x)).val = (boundaryCoordinates x).val
  boundarySphere : ∀ n : ℕ, Module.finrank ℝ N = n + 1 →
    Nonempty (Diffeomorph J (𝓡 n) space.boundary (Hemisphere.Sphere n) ∞)

namespace SmoothBoundaryDisk

variable {J N} (D : SmoothBoundaryDisk J N)

theorem inclusion_coordinates (x : D.space.boundary) :
    D.bodyCoordinates (D.space.inclusion x) =
      ⟨(D.boundaryCoordinates x).val,
        sphere_subset_closedBall (D.boundaryCoordinates x).property⟩ :=
  Subtype.ext (D.boundary_point x)

def transport {V : SmoothBoundaryBody J} (e : SmoothBoundaryBody.Equiv D.space V) :
    SmoothBoundaryDisk J N where
  space := V
  bodyCoordinates := e.body.symm.trans D.bodyCoordinates
  boundaryCoordinates := e.boundary.symm.toHomeomorph.trans D.boundaryCoordinates
  boundary_point x := by
    change (D.bodyCoordinates (e.body.symm (V.inclusion x))).val = _
    exact (congrArg (fun z : D.space.body => (D.bodyCoordinates z).val)
      (e.symm.boundary_point x)).trans (D.boundary_point (e.boundary.symm x))
  boundarySphere n hn := (D.boundarySphere n hn).map (fun s => e.boundary.symm.trans s)

end SmoothBoundaryDisk
end Wikipedia.SmoothSixDPoincare
