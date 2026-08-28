import Wikipedia.SmoothSixDPoincare.NativePointCoordinates
import Wikipedia.SmoothSixDPoincare.NormalizedCoverConnecting

/-!
# Native point classes under an actual point-moving homeomorphism

The homeomorphism carries the source chart neighborhood into the target
one. In the genuine overlap-sphere coordinates, its map is exactly the
target chart inverse of the moved source boundary, radially normalized.
Native connecting-map naturality gives its action on the source classes.
-/

noncomputable section

open Set Metric Topology ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.LocalDegree.PointTransition

open Wikipedia.HopfProblem.SingularMayerVietoris

theorem maps_point_complement {M : Type} [TopologicalSpace M]
    (e : M ≃ₜ M) (x y : M) (he : e x = y) : MapsTo e {x}ᶜ {y}ᶜ := by
  intro z hz h
  exact hz (e.injective (h.trans he.symm))

variable {E F G M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  (x y : M) {fx : M → F} {fy : M → G}
  {Lx : E ≃L[ℝ] F} {Ly : E ≃L[ℝ] G} {Wx Wy : Set M}
  (dx : NeighborhoodData (fx ∘ NativeParametrization.centered (D := E) x) Lx
    ((NativeParametrization.centered (D := E) x).source ∩
      NativeParametrization.centered (D := E) x ⁻¹' Wx))
  (dy : NeighborhoodData (fy ∘ NativeParametrization.centered (D := E) y) Ly
    ((NativeParametrization.centered (D := E) y).source ∩
      NativeParametrization.centered (D := E) y ⁻¹' Wy))
  (e : M ≃ₜ M) (he : e x = y)
  (hV : MapsTo e (NativeNeighborhood.openSet x dx) (NativeNeighborhood.openSet y dy))

def coordinateMap : C(sphere (0 : E) 1, sphere (0 : E) 1) :=
  CoverNaturality.overlapCoordinateMap {x}ᶜ (NativeNeighborhood.openSet x dx)
    {y}ᶜ (NativeNeighborhood.openSet y dy) e.toHomotopyEquiv.toFun
    (maps_point_complement e x y he) hV
    (NativeNeighborhood.overlapSphereEquiv x dx) (NativeNeighborhood.overlapSphereEquiv y dy)

/-- The coordinate map is the literal centered-chart transition on the original boundary. -/
theorem coordinateMap_coe (u : sphere (0 : E) 1) :
    (coordinateMap x y dx dy e he hV u).val =
      ‖(NativeParametrization.centered (D := E) y).symm
        (e (NativeParametrization.centered (D := E) x (dx.innerBoundary.radius • (u : E))))‖⁻¹ •
      (NativeParametrization.centered (D := E) y).symm
        (e (NativeParametrization.centered (D := E) x (dx.innerBoundary.radius • (u : E)))) := rfl

variable [T1Space M]

theorem connecting_naturality (k : ℕ) (a : SingularHomology M (k + 1)) :
    singularHomologyMap (coordinateMap x y dx dy e he hV) k
      (NativeNeighborhood.sphereConnecting x dx k a) =
        NativeNeighborhood.sphereConnecting y dy k
          (singularHomologyMap e.toHomotopyEquiv.toFun (k + 1) a) :=
  CoverNaturality.normalized_connecting_naturality {x}ᶜ (NativeNeighborhood.openSet x dx)
    {y}ᶜ (NativeNeighborhood.openSet y dy) e.toHomotopyEquiv.toFun
    (maps_point_complement e x y he) hV
    (NativeNeighborhood.overlapSphereEquiv x dx) (NativeNeighborhood.overlapSphereEquiv y dy)
    isClosed_singleton.isOpen_compl (NativeNeighborhood.isOpen_openSet x dx)
    (NativeNeighborhood.singlePoint_cover x dx)
    isClosed_singleton.isOpen_compl (NativeNeighborhood.isOpen_openSet y dy)
    (NativeNeighborhood.singlePoint_cover y dy) k a

end Wikipedia.SmoothSixDPoincare.LocalDegree.PointTransition
