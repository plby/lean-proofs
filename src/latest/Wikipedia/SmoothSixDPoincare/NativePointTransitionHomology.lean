import Wikipedia.SmoothSixDPoincare.NativePointShrink
import Wikipedia.SmoothSixDPoincare.LocalDegreeBoundarySigns

/-!
# The actual point-coordinate transition acts by its actual derivative

Use the target chart inverse after the original homeomorphism as the
auxiliary local function at the source. Its constructed inner boundary is
exactly the sphere-coordinate map from cover naturality. Linearization
therefore computes that map, while radius/function independence recovers
any original source neighborhood data.
-/

noncomputable section

open Set Metric Topology ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.LocalDegree.PointTransition

open Wikipedia.HopfProblem.SingularMayerVietoris

variable {E G M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  (x y : M) (e : M ≃ₜ M) (he : e x = y)
  {fy : M → G} {Ly : E ≃L[ℝ] G} {Wy : Set M}
  (dy : NeighborhoodData (fy ∘ NativeParametrization.centered (D := E) y) Ly
    ((NativeParametrization.centered (D := E) y).source ∩
      NativeParametrization.centered (D := E) y ⁻¹' Wy))
  {Lx : E ≃L[ℝ] E} {Wx : Set M}
  (dx : NeighborhoodData
    (((NativeParametrization.centered (D := E) y).symm ∘ e) ∘
      NativeParametrization.centered (D := E) x) Lx
    ((NativeParametrization.centered (D := E) x).source ∩
      NativeParametrization.centered (D := E) x ⁻¹' Wx))
  (hV : MapsTo e (NativeNeighborhood.openSet x dx) (NativeNeighborhood.openSet y dy))

theorem coordinateMap_eq_boundary :
    coordinateMap x y dx dy e he hV = dx.innerBoundary.normalizedMap := rfl

theorem coordinateMap_homology (k : ℕ) :
    singularHomologyMap (coordinateMap x y dx dy e he hV) k =
      singularHomologyMap
        (LinearSphereAction.sphereMap Lx.toContinuousLinearMap Lx.injective) k := by
  rw [coordinateMap_eq_boundary]
  exact dx.innerBoundary.normalized_homology_compare k

variable [T1Space M]
  {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {f₀ : M → F} {L₀ : E ≃L[ℝ] F} {W₀ : Set M}
  (d₀ : NeighborhoodData (f₀ ∘ NativeParametrization.centered (D := E) x) L₀
    ((NativeParametrization.centered (D := E) x).source ∩
      NativeParametrization.centered (D := E) x ⁻¹' W₀))

include he dx hV in
/-- The original source point class transforms by the actual coordinate derivative. -/
theorem connecting_derivative_naturality (k : ℕ) (a : SingularHomology M (k + 1)) :
    NativeNeighborhood.sphereConnecting y dy k
      (singularHomologyMap e.toHomotopyEquiv.toFun (k + 1) a) =
      singularHomologyMap (LinearSphereAction.sphereMap Lx.toContinuousLinearMap Lx.injective) k
        (NativeNeighborhood.sphereConnecting x d₀ k a) := by
  have h := connecting_naturality x y dx dy e he hV k a
  rw [coordinateMap_homology x y e he dy dx hV k,
    NativeNeighborhood.sphereConnecting_eq x dx d₀ k a] at h
  exact h.symm

end Wikipedia.SmoothSixDPoincare.LocalDegree.PointTransition
