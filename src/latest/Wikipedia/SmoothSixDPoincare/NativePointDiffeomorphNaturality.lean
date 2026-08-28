import Wikipedia.SmoothSixDPoincare.NativeChartTransition
import Wikipedia.SmoothSixDPoincare.NativePointTransitionHomology

/-!
# Native point classes transform by the actual chart derivative of a diffeomorphism

Construct the auxiliary transition neighborhood inside the preimage of the
target neighborhood. This discharges the cover-map hypothesis and gives a
formula for the original source and target point classes with no auxiliary
neighborhood or local-degree assumption in the theorem's hypotheses.
-/

noncomputable section

open Set Metric Topology Filter ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.LocalDegree

open Wikipedia.HopfProblem.SingularMayerVietoris

variable {E F G M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T1Space M]
  (x y : M) {fx : M → F} {fy : M → G}
  {Lx : E ≃L[ℝ] F} {Ly : E ≃L[ℝ] G} {Wx Wy : Set M}
  (dx : NeighborhoodData (fx ∘ NativeParametrization.centered (D := E) x) Lx
    ((NativeParametrization.centered (D := E) x).source ∩
      NativeParametrization.centered (D := E) x ⁻¹' Wx))
  (dy : NeighborhoodData (fy ∘ NativeParametrization.centered (D := E) y) Ly
    ((NativeParametrization.centered (D := E) y).source ∩
      NativeParametrization.centered (D := E) y ⁻¹' Wy))
  (e : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞) (he : e x = y)

theorem pointConnecting_diffeomorph (k : ℕ) (a : SingularHomology M (k + 1)) :
    NativeNeighborhood.sphereConnecting y dy k
      (singularHomologyMap e.toHomeomorph.toHomotopyEquiv.toFun (k + 1) a) =
      singularHomologyMap
        (LinearSphereAction.sphereMap (NativeChartTransition.linear x y e he).toContinuousLinearMap
          (NativeChartTransition.linear x y e he).injective) k
        (NativeNeighborhood.sphereConnecting x dx k a) := by
  let W := e.toHomeomorph ⁻¹' NativeNeighborhood.openSet y dy
  have hW : W ∈ 𝓝 x := by
    apply e.toHomeomorph.continuous.continuousAt
    have hy := (NativeNeighborhood.isOpen_openSet y dy).mem_nhds
      (NativeNeighborhood.center_mem_openSet y dy)
    exact he.symm ▸ hy
  obtain ⟨b⟩ := NativeChartTransition.nonempty_neighborhoodData x y e he W hW
  have hV : MapsTo e.toHomeomorph (NativeNeighborhood.openSet x b)
      (NativeNeighborhood.openSet y dy) := NativeNeighborhood.openSet_subset x b
  exact PointTransition.connecting_derivative_naturality x y e.toHomeomorph he dy b hV dx k a

end Wikipedia.SmoothSixDPoincare.LocalDegree
