import Wikipedia.SmoothSixDPoincare.NativePointTransition

/-!
# The actual native point connecting map is independent of neighborhood radius

Restrict the same whole-ball estimate to any smaller positive radius.
The identity cover map has exactly the identity sphere-coordinate map,
because the actual centered chart cancels with its inverse. Naturality
therefore proves radius independence, and a common smaller radius compares
any two constructed neighborhood data at the same native point.
-/

noncomputable section

open Set Metric Topology ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.LocalDegree

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

namespace NeighborhoodData

variable {f : E → F} {L : E ≃L[ℝ] F} {s : Set E}

def restrictRadius (d : NeighborhoodData f L s) (r : ℝ) (hr : 0 < r) (hrR : r ≤ d.radius) :
    NeighborhoodData f L s where
  radius := r
  radius_pos := hr
  center_zero := d.center_zero
  ball_subset := (closedBall_subset_closedBall hrR).trans d.ball_subset
  continuous := d.continuous.mono (closedBall_subset_closedBall hrR)
  remainder_bound x hx := d.remainder_bound x (closedBall_subset_closedBall hrR hx)

end NeighborhoodData

namespace NativeNeighborhood

open Wikipedia.HopfProblem.SingularMayerVietoris
  Wikipedia.HopfProblem.PeriodTorusHigherHomology

private theorem identity_center {M : Type} [TopologicalSpace M] (x : M) :
    (Homeomorph.refl M) x = x := rfl

variable {M : Type} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  (x : M) {f : M → F} {L : E ≃L[ℝ] F} {W : Set M}
  (d : NeighborhoodData (f ∘ NativeParametrization.centered (D := E) x) L
    ((NativeParametrization.centered (D := E) x).source ∩
      NativeParametrization.centered (D := E) x ⁻¹' W))
  (r : ℝ) (hr : 0 < r) (hrR : r ≤ d.radius)

theorem openSet_restrictRadius_subset : openSet x (d.restrictRadius r hr hrR) ⊆ openSet x d := by
  change (NativeParametrization.centered (D := E) x).toOpenPartialHomeomorph '' ball 0 r ⊆
    (NativeParametrization.centered (D := E) x).toOpenPartialHomeomorph '' ball 0 d.radius
  exact image_mono (ball_subset_ball hrR)

theorem mapsTo_restrictRadius :
    MapsTo (Homeomorph.refl M) (openSet x (d.restrictRadius r hr hrR)) (openSet x d) :=
  openSet_restrictRadius_subset x d r hr hrR

theorem coordinateMap_restrictRadius :
    PointTransition.coordinateMap x x (d.restrictRadius r hr hrR) d (Homeomorph.refl M)
      (identity_center x) (mapsTo_restrictRadius x d r hr hrR) =
        ContinuousMap.id (sphere (0 : E) 1) := by
  apply ContinuousMap.ext
  intro u
  apply Subtype.ext
  rw [PointTransition.coordinateMap_coe]
  let ds := d.restrictRadius r hr hrR
  change ‖(NativeParametrization.centered (D := E) x).symm
      (NativeParametrization.centered (D := E) x (ds.innerBoundary.radius • (u : E)))‖⁻¹ •
    (NativeParametrization.centered (D := E) x).symm
      (NativeParametrization.centered (D := E) x (ds.innerBoundary.radius • (u : E))) = (u : E)
  have hu : ds.innerBoundary.radius • (u : E) ∈ (NativeParametrization.centered x).source :=
    closedBall_subset_source x ds (ball_subset_closedBall (ds.innerBoundary_mem_ball u))
  have hleft : (NativeParametrization.centered (D := E) x).symm
      (NativeParametrization.centered (D := E) x (ds.innerBoundary.radius • (u : E))) =
        ds.innerBoundary.radius • (u : E) := (NativeParametrization.centered x).left_inv' hu
  rw [hleft, norm_radius_smul _ ds.innerBoundary.radius_pos,
    inv_smul_smul₀ ds.innerBoundary.radius_pos.ne']

variable [T1Space M]

theorem sphereConnecting_restrictRadius (k : ℕ) (a : SingularHomology M (k + 1)) :
    sphereConnecting x (d.restrictRadius r hr hrR) k a = sphereConnecting x d k a := by
  have h := PointTransition.connecting_naturality x x (d.restrictRadius r hr hrR) d
    (Homeomorph.refl M) (identity_center x) (mapsTo_restrictRadius x d r hr hrR) k a
  rw [coordinateMap_restrictRadius, singularHomologyMap_id, LinearMap.id_apply] at h
  change sphereConnecting x (d.restrictRadius r hr hrR) k a =
    sphereConnecting x d k (singularHomologyMap (ContinuousMap.id M) (k + 1) a) at h
  rwa [singularHomologyMap_id, LinearMap.id_apply] at h

variable {F' : Type} [NormedAddCommGroup F'] [NormedSpace ℝ F']
  {f' : M → F'} {L' : E ≃L[ℝ] F'} {W' : Set M}

/-- The actual source point map does not depend on the auxiliary regular-zero function or radius. -/
theorem sphereConnecting_eq
    (d' : NeighborhoodData (f' ∘ NativeParametrization.centered (D := E) x) L'
      ((NativeParametrization.centered (D := E) x).source ∩
        NativeParametrization.centered (D := E) x ⁻¹' W'))
    (k : ℕ) (a : SingularHomology M (k + 1)) :
    sphereConnecting x d k a = sphereConnecting x d' k a := by
  let ρ := min d.radius d'.radius
  have hρ : 0 < ρ := lt_min d.radius_pos d'.radius_pos
  rw [← sphereConnecting_restrictRadius x d ρ hρ (min_le_left _ _) k a,
    ← sphereConnecting_restrictRadius x d' ρ hρ (min_le_right _ _) k a]
  rfl

end NativeNeighborhood

end Wikipedia.SmoothSixDPoincare.LocalDegree
