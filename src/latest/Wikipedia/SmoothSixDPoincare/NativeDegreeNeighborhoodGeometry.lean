import Wikipedia.SmoothSixDPoincare.NativeLocalDegreeNeighborhood
import Wikipedia.SmoothSixDPoincare.ChartPuncturedBall

/-!
# The original open neighborhood of a native regular zero

The constructed coordinate ball gives an open set in the original manifold,
contained in the prescribed neighborhood. Its only zero is the original
center. The punctured set is homotopy equivalent to the actual half-radius
boundary through the original centered chart.
-/

noncomputable section

open Set Metric Topology ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.LocalDegree.NativeNeighborhood

variable {E F M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  (x : M) {f : M → F} {L : E ≃L[ℝ] F} {W : Set M}
  (d : NeighborhoodData (f ∘ NativeParametrization.centered (D := E) x) L
    ((NativeParametrization.centered (D := E) x).source ∩
      NativeParametrization.centered (D := E) x ⁻¹' W))

def openSet : Set M :=
  ChartPuncturedBall.openSet
    (NativeParametrization.centered (D := E) x).toOpenPartialHomeomorph d.radius

theorem closedBall_subset_source :
    closedBall (0 : E) d.radius ⊆ (NativeParametrization.centered x).source :=
  d.ball_subset.trans inter_subset_left

theorem isOpen_openSet : IsOpen (openSet x d) :=
  ChartPuncturedBall.isOpen_openSet (NativeParametrization.centered x).toOpenPartialHomeomorph
    d.radius (closedBall_subset_source x d)

theorem center_mem_openSet : x ∈ openSet x d := by
  have h := ChartPuncturedBall.center_mem_openSet
    (NativeParametrization.centered (D := E) x).toOpenPartialHomeomorph d.radius d.radius_pos
  change NativeParametrization.centered x (0 : E) ∈ openSet x d at h
  rwa [NativeParametrization.centered_zero] at h

theorem openSet_subset : openSet x d ⊆ W := by
  rintro y ⟨u, hu, rfl⟩
  exact (d.ball_subset (ball_subset_closedBall hu)).2

/-- On this actual open neighborhood the original function vanishes exactly at the center. -/
theorem image_eq_zero_iff {y : M} (hy : y ∈ openSet x d) : f y = 0 ↔ y = x := by
  obtain ⟨u, hu, rfl⟩ := hy
  have hzero : f (NativeParametrization.centered x u) = 0 ↔ u = 0 :=
    d.image_eq_zero_iff (ball_subset_closedBall hu)
  change f (NativeParametrization.centered x u) = 0 ↔ NativeParametrization.centered x u = x
  rw [hzero]
  constructor
  · rintro rfl
    exact NativeParametrization.centered_zero x
  · intro h
    apply (NativeParametrization.centered x).toOpenPartialHomeomorph.injOn
      ((closedBall_subset_source x d) (ball_subset_closedBall hu))
      (NativeParametrization.zero_mem_centered_source x)
    exact h.trans (NativeParametrization.centered_zero x).symm

def puncturedHomeomorph : PuncturedBall.Space E d.radius ≃ₜ ↥({x}ᶜ ∩ openSet x d) :=
  (ChartPuncturedBall.puncturedHomeomorph
    (NativeParametrization.centered x).toOpenPartialHomeomorph d.radius d.radius_pos
    (closedBall_subset_source x d)).trans (Homeomorph.setCongr (by
      change {NativeParametrization.centered x (0 : E)}ᶜ ∩ openSet x d = _
      rw [NativeParametrization.centered_zero]))

theorem puncturedHomeomorph_apply (u : PuncturedBall.Space E d.radius) :
    (puncturedHomeomorph x d u).val = NativeParametrization.centered x u.val := rfl

def overlapSphereEquiv : sphere (0 : E) 1 ≃ₕ ↥({x}ᶜ ∩ openSet x d) :=
  (PuncturedBall.sphereHomotopyEquiv d.radius d.innerBoundary.radius
    d.innerBoundary.radius_pos (by
      rw [d.innerBoundary_radius]
      exact half_lt_self d.radius_pos)).trans (puncturedHomeomorph x d).toHomotopyEquiv

theorem overlapSphereEquiv_apply (u : sphere (0 : E) 1) :
    (overlapSphereEquiv x d u).val =
      NativeParametrization.centered x (d.innerBoundary.radius • (u : E)) := rfl

end Wikipedia.SmoothSixDPoincare.LocalDegree.NativeNeighborhood
