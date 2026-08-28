import Wikipedia.SmoothSixDPoincare.NativeDegreeNeighborhoodGeometry
import Wikipedia.SmoothSixDPoincare.LocalDegreeBoundaryHomology

/-!
# The original finite representative on a punctured native neighborhood

The full-ball estimate gives a continuous map to the punctured target on
the entire punctured neighborhood. Composing with the actual overlap-sphere
equivalence recovers precisely the already-checked inner boundary map.
-/

noncomputable section

open Set Metric Topology ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.LocalDegree

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

namespace NeighborhoodData

variable {f : E → F} {L : E ≃L[ℝ] F} {s : Set E} (d : NeighborhoodData f L s)

def puncturedMap : C(PuncturedBall.Space E d.radius, PuncturedRadial.Space F) :=
  ⟨fun x => ⟨f x.val, d.image_ne_zero
      (mem_closedBall_zero_iff.mpr x.property.2.le) x.property.1⟩,
    (d.continuous.comp_continuous continuous_subtype_val
      (fun x => mem_closedBall_zero_iff.mpr x.property.2.le)).subtype_mk _⟩

theorem puncturedMap_coe (x : PuncturedBall.Space E d.radius) :
    (d.puncturedMap x).val = f x.val := rfl

theorem puncturedMap_sphereEquiv :
    d.puncturedMap.comp (PuncturedBall.sphereHomotopyEquiv d.radius d.innerBoundary.radius
      d.innerBoundary.radius_pos (by
        rw [d.innerBoundary_radius]
        exact half_lt_self d.radius_pos)).toFun = d.innerBoundary.map := rfl

end NeighborhoodData

namespace NativeNeighborhood

variable {M : Type} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  (x : M) {f : M → F} {L : E ≃L[ℝ] F} {W : Set M}
  (d : NeighborhoodData (f ∘ NativeParametrization.centered (D := E) x) L
    ((NativeParametrization.centered (D := E) x).source ∩
      NativeParametrization.centered (D := E) x ⁻¹' W))

def overlapMap : C(↥({x}ᶜ ∩ openSet x d), PuncturedRadial.Space F) :=
  d.puncturedMap.comp (puncturedHomeomorph x d).symm.toHomotopyEquiv.toFun

theorem overlapMap_coe (y : ↥({x}ᶜ ∩ openSet x d)) : (overlapMap x d y).val = f y.val := by
  have h := congrArg Subtype.val ((puncturedHomeomorph x d).apply_symm_apply y)
  change NativeParametrization.centered x ((puncturedHomeomorph x d).symm y).val = y.val at h
  exact congrArg f h

/-- The punctured overlap map has exactly the original half-radius boundary values. -/
theorem overlapMap_sphereEquiv :
    (overlapMap x d).comp (overlapSphereEquiv x d).toFun = d.innerBoundary.map := by
  apply ContinuousMap.ext
  intro u
  apply Subtype.ext
  rw [ContinuousMap.comp_apply, overlapMap_coe, overlapSphereEquiv_apply,
    BoundaryData.map_coe]
  rfl

def normalizedOverlapMap : C(↥({x}ᶜ ∩ openSet x d), sphere (0 : F) 1) :=
  PuncturedRadial.toSphere.comp (overlapMap x d)

theorem normalizedOverlapMap_sphereEquiv :
    (normalizedOverlapMap x d).comp (overlapSphereEquiv x d).toFun =
      d.innerBoundary.normalizedMap := by
  change (PuncturedRadial.toSphere.comp (overlapMap x d)).comp _ = _
  rw [ContinuousMap.comp_assoc, overlapMap_sphereEquiv]
  rfl

end NativeNeighborhood

end Wikipedia.SmoothSixDPoincare.LocalDegree
