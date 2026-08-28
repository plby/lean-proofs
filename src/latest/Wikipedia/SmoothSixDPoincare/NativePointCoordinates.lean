import Wikipedia.SmoothSixDPoincare.NativePointConnecting

/-!
# Exact inverse coordinates of the native point-overlap sphere equivalence

The inverse map is the original centered chart inverse followed by radial
normalization. This point formula allows cover naturality to be compared
with the actual coordinate transition and its derivative.
-/

noncomputable section

open Set Metric ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare

namespace NativeParametrization

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

theorem centered_symm_self (x : M) : (centered (D := E) x).symm x = 0 := by
  have h := (centered (D := E) x).left_inv' (zero_mem_centered_source x)
  rwa [centered_zero] at h

end NativeParametrization

namespace LocalDegree.NativeNeighborhood

variable {E F M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  (x : M) {f : M → F} {L : E ≃L[ℝ] F} {W : Set M}
  (d : NeighborhoodData (f ∘ NativeParametrization.centered (D := E) x) L
    ((NativeParametrization.centered (D := E) x).source ∩
      NativeParametrization.centered (D := E) x ⁻¹' W))

theorem puncturedHomeomorph_symm_apply (y : ↥({x}ᶜ ∩ openSet x d)) :
    ((puncturedHomeomorph x d).symm y).val =
      (NativeParametrization.centered (D := E) x).symm y.val := rfl

theorem overlapSphereEquiv_inv_coe (y : ↥({x}ᶜ ∩ openSet x d)) :
    ((overlapSphereEquiv x d).invFun y).val =
      ‖(NativeParametrization.centered (D := E) x).symm y.val‖⁻¹ •
        (NativeParametrization.centered (D := E) x).symm y.val := rfl

theorem inverse_coordinate_ne_zero (y : ↥({x}ᶜ ∩ openSet x d)) :
    (NativeParametrization.centered (D := E) x).symm y.val ≠ 0 :=
  ((puncturedHomeomorph x d).symm y).property.1

end LocalDegree.NativeNeighborhood

end Wikipedia.SmoothSixDPoincare
