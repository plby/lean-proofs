import Wikipedia.NoExoticSixSphere.SphereResolutionPinchScaleHomotopy
import Wikipedia.NoExoticSixSphere.TransverseSpherePinchResolution

/-!
# Immersed resolution of a pinch at any prescribed positive comparison scale

The geometric cap scale remains the one constructed from the transverse
target chart. The homotopy target may use a fixed positive scale independent
of that chart. The source homeomorphism and southern reflection remain
explicit; no double-point or frame-parity formula is asserted here.
-/

noncomputable section

open Set Function Metric Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereSumNeck

open GLOrthonormalization

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  [IsManifold (𝓡 6) ∞ M] [T2Space M] [CompactSpace M]
  (F G : C(Sphere 3, M))

theorem exists_immersed_fixed_scale_pinch {δ : ℝ} (hδ : 0 < δ)
    (hF : ContMDiff (𝓡 3) (𝓡 6) ∞ F) (hG : ContMDiff (𝓡 3) (𝓡 6) ∞ G)
    (hFi : ∀ x, Injective (mfderiv (𝓡 3) (𝓡 6) F x))
    (hGi : ∀ x, Injective (mfderiv (𝓡 3) (𝓡 6) G x))
    (hzero : F (sourceChart 0) = G (sourceChart 0))
    (ht : Surjective ((mfderiv (𝓡 3) (𝓡 6) F (sourceChart 0)).coprod
      (mfderiv (𝓡 3) (𝓡 6) G (sourceChart 0)))) :
    ∃ (ε : ℝ) (hε : 0 < ε) (K : C(Sphere 3, M)),
      ContMDiff (𝓡 3) (𝓡 6) ∞ K ∧
      (∀ x, Injective (mfderiv (𝓡 3) (𝓡 6) K x)) ∧
      K.Homotopic (comparisonPinch F G δ hδ.ne' hzero) ∧
      (∀ x ∈ northRegion, K x = F (sphereCap ε x)) ∧
      (∀ x ∈ southRegion, K x = G (sphereCap ε (reflectHead x))) := by
  obtain ⟨ε, hε, K, hK, hKi, H, hN, hS⟩ :=
    exists_immersed_reparametrized_pinch F G hF hG hFi hGi hzero ht
  exact ⟨ε, hε, K, hK, hKi,
    H.trans (comparisonPinch_scale_homotopic F G hε hδ hzero), hN, hS⟩

end NoExoticSixSphere.SphereSumNeck
