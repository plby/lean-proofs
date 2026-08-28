import Wikipedia.NoExoticSixSphere.SphereFourTubeMeridianOperator
import Wikipedia.NoExoticSixSphere.EmbeddedTimeBoundaryGermParity

/-!
# Zero parity of the actual normal meridian for the original induced frame

The actual normal disk supplies its smooth immersive boundary germ,
positive radial time derivative, and extending normal-plus-derivative
operator. The signed criterion therefore gives parity zero for the
original outward zero-frame in the native regular zero atlas.
-/

noncomputable section

open Function Set ContinuousMap
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.SphereFourTube

open GLOrthonormalization EmbeddedTime

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  [IsManifold (𝓡 7) ∞ M] [T2Space M]
  (Φ : PartialDiffeomorph ((𝓡 3).prod (𝓡 4)) (𝓡 7) (Sphere 3 × Vector 4) M ∞)
  (hΦ : Φ.source = univ) (τ : C(M, ℝ))
  (hinner : ∀ p : Sphere 3 × Vector 4, ‖p.2‖ ≤ 3 / 2 → τ (Φ p) = ‖p.2‖ ^ 2 - 1)
  (hτ : ContMDiff (𝓡 7) 𝓘(ℝ, ℝ) ∞ τ)
  (hreg : ∀ x, τ x = 0 → Surjective (mfderiv (𝓡 7) 𝓘(ℝ, ℝ) τ x))
  (e : EuclideanEmbedding 7 M) (r : e.TubularRetraction)
  (a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel) (m : M)

theorem meridian_sphereParity_zero (s : Sphere 3) : letI := zeroAtlas (n := 6) τ hτ hreg;
    (zeroEmbedding (n := 6) e τ hτ hreg).sphereParity
      (zeroNormalFrame (n := 6) e r τ hτ hreg a m) (meridianMap Φ hΦ τ hinner s)
      (contMDiff_meridianMap Φ hΦ τ hinner hτ hreg s)
      (meridianMap_injective Φ hΦ τ hinner s)
      (meridianMap_mfderiv_injective Φ hΦ τ hinner hτ hreg s) = 0 := by
  let := zeroAtlas (n := 6) τ hτ hreg
  apply (sphereParity_zero_iff_signed_germOperator_extends e r τ hτ hreg a m true
    (meridianMap Φ hΦ τ hinner s) (normalDisk Φ s)
    (fun _ ↦ (contMDiff_normalDisk Φ hΦ s).contMDiffAt) (fun _ ↦ rfl)
    (normalDiskBoundaryOperator Φ hΦ e a s)
    (normalDiskBoundaryOperator_value Φ hΦ e a s) ?_
    (contMDiff_meridianMap Φ hΦ τ hinner hτ hreg s)
    (meridianMap_injective Φ hΦ τ hinner s)
    (meridianMap_mfderiv_injective Φ hΦ τ hinner hτ hreg s)).mpr
  · exact normalDiskBoundaryOperator_extends Φ hΦ e a s
  · intro v
    change 0 < fderiv ℝ (τ ∘ normalDisk Φ s) v.val v.val
    rw [normalDisk_radial_time_derivative Φ τ hinner s v]
    norm_num

end NoExoticSixSphere.SphereFourTube
