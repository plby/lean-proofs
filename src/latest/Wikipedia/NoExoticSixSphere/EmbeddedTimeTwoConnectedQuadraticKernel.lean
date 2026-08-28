import Wikipedia.NoExoticSixSphere.EmbeddedTimeHalfImageSphereParity
import Wikipedia.NoExoticSixSphere.GeometricCapPairingComparison
import Wikipedia.NoExoticSixSphere.MiddleHomologyKernelObstruction

/-!
# The full mod-two quadratic kernel for a two-connected native boundary

Actual integral classes in the two-connected native zero boundary have
embedded sphere representatives. The even-half-image theorem proves zero
integral parity for every lift supplied by the exact coefficient sequence.
Consequently the original quadratic form vanishes on the full mod-two
boundary-to-half kernel, including classes with nonzero half-image
obstruction. The whole boundary is assumed two-connected in this file;
the corresponding sum comparison for disconnected boundaries is separate.
-/

noncomputable section

open Function Set ContinuousMap
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.EmbeddedTime

open GLOrthonormalization SmoothCube EuclideanEmbedding
open Wikipedia.HopfProblem.SingularMayerVietoris Wikipedia.HopfProblem.SphereHomologyCoefficients
open Wikipedia.HopfProblem.DegreeCollapse Wikipedia.HopfProblem.DegreeCollapse.TimeCollar

attribute [local instance] modHomologyModule

variable {M B : Type} [TopologicalSpace M] [TopologicalSpace B]
  [ChartedSpace (Vector 7) M] [IsManifold (𝓡 7) ∞ M] [T2Space M] [CompactSpace M]
  (e : EuclideanEmbedding 7 M) (r : e.TubularRetraction) (t : C(M, ℝ))
  (ht : ContMDiff (𝓡 7) 𝓘(ℝ, ℝ) ∞ t)
  (hreg : ∀ x, t x = 0 → Surjective (mfderiv (𝓡 7) 𝓘(ℝ, ℝ) t x))
  (a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel) (m : M)
  (C : TimeCollar t B) [SimplyConnectedSpace (NonnegativeHalf t)]
  [Subsingleton (SingularHomology (NonnegativeHalf t) 2)]
  [SimplyConnectedSpace {x : M // t x = 0}] (z : {x : M // t x = 0})
  [Subsingleton (π_ 2 {x : M // t x = 0} z)]

local instance twoConnectedBoundaryCompact : CompactSpace {x : M // t x = 0} :=
  (isClosed_eq t.continuous continuous_const).isClosedEmbedding_subtypeVal.compactSpace

include C in
theorem integralHomologyParity_zero_of_even_half_image :
    letI := zeroAtlas (n := 6) t ht hreg;
    letI := zero_isManifold (n := 6) t ht hreg;
    ∀ (rZ : (zeroEmbedding (n := 6) e t ht hreg).TubularRetraction)
      (x : SingularHomology {p : M // t p = 0} 3) (y : SingularHomology (NonnegativeHalf t) 3),
      singularHomologyMap (SphereFourTube.zeroToHalf t) 3 x = (2 : ℤ) • y →
      (zeroEmbedding (n := 6) e t ht hreg).integralHomologyParity
        (zeroNormalFrame (n := 6) e r t ht hreg a m) rZ z x = 0 := by
  let := zeroAtlas (n := 6) t ht hreg
  let := zero_isManifold (n := 6) t ht hreg
  intro rZ x y hclass
  let f := (integralClassRepresentative z x).val
  obtain ⟨g, hg, H, hd, hi⟩ := TripleParameters.exists_embedded_sphere_representative
    (zeroEmbedding (n := 6) e t ht hreg) rZ f
  have hgclass : integralSphereClass g = x :=
    (integralSphereClass_homotopic H).symm.trans (integralSphereClass_representative z x)
  rw [← hgclass, integralHomologyParity_sphereClass,
    geometricSphereParity_eq_of_embedding _ _ _ _ hg hi.injective hd]
  apply sphereParity_zero_of_even_cube_half_image e r t ht hreg a m C g y
    (by rw [hgclass]; exact hclass) hg hi.injective hd

include C in
theorem modTwoQuadraticForm_zero_on_full_boundary_kernel :
    letI := zeroAtlas (n := 6) t ht hreg;
    letI := zero_isManifold (n := 6) t ht hreg;
    ∀ (rZ : (zeroEmbedding (n := 6) e t ht hreg).TubularRetraction)
      (b : ModHomology 2 {x : M // t x = 0} 3),
      modHomologyMap 2 (SphereFourTube.zeroToHalf t) 3 b = 0 →
      (zeroEmbedding (n := 6) e t ht hreg).modTwoHomologyQuadraticForm
        (zeroNormalFrame (n := 6) e r t ht hreg a m) rZ z b = 0 := by
  let := zeroAtlas (n := 6) t ht hreg
  let := zero_isManifold (n := 6) t ht hreg
  let : Subsingleton (SingularHomology {x : M // t x = 0} 2) :=
    (Wikipedia.HopfProblem.SecondHurewicz.SimplyConnected.hurewiczPi2Equiv z
      ).symm.injective.subsingleton
  intro rZ b hker
  obtain ⟨x, y, hx, hclass⟩ :=
    (MiddleKernelCoefficients.kernel_iff_has_half (SphereFourTube.zeroToHalf t) b).mp hker
  rw [modTwoHomologyQuadraticForm_apply, ← hx, modTwoHomologyParity_reduction]
  exact integralHomologyParity_zero_of_even_half_image e r t ht hreg a m C z rZ x y hclass

end NoExoticSixSphere.EmbeddedTime
