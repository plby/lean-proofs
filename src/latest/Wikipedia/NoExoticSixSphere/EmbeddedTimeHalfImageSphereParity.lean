import Wikipedia.NoExoticSixSphere.SphereFourTubeHalfImageSphereParity
import Wikipedia.NoExoticSixSphere.SphereFourTubeExteriorConnectivity
import Wikipedia.NoExoticSixSphere.TimeCollarPositiveCoreTube

/-!
# Original sphere parity vanishes for every even integral half image

An arbitrary integral half-image class is represented by the actual positive
core tube. Its regular collared exterior is constructed and proved
two-connected. The double-core annulus comparison then proves zero parity
for the original embedded boundary sphere and original outward frame.
The half-image class may be nonzero or torsion. No auxiliary exterior,
annulus, or vanishing half-image obstruction is assumed.
-/

noncomputable section

open Function Set ContinuousMap
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.EmbeddedTime

open GLOrthonormalization SphereFourTube
open Wikipedia.HopfProblem.SingularMayerVietoris Wikipedia.HopfProblem.SphereHomology
open Wikipedia.HopfProblem.DegreeCollapse Wikipedia.HopfProblem.DegreeCollapse.TimeCollar

variable {M B : Type} [TopologicalSpace M] [TopologicalSpace B]
  [ChartedSpace (Vector 7) M] [IsManifold (𝓡 7) ∞ M] [T2Space M] [CompactSpace M]
  (e : EuclideanEmbedding 7 M) (r : e.TubularRetraction) (t : C(M, ℝ))
  (ht : ContMDiff (𝓡 7) 𝓘(ℝ, ℝ) ∞ t)
  (hreg : ∀ x, t x = 0 → Surjective (mfderiv (𝓡 7) 𝓘(ℝ, ℝ) t x))
  (a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel) (m : M)
  (C : TimeCollar t B) [SimplyConnectedSpace (NonnegativeHalf t)]
  [Subsingleton (SingularHomology (NonnegativeHalf t) 2)]

include C in
theorem sphereParity_zero_of_even_half_image
    (f : C(Sphere 3, {x : M // t x = 0})) (y : SingularHomology (NonnegativeHalf t) 3)
    (hclass : singularHomologyMap (SphereFourTube.zeroToHalf t) 3
      (singularHomologyMap f 3 (unitSphereTopClass 2)) = (2 : ℤ) • y) :
    letI := zeroAtlas (n := 6) t ht hreg;
    ∀ (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f) (hi : Injective f)
      (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) f s)),
      (zeroEmbedding (n := 6) e t ht hreg).sphereParity
        (zeroNormalFrame (n := 6) e r t ht hreg a m) f hf hi hd = 0 := by
  let := zeroAtlas (n := 6) t ht hreg
  intro hf hi hd
  obtain ⟨g, _, _, _, hgclass, Φ, hΦ, hΦpos, hcore⟩ :=
    exists_positive_core_fourNormalTube e a C y
  have hpos : ∀ x ∈ Φ.target, 0 < t x := fun x hx ↦ hΦpos hx
  have hcoreMap : coreInHalf Φ hΦ t hpos = C.interiorToHalf.comp g := by
    apply ContinuousMap.ext
    intro s
    apply Subtype.ext
    exact hcore s
  have hcoreClass : singularHomologyMap (SphereFourTube.zeroToHalf t) 3
      (singularHomologyMap f 3 (unitSphereTopClass 2)) =
      (2 : ℤ) • singularHomologyMap (coreInHalf Φ hΦ t hpos) 3 (unitSphereTopClass 2) := by
    rw [hcoreMap, hgclass]
    exact hclass
  obtain ⟨τ, D, hτ, hτreg, hout, hinner, hhalf, hSC, hH₂, _, _, _⟩ :=
    exists_two_connected_collared_exterior Φ hΦ t C hpos ht hreg
  let : SimplyConnectedSpace (NonnegativeHalf τ) := hSC
  let : Subsingleton (SingularHomology (NonnegativeHalf τ) 2) := hH₂
  let w : NonnegativeHalf τ := Classical.arbitrary _
  let : Subsingleton (π_ 2 (NonnegativeHalf τ) w) :=
    (Wikipedia.HopfProblem.SecondHurewicz.SimplyConnected.hurewiczPi2Equiv w).injective.subsingleton
  exact SphereFourTube.sphereParity_zero_of_double_core_image
    Φ hΦ t τ hpos hout hhalf hinner ht hτ hreg hτreg e r a m D w f hcoreClass hf hi hd

include C in
theorem sphereParity_zero_of_even_cube_half_image
    (f : C(Sphere 3, {x : M // t x = 0})) (y : SingularHomology (NonnegativeHalf t) 3)
    (hclass : singularHomologyMap (SphereFourTube.zeroToHalf t) 3
      (SmoothCube.integralSphereClass f) = (2 : ℤ) • y) :
    letI := zeroAtlas (n := 6) t ht hreg;
    ∀ (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f) (hi : Injective f)
      (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) f s)),
      (zeroEmbedding (n := 6) e t ht hreg).sphereParity
        (zeroNormalFrame (n := 6) e r t ht hreg a m) f hf hi hd = 0 := by
  let := zeroAtlas (n := 6) t ht hreg
  intro hf hi hd
  rcases CubeSphereGenerator.standard_or_negative with hp | hn
  · exact sphereParity_zero_of_even_half_image e r t ht hreg a m C f y
      (by simpa only [SmoothCube.integralSphereClass, hp] using hclass) hf hi hd
  · exact sphereParity_zero_of_even_half_image e r t ht hreg a m C f (-y)
      (by simpa only [SmoothCube.integralSphereClass, hn, map_neg, neg_neg, zsmul_neg]
        using congrArg Neg.neg hclass) hf hi hd

end NoExoticSixSphere.EmbeddedTime
