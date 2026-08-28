import Wikipedia.NoExoticSixSphere.SphereFourTubeMeridianParity
import Wikipedia.NoExoticSixSphere.PullbackIntegralSphereMarking

/-!
# Zero quadratic value of the actual even-longitude tube-boundary class

The specified product map takes values in the native regular zero fiber,
with its original ambient embedding and outward induced frame. The source
is two-connected; no connectedness of the whole zero boundary is assumed.
The actual marked meridian has zero parity, so the integral class with
longitude coefficient two has zero pulled-back quadratic value.
-/

noncomputable section

open Function Set ContinuousMap
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.SphereFourTube

open GLOrthonormalization EmbeddedTime SmoothCube ProductThirdHomology
open Wikipedia.HopfProblem.SingularMayerVietoris Wikipedia.HopfProblem.SphereHomology

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  [IsManifold (𝓡 7) ∞ M] [T2Space M]
  (Φ : PartialDiffeomorph ((𝓡 3).prod (𝓡 4)) (𝓡 7) (Sphere 3 × Vector 4) M ∞)
  (hΦ : Φ.source = univ) (τ : C(M, ℝ))
  (hinner : ∀ p : Sphere 3 × Vector 4, ‖p.2‖ ≤ 3 / 2 → τ (Φ p) = ‖p.2‖ ^ 2 - 1)

def boundaryMap : C(Sphere 3 × Sphere 3, {x : M // τ x = 0}) :=
  ⟨fun p ↦ ⟨Φ (p.1, p.2.val), unitBoundary_time_zero Φ τ hinner p⟩,
    ((contMDiff Φ hΦ).continuous.comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _⟩

theorem boundaryMap_to_half : (zeroToHalf τ).comp (boundaryMap Φ hΦ τ hinner) =
    boundaryInNewHalf Φ hΦ τ hinner := rfl

theorem boundaryMap_rightSection (s : Sphere 3) :
    (boundaryMap Φ hΦ τ hinner).comp (rightSection s) = meridianMap Φ hΦ τ hinner s := rfl

variable [CompactSpace M] (hτ : ContMDiff (𝓡 7) 𝓘(ℝ, ℝ) ∞ τ)
  (hreg : ∀ x, τ x = 0 → Surjective (mfderiv (𝓡 7) 𝓘(ℝ, ℝ) τ x))
  (e : EuclideanEmbedding 7 M) (r : e.TubularRetraction)
  (a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel) (m : M)

local instance boundaryZeroCompact : CompactSpace {x : M // τ x = 0} :=
  (isClosed_eq τ.continuous continuous_const).isClosedEmbedding_subtypeVal.compactSpace

local instance boundarySourcePiTwo (s : Sphere 3) : Subsingleton (π_ 2 (Sphere 3) s) :=
  subsingleton_sphereHomotopyGroup (by decide) s

local instance boundarySourceSimplyConnected : SimplyConnectedSpace (Sphere 3 × Sphere 3) :=
  HigherHomotopy.simplyConnected_product

local instance boundarySourceProductPiTwo (p : Sphere 3 × Sphere 3) :
    Subsingleton (π_ 2 (Sphere 3 × Sphere 3) p) :=
  HigherHomotopy.subsingleton_product p.1 p.2

theorem boundary_marked_meridian_parity_zero :
    letI := zeroAtlas (n := 6) τ hτ hreg;
    letI := zero_isManifold (n := 6) τ hτ hreg;
    ∀ (rZ : (zeroEmbedding (n := 6) e τ hτ hreg).TubularRetraction)
    (p : Sphere 3 × Sphere 3) (s : Sphere 3),
    (zeroEmbedding (n := 6) e τ hτ hreg).pullbackIntegralParity
      (zeroNormalFrame (n := 6) e r τ hτ hreg a m) rZ (boundaryMap Φ hΦ τ hinner) p
      (singularHomologyMap (rightSection s) 3 (unitSphereTopClass 2)) = 0 := by
  let := zeroAtlas (n := 6) τ hτ hreg
  let := zero_isManifold (n := 6) τ hτ hreg
  intro rZ p s
  rw [EuclideanEmbedding.pullbackIntegralParity_markedSphereClass, boundaryMap_rightSection]
  rw [EuclideanEmbedding.geometricSphereParity_eq_of_embedding _ _ _ _
    (contMDiff_meridianMap Φ hΦ τ hinner hτ hreg s)
    (meridianMap_injective Φ hΦ τ hinner s)
    (meridianMap_mfderiv_injective Φ hΦ τ hinner hτ hreg s)]
  exact meridian_sphereParity_zero Φ hΦ τ hinner hτ hreg e r a m s

theorem boundary_even_longitude_parity_zero :
    letI := zeroAtlas (n := 6) τ hτ hreg;
    letI := zero_isManifold (n := 6) τ hτ hreg;
    ∀ (rZ : (zeroEmbedding (n := 6) e τ hτ hreg).TubularRetraction)
    (p : Sphere 3 × Sphere 3) (s v₀ : Sphere 3)
    (v : SingularHomology (Sphere 3 × Sphere 3) 3)
    (_ : singularHomologyMap ContinuousMap.fst 3 v = (2 : ℤ) • unitSphereTopClass 2),
    (zeroEmbedding (n := 6) e τ hτ hreg).pullbackIntegralParity
      (zeroNormalFrame (n := 6) e r τ hτ hreg a m) rZ (boundaryMap Φ hΦ τ hinner) p v = 0 := by
  let := zeroAtlas (n := 6) τ hτ hreg
  let := zero_isManifold (n := 6) τ hτ hreg
  intro rZ p s v₀ v hfst
  obtain ⟨k, hk⟩ := two_longitude_decomposition s v₀ v hfst
  rw [hk]
  apply EuclideanEmbedding.pullbackIntegralParity_even_longitude
  exact boundary_marked_meridian_parity_zero Φ hΦ τ hinner hτ hreg e r a m rZ p s

theorem boundary_sphere_geometricParity_zero :
    letI := zeroAtlas (n := 6) τ hτ hreg;
    letI := zero_isManifold (n := 6) τ hτ hreg;
    ∀ (rZ : (zeroEmbedding (n := 6) e τ hτ hreg).TubularRetraction)
    (p : Sphere 3 × Sphere 3) (s v₀ : Sphere 3) (f : C(Sphere 3, Sphere 3 × Sphere 3))
    (_ : singularHomologyMap ContinuousMap.fst 3
      (singularHomologyMap f 3 (unitSphereTopClass 2)) = (2 : ℤ) • unitSphereTopClass 2),
    (zeroEmbedding (n := 6) e τ hτ hreg).geometricSphereParity
      (zeroNormalFrame (n := 6) e r τ hτ hreg a m) rZ
      ((boundaryMap Φ hΦ τ hinner).comp f) = 0 := by
  let := zeroAtlas (n := 6) τ hτ hreg
  let := zero_isManifold (n := 6) τ hτ hreg
  intro rZ p s v₀ f hfst
  rw [← EuclideanEmbedding.pullbackIntegralParity_markedSphereClass _ _ _ _ p f]
  exact boundary_even_longitude_parity_zero Φ hΦ τ hinner hτ hreg e r a m rZ p s v₀ _ hfst

variable (t : C(M, ℝ)) (hpos : ∀ x ∈ Φ.target, 0 < t x)
  (hout : ∀ x ∉ closedRegion Φ 2, τ x = t x)
  (hhalf : ∀ x, 0 ≤ τ x ↔ 0 ≤ t x ∧ x ∉ openRegion Φ 1)

include hhalf in
theorem exists_old_boundary_zero_quadratic_relation
    (x : SingularHomology {q : M // t q = 0} 3)
    (hclass : singularHomologyMap (zeroToHalf t) 3 x =
      (2 : ℤ) • singularHomologyMap (coreInHalf Φ hΦ t hpos) 3 (unitSphereTopClass 2)) :
    letI := zeroAtlas (n := 6) τ hτ hreg;
    letI := zero_isManifold (n := 6) τ hτ hreg;
    ∀ (rZ : (zeroEmbedding (n := 6) e τ hτ hreg).TubularRetraction)
    (p : Sphere 3 × Sphere 3), ∃ v : SingularHomology (Sphere 3 × Sphere 3) 3,
      singularHomologyMap (oldZeroToNewHalf Φ hΦ t τ hpos hout) 3 x =
        singularHomologyMap ((zeroToHalf τ).comp (boundaryMap Φ hΦ τ hinner)) 3 v ∧
      (zeroEmbedding (n := 6) e τ hτ hreg).pullbackIntegralParity
        (zeroNormalFrame (n := 6) e r τ hτ hreg a m) rZ (boundaryMap Φ hΦ τ hinner) p v = 0 ∧
      singularHomologyMap ContinuousMap.fst 3 v = (2 : ℤ) • unitSphereTopClass 2 := by
  let := zeroAtlas (n := 6) τ hτ hreg
  let := zero_isManifold (n := 6) τ hτ hreg
  intro rZ p
  obtain ⟨v, hv, hfst⟩ :=
    old_boundary_class_of_double_core_image Φ hΦ t τ hpos hout hhalf hinner x hclass
  refine ⟨v, ?_, ?_, hfst⟩
  · rw [boundaryMap_to_half]
    exact hv
  · exact boundary_even_longitude_parity_zero Φ hΦ τ hinner hτ hreg e r a m rZ p p.1 p.2 v hfst

end NoExoticSixSphere.SphereFourTube
