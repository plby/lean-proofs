import Wikipedia.NoExoticSixSphere.SphereFourTubeBoundaryImmersion
import Wikipedia.NoExoticSixSphere.QuaternionicHopfProductEuclideanFrame
import Wikipedia.HopfProblem.DegreeCollapseEmbeddedSphereRepresentative
import Wikipedia.HopfProblem.DegreeCollapseIntegralSphereRepresentatives

/-!
# Actual embedded tube-boundary representatives with the original marking

Hurewicz and native Whitney cancellation are applied in the product source.
The proved smooth injective immersion into the native zero fiber then
preserves smooth embedded representatives. The auxiliary product frame is
used only to construct source representatives; parity is always computed
with the original outward induced frame on the actual zero boundary.
-/

noncomputable section

open Function Set ContinuousMap
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.SphereFourTube

open GLOrthonormalization EmbeddedTime QuaternionicHopf SmoothCube
open Wikipedia.HopfProblem.SingularMayerVietoris Wikipedia.HopfProblem.SphereHomology
open Wikipedia.HopfProblem.PeriodTorusHigherHomology Wikipedia.HopfProblem.DegreeCollapse

local instance : ChartedSpace (Vector 6) (Sphere 3 × Sphere 3) := southPairEuclideanAtlas
local instance : IsManifold (𝓡 6) ∞ (Sphere 3 × Sphere 3) := southPairEuclideanIsManifold
local instance : SimplyConnectedSpace (Sphere 3 × Sphere 3) :=
  HigherHomotopy.simplyConnected_product

local instance representativeSpherePiTwo (s : Sphere 3) : Subsingleton (π_ 2 (Sphere 3) s) :=
  subsingleton_sphereHomotopyGroup (by decide) s

local instance representativeProductPiTwo (p : Sphere 3 × Sphere 3) :
    Subsingleton (π_ 2 (Sphere 3 × Sphere 3) p) :=
  HigherHomotopy.subsingleton_product p.1 p.2

theorem exists_product_embedded_representative (p : Sphere 3 × Sphere 3)
    (v : SingularHomology (Sphere 3 × Sphere 3) 3) :
    ∃ g : C(Sphere 3, Sphere 3 × Sphere 3), ContMDiff (𝓡 3) (𝓡 6) ∞ g ∧
      Topology.IsClosedEmbedding g ∧ (∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) g s)) ∧
      singularHomologyMap g 3 (unitSphereTopClass 2) = v := by
  obtain ⟨f, hf⟩ := IntegralSphereRepresentatives.exists_sphereMap_of_piTwo p v
  obtain ⟨g, hg, H, hd, hi⟩ :=
    TripleParameters.exists_embedded_representative_of_normalFrame southPairEuclideanEmbedding
      southPairEuclideanNormalFrame f
  refine ⟨g, hg, hi, hd, ?_⟩
  rw [← homotopic_homologyMap H 3]
  exact hf

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  [IsManifold (𝓡 7) ∞ M] [T2Space M]
  (Φ : PartialDiffeomorph ((𝓡 3).prod (𝓡 4)) (𝓡 7) (Sphere 3 × Vector 4) M ∞)
  (hΦ : Φ.source = univ) (τ : C(M, ℝ))
  (hinner : ∀ p : Sphere 3 × Vector 4, ‖p.2‖ ≤ 3 / 2 → τ (Φ p) = ‖p.2‖ ^ 2 - 1)
  (hτ : ContMDiff (𝓡 7) 𝓘(ℝ, ℝ) ∞ τ)
  (hreg : ∀ x, τ x = 0 → Surjective (mfderiv (𝓡 7) 𝓘(ℝ, ℝ) τ x))

theorem exists_native_boundary_representative (p : Sphere 3 × Sphere 3)
    (v : SingularHomology (Sphere 3 × Sphere 3) 3) :
    letI := zeroAtlas (n := 6) τ hτ hreg;
    ∃ g : C(Sphere 3, Sphere 3 × Sphere 3),
      singularHomologyMap g 3 (unitSphereTopClass 2) = v ∧
      ContMDiff (𝓡 3) (𝓡 6) ∞ ((boundaryMap Φ hΦ τ hinner).comp g) ∧
      Topology.IsClosedEmbedding ((boundaryMap Φ hΦ τ hinner).comp g) ∧
      ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) ((boundaryMap Φ hΦ τ hinner).comp g) s) := by
  let := zeroAtlas (n := 6) τ hτ hreg
  obtain ⟨g, hg, hi, hd, hclass⟩ := exists_product_embedded_representative p v
  have hB := contMDiff_boundaryMap_euclidean Φ hΦ τ hinner hτ hreg
  refine ⟨g, hclass, hB.comp hg, ?_, ?_⟩
  · exact ((boundaryMap Φ hΦ τ hinner).comp g).continuous.isClosedEmbedding
      ((boundaryMap_injective Φ hΦ τ hinner).comp hi.injective)
  · intro s
    change Injective (mfderiv (𝓡 3) (𝓡 6) ((boundaryMap Φ hΦ τ hinner) ∘ g) s)
    rw [mfderiv_comp s (hB.mdifferentiableAt (by simp)) (hg.mdifferentiableAt (by simp))]
    exact (boundaryMap_euclidean_mfderiv_injective Φ hΦ τ hinner hτ hreg (g s)).comp (hd s)

variable [CompactSpace M] (e : EuclideanEmbedding 7 M) (r : e.TubularRetraction)
  (a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel) (m : M)

theorem exists_native_zero_parity_boundary_representative (p : Sphere 3 × Sphere 3)
    (v : SingularHomology (Sphere 3 × Sphere 3) 3)
    (hfst : singularHomologyMap ContinuousMap.fst 3 v = (2 : ℤ) • unitSphereTopClass 2) :
    letI := zeroAtlas (n := 6) τ hτ hreg;
    ∃ (g : C(Sphere 3, Sphere 3 × Sphere 3))
      (hg : ContMDiff (𝓡 3) (𝓡 6) ∞ ((boundaryMap Φ hΦ τ hinner).comp g))
      (hi : Injective ((boundaryMap Φ hΦ τ hinner).comp g))
      (hd : ∀ s, Injective
        (mfderiv (𝓡 3) (𝓡 6) ((boundaryMap Φ hΦ τ hinner).comp g) s)),
      singularHomologyMap g 3 (unitSphereTopClass 2) = v ∧
      (zeroEmbedding (n := 6) e τ hτ hreg).sphereParity
        (zeroNormalFrame (n := 6) e r τ hτ hreg a m)
        ((boundaryMap Φ hΦ τ hinner).comp g) hg hi hd = 0 := by
  let := zeroAtlas (n := 6) τ hτ hreg
  let := zero_isManifold (n := 6) τ hτ hreg
  let : CompactSpace {x : M // τ x = 0} :=
    (isClosed_eq τ.continuous continuous_const).isClosedEmbedding_subtypeVal.compactSpace
  let : Nonempty {x : M // τ x = 0} := ⟨boundaryMap Φ hΦ τ hinner p⟩
  obtain ⟨g, hclass, hg, hi, hd⟩ :=
    exists_native_boundary_representative Φ hΦ τ hinner hτ hreg p v
  obtain ⟨rZ⟩ := (zeroEmbedding (n := 6) e τ hτ hreg).nonempty_tubularRetraction
    (zeroNormalFrame (n := 6) e r τ hτ hreg a m)
  have hpar := boundary_sphere_geometricParity_zero Φ hΦ τ hinner hτ hreg e r a m rZ
    p p.1 p.2 g (by rw [hclass]; exact hfst)
  rw [EuclideanEmbedding.geometricSphereParity_eq_of_embedding _ _ _ _ hg hi.injective hd] at hpar
  exact ⟨g, hg, hi.injective, hd, hclass, hpar⟩

end NoExoticSixSphere.SphereFourTube
