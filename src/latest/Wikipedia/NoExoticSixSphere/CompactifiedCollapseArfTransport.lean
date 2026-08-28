import Wikipedia.NoExoticSixSphere.CompactifiedCollapseSphereParity
import Wikipedia.NoExoticSixSphere.DiffeomorphQuadraticTransport

/-!
# The original geometric Arf invariant survives collapse compactification

The exact original sphere-parity comparison gives a quadratic isometry
through the homology map of the native fiber diffeomorphism. Removing
the genuine target projection chart then recovers the original default
defining-equation frame. Tubular retractions and basepoints are independent.
-/

noncomputable section

open Function Filter Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding.FramedCollapseData

open GLOrthonormalization

variable {M : Type} [TopologicalSpace M] [T2Space M] [ChartedSpace (Vector 6) M]
  [IsManifold (𝓡 6) ∞ M] [CompactSpace M] [SimplyConnectedSpace M]
  {e : EuclideanEmbedding 6 M}
  {a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel}
  (d : e.FramedCollapseData a)
  (g : C(Sphere e.ambientDimension, Sphere (e.ambientDimension - 6)))
  (hg : ContMDiff (𝓡 e.ambientDimension) (𝓡 (e.ambientDimension - 6)) ∞ g)
  (hreg : ∀ y, g y = sphereZero (e.ambientDimension - 6) →
    Surjective (mfderiv (𝓡 e.ambientDimension) (𝓡 (e.ambientDimension - 6)) g y))
  (hN : e.ambientDimension = (e.ambientDimension - 6) + 6)
  (hfiber : ∀ y, g y = sphereZero (e.ambientDimension - 6) ↔ ∃ x, e.compactifiedEmbedding x = y)
  (hgerm : ∀ x, (g : Sphere e.ambientDimension → Sphere (e.ambientDimension - 6))
    =ᶠ[𝓝 (e.compactifiedEmbedding x)] d.sphereMap)
  (b : Sphere e.ambientDimension)
  [SimplyConnectedSpace
    {y : Sphere e.ambientDimension // g y = sphereZero (e.ambientDimension - 6)}]
  (r : e.TubularRetraction) (m : M)
  (m' : {y : Sphere e.ambientDimension // g y = sphereZero (e.ambientDimension - 6)})
  [Subsingleton (π_ 2 M m)]
  [Subsingleton (π_ 2
    {y : Sphere e.ambientDimension // g y = sphereZero (e.ambientDimension - 6)} m')]

local notation "eC" => RegularSphereFiber.embedding g hg (sphereZero (e.ambientDimension - 6))
  hreg 6 hN
local notation "aC" => RegularSphereFiber.frameWithTargetChart g hg
  (sphereZero (e.ambientDimension - 6)) hreg 6 hN b
  (sphereProjectionDiffeomorph (e.ambientDimension - 6)) (sphereZero_mem_projection_source _)
local notation "D" => e.diffeomorphToCompactifiedFiber g hg hreg hN hfiber

include hfiber hgerm in
theorem geometricArf_compactified_targetChart :
    letI := regularFiberAtlas g hg (sphereZero (e.ambientDimension - 6)) hreg 6
      (by simpa using hN);
    letI := regularFiber_isManifold g hg (sphereZero (e.ambientDimension - 6)) hreg 6 _;
    letI := RegularSphereFiber.fiber_compact g (sphereZero (e.ambientDimension - 6));
    ∀ r' : (eC).TubularRetraction,
      GeometricArf.invariant eC aC r' m' = GeometricArf.invariant e a r m := by
  let := regularFiberAtlas g hg (sphereZero (e.ambientDimension - 6)) hreg 6
    (by simpa using hN)
  let := regularFiber_isManifold g hg (sphereZero (e.ambientDimension - 6)) hreg 6
    (by simpa using hN)
  let := RegularSphereFiber.fiber_compact g (sphereZero (e.ambientDimension - 6))
  intro r'
  exact (DiffeomorphQuadraticTransport.geometricArf_eq D e eC a aC
    (fun f hf hi hdf ↦ d.compactified_sphereParity g hg hreg hN hfiber hgerm b f hf hdf hi)
    r r' m m').symm

include hfiber hgerm in
theorem geometricArf_compactified :
    letI := regularFiberAtlas g hg (sphereZero (e.ambientDimension - 6)) hreg 6
      (by simpa using hN);
    letI := regularFiber_isManifold g hg (sphereZero (e.ambientDimension - 6)) hreg 6 _;
    letI := RegularSphereFiber.fiber_compact g (sphereZero (e.ambientDimension - 6));
    ∀ r' : (eC).TubularRetraction,
      GeometricArf.invariant eC
        (RegularSphereFiber.frame g hg (sphereZero (e.ambientDimension - 6)) hreg 6 hN b)
        r' m' = GeometricArf.invariant e a r m := by
  let := regularFiberAtlas g hg (sphereZero (e.ambientDimension - 6)) hreg 6
    (by simpa using hN)
  let := regularFiber_isManifold g hg (sphereZero (e.ambientDimension - 6)) hreg 6
    (by simpa using hN)
  let := RegularSphereFiber.fiber_compact g (sphereZero (e.ambientDimension - 6))
  intro r'
  have hC := RegularSphereFiber.geometricArf_frameWithTargetChart g hg
    (sphereZero (e.ambientDimension - 6)) hreg hN b
    (sphereProjectionDiffeomorph (e.ambientDimension - 6)) (sphereZero_mem_projection_source _)
    m' m' r' r'
  exact hC.symm.trans
    (d.geometricArf_compactified_targetChart g hg hreg hN hfiber hgerm b r m m' r')

end NoExoticSixSphere.EuclideanEmbedding.FramedCollapseData
