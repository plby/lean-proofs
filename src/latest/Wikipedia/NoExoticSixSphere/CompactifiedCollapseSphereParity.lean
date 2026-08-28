import Wikipedia.NoExoticSixSphere.CompactifiedCollapseSphereFrame
import Wikipedia.NoExoticSixSphere.StereographicDiskFrameCoordinates

/-!
# Original sphere parity is unchanged by collapse compactification

The fixed normal-coordinate change and the actual variable ambient
coordinates transport the original twisted disk-extension criterion.
The latter coordinates extend over the entire disk by the already
constructed global augmented differential. The moving source twist
is retained and is not assumed to extend over the disk.
-/

noncomputable section

open Function Filter Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding.FramedCollapseData

open GLOrthonormalization StereographicEquator Stiefel NormalFrameSourceCoordinates
open SpanningDiskFrameCoordinates DiskBoundary DiffeomorphSphereComposition

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  [IsManifold (𝓡 6) ∞ M] {e : EuclideanEmbedding 6 M}
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
  (f : Sphere 3 → M) (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f)
  (hdf : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) f s))

local notation "eC" => RegularSphereFiber.embedding g hg (sphereZero (e.ambientDimension - 6))
  hreg 6 hN
local notation "aC" => RegularSphereFiber.frameWithTargetChart g hg
  (sphereZero (e.ambientDimension - 6)) hreg 6 hN b
  (sphereProjectionDiffeomorph (e.ambientDimension - 6)) (sphereZero_mem_projection_source _)
local notation "D" => e.diffeomorphToCompactifiedFiber g hg hreg hN hfiber

include hgerm in
theorem compactified_raw_twisted_extension_iff :
    letI := regularFiberAtlas g hg (sphereZero (e.ambientDimension - 6)) hreg 6
      (by simpa using hN);
    Extends (twistedBlockMap ((eC).rawSphereFrameOperatorMap aC (D ∘ f)
      (DiffeomorphSphereComposition.smooth D f hf)
      (DiffeomorphSphereComposition.mfderiv_injective D f hf hdf))) ↔
    Extends (twistedBlockMap (e.rawSphereFrameOperatorMap a f hf hdf)) := by
  let := regularFiberAtlas g hg (sphereZero (e.ambientDimension - 6)) hreg 6
    (by simpa using hN)
  let F := e.rawSphereFrameOperatorMap a f hf hdf
  let G := (eC).rawSphereFrameOperatorMap aC (D ∘ f)
    (DiffeomorphSphereComposition.smooth D f hf)
    (DiffeomorphSphereComposition.mfderiv_injective D f hf hdf)
  let Q := d.compactifiedNormalCoordinates hN
  have hs := extends_twisted_sourceChange_iff Q G
  have ht := extends_twisted_augmented_iff e.ambientDimension ((e.ambientDimension - 6) + 1)
    (e.toFun ∘ f) (e.smooth.comp hf) ((NormalFrameStabilization.map 1).comp F)
    ((sourceChange Q).comp G) (fun s ↦ by
      simp only [ContinuousMap.comp_apply, NormalFrameStabilization.map_value]
      exact d.compactified_rawSphereFrameOperator g hg hreg hN hfiber f hf hgerm b s)
  have hb := NormalFrameStabilization.extends_twisted_stabilization_iff hN 1 F
  exact hs.symm.trans (ht.trans hb)

include hgerm in
theorem compactified_sphereParity (hi : Injective f) :
    letI := regularFiberAtlas g hg (sphereZero (e.ambientDimension - 6)) hreg 6
      (by simpa using hN);
    (eC).sphereParity aC (D ∘ f) (DiffeomorphSphereComposition.smooth D f hf)
      (DiffeomorphSphereComposition.injective D f hi)
      (DiffeomorphSphereComposition.mfderiv_injective D f hf hdf) =
        e.sphereParity a f hf hi hdf := by
  let := regularFiberAtlas g hg (sphereZero (e.ambientDimension - 6)) hreg 6
    (by simpa using hN)
  apply zmodTwo_eq_of_zero_iff
  have ht := (eC).sphereParity_zero_iff_raw_twisted_extension aC (D ∘ f)
    (DiffeomorphSphereComposition.smooth D f hf)
    (DiffeomorphSphereComposition.mfderiv_injective D f hf hdf)
    (DiffeomorphSphereComposition.injective D f hi)
  have hs := e.sphereParity_zero_iff_raw_twisted_extension a f hf hdf hi
  exact ht.trans ((d.compactified_raw_twisted_extension_iff
    g hg hreg hN hfiber hgerm b f hf hdf).trans hs.symm)

end NoExoticSixSphere.EuclideanEmbedding.FramedCollapseData
