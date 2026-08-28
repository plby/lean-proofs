import Wikipedia.NoExoticSixSphere.RoundedTraceVerticalTubeRegularity

/-!
# Target coordinates at either end of the actual time slab

At the lower end the first coordinate is time; at the upper end it is
one minus time. Both coordinate maps are genuine ambient homeomorphisms,
and the whole slab lies in their nonnegative half-spaces.
-/

noncomputable section

open Set Function Filter
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace

open GLOrthonormalization Stiefel

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M] [CompactSpace M]
  [IsManifold (𝓡 6) ∞ M] {e : EuclideanEmbedding 6 M}
  {a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f)

def tubeSlab : Set (TimeGraphSpace (e := e)) :=
  {z | timeGraphTimeFunctional (e := e) z ∈ Icc 0 1}

def tubeEndCoordinates (top : Bool) : TimeGraphSpace (e := e) ≃ₜ
    (ℝ × Vector (e.ambientDimension + 6)) :=
  (timeGraphCoordinates (e := e)).toHomeomorph.trans
    (if top then (Homeomorph.subLeft (1 : ℝ)).prodCongr (Homeomorph.refl _)
     else Homeomorph.refl _)

theorem tubeEndCoordinates_first (top : Bool) (z : TimeGraphSpace (e := e)) :
    (tubeEndCoordinates (e := e) top z).1 =
      if top then 1 - timeGraphTimeFunctional (e := e) z
      else timeGraphTimeFunctional (e := e) z := by
  cases top <;> rfl

theorem tubeEndCoordinates_slab_nonneg (top : Bool) {z : TimeGraphSpace (e := e)}
    (hz : z ∈ tubeSlab (e := e)) : 0 ≤ (tubeEndCoordinates (e := e) top z).1 := by
  rw [tubeEndCoordinates_first]
  cases top
  · exact hz.1
  · exact sub_nonneg.mpr hz.2

theorem tubeEndCoordinates_image_slab (top : Bool) :
    tubeEndCoordinates (e := e) top '' tubeSlab (e := e) ⊆ {z | 0 ≤ z.1} := by
  rintro _ ⟨z, hz, rfl⟩
  exact tubeEndCoordinates_slab_nonneg top hz

theorem mem_nhdsWithin_slab_of_end_coordinates (top : Bool)
    {s : Set (TimeGraphSpace (e := e))} {z : TimeGraphSpace (e := e)}
    (hs : tubeEndCoordinates (e := e) top '' s ∈
      𝓝[{y | 0 ≤ y.1}] (tubeEndCoordinates (e := e) top z)) :
    s ∈ 𝓝[tubeSlab (e := e)] z := by
  let T := tubeEndCoordinates (e := e) top
  have hS : T '' s ∈ 𝓝[T '' tubeSlab (e := e)] (T z) :=
    (nhdsWithin_mono _ (tubeEndCoordinates_image_slab top)) hs
  rw [← T.isEmbedding.map_nhdsWithin_eq] at hS
  change T ⁻¹' (T '' s) ∈ 𝓝[tubeSlab (e := e)] z at hS
  simpa only [preimage_image_eq _ T.injective] using hS

end NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace
