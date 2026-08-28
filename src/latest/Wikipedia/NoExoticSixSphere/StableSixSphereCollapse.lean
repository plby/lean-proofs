import Wikipedia.NoExoticSixSphere.StableSixSphereMaps
import Wikipedia.NoExoticSixSphere.LocalSphereCollapse

/-!
# The original framed six-manifold's actual stable collapse class

The collapse is placed in the sixth-stem system by equality of dimensions
only. Vanishing of its actual direct-limit class is proved equivalent to
an actual finite nullhomotopy of the original sphere map. Vanishing itself
is not assumed as a class instance and is not established by this file.
-/

noncomputable section

open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding.FramedCollapseData

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 6)) M]
  {e : EuclideanEmbedding 6 M}
  {a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel}
  (d : e.FramedCollapseData a) (hd : 8 ≤ e.ambientDimension)

def sixthStageMap : StableSixSphereMaps.StageMap (e.ambientDimension - 8) :=
  SphereMapSuspension.reindex (by omega) (by omega) d.sphereMap

def sixthStableClass : StableSixSphereMaps.Class :=
  StableSixSphereMaps.ofMap (d.sixthStageMap hd)

theorem sixthStageMap_iterate_nullhomotopic_iff (r : ℕ) :
    (SphereMapSuspension.iterate (d.sixthStageMap hd) r).Nullhomotopic ↔
      (SphereMapSuspension.iterate d.sphereMap r).Nullhomotopic :=
  SphereMapSuspension.iterate_reindex_nullhomotopic_iff (by omega) (by omega) d.sphereMap r

/-- The zero-class criterion is for the original collapse, with no change of atlas or framing. -/
theorem sixthStableClass_eq_null_iff :
    d.sixthStableClass hd = StableSixSphereMaps.nullClass ↔
      ∃ r : ℕ, (SphereMapSuspension.iterate d.sphereMap r).Nullhomotopic := by
  change StableSixSphereMaps.ofMap (d.sixthStageMap hd) = _ ↔ _
  rw [StableSixSphereMaps.ofMap_eq_nullClass_iff]
  exact exists_congr (fun r ↦ d.sixthStageMap_iterate_nullhomotopic_iff hd r)

end NoExoticSixSphere.EuclideanEmbedding.FramedCollapseData
