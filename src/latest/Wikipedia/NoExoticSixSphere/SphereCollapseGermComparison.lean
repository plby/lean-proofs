import Wikipedia.NoExoticSixSphere.SphereFiberGermHomotopy
import Wikipedia.NoExoticSixSphere.LocalSphereCollapse
import Wikipedia.NoExoticSixSphere.IteratedSphereSuspension

/-!
# Fiber-germ comparison for the actual framed collapse and its finite suspensions

An arbitrary sphere map with the original framed collapse's exact fiber and
the same local germ along the compactified embedding is homotopic to that
collapse. This does not require a homotopy as input. A common infinity value
is fixed by the constructed homotopy. At every specified finite suspension
stage, nullhomotopy of one map is therefore equivalent to nullhomotopy of
the other. No existence of such a nullhomotopy is inferred.
-/

noncomputable section

open Filter Topology
open scoped Manifold ContDiff unitInterval

namespace NoExoticSixSphere.EuclideanEmbedding.FramedCollapseData

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {e : EuclideanEmbedding n M}
  {a : SmoothRangeFrame (𝓡 n) e.normalProjection e.NormalModel}
  (d : e.FramedCollapseData a)
  (g : C(Sphere e.ambientDimension, Sphere (e.ambientDimension - n)))
  (hfiber : ∀ y, g y = sphereZero (e.ambientDimension - n) ↔
    ∃ x, e.compactifiedEmbedding x = y)
  (hgerm : ∀ x, (g : Sphere e.ambientDimension → Sphere (e.ambientDimension - n))
    =ᶠ[𝓝 (e.compactifiedEmbedding x)] d.sphereMap)

include hfiber hgerm

/-- Exact fiber and local map germs supply an actual global homotopy of collapse maps. -/
theorem exists_homotopy_of_fiber_germs :
    ∃ H : d.sphereMap.Homotopy g, ∀ (t : I) (y : Sphere e.ambientDimension),
      d.sphereMap y = g y → H (t, y) = d.sphereMap y := by
  apply SphereFiberGerm.exists_homotopy_of_fiber_germs d.sphereMap g
    (sphereZero (e.ambientDimension - n))
  · intro y
    exact (d.sphereMap_zero_iff y).trans (hfiber y).symm
  · intro y hy
    obtain ⟨x, rfl⟩ := (d.sphereMap_zero_iff y).mp hy
    exact (hgerm x).symm

/-- The comparison retains the actual distinguished basepoint at infinity. -/
theorem exists_based_homotopy_of_fiber_germs
    (hinfty : g (sphereInfinity e.ambientDimension) = sphereInfinity (e.ambientDimension - n)) :
    ∃ H : d.sphereMap.Homotopy g, ∀ t : I,
      H (t, sphereInfinity e.ambientDimension) = sphereInfinity (e.ambientDimension - n) := by
  obtain ⟨H, hH⟩ := d.exists_homotopy_of_fiber_germs g hfiber hgerm
  refine ⟨H, fun t ↦ ?_⟩
  rw [hH t _ (d.sphereMap_infty.trans hinfty.symm), d.sphereMap_infty]

/-- Comparison at the same actual finite suspension stage, not just an abstract stable class. -/
theorem iterate_nullhomotopic_iff_of_fiber_germs (r : ℕ) :
    (SphereMapSuspension.iterate d.sphereMap r).Nullhomotopic ↔
      (SphereMapSuspension.iterate g r).Nullhomotopic := by
  obtain ⟨H, -⟩ := d.exists_homotopy_of_fiber_germs g hfiber hgerm
  have Hr := SphereMapSuspension.iterate_homotopic (show d.sphereMap.Homotopic g from ⟨H⟩) r
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨b, Hr.symm.trans hb⟩
  · rintro ⟨b, hb⟩
    exact ⟨b, Hr.trans hb⟩

end NoExoticSixSphere.EuclideanEmbedding.FramedCollapseData
