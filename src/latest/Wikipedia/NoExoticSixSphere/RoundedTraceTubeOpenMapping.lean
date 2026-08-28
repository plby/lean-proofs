import Wikipedia.NoExoticSixSphere.RoundedTraceTubeBoundarySigns
import Wikipedia.NoExoticSixSphere.HalfSpaceChartOpenMapping
import Wikipedia.NoExoticSixSphere.LocalChartImageNeighborhood

/-!
# Relative openness of the actual regular tube in the time slab

At boundary points, the source-chart and target-end side conditions are
those proved for this tube. Interior points use the same actual chart
extension with an ambient-open chart neighborhood.
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

theorem verticalTube_image_mem_nhdsWithin_slab_boundary
    (q : ambientSet A × TimeGraphFrameSpace (e := e))
    (hreg : Bijective (verticalTubeDifferential A q)) (hb : q.1 ∈ traceBoundarySet A)
    {s : Set (ambientSet A × TimeGraphFrameSpace (e := e))} (hs : s ∈ 𝓝 q) :
    verticalTube A '' s ∈ 𝓝[tubeSlab (e := e)] (verticalTube A q) := by
  let := traceChartedSpace A
  obtain ⟨U, G, hU, hqU, _, hEq⟩ := exists_verticalTube_chart_extension A q hreg
  obtain ⟨top, htop⟩ := exists_zero_tubeEndTime A q.1 hb
  let R := (tubeModelCoordinates (e := e)).toHomeomorph
  let T := tubeEndCoordinates (e := e) top
  let H := R.symm.trans (G.trans T)
  have hcoord : (tubeChart A q q).1 = 0 :=
    (tubeChart_first_zero_iff A q q (mem_extChartAt_source q)).mpr hb
  have he : ∀ᶠ y in 𝓝 q, (T ∘ verticalTube A) y = H (tubeChart A q y) ∧
      ((tubeChart A q y).1 = 0 → ((T ∘ verticalTube A) y).1 = 0) ∧
      (0 < (tubeChart A q y).1 → 0 < ((T ∘ verticalTube A) y).1) := by
    filter_upwards [hU.mem_nhds hqU, eventually_tubeChart_boundary_signs A q hb top htop]
      with y hy hysign
    refine ⟨?_, hysign⟩
    change T (verticalTube A y) = T (G (R.symm (R (extChartAt
      ((ProductHalfSpace.model (Vector 6)).prod 𝓘(ℝ, TimeGraphFrameSpace (e := e))) q y))))
    rw [R.symm_apply_apply]
    exact congrArg T (hEq hy)
  have himage := ProductHalfSpace.image_mem_nhdsWithin_of_halfSpace_chart
    (tubeChart A q) (T ∘ verticalTube A) H (map_tubeChart_nhds A q) hcoord he hs
  apply mem_nhdsWithin_slab_of_end_coordinates top
  rw [← image_comp]
  exact himage

theorem verticalTube_image_mem_nhds_interior
    (q : ambientSet A × TimeGraphFrameSpace (e := e))
    (hreg : Bijective (verticalTubeDifferential A q)) (hb : q.1 ∉ traceBoundarySet A)
    {s : Set (ambientSet A × TimeGraphFrameSpace (e := e))} (hs : s ∈ 𝓝 q) :
    verticalTube A '' s ∈ 𝓝 (verticalTube A q) := by
  let := traceChartedSpace A
  let I := (ProductHalfSpace.model (Vector 6)).prod 𝓘(ℝ, TimeGraphFrameSpace (e := e))
  let c := extChartAt I q
  obtain ⟨U, G, hU, hqU, _, hEq⟩ := exists_verticalTube_chart_extension A q hreg
  have hint : c q ∈ interior (range I) := by
    rw [tubeModel_interior]
    exact (tubeChart_first_pos_iff A q q (mem_extChartAt_source q)).mpr hb
  have hc : Filter.map c (𝓝 q) = 𝓝 (c q) := by
    rw [map_extChartAt_nhds, nhdsWithin_eq_nhds.mpr (mem_interior_iff_mem_nhds.mp hint)]
  have he : ∀ᶠ y in 𝓝 q, verticalTube A y = G (c y) :=
    Filter.eventually_of_mem (hU.mem_nhds hqU) (fun y hy ↦ hEq hy)
  exact image_mem_nhds_of_homeomorph_chart c (verticalTube A) G hc he hs

theorem verticalTube_image_mem_nhdsWithin_slab
    (q : ambientSet A × TimeGraphFrameSpace (e := e))
    (hreg : Bijective (verticalTubeDifferential A q))
    {s : Set (ambientSet A × TimeGraphFrameSpace (e := e))} (hs : s ∈ 𝓝 q) :
    verticalTube A '' s ∈ 𝓝[tubeSlab (e := e)] (verticalTube A q) := by
  by_cases hb : q.1 ∈ traceBoundarySet A
  · exact verticalTube_image_mem_nhdsWithin_slab_boundary A q hreg hb hs
  · exact mem_nhdsWithin_of_mem_nhds (verticalTube_image_mem_nhds_interior A q hreg hb hs)

theorem isOpen_verticalTube_image_in_slab
    {s : Set (ambientSet A × TimeGraphFrameSpace (e := e))} (hs : IsOpen s)
    (hreg : ∀ q ∈ s, Bijective (verticalTubeDifferential A q)) :
    IsOpen {z : tubeSlab (e := e) | z.val ∈ verticalTube A '' s} := by
  rw [isOpen_iff_mem_nhds]
  intro z hz
  obtain ⟨q, hqs, hqz⟩ := hz
  have hn := verticalTube_image_mem_nhdsWithin_slab A q (hreg q hqs) (hs.mem_nhds hqs)
  rw [hqz, ← map_nhds_subtype_val z] at hn
  exact hn

end NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace
