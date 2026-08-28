import Wikipedia.NoExoticSixSphere.RoundedTraceVerticalTubeEmbedding
import Wikipedia.NoExoticSixSphere.BoundaryModelImmersionNeighborhood
import Wikipedia.NoExoticSixSphere.ConvexModelHomeomorphExtension

/-!
# Uniformly invertible differential of the actual slab tube

Openness of the differential's invertibility locus is proved using tangent
trivializations for the native boundary model. Compactness then gives a
uniform radius, and shrinking preserves the checked embedding and end levels.
This does not yet assert relative openness of the tube image in the slab.
-/

noncomputable section

open Function Set Metric Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace

open GLOrthonormalization Stiefel

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M] [CompactSpace M]
  [IsManifold (𝓡 6) ∞ M] {e : EuclideanEmbedding 6 M}
  {a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f)

theorem isOpen_verticalTube_regular :
    IsOpen {q | Bijective (verticalTubeDifferential A q)} := by
  let := traceChartedSpace A
  let := trace_isManifold A
  exact isOpen_bijective_mvfderiv (contMDiff_verticalTube A)

theorem exists_verticalTube_regular_radius :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (p : ambientSet A) (v : TimeGraphFrameSpace (e := e)),
      ‖v‖ ≤ ε → Bijective (verticalTubeDifferential A (p, v)) := by
  let := isCompact_iff_compactSpace.mp (isCompact_ambientSet A)
  have hcore : (univ : Set (ambientSet A)) ×ˢ {0} ⊆
      {q | Bijective (verticalTubeDifferential A q)} := by
    rintro ⟨p, v⟩ ⟨_, hv⟩
    rcases mem_singleton_iff.mp hv with rfl
    exact bijective_verticalTubeDifferential_core A p
  obtain ⟨ε, hε, hball⟩ :=
    Wikipedia.SmoothSixDPoincare.DiskFraming.exists_pos_prod_closedBall_subset
      isCompact_univ (isOpen_verticalTube_regular A) hcore
  exact ⟨ε, hε, fun p v hv ↦ hball ⟨mem_univ p, mem_closedBall_zero_iff.mpr hv⟩⟩

theorem exists_verticalTube_chart_extension
    (q : ambientSet A × TimeGraphFrameSpace (e := e))
    (hq : Bijective (verticalTubeDifferential A q)) : letI := traceChartedSpace A;
    ∃ (U : Set (ambientSet A × TimeGraphFrameSpace (e := e)))
      (G : ((ℝ × Vector 6) × TimeGraphFrameSpace (e := e)) ≃ₜ TimeGraphSpace (e := e)),
      IsOpen U ∧ q ∈ U ∧
      U ⊆ (extChartAt ((ProductHalfSpace.model (Vector 6)).prod
        𝓘(ℝ, TimeGraphFrameSpace (e := e))) q).source ∧
      EqOn (verticalTube A) (G ∘ extChartAt ((ProductHalfSpace.model (Vector 6)).prod
        𝓘(ℝ, TimeGraphFrameSpace (e := e))) q) U := by
  let := traceChartedSpace A
  let L := ContinuousLinearEquiv.ofBijective (verticalTubeDifferential A q)
    (LinearMap.ker_eq_bot.mpr hq.1) (LinearMap.range_eq_top.mpr hq.2)
  exact exists_homeomorph_chart_of_convex_model q (convex_verticalTubeModel (e := e))
    ((contMDiff_verticalTube A).contMDiffAt.of_le (by simp)) L rfl

theorem exists_verticalTube_regular_embedding_radius :
    ∃ ε : ℝ, 0 < ε ∧
      IsClosedEmbedding
        (fun q : ambientSet A × closedBall (0 : TimeGraphFrameSpace (e := e)) ε ↦
          verticalTube A (q.1, q.2.val)) ∧
      ∀ (p : ambientSet A) (v : TimeGraphFrameSpace (e := e)), ‖v‖ ≤ ε →
        Bijective (verticalTubeDifferential A (p, v)) ∧
        timeGraphTimeFunctional (e := e) (verticalTube A (p, v)) ∈ Icc 0 1 ∧
        (timeGraphTimeFunctional (e := e) (verticalTube A (p, v)) = 0 ↔ p ∈ otherEnd A) ∧
        (timeGraphTimeFunctional (e := e) (verticalTube A (p, v)) = 1 ↔ p ∈ topEnd A) := by
  let := isCompact_iff_compactSpace.mp (isCompact_ambientSet A)
  obtain ⟨ε, hε, he, hslab⟩ := exists_verticalTube_embedding_radius A
  obtain ⟨η, hη, hreg⟩ := exists_verticalTube_regular_radius A
  let r := min ε η
  let := isCompact_iff_compactSpace.mp
    (isCompact_closedBall (0 : TimeGraphFrameSpace (e := e)) r)
  let j : ambientSet A × closedBall (0 : TimeGraphFrameSpace (e := e)) r →
      ambientSet A × closedBall (0 : TimeGraphFrameSpace (e := e)) ε :=
    fun q ↦ (q.1, ⟨q.2.val, closedBall_subset_closedBall (min_le_left ε η) q.2.property⟩)
  have hj : Injective j := by
    intro q q' h
    have hb : q.1 = q'.1 := congrArg
      (fun z : ambientSet A × closedBall (0 : TimeGraphFrameSpace (e := e)) ε ↦ z.1) h
    have hv : q.2.val = q'.2.val := congrArg
      (fun z : ambientSet A × closedBall (0 : TimeGraphFrameSpace (e := e)) ε ↦ z.2.val) h
    exact Prod.ext hb (Subtype.ext hv)
  have hc : Continuous
      (fun q : ambientSet A × closedBall (0 : TimeGraphFrameSpace (e := e)) r ↦
        verticalTube A (q.1, q.2.val)) :=
    (continuous_verticalTube A).comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  refine ⟨r, lt_min hε hη, hc.isClosedEmbedding (he.injective.comp hj), ?_⟩
  intro p v hv
  exact ⟨hreg p v (hv.trans (min_le_right ε η)),
    hslab p v (hv.trans (min_le_left ε η))⟩

end NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace
