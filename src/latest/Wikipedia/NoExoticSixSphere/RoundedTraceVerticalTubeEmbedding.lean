import Wikipedia.NoExoticSixSphere.RoundedTraceVerticalTubeSlab
import Wikipedia.NoExoticSixSphere.ConvexModelLocalInjectivity
import Wikipedia.NoExoticSixSphere.CompactCoreImmersion

/-!
# A uniformly embedded displacement tube respecting the slab ends

Local injectivity is proved in the genuine convex boundary model. Compactness
and injectivity of the original graph then give one radius on which the whole
closed fiber tube is embedded. The same radius preserves exact end preimages.
Relative openness of the image and smoothness of its inverse remain separate.
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

theorem convex_verticalTubeModel : Convex ℝ
    (range ((ProductHalfSpace.model (Vector 6)).prod 𝓘(ℝ, TimeGraphFrameSpace (e := e)))) := by
  rw [ModelWithCorners.range_prod, ProductHalfSpace.model_range, ModelWithCorners.range_eq_univ]
  exact ((convex_Ici (0 : ℝ)).linear_preimage (LinearMap.fst ℝ ℝ (Vector 6))).prod convex_univ

theorem exists_open_injOn_verticalTube_core (p : ambientSet A) :
    ∃ U : Set (ambientSet A × TimeGraphFrameSpace (e := e)),
      IsOpen U ∧ (p, 0) ∈ U ∧ InjOn (verticalTube A) U := by
  let := traceChartedSpace A
  apply exists_open_injOn_of_convex_model (p, 0) (convex_verticalTubeModel (e := e))
    ((contMDiff_verticalTube A).contMDiffAt.of_le (by simp)) (transverseSumEquiv A p)
  exact verticalTubeDifferential_core A p

theorem exists_verticalTube_injective_radius :
    ∃ ε : ℝ, 0 < ε ∧ InjOn (verticalTube A)
      ((univ : Set (ambientSet A)) ×ˢ closedBall (0 : TimeGraphFrameSpace (e := e)) ε) := by
  let := isCompact_iff_compactSpace.mp (isCompact_ambientSet A)
  let K : Set (ambientSet A × TimeGraphFrameSpace (e := e)) := univ ×ˢ {0}
  have hK : IsCompact K := isCompact_univ.prod isCompact_singleton
  have hi : InjOn (verticalTube A) K := by
    rintro ⟨p, v⟩ ⟨_, hv⟩ ⟨q, w⟩ ⟨_, hw⟩ he
    rcases mem_singleton_iff.mp hv with rfl
    rcases mem_singleton_iff.mp hw with rfl
    rw [verticalTube_core, verticalTube_core] at he
    exact Prod.ext (injective_timeGraph A he) rfl
  have hlocal : ∀ q ∈ K, ∃ U ∈ 𝓝 q, InjOn (verticalTube A) U := by
    rintro ⟨p, v⟩ ⟨_, hv⟩
    rcases mem_singleton_iff.mp hv with rfl
    obtain ⟨U, hU, hp, hiU⟩ := exists_open_injOn_verticalTube_core A p
    exact ⟨U, hU.mem_nhds hp, hiU⟩
  obtain ⟨U, hU, hKU, hiU⟩ := hi.exists_isOpen_superset hK
    (fun q _ ↦ (continuous_verticalTube A).continuousAt) hlocal
  obtain ⟨ε, hε, hball⟩ :=
    Wikipedia.SmoothSixDPoincare.DiskFraming.exists_pos_prod_closedBall_subset
      isCompact_univ hU hKU
  exact ⟨ε, hε, hiU.mono hball⟩

theorem exists_verticalTube_embedding_radius :
    ∃ ε : ℝ, 0 < ε ∧
      IsClosedEmbedding
        (fun q : ambientSet A × closedBall (0 : TimeGraphFrameSpace (e := e)) ε ↦
          verticalTube A (q.1, q.2.val)) ∧
      ∀ (p : ambientSet A) (v : TimeGraphFrameSpace (e := e)), ‖v‖ ≤ ε →
        timeGraphTimeFunctional (e := e) (verticalTube A (p, v)) ∈ Icc 0 1 ∧
        (timeGraphTimeFunctional (e := e) (verticalTube A (p, v)) = 0 ↔ p ∈ otherEnd A) ∧
        (timeGraphTimeFunctional (e := e) (verticalTube A (p, v)) = 1 ↔ p ∈ topEnd A) := by
  let := isCompact_iff_compactSpace.mp (isCompact_ambientSet A)
  obtain ⟨ε, hε, hi⟩ := exists_verticalTube_injective_radius A
  obtain ⟨η, hη, hslab⟩ := exists_verticalTube_slab_radius A
  let r := min ε η
  let := isCompact_iff_compactSpace.mp
    (isCompact_closedBall (0 : TimeGraphFrameSpace (e := e)) r)
  have hmem (q : ambientSet A × closedBall (0 : TimeGraphFrameSpace (e := e)) r) :
      (q.1, q.2.val) ∈ (univ : Set (ambientSet A)) ×ˢ
        closedBall (0 : TimeGraphFrameSpace (e := e)) ε :=
    ⟨mem_univ _, closedBall_subset_closedBall (min_le_left ε η) q.2.property⟩
  have hc : Continuous
      (fun q : ambientSet A × closedBall (0 : TimeGraphFrameSpace (e := e)) r ↦
        verticalTube A (q.1, q.2.val)) :=
    (continuous_verticalTube A).comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  refine ⟨r, lt_min hε hη, hc.isClosedEmbedding ?_, ?_⟩
  · intro q q' he
    have hq := hi (hmem q) (hmem q') he
    have hb : q.1 = q'.1 := congrArg
      (fun z : ambientSet A × TimeGraphFrameSpace (e := e) ↦ z.1) hq
    have hv : q.2.val = q'.2.val := congrArg
      (fun z : ambientSet A × TimeGraphFrameSpace (e := e) ↦ z.2) hq
    exact Prod.ext hb (Subtype.ext hv)
  · intro p v hv
    exact hslab p v (hv.trans (min_le_right ε η))

end NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace
