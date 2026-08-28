import Wikipedia.NoExoticSixSphere.RoundedTraceVerticalTube
import Wikipedia.SmoothSixDPoincare.DiskTubularNeighborhood

/-!
# A uniform positive fiber radius respecting both slab ends

Near the native boundary, the entire displacement map preserves time exactly.
Away from it, interior time values stay interior on an open neighborhood of
the zero section. Compactness then gives a single positive radius for all bases.
This proves slab containment and exact end preimages, not tube injectivity.
-/

noncomputable section

open Function Set Metric
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace

open GLOrthonormalization Stiefel

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M] [CompactSpace M]
  [IsManifold (𝓡 6) ∞ M] {e : EuclideanEmbedding 6 M}
  {a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f)

theorem verticalTube_time_otherEnd {p : ambientSet A} (hp : p ∈ otherEnd A)
    (v : TimeGraphFrameSpace (e := e)) :
    timeGraphTimeFunctional (e := e) (verticalTube A (p, v)) = 0 := by
  let := traceChartedSpace A
  have hb := ((mem_otherEnd_iff A p).mp hp).1
  exact (verticalTube_time_boundary A ⟨p, hb⟩ v).trans (bordismTime_otherEnd A hp)

theorem verticalTube_time_topEnd {p : ambientSet A} (hp : p ∈ topEnd A)
    (v : TimeGraphFrameSpace (e := e)) :
    timeGraphTimeFunctional (e := e) (verticalTube A (p, v)) = 1 := by
  let := traceChartedSpace A
  have hb := ((mem_topEnd_iff A p).mp hp).1
  exact (verticalTube_time_boundary A ⟨p, hb⟩ v).trans (bordismTime_topEnd A hp)

theorem exists_verticalTube_slab_radius :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (p : ambientSet A) (v : TimeGraphFrameSpace (e := e)), ‖v‖ ≤ ε →
      timeGraphTimeFunctional (e := e) (verticalTube A (p, v)) ∈ Icc 0 1 ∧
      (timeGraphTimeFunctional (e := e) (verticalTube A (p, v)) = 0 ↔ p ∈ otherEnd A) ∧
      (timeGraphTimeFunctional (e := e) (verticalTube A (p, v)) = 1 ↔ p ∈ topEnd A) := by
  let := traceChartedSpace A
  let := isCompact_iff_compactSpace.mp (isCompact_ambientSet A)
  obtain ⟨U, hU, hbU, htime⟩ := exists_verticalTube_time_neighborhood A
  let τ : ambientSet A × TimeGraphFrameSpace (e := e) → ℝ :=
    fun q ↦ timeGraphTimeFunctional (e := e) (verticalTube A q)
  have hτ : Continuous τ :=
    (timeGraphTimeFunctional (e := e)).continuous.comp (continuous_verticalTube A)
  let V : Set (ambientSet A × TimeGraphFrameSpace (e := e)) :=
    (U ×ˢ univ) ∪ τ ⁻¹' Ioo 0 1
  have hV : IsOpen V := (hU.prod isOpen_univ).union (isOpen_Ioo.preimage hτ)
  have hcore : (univ : Set (ambientSet A)) ×ˢ {(0 : TimeGraphFrameSpace (e := e))} ⊆ V := by
    rintro ⟨p, v⟩ ⟨_, hv⟩
    have hz : v = 0 := hv
    subst v
    by_cases hb : (ProductHalfSpace.model (Vector 6)).IsBoundaryPoint p
    · exact Or.inl ⟨hbU ⟨⟨p, hb⟩, rfl⟩, mem_univ _⟩
    · apply Or.inr
      change timeGraphTimeFunctional (e := e) (verticalTube A (p, 0)) ∈ Ioo 0 1
      simp only [verticalTube_time, map_zero, add_zero]
      exact bordismTime_interior A p hb
  obtain ⟨ε, hε, hball⟩ :=
    Wikipedia.SmoothSixDPoincare.DiskFraming.exists_pos_prod_closedBall_subset
      isCompact_univ hV hcore
  refine ⟨ε, hε, ?_⟩
  intro p v hv
  have hv' : v ∈ closedBall (0 : TimeGraphFrameSpace (e := e)) ε := by
    simpa only [mem_closedBall, dist_zero_right] using hv
  have hmem : (p, v) ∈ V := hball ⟨mem_univ p, hv'⟩
  rcases hmem with hp | hp
  · have he := htime p hp.1 v
    rw [he]
    exact ⟨bordismTime_mem_Icc A p, bordismTime_zero_iff A p, bordismTime_one_iff A p⟩
  · change τ (p, v) ∈ Ioo 0 1 at hp
    refine ⟨⟨hp.1.le, hp.2.le⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · intro hz
      exact ((ne_of_gt hp.1) hz).elim
    · intro hb
      exact verticalTube_time_otherEnd A hb v
    · intro ho
      exact ((ne_of_lt hp.2) ho).elim
    · intro hb
      exact verticalTube_time_topEnd A hb v

end NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace
