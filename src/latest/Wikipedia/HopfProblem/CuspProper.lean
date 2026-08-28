import Wikipedia.HopfProblem.CuspQuotient
import Wikipedia.HopfProblem.ToricReduction
import Mathlib.Topology.Maps.Proper.CompactlyGenerated

/-!
# Properness of the cusp filling

Finitely many closed unit polydiscs provide compact representatives for
the quotient over each smaller closed disc. Density of the torus and
Hausdorffness extend this coverage to the central fibre.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.CuspQuotient

open ToricCharts ToricFan ToricSpace

def compactRepresentatives (η : ℝ) : Set Space :=
  ⋃ s ∈ boundedTriangles, inclusion s ''
    (Metric.closedBall (0 : CoordinateSpace 3) 1 ∩
      Triangle.time ⁻¹' Metric.closedBall 0 η)

theorem compactRepresentatives_compact (η : ℝ) : IsCompact (compactRepresentatives η) := by
  apply boundedTriangles_finite.isCompact_biUnion
  intro s _
  exact ((isCompact_closedBall _ _).inter_right
    (Metric.isClosed_closedBall.preimage Triangle.time_holomorphic.continuous)).image
      (inclusion_openEmbedding s).continuous

theorem compactRepresentatives_time {η : ℝ} {x : Space}
    (hx : x ∈ compactRepresentatives η) : ‖time x‖ ≤ η := by
  obtain ⟨s, _, z, hz, rfl⟩ := mem_iUnion₂.mp hx
  simpa only [time_inclusion, Set.mem_preimage, Metric.mem_closedBall, dist_zero_right] using hz.2

def tubeRepresentatives (ε η : ℝ) : Set (Tube (disc ε)) :=
  Subtype.val ⁻¹' compactRepresentatives η

theorem tubeRepresentatives_compact {ε η : ℝ} (hηε : η < ε) :
    IsCompact (tubeRepresentatives ε η) := by
  apply IsEmbedding.subtypeVal.isInducing.isCompact_preimage'
    (compactRepresentatives_compact η)
  intro x hx
  have hxt : x ∈ tubeOpen (disc ε) := by
    change time x ∈ Metric.ball 0 ε
    simpa only [Metric.mem_ball, dist_zero_right] using
      (compactRepresentatives_time hx).trans_lt hηε
  exact ⟨⟨x, hxt⟩, rfl⟩

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)

def quotientRepresentatives (η : ℝ) : Set (QuotientSpace C ε) :=
  quotientMap C ε '' tubeRepresentatives ε η

theorem quotientRepresentatives_compact {η : ℝ} (hηε : η < ε) :
    IsCompact (quotientRepresentatives C ε η) :=
  (tubeRepresentatives_compact hηε).image (quotientMap_continuous C ε)

theorem torus_mem_quotientRepresentatives (hε1 : ε < 1) (hR : SmallDrift C ε)
    {η : ℝ} {x : Tube (disc ε)} (hx : (x : Space) ∈ openTorus)
    (hxη : ‖time (x : Space)‖ ≤ η) :
    quotientMap C ε x ∈ quotientRepresentatives C ε η := by
  have hxt : ‖time (x : Space)‖ < ε := by
    have hxε : time (x : Space) ∈ Metric.ball 0 ε := x.2
    simpa only [Metric.mem_ball, dist_zero_right] using hxε
  have ht : 0 < ‖time (x : Space)‖ := norm_pos_iff.mpr ((mem_openTorus_iff _).mp hx)
  obtain ⟨v, s, hs, z, hz, he⟩ := exists_bounded_chart_translate C hx
    (Real.log_neg ht (hxt.trans hε1)) (hR _ ht hxt)
  refine ⟨tubeTranslate C (disc ε) v x, ?_, quotientMap_translate C ε v x⟩
  change twistedTranslate C v (x : Space) ∈ compactRepresentatives η
  refine mem_iUnion₂.mpr ⟨s, hs, z, ⟨hz, ?_⟩, he⟩
  change Triangle.time z ∈ Metric.closedBall 0 η
  rw [← time_inclusion s z, he, time_twistedTranslate, Metric.mem_closedBall, dist_zero_right]
  exact hxη

theorem tube_torus_dense :
    Dense ((Subtype.val : Tube (disc ε) → Space) ⁻¹' openTorus) :=
  openTorus_dense.preimage (tubeOpen (disc ε)).isOpen.isOpenEmbedding_subtypeVal.isOpenMap

theorem mem_quotientRepresentatives (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : SmallDrift C ε) {η : ℝ} (hη : 0 < η) (hηε : η < ε)
    {x : Tube (disc ε)} (hxη : ‖time (x : Space)‖ ≤ η) :
    quotientMap C ε x ∈ quotientRepresentatives C ε η := by
  let := quotient_t2Space C ε hε hε1 hC hR
  by_cases hx : (x : Space) ∈ openTorus
  · exact torus_mem_quotientRepresentatives C ε hε1 hR hx hxη
  have hzero : time (x : Space) = 0 := by simpa only [mem_openTorus_iff, not_not] using hx
  let A := quotientMap C ε ⁻¹' quotientRepresentatives C ε η
  have hA : IsClosed A := (quotientRepresentatives_compact C ε hηε).isClosed.preimage
    (quotientMap_continuous C ε)
  let U : Set (Tube (disc ε)) := {p | ‖time (p : Space)‖ < η}
  have hU : IsOpen U := isOpen_lt
    (time_holomorphic.continuous.comp continuous_subtype_val).norm continuous_const
  by_contra hn
  have hxU : x ∈ U := by simpa [U, hzero] using hη
  obtain ⟨p, hp, hpU, hpA⟩ := (tube_torus_dense ε).exists_mem_open
    (hU.inter hA.isOpen_compl) ⟨x, hxU, hn⟩
  exact hpA (torus_mem_quotientRepresentatives C ε hε1 hR hp hpU.le)

theorem closedDisc_preimage_compact (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : SmallDrift C ε) {η : ℝ} (hη : 0 < η) (hηε : η < ε) :
    IsCompact (projection C ε ⁻¹' Metric.closedBall 0 η) := by
  have he : projection C ε ⁻¹' Metric.closedBall 0 η = quotientRepresentatives C ε η := by
    ext q
    constructor
    · induction q using Quotient.inductionOn with
      | h x =>
        intro hx
        exact mem_quotientRepresentatives C ε hε hε1 hC hR hη hηε
          (by simpa only [Set.mem_preimage, projection, Quotient.lift_mk,
            Metric.mem_closedBall, dist_zero_right] using hx)
    · rintro ⟨x, hx, rfl⟩
      simpa only [Set.mem_preimage, projection_quotientMap,
        Metric.mem_closedBall, dist_zero_right] using
        compactRepresentatives_time hx
  rw [he]
  exact quotientRepresentatives_compact C ε hηε

theorem baseMap_proper (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : SmallDrift C ε) : IsProperMap (baseMap C ε) := by
  apply isProperMap_iff_isCompact_preimage.mpr
  refine ⟨baseMap_continuous C ε, ?_⟩
  intro K hK
  rcases K.eq_empty_or_nonempty with rfl | hne
  · simp
  obtain ⟨t, ht, hmax⟩ := hK.exists_isMaxOn hne continuous_subtype_val.norm.continuousOn
  have htε : ‖(t : ℂ)‖ < ε := by
    have htball : (t : ℂ) ∈ Metric.ball 0 ε := t.2
    simpa only [Metric.mem_ball, dist_zero_right] using htball
  obtain ⟨η, htη, hηε⟩ := exists_between htε
  have hη : 0 < η := (norm_nonneg _).trans_lt htη
  apply (closedDisc_preimage_compact C ε hε hε1 hC hR hη hηε).of_isClosed_subset
    (hK.isClosed.preimage (baseMap_continuous C ε))
  intro q hq
  have hb : ‖projection C ε q‖ ≤ ‖(t : ℂ)‖ := hmax hq
  simpa only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right] using hb.trans htη.le

theorem fibre_compact (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : SmallDrift C ε) (t : disc ε) : IsCompact (baseMap C ε ⁻¹' {t}) :=
  (baseMap_proper C ε hε hε1 hC hR).isCompact_preimage isCompact_singleton

end Wikipedia.HopfProblem.CuspQuotient
