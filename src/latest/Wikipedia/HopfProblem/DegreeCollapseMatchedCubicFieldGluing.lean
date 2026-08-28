import Wikipedia.HopfProblem.DegreeCollapseClosedAxisFieldGluing
import Wikipedia.HopfProblem.DegreeCollapseCubicOverlapGerms
import Wikipedia.HopfProblem.DegreeCollapseEndpointAxisBounds
import Wikipedia.HopfProblem.DegreeCollapseNativeCubicFieldCancellation

/-!
# Constructing a full cubic field chart from the matched exterior formulas

Endpoint convergence chooses both regular cuts in their actual boxes
and beyond the matching time thresholds. The matched formulas construct
full spatial chart germs and agreement on the complete remaining endpoint
axis segments. The actual middle chart supplies closed-axis injectivity,
so the native gluing theorem produces one chart containing both critical
endpoints and carrying the exact cubic field everywhere on its target.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [T2Space M] {m : ℕ}

theorem exists_matched_full_cubic_field_chart (σ : Fin m → ℝ) {a : ℝ} (ha : 0 < a)
    (Φq Φm Φp : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞)
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (hqfield : ∀ y ∈ Φq.target, V y = nativeCubicDescent σ Φq (-(a ^ 2)) y)
    (hmfield : ∀ y ∈ Φm.target, V y = nativeCubicDescent σ Φm (-(a ^ 2)) y)
    (hpfield : ∀ y ∈ Φp.target, V y = nativeCubicDescent σ Φp (-(a ^ 2)) y)
    {rq rp : ℝ} (hrq : 0 < rq) (hrp : 0 < rp)
    (hboxq : closedBall (-a, (0 : Fin m → ℝ)) rq ⊆ Φq.source)
    (hboxp : closedBall (a, (0 : Fin m → ℝ)) rp ⊆ Φp.source)
    (hmiddle : ∀ s ∈ Ioo (-a) a, (s, (0 : Fin m → ℝ)) ∈ Φm.source)
    (hleft : Φq (-a, 0) ∉ Φm.target) (hright : Φp (a, 0) ∉ Φm.target)
    (hne : Φq (-a, 0) ≠ Φp (a, 0))
    (hmatchq : ∀ᶠ z : Fin m → ℝ in 𝓝 0, ∀ t : ℝ, t ≤ -1 →
      cubicFlowCylinder σ a (z, t) ∈ closedBall (-a, (0 : Fin m → ℝ)) rq →
      Φq (cubicFlowCylinder σ a (z, t)) = Φm (cubicFlowCylinder σ a (z, t)))
    (hmatchp : ∀ᶠ z : Fin m → ℝ in 𝓝 0, ∀ t : ℝ, 2 ≤ t →
      cubicFlowCylinder σ a (z, t) ∈ closedBall (a, (0 : Fin m → ℝ)) rp →
      Φp (cubicFlowCylinder σ a (z, t)) = Φm (cubicFlowCylinder σ a (z, t))) :
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞,
      Icc (-a) a ×ˢ {(0 : Fin m → ℝ)} ⊆ Φ.source ∧
      (∀ y ∈ Φ.target, V y = nativeCubicDescent σ Φ (-(a ^ 2)) y) ∧
      Φ (-a, 0) = Φq (-a, 0) ∧ Φ (a, 0) = Φp (a, 0) ∧
      (∀ s ∈ Ioo (-a) a, Φ (s, 0) = Φm (s, 0)) ∧
      ((Φ : Model m → M) =ᶠ[𝓝 (-a, (0 : Fin m → ℝ))] Φq) ∧
      ((Φ : Model m → M) =ᶠ[𝓝 (a, (0 : Fin m → ℝ))] Φp) := by
  have hqmatch : ∀ᶠ z : Fin m → ℝ in 𝓝 0, ∀ t ∈ Iio (-1 : ℝ),
      cubicFlowCylinder σ a (z, t) ∈ closedBall (-a, (0 : Fin m → ℝ)) rq →
      Φq (cubicFlowCylinder σ a (z, t)) = Φm (cubicFlowCylinder σ a (z, t)) := by
    filter_upwards [hmatchq] with z hz
    exact fun t ht => hz t ht.le
  have hpmatch : ∀ᶠ z : Fin m → ℝ in 𝓝 0, ∀ t ∈ Ioi (2 : ℝ),
      cubicFlowCylinder σ a (z, t) ∈ closedBall (a, (0 : Fin m → ℝ)) rp →
      Φp (cubicFlowCylinder σ a (z, t)) = Φm (cubicFlowCylinder σ a (z, t)) := by
    filter_upwards [hmatchp] with z hz
    exact fun t ht => hz t ht.le
  obtain ⟨Tq, hTq, hqball, hgq⟩ := exists_cubic_spatial_overlap_germ σ ha Φq Φm hrq
    (tendsto_cubicFlowCylinder_axis_atBot σ ha) isOpen_Iio (Iio_mem_atBot (-1 : ℝ)) hqmatch
  obtain ⟨Tp, hTp, hpball, hgp⟩ := exists_cubic_spatial_overlap_germ σ ha Φp Φm hrp
    (tendsto_cubicFlowCylinder_axis_atTop σ ha) isOpen_Ioi (Ioi_mem_atTop (2 : ℝ)) hpmatch
  have hcutq := cubicAxisParameter_mem ha Tq
  have hcutp := cubicAxisParameter_mem ha Tp
  have horder : cubicAxisParameter a Tq < cubicAxisParameter a Tp :=
    strictMono_cubicAxisParameter ha (by change Tq < -1 at hTq; change 2 < Tp at hTp; linarith)
  have hgq' : (Φq : Model m → M) =ᶠ[𝓝 (cubicAxisParameter a Tq, 0)] Φm := by
    simpa only [cubicFlowCylinder_axis, cubicModelOrbit] using hgq
  have hgp' : (Φp : Model m → M) =ᶠ[𝓝 (cubicAxisParameter a Tp, 0)] Φm := by
    simpa only [cubicFlowCylinder_axis, cubicModelOrbit] using hgp
  have hqsegment := outgoing_axis_segment_in_box σ ha hrq (ball_subset_closedBall hqball)
  have hpsegment := incoming_axis_segment_in_box σ ha hrp (ball_subset_closedBall hpball)
  have hqaxis (s : ℝ) (hs : s ∈ Ioc (-a) (cubicAxisParameter a Tq)) :
      Φq (s, 0) = Φm (s, 0) := by
    have hs' : s ∈ Ioo (-a) a := ⟨hs.1, hs.2.trans_lt hcutq.2⟩
    obtain ⟨hb, ht⟩ := hqsegment s ⟨hs.1.le, hs.2⟩
    have hball : cubicFlowCylinder σ a (0, cubicAxisClock a s) ∈
        closedBall (-a, (0 : Fin m → ℝ)) rq := by
      rw [cubicFlowCylinder_zero_clock σ ha hs']; exact hb
    have hh := hmatchq.self_of_nhds (cubicAxisClock a s) ((ht hs.1).trans hTq.le) hball
    simpa only [cubicFlowCylinder_zero_clock σ ha hs'] using hh
  have hpaxis (s : ℝ) (hs : s ∈ Ico (cubicAxisParameter a Tp) a) :
      Φp (s, 0) = Φm (s, 0) := by
    have hs' : s ∈ Ioo (-a) a := ⟨hcutp.1.trans_le hs.1, hs.2⟩
    obtain ⟨hb, ht⟩ := hpsegment s ⟨hs.1, hs.2.le⟩
    have hball : cubicFlowCylinder σ a (0, cubicAxisClock a s) ∈
        closedBall (a, (0 : Fin m → ℝ)) rp := by
      rw [cubicFlowCylinder_zero_clock σ ha hs']; exact hb
    have hh := hmatchp.self_of_nhds (cubicAxisClock a s) (hTp.le.trans (ht hs.2)) hball
    simpa only [cubicFlowCylinder_zero_clock σ ha hs'] using hh
  exact FieldChartGluing.exists_closed_axis_native_field_chart Φq Φm Φp
    (cubicDescent σ (-(a ^ 2))) V hqfield hmfield hpfield hcutq.1 horder hcutp.2
    (fun s hs => hboxq (hqsegment s hs).1) hmiddle
    (fun s hs => hboxp (hpsegment s hs).1) hgq' hgp' hqaxis hpaxis hleft hright hne

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
