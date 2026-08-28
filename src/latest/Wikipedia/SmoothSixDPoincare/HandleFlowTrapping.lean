import Wikipedia.SmoothSixDPoincare.MorseChartFlow
import Wikipedia.SmoothSixDPoincare.ManifoldHandleNeighborhood
import Wikipedia.SmoothSixDPoincare.FlowTrapping

/-!
# Local trapping and strict entry for the actual embedded handle

The model boundary-crossing argument is transported to the original
manifold using native integral-curve uniqueness and the actual chart.
-/

noncomputable section

open Set Metric Manifold Filter
open scoped ContDiff Topology

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.SignedMorseChart

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {f : M → ℝ} {p : M} (c : SignedMorseChart (E := E) f p)

open Classical in
/-- Near any point in the chart where fields agree, the actual attachment is entered immediately. -/
theorem exists_local_attachingUnion_entry
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hblock : closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
      closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆ c.splitChart.target)
    {x : M} (hx : x ∈ c.splitChart.source)
    (heq : ∀ᶠ y in 𝓝 x, V y = c.descentField y)
    (hAx : x ∈ {y | f y ≤ f p - ρ ^ 2} ∪ range (c.attachingHandleMap ρ hρ hblock)) :
    ∃ ε > (0 : ℝ), ∀ t ∈ Ioc 0 ε,
      F t x ∈ interior ({y | f y ≤ f p - ρ ^ 2} ∪
        range (c.attachingHandleMap ρ hρ hblock)) := by
  let e := c.splitChart.toOpenPartialHomeomorph
  have hmodel := (c.mem_attachingUnion_iff_model ρ hρ hblock hx).mp hAx
  have hαc : Continuous (fun t : ℝ => MorseHandle.descentFlow t (c.splitChart x)) :=
    MorseHandle.descentFlow.continuous continuous_id continuous_const
  have hα₀ : MorseHandle.descentFlow 0 (c.splitChart x) = e x :=
    MorseHandle.descentFlow.map_zero_apply _
  have htarget : ∀ᶠ t in 𝓝 (0 : ℝ), MorseHandle.descentFlow t (c.splitChart x) ∈ e.target :=
    hαc.continuousAt.preimage_mem_nhds (e.open_target.mem_nhds (hα₀ ▸ e.map_source hx))
  have hFc : Continuous (fun t : ℝ => F t x) := F.continuous continuous_id continuous_const
  have hsource : ∀ᶠ t in 𝓝 (0 : ℝ), F t x ∈ e.source :=
    hFc.continuousAt.preimage_mem_nhds (e.open_source.mem_nhds (by
      rw [F.map_zero_apply]
      exact hx))
  have heqF := c.eventually_flow_eq_descentModel hV F hcurve hx heq
  obtain ⟨ε, hε, hεall⟩ := Metric.eventually_nhds_iff.mp ((heqF.and htarget).and hsource)
  refine ⟨ε / 2, half_pos hε, ?_⟩
  intro t ht
  have hdist : dist t (0 : ℝ) < ε := by
    rw [Real.dist_eq, sub_zero, abs_of_pos ht.1]
    linarith [ht.2]
  obtain ⟨⟨heqt, htar⟩, hsrc⟩ := hεall hdist
  apply c.mem_interior_attachingUnion_of_model ρ hρ hblock hsrc
  have hcoord : c.splitChart (F t x) = MorseHandle.descentFlow t (c.splitChart x) := by
    rw [heqt]
    exact e.right_inv htar
  rw [hcoord]
  exact MorseHandle.descentFlow_mem_interior_lower_union_handle hρ ht.1 hmodel

open Classical in
/-- The actual lower sublevel with one embedded handle adjoined is forward invariant. -/
theorem forwardInvariant_attachingUnion [T2Space M] (hf : Continuous f)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hmono : ∀ x, Antitone (fun t => f (F t x)))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hblock : closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
      closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆ c.splitChart.target)
    (hagreement : ∀ x ∈ range (c.attachingHandleMap ρ hρ hblock),
      ∀ᶠ y in 𝓝 x, V y = c.descentField y) :
    ∀ x ∈ {y | f y ≤ f p - ρ ^ 2} ∪ range (c.attachingHandleMap ρ hρ hblock),
      ∀ t : ℝ, 0 ≤ t →
        F t x ∈ {y | f y ≤ f p - ρ ^ 2} ∪ range (c.attachingHandleMap ρ hρ hblock) := by
  apply FlowConstruction.forwardInvariant_of_local F
    ((isClosed_le hf continuous_const).union
      (c.attachingHandleMap_isClosedEmbedding ρ hρ hblock).isClosed_range)
  intro x hx
  rcases hx with hx | hx
  · refine ⟨1, zero_lt_one, ?_⟩
    intro t ht
    left
    have hle : f (F t x) ≤ f x := by simpa only [F.map_zero_apply] using hmono x ht.1
    exact hle.trans hx
  · have hxsource : x ∈ c.splitChart.source := by
      obtain ⟨z, rfl⟩ := hx
      exact c.splitChart.toOpenPartialHomeomorph.map_target
        (hblock (MorseHandle.modelMap_mem_product hρ z))
    obtain ⟨ε, hε, hentry⟩ := c.exists_local_attachingUnion_entry hV F hcurve ρ hρ hblock
      hxsource (hagreement x hx) (Or.inr hx)
    refine ⟨ε, hε, ?_⟩
    intro t ht
    rcases ht.1.eq_or_lt with hzero | hpos
    · rw [← hzero, F.map_zero_apply]
      exact Or.inr hx
    · exact interior_subset (hentry t ⟨hpos, ht.2⟩)

open Classical in
/-- Strict descent along the bottom level gives global strict entry into the actual attachment. -/
theorem interior_entry_attachingUnion [T2Space M] (hf : Continuous f)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hmono : ∀ x, Antitone (fun t => f (F t x)))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hblock : closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
      closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆ c.splitChart.target)
    (hagreement : ∀ x ∈ range (c.attachingHandleMap ρ hρ hblock),
      ∀ᶠ y in 𝓝 x, V y = c.descentField y)
    (hbottom : ∀ x, f x = f p - ρ ^ 2 → ∀ t : ℝ, 0 < t → f (F t x) < f x) :
    ∀ x ∈ {y | f y ≤ f p - ρ ^ 2} ∪ range (c.attachingHandleMap ρ hρ hblock),
      ∀ t : ℝ, 0 < t → F t x ∈ interior
        ({y | f y ≤ f p - ρ ^ 2} ∪ range (c.attachingHandleMap ρ hρ hblock)) := by
  apply FlowConstruction.interior_entry_of_local F
    (c.forwardInvariant_attachingUnion hf hV F hcurve hmono ρ hρ hblock hagreement)
  intro x hx
  rcases hx with hx | hx
  · refine ⟨1, zero_lt_one, ?_⟩
    intro t ht
    have hlow : f (F t x) < f p - ρ ^ 2 := by
      change f x ≤ f p - ρ ^ 2 at hx
      rcases lt_or_eq_of_le hx with hlt | heq
      · have hle : f (F t x) ≤ f x := by
          simpa only [F.map_zero_apply] using hmono x ht.1.le
        exact hle.trans_lt hlt
      · exact (hbottom x heq t ht.1).trans_le hx
    apply mem_interior.mpr
    exact ⟨{y | f y < f p - ρ ^ 2},
      fun y hy => Or.inl (show f y ≤ f p - ρ ^ 2 from le_of_lt hy),
      isOpen_lt hf continuous_const, hlow⟩
  · have hxsource : x ∈ c.splitChart.source := by
      obtain ⟨z, rfl⟩ := hx
      exact c.splitChart.toOpenPartialHomeomorph.map_target
        (hblock (MorseHandle.modelMap_mem_product hρ z))
    exact c.exists_local_attachingUnion_entry hV F hcurve ρ hρ hblock
      hxsource (hagreement x hx) (Or.inr hx)

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.SignedMorseChart
