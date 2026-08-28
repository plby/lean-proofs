import Wikipedia.HopfProblem.DegreeCollapseSectionAttachingClass

/-!
# The original core union includes into the upper sublevel by a homotopy equivalence

Use the actual adapted common field on the full native handle block.
The critical attachment deformation and relative handle-core deformation
both have literal inclusion as forward map. Their composition therefore
retains the ordinary sublevel maps needed for a coherent presentation.
-/

noncomputable section

open Set Function Filter Metric Manifold ContinuousMap Topology
open scoped ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}

theorem AdaptedSurgeryWindows.exists_native_core_inclusion_equiv
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p : criticalPoints E f) :
    ∃ e : ↥({y : M | f y ≤ S.toSurgeryWindows.lower p} ∪ range (S.data p).coreMap) ≃ₕ
        {y : M // f y ≤ S.toSurgeryWindows.upper p},
      ∀ x, (e x).val = x.val := by
  let d := S.data p
  have hagreement : ∀ x ∈ range (d.chart.attachingHandleMap d.radius d.radius_pos d.block),
      ∀ᶠ y in 𝓝 x, S.field y = d.chart.descentField y := by
    rintro x ⟨z, rfl⟩
    exact S.model_germ p _ (MorseHandle.modelMap_mem_product d.radius_pos z)
  obtain ⟨B, hB⟩ := d.chart.exists_attachingUnionHomotopyEquiv hf S.smooth S.zero S.descent
    S.flow S.integral d.radius d.radius_pos d.block hagreement (S.isolated p)
  let C := ClosedHandleCore.unionHomotopyEquiv
    {y : M | f y ≤ S.toSurgeryWindows.lower p} d.handleMap
    (isClosed_le hf.continuous continuous_const)
    (d.chart.attachingHandleMap_isClosedEmbedding d.radius d.radius_pos d.block)
    (d.chart.attachingHandleMap_lower_iff d.radius d.radius_pos d.block)
  exact ⟨C.trans B, fun x => hB (C x)⟩

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
