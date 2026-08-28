import Wikipedia.HopfProblem.DegreeCollapsePhaseFlowPlaneChart
import Wikipedia.HopfProblem.DegreeCollapseCancellationSheetBasins

/-!
# Exact native basin-plane charts for the cancellation sheets

Both actual cancellation sheets are coordinate-plane germs in genuine
native partial diffeomorphisms. On each entire chart source, the actual
endpoint basin is exactly the corresponding linear coordinate plane.
-/

noncomputable section

open Set Function Filter Manifold
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {m : ℕ} {f : M → ℝ} {p q : M}

open Classical in
theorem NativeConnectionCancellationData.outgoing_basin_chart
    (D : NativeConnectionCancellationData (E := E) f p q m) :
    ∃ P : PartialDiffeomorph
        𝓘(ℝ, (MorseHandle.NegativeSpace D.σ × MorseHandle.PositiveSpace D.σ) × ℝ) 𝓘(ℝ, E)
        ((MorseHandle.NegativeSpace D.σ × MorseHandle.PositiveSpace D.σ) × ℝ) M ∞,
      (0 : (MorseHandle.NegativeSpace D.σ × MorseHandle.PositiveSpace D.σ) × ℝ) ∈ P.source ∧
      P 0 = D.A 0 ∧
      D.outgoingSheet =ᶠ[𝓝 0] (fun w : ℝ × MorseHandle.NegativeSpace D.σ => P ((w.2, 0), w.1)) ∧
      ∀ w ∈ P.source, Tendsto (fun t => D.flow t (P w)) atBot (𝓝 q) ↔ w.1.2 = 0 := by
  have hflow := FlowSuspension.native_vertical_cylinder_flow D.A D.slices.source
    (D.smooth_field.of_le (by simp)) D.vertical D.flow D.integral
  have hQU : D.slices.Q.target ⊆ D.slices.labelDomain := fun _ hz => D.slices.Q_target ▸ hz
  have hQ0 : 0 ∈ D.slices.Q.source := D.slices.Q_source ▸ D.slices.zero_source
  let S := fun u => D.Φq (cubicFlowCylinder D.σ (1 / 2)
    ((MorseHandle.splitCoordinates D.σ).symm u, D.Tq))
  have hbasin (u) (hu : u ∈ D.slices.Q.source) :
      Tendsto (fun t => D.flow t (S u)) atBot (𝓝 q) ↔ u.2 = 0 :=
    outgoing_cubic_slice_basin D.σ D.signs (1 / 2) D.Tq D.Φq D.flow D.basinQ u
      (D.boxQ (D.slices.sliceQ u hu))
  obtain ⟨P, -, h0P, hP0, hformula, hplane⟩ :=
    FlowSuspension.exists_phase_flow_basin_chart D.A D.slices.source D.flow hflow
      D.slices.Q hQU hQ0 D.slices.Q_zero S D.slices.phaseQ D.Tq
      D.slices.smooth_phaseQ D.slices.zero_phaseQ D.slices.formulaQ
      (fun y => Tendsto (fun t => D.flow t y) atBot (𝓝 q))
      (fun t y => flow_time_atBot_limit_iff D.flow t y q) (fun u => u.2 = 0) hbasin
  have heq := FlowSuspension.phase_flow_chart_subsheet_germ P D.slices.Q.open_source hQ0
    D.flow S D.Tq hformula
    (ContinuousLinearMap.inl ℝ (MorseHandle.NegativeSpace D.σ) (MorseHandle.PositiveSpace D.σ))
  refine ⟨P, h0P, hP0, ?_, hplane⟩
  unfold NativeConnectionCancellationData.outgoingSheet
  simpa only [ContinuousLinearMap.inl_apply] using heq

open Classical in
theorem NativeConnectionCancellationData.incoming_basin_chart
    (D : NativeConnectionCancellationData (E := E) f p q m) :
    ∃ P : PartialDiffeomorph
        𝓘(ℝ, (MorseHandle.NegativeSpace D.σ × MorseHandle.PositiveSpace D.σ) × ℝ) 𝓘(ℝ, E)
        ((MorseHandle.NegativeSpace D.σ × MorseHandle.PositiveSpace D.σ) × ℝ) M ∞,
      (0 : (MorseHandle.NegativeSpace D.σ × MorseHandle.PositiveSpace D.σ) × ℝ) ∈ P.source ∧
      P 0 = D.A 0 ∧
      D.incomingSheet =ᶠ[𝓝 0] (fun w : ℝ × MorseHandle.PositiveSpace D.σ => P ((0, w.2), w.1)) ∧
      ∀ w ∈ P.source, Tendsto (fun t => D.flow t (P w)) atTop (𝓝 p) ↔ w.1.1 = 0 := by
  have hflow := FlowSuspension.native_vertical_cylinder_flow D.A D.slices.source
    (D.smooth_field.of_le (by simp)) D.vertical D.flow D.integral
  have hPU : D.slices.P.target ⊆ D.slices.labelDomain := fun _ hz => D.slices.P_target ▸ hz
  have hP0 : 0 ∈ D.slices.P.source := by
    rw [D.slices.P_source, ← D.slices.H_zero]
    exact D.slices.H.map_source' D.slices.zero_source
  let S := fun u => D.Φp (cubicFlowCylinder D.σ (1 / 2)
    ((MorseHandle.splitCoordinates D.σ).symm u, D.Tp))
  have hbasin (u) (hu : u ∈ D.slices.P.source) :
      Tendsto (fun t => D.flow t (S u)) atTop (𝓝 p) ↔ u.1 = 0 :=
    incoming_cubic_slice_basin D.σ (1 / 2) D.Tp D.Φp D.flow D.basinP u
      (D.boxP (D.slices.sliceP u hu))
  obtain ⟨P, -, h0P, hPzero, hformula, hplane⟩ :=
    FlowSuspension.exists_phase_flow_basin_chart D.A D.slices.source D.flow hflow
      D.slices.P hPU hP0 D.slices.P_zero S D.slices.phaseP D.Tp
      D.slices.smooth_phaseP D.slices.zero_phaseP D.slices.formulaP
      (fun y => Tendsto (fun t => D.flow t y) atTop (𝓝 p))
      (fun t y => flow_time_atTop_limit_iff D.flow t y p) (fun u => u.1 = 0) hbasin
  have heq := FlowSuspension.phase_flow_chart_subsheet_germ P D.slices.P.open_source hP0
    D.flow S D.Tp hformula
    (ContinuousLinearMap.inr ℝ (MorseHandle.NegativeSpace D.σ) (MorseHandle.PositiveSpace D.σ))
  refine ⟨P, h0P, hPzero, ?_, hplane⟩
  unfold NativeConnectionCancellationData.incomingSheet
  simpa only [ContinuousLinearMap.inr_apply] using heq

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
