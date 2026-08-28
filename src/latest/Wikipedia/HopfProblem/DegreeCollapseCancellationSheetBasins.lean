import Wikipedia.HopfProblem.DegreeCollapseCancellationFlowSheets

/-!
# The constructed native sheets lie in the actual endpoint basins

The signed cubic slice planes give the original endpoint limits. The
finite complete-flow shifts in the actual sheet definitions preserve
those limits throughout a genuine neighborhood of the reference point.
-/

noncomputable section

open Set Function Filter Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {m : ℕ} {f : M → ℝ} {p q : M}

theorem NativeConnectionCancellationData.outgoingSheet_basin
    (D : NativeConnectionCancellationData (E := E) f p q m) :
    ∀ᶠ w : ℝ × MorseHandle.NegativeSpace D.σ in 𝓝 0,
      Tendsto (fun t => D.flow t (D.outgoingSheet w)) atBot (𝓝 q) := by
  have hQ0 : 0 ∈ D.slices.Q.source := D.slices.Q_source ▸ D.slices.zero_source
  have hnear : ∀ᶠ w : ℝ × MorseHandle.NegativeSpace D.σ in 𝓝 0,
      (w.2, (0 : MorseHandle.PositiveSpace D.σ)) ∈ D.slices.Q.source :=
    (continuous_snd.prodMk continuous_const).continuousAt.eventually
      (D.slices.Q.open_source.mem_nhds hQ0)
  filter_upwards [hnear] with w hw
  have hb := outgoing_cubic_slice_basin D.σ D.signs (1 / 2) D.Tq D.Φq D.flow
    D.basinQ (w.2, 0) (D.boxQ (D.slices.sliceQ (w.2, 0) hw))
  exact (flow_time_atBot_limit_iff D.flow (w.1 - D.Tq) _ q).mpr (hb.mpr rfl)

theorem NativeConnectionCancellationData.incomingSheet_basin
    (D : NativeConnectionCancellationData (E := E) f p q m) :
    ∀ᶠ w : ℝ × MorseHandle.PositiveSpace D.σ in 𝓝 0,
      Tendsto (fun t => D.flow t (D.incomingSheet w)) atTop (𝓝 p) := by
  have hP0 : 0 ∈ D.slices.P.source := by
    rw [D.slices.P_source, ← D.slices.H_zero]
    exact D.slices.H.map_source' D.slices.zero_source
  have hnear : ∀ᶠ w : ℝ × MorseHandle.PositiveSpace D.σ in 𝓝 0,
      ((0 : MorseHandle.NegativeSpace D.σ), w.2) ∈ D.slices.P.source :=
    (continuous_const.prodMk continuous_snd).continuousAt.eventually
      (D.slices.P.open_source.mem_nhds hP0)
  filter_upwards [hnear] with w hw
  have hb := incoming_cubic_slice_basin D.σ (1 / 2) D.Tp D.Φp D.flow
    D.basinP (0, w.2) (D.boxP (D.slices.sliceP (0, w.2) hw))
  exact (flow_time_atTop_limit_iff D.flow (w.1 - D.Tp) _ p).mpr (hb.mpr rfl)

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
