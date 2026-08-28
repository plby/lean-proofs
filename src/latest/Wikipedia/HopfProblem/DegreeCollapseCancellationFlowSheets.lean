import Wikipedia.HopfProblem.DegreeCollapseActualCancellationData
import Wikipedia.HopfProblem.DegreeCollapseFlowSheetCoordinates
import Wikipedia.HopfProblem.DegreeCollapseNativeFlowTransversality

/-!
# Actual native endpoint flow sheets for the constructed cancellation data

These maps are defined by the complete flow applied to the original
endpoint slices. Their smoothness, common reference point, and exact
transverse-label germs are proved. Native transversality of these actual
flow sheets implies the cancellation criterion.
-/

noncomputable section

open Set Function Filter Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {m : ℕ} {f : M → ℝ} {p q : M}

def NativeConnectionCancellationData.outgoingSheet
    (D : NativeConnectionCancellationData (E := E) f p q m)
    (w : ℝ × MorseHandle.NegativeSpace D.σ) : M :=
  D.flow (w.1 - D.Tq) (D.Φq (cubicFlowCylinder D.σ (1 / 2)
    ((MorseHandle.splitCoordinates D.σ).symm (w.2, 0), D.Tq)))

def NativeConnectionCancellationData.incomingSheet
    (D : NativeConnectionCancellationData (E := E) f p q m)
    (w : ℝ × MorseHandle.PositiveSpace D.σ) : M :=
  D.flow (w.1 - D.Tp) (D.Φp (cubicFlowCylinder D.σ (1 / 2)
    ((MorseHandle.splitCoordinates D.σ).symm (0, w.2), D.Tp)))

theorem NativeConnectionCancellationData.outgoingSheet_properties
    (D : NativeConnectionCancellationData (E := E) f p q m) :
    ContMDiffAt 𝓘(ℝ, ℝ × MorseHandle.NegativeSpace D.σ) 𝓘(ℝ, E) ∞ D.outgoingSheet 0 ∧
      D.outgoingSheet 0 = D.A 0 ∧
      (fun w : ℝ × MorseHandle.NegativeSpace D.σ => (D.A.symm (D.outgoingSheet w)).1) =ᶠ[𝓝 0]
        (fun w : ℝ × MorseHandle.NegativeSpace D.σ => D.slices.Q (w.2, 0)) := by
  have hflow := FlowSuspension.native_vertical_cylinder_flow D.A D.slices.source
    (D.smooth_field.of_le (by simp)) D.vertical D.flow D.integral
  have hQU : D.slices.Q.target ⊆ D.slices.labelDomain := fun _ hz => D.slices.Q_target ▸ hz
  have hQ0 : 0 ∈ D.slices.Q.source := D.slices.Q_source ▸ D.slices.zero_source
  have hh := FlowSuspension.phase_flow_subsheet_properties D.A D.slices.source D.flow hflow
    D.slices.Q hQU hQ0 D.slices.Q_zero
    (fun u => D.Φq (cubicFlowCylinder D.σ (1 / 2) ((MorseHandle.splitCoordinates D.σ).symm u, D.Tq)))
    D.slices.phaseQ D.Tq D.slices.smooth_phaseQ D.slices.zero_phaseQ D.slices.formulaQ
    (ContinuousLinearMap.inl ℝ (MorseHandle.NegativeSpace D.σ) (MorseHandle.PositiveSpace D.σ))
  unfold NativeConnectionCancellationData.outgoingSheet
  simpa only [ContinuousLinearMap.inl_apply,
    Prod.fst_zero, Prod.snd_zero, zero_sub] using hh

theorem NativeConnectionCancellationData.incomingSheet_properties
    (D : NativeConnectionCancellationData (E := E) f p q m) :
    ContMDiffAt 𝓘(ℝ, ℝ × MorseHandle.PositiveSpace D.σ) 𝓘(ℝ, E) ∞ D.incomingSheet 0 ∧
      D.incomingSheet 0 = D.A 0 ∧
      (fun w : ℝ × MorseHandle.PositiveSpace D.σ => (D.A.symm (D.incomingSheet w)).1) =ᶠ[𝓝 0]
        (fun w : ℝ × MorseHandle.PositiveSpace D.σ => D.slices.P (0, w.2)) := by
  have hflow := FlowSuspension.native_vertical_cylinder_flow D.A D.slices.source
    (D.smooth_field.of_le (by simp)) D.vertical D.flow D.integral
  have hPU : D.slices.P.target ⊆ D.slices.labelDomain := fun _ hz => D.slices.P_target ▸ hz
  have hP0 : 0 ∈ D.slices.P.source := by
    rw [D.slices.P_source, ← D.slices.H_zero]
    exact D.slices.H.map_source' D.slices.zero_source
  have hh := FlowSuspension.phase_flow_subsheet_properties D.A D.slices.source D.flow hflow
    D.slices.P hPU hP0 D.slices.P_zero
    (fun u => D.Φp (cubicFlowCylinder D.σ (1 / 2) ((MorseHandle.splitCoordinates D.σ).symm u, D.Tp)))
    D.slices.phaseP D.Tp D.slices.smooth_phaseP D.slices.zero_phaseP D.slices.formulaP
    (ContinuousLinearMap.inr ℝ (MorseHandle.NegativeSpace D.σ) (MorseHandle.PositiveSpace D.σ))
  unfold NativeConnectionCancellationData.incomingSheet
  simpa only [ContinuousLinearMap.inr_apply,
    Prod.fst_zero, Prod.snd_zero, zero_sub] using hh

theorem NativeConnectionCancellationData.transverse_of_native_sheets
    (D : NativeConnectionCancellationData (E := E) f p q m)
    (htrans : NativeTransversality.At
      𝓘(ℝ, ℝ × MorseHandle.NegativeSpace D.σ) 𝓘(ℝ, ℝ × MorseHandle.PositiveSpace D.σ)
      𝓘(ℝ, E) D.outgoingSheet D.incomingSheet 0 0) : D.Transverse := by
  obtain ⟨hout, hout0, houtlabel⟩ := D.outgoingSheet_properties
  obtain ⟨hin, hin0, hinlabel⟩ := D.incomingSheet_properties
  have hQ0 : 0 ∈ D.slices.Q.source := D.slices.Q_source ▸ D.slices.zero_source
  have hP0 : 0 ∈ D.slices.P.source := by
    rw [D.slices.P_source, ← D.slices.H_zero]
    exact D.slices.H.map_source' D.slices.zero_source
  have hQdiff := (D.slices.Q.contMDiffOn_toFun.contDiffOn.contDiffAt
    (D.slices.Q.open_source.mem_nhds hQ0)).differentiableAt (by simp)
  have hPdiff := (D.slices.P.contMDiffOn_toFun.contDiffOn.contDiffAt
    (D.slices.P.open_source.mem_nhds hP0)).differentiableAt (by simp)
  have hq : DifferentiableAt ℝ (fun x : MorseHandle.NegativeSpace D.σ => D.slices.Q (x, 0)) 0 :=
    hQdiff.comp (f := fun x : MorseHandle.NegativeSpace D.σ => (x, 0)) 0
      (ContinuousLinearMap.inl ℝ (MorseHandle.NegativeSpace D.σ)
        (MorseHandle.PositiveSpace D.σ)).differentiableAt
  have hp : DifferentiableAt ℝ (fun y : MorseHandle.PositiveSpace D.σ => D.slices.P (0, y)) 0 :=
    hPdiff.comp (f := fun y : MorseHandle.PositiveSpace D.σ => (0, y)) 0
      (ContinuousLinearMap.inr ℝ (MorseHandle.NegativeSpace D.σ)
        (MorseHandle.PositiveSpace D.σ)).differentiableAt
  have hA0 : (0 : (Fin m → ℝ) × ℝ) ∈ D.A.source := by
    rw [D.slices.source]
    exact ⟨D.slices.zero_domain, mem_univ _⟩
  exact TransverseGerms.transverse_labels_of_native_flow_sheets D.A hA0
    D.outgoingSheet D.incomingSheet (hout.mdifferentiableAt (by simp))
    (hin.mdifferentiableAt (by simp)) hout0 hin0 hq hp houtlabel hinlabel htrans

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
