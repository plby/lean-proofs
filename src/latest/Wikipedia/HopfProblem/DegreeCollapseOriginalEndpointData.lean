import Wikipedia.HopfProblem.DegreeCollapseNativeEndpointPhaseData
import Wikipedia.HopfProblem.DegreeCollapseCommonNativeTransverseData
import Wikipedia.HopfProblem.DegreeCollapseSignedTransversePlanes

/-!
# Constructed original transverse data for the two endpoint slices

The endpoint charts and the original full flow cylinder construct both
transverse maps and smooth phases, their actual relative map, and a common
native cylinder restriction. All signed coordinate and box memberships
are retained. Transversality is not inferred from the unique connection.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] {m : ℕ}

structure NativeEndpointSliceData (σ : Fin m → ℝ) (a : ℝ)
    (Φq Φp : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞)
    (A : PartialDiffeomorph 𝓘(ℝ, (Fin m → ℝ) × ℝ) 𝓘(ℝ, E) ((Fin m → ℝ) × ℝ) M ∞)
    (Rq Rp Tq Tp : ℝ) where
  labelDomain : Set (Fin m → ℝ)
  open_domain : IsOpen labelDomain
  zero_domain : (0 : Fin m → ℝ) ∈ labelDomain
  source : A.source = labelDomain ×ˢ univ
  Q : PartialDiffeomorph
    𝓘(ℝ, MorseHandle.NegativeSpace σ × MorseHandle.PositiveSpace σ) 𝓘(ℝ, Fin m → ℝ)
    (MorseHandle.NegativeSpace σ × MorseHandle.PositiveSpace σ) (Fin m → ℝ) ∞
  P : PartialDiffeomorph
    𝓘(ℝ, MorseHandle.NegativeSpace σ × MorseHandle.PositiveSpace σ) 𝓘(ℝ, Fin m → ℝ)
    (MorseHandle.NegativeSpace σ × MorseHandle.PositiveSpace σ) (Fin m → ℝ) ∞
  H : PartialDiffeomorph
    𝓘(ℝ, MorseHandle.NegativeSpace σ × MorseHandle.PositiveSpace σ)
    𝓘(ℝ, MorseHandle.NegativeSpace σ × MorseHandle.PositiveSpace σ)
    (MorseHandle.NegativeSpace σ × MorseHandle.PositiveSpace σ)
    (MorseHandle.NegativeSpace σ × MorseHandle.PositiveSpace σ) ∞
  zero_source : 0 ∈ H.source
  H_zero : H 0 = 0
  Q_zero : Q 0 = 0
  P_zero : P 0 = 0
  Q_source : Q.source = H.source
  P_source : P.source = H.target
  Q_target : Q.target = labelDomain
  P_target : P.target = labelDomain
  diagram : ∀ u ∈ H.source, P (H u) = Q u
  phaseQ : (MorseHandle.NegativeSpace σ × MorseHandle.PositiveSpace σ) → ℝ
  phaseP : (MorseHandle.NegativeSpace σ × MorseHandle.PositiveSpace σ) → ℝ
  smooth_phaseQ : ContDiff ℝ ∞ phaseQ
  smooth_phaseP : ContDiff ℝ ∞ phaseP
  zero_phaseQ : phaseQ 0 = 0
  zero_phaseP : phaseP 0 = 0
  sliceQ : ∀ u ∈ Q.source,
    cubicFlowCylinder σ a ((MorseHandle.splitCoordinates σ).symm u, Tq) ∈
      closedBall (-a, (0 : Fin m → ℝ)) Rq
  sliceP : ∀ u ∈ P.source,
    cubicFlowCylinder σ a ((MorseHandle.splitCoordinates σ).symm u, Tp) ∈
      closedBall (a, (0 : Fin m → ℝ)) Rp
  formulaQ : ∀ u ∈ Q.source,
    Φq (cubicFlowCylinder σ a ((MorseHandle.splitCoordinates σ).symm u, Tq)) =
      A (Q u, Tq + phaseQ u)
  formulaP : ∀ u ∈ P.source,
    Φp (cubicFlowCylinder σ a ((MorseHandle.splitCoordinates σ).symm u, Tp)) =
      A (P u, Tp + phaseP u)

open Classical in
theorem exists_original_endpoint_slice_data (σ : Fin m → ℝ) {a : ℝ} (ha : 0 < a)
    (Φq Φp : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞)
    (A : PartialDiffeomorph 𝓘(ℝ, (Fin m → ℝ) × ℝ) 𝓘(ℝ, E) ((Fin m → ℝ) × ℝ) M ∞)
    {U : Set (Fin m → ℝ)} (hsource : A.source = U ×ˢ univ) (h0U : 0 ∈ U)
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (hqfield : ∀ y ∈ Φq.target, V y = nativeCubicDescent σ Φq (-(a ^ 2)) y)
    (hpfield : ∀ y ∈ Φp.target, V y = nativeCubicDescent σ Φp (-(a ^ 2)) y)
    (hAfield : ∀ y ∈ A.target, V y = FlowConstruction.partialChartField A.symm
      (fun _ : (Fin m → ℝ) × ℝ => (0, 1)) y)
    {Rq Rp δq δp Tq Tp : ℝ} (hδq : 0 < δq) (hδp : 0 < δp)
    (hboxq : closedBall (-a, (0 : Fin m → ℝ)) Rq ⊆ Φq.source)
    (hboxp : closedBall (a, (0 : Fin m → ℝ)) Rp ⊆ Φp.source)
    (hsliceq : ∀ z : Fin m → ℝ, ‖z‖ ≤ δq →
      cubicFlowCylinder σ a (z, Tq) ∈ ball (-a, (0 : Fin m → ℝ)) Rq)
    (hslicep : ∀ z : Fin m → ℝ, ‖z‖ ≤ δp →
      cubicFlowCylinder σ a (z, Tp) ∈ ball (a, (0 : Fin m → ℝ)) Rp)
    (hpointq : Φq (cubicFlowCylinder σ a (0, Tq)) = A (0, Tq))
    (hpointp : Φp (cubicFlowCylinder σ a (0, Tp)) = A (0, Tp)) :
    ∃ B : PartialDiffeomorph 𝓘(ℝ, (Fin m → ℝ) × ℝ) 𝓘(ℝ, E) ((Fin m → ℝ) × ℝ) M ∞,
      B.source ⊆ A.source ∧ B.target ⊆ A.target ∧ (∀ z, B z = A z) ∧
      (∀ y ∈ B.target, V y = FlowConstruction.partialChartField B.symm
        (fun _ : (Fin m → ℝ) × ℝ => (0, 1)) y) ∧
      Nonempty (NativeEndpointSliceData σ a Φq Φp B Rq Rp Tq Tp) := by
  obtain ⟨Q, v, hQ0, hQfix, hv0, hv, hQU, hQslice, hQphase⟩ :=
    FlowSuspension.exists_native_endpoint_slice_phase σ ha Φq A hsource h0U V
      hqfield hAfield hδq hboxq hsliceq hpointq
  obtain ⟨P, w, hP0, hPfix, hw0, hw, hPU, hPslice, hPphase⟩ :=
    FlowSuspension.exists_native_endpoint_slice_phase σ ha Φp A hsource h0U V
      hpfield hAfield hδp hboxp hslicep hpointp
  let e := MorseHandle.splitCoordinates σ
  obtain ⟨Q', P', H, O, hO, h0O, h0H, hH0, hQ'0, hP'0, hQ's, hP's, hQ't, hP't,
      hOsub, hQ'sub, hP'sub, hQ'map, hP'map, hdiagram, _⟩ :=
    TransverseGerms.exists_common_transverse_coordinates e Q P hQ0 hP0 hQfix hPfix
  have hOU : O ⊆ U := fun _ hz => hQU (hOsub hz).1
  obtain ⟨B, hBs, hBsub, hBt, hBmap, hBfield⟩ :=
    TransverseGerms.exists_restricted_native_cylinder A hsource hO hOU V hAfield
  refine ⟨B, hBsub, hBt, hBmap, hBfield, ⟨{
    labelDomain := O
    open_domain := hO
    zero_domain := h0O
    source := hBs
    Q := Q'
    P := P'
    H := H
    zero_source := h0H
    H_zero := hH0
    Q_zero := hQ'0
    P_zero := hP'0
    Q_source := hQ's
    P_source := hP's
    Q_target := hQ't
    P_target := hP't
    diagram := hdiagram
    phaseQ := fun u => v (e.symm u)
    phaseP := fun u => w (e.symm u)
    smooth_phaseQ := hv.comp e.symm.contDiff
    smooth_phaseP := hw.comp e.symm.contDiff
    zero_phaseQ := by rw [map_zero, hv0]
    zero_phaseP := by rw [map_zero, hw0]
    sliceQ := fun u hu => hQslice (e.symm u) (hQ'sub u hu)
    sliceP := fun u hu => hPslice (e.symm u) (hP'sub u hu)
    formulaQ := ?_
    formulaP := ?_
  }⟩⟩
  · intro u hu
    rw [hBmap, hQ'map]
    exact hQphase (e.symm u) (hQ'sub u hu)
  · intro u hu
    rw [hBmap, hP'map]
    exact hPphase (e.symm u) (hP'sub u hu)

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
