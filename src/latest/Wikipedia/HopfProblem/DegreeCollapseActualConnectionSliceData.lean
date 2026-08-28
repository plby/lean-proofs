import Wikipedia.HopfProblem.DegreeCollapseOriginalEndpointData
import Wikipedia.HopfProblem.DegreeCollapseMatchedEndpointBasins
import Wikipedia.HopfProblem.DegreeCollapseClockNormalizedBasins

/-!
# Actual Morse connections construct all original endpoint slice data

Adjacent Morse indices and the original field germs give matching cubic
endpoint charts with exact basin equations. Clock normalization preserves
those equations. The actual regular cylinder then constructs the phases,
signed transverse charts, and their common native domain. No endpoint
chart, phase, or transverse map is supplied to this construction.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {m : ℕ} {f : M → ℝ} {p q x : M}

open Classical in
theorem exists_actual_connection_slice_data
    (cp : SignedMorseChart (E := E) f p) (cq : SignedMorseChart (E := E) f q)
    (hf : Continuous f) (hdim : Module.finrank ℝ E = m + 1)
    (hindex : Fintype.card {i // cq.weights i = -1} =
      Fintype.card {i // cp.weights i = -1} + 1)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun y => (⟨y, V y⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ y, IsMIntegralCurve (fun t => F t y) V)
    (hmono : ∀ y, Antitone (fun t => f (F t y)))
    (hxp : x ≠ p) (hxq : x ≠ q)
    (hp : Tendsto (fun t => F t x) atTop (𝓝 p))
    (hq : Tendsto (fun t => F t x) atBot (𝓝 q))
    (heqp : ∀ᶠ y in 𝓝 p, V y = cp.descentField y)
    (heqq : ∀ᶠ y in 𝓝 q, V y = cq.descentField y)
    (A : PartialDiffeomorph 𝓘(ℝ, (Fin m → ℝ) × ℝ) 𝓘(ℝ, E) ((Fin m → ℝ) × ℝ) M ∞)
    {U : Set (Fin m → ℝ)} (hAsource : A.source = U ×ˢ univ) (h0U : 0 ∈ U)
    (hAfield : ∀ y ∈ A.target, V y = FlowConstruction.partialChartField A.symm
      (fun _ : (Fin m → ℝ) × ℝ => (0, 1)) y)
    (hAaxis : ∀ t : ℝ, A (0, t) = F t x) :
    ∃ (σ : Fin m → ℝ)
      (Ψq Ψp : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞)
      (B : PartialDiffeomorph 𝓘(ℝ, (Fin m → ℝ) × ℝ) 𝓘(ℝ, E) ((Fin m → ℝ) × ℝ) M ∞)
      (Rq Rp Tq Tp : ℝ),
      (∀ i, σ i = -1 ∨ σ i = 1) ∧ 0 < Rq ∧ 0 < Rp ∧
      Ψq (-(1 / 2 : ℝ), 0) = q ∧ Ψp (1 / 2, 0) = p ∧
      closedBall (-(1 / 2 : ℝ), (0 : Fin m → ℝ)) Rq ⊆ Ψq.source ∧
      closedBall (1 / 2, (0 : Fin m → ℝ)) Rp ⊆ Ψp.source ∧
      (∀ y ∈ Ψq.target, V y = nativeCubicDescent σ Ψq (-(1 / 2 : ℝ) ^ 2) y) ∧
      (∀ y ∈ Ψp.target, V y = nativeCubicDescent σ Ψp (-(1 / 2 : ℝ) ^ 2) y) ∧
      (∀ z ∈ Ψq.source, Tendsto (fun t => F t (Ψq z)) atBot (𝓝 q) ↔
        ∀ i, σ i = 1 → z.2 i = 0) ∧
      (∀ z ∈ Ψp.source, Tendsto (fun t => F t (Ψp z)) atTop (𝓝 p) ↔
        ∀ i, σ i = -1 → z.2 i = 0) ∧
      B.source ⊆ A.source ∧ B.target ⊆ A.target ∧ (∀ z, B z = A z) ∧
      (∀ y ∈ B.target, V y = FlowConstruction.partialChartField B.symm
        (fun _ : (Fin m → ℝ) × ℝ => (0, 1)) y) ∧
      Nonempty (NativeEndpointSliceData σ (1 / 2) Ψq Ψp B Rq Rp Tq Tp) := by
  have ha : (0 : ℝ) < 1 / 2 := by norm_num
  obtain ⟨σ, Φp, Φq, hσ, hpc, hpv, hqc, hqv, hpfield, hqfield,
      hpbasin, hqbasin, hptail, hqtail⟩ :=
    exists_matched_connection_basin_endpoints cp cq hf hdim hindex (hV.of_le (by simp))
      F hF hmono hxp hxq hp hq heqp heqq
  obtain ⟨Ψp, Rp, δp, Tp, hps, hpval, hRp, hδp, hpbox, hpslice, hpf, hpaxis, hplimits⟩ :=
    exists_basin_preserving_endpoint_clock σ ha Φp hV hpfield F hF
      (show (1 / 2 : ℝ) ∈ Icc (-(1 / 2 : ℝ)) (1 / 2) by constructor <;> norm_num)
      rfl hpc x (by rw [hpv]; exact hp) hptail
  obtain ⟨Ψq, Rq, δq, Tq, hqs, hqval, hRq, hδq, hqbox, hqslice, hqf, hqaxis, hqlimits⟩ :=
    exists_basin_preserving_endpoint_clock σ ha Φq hV hqfield F hF
      (show (-(1 / 2 : ℝ)) ∈ Icc (-(1 / 2 : ℝ)) (1 / 2) by constructor <;> norm_num)
      (by ring) hqc x (by rw [hqv]; exact hq) hqtail
  have hqp : Ψq (cubicFlowCylinder σ (1 / 2) (0, Tq)) = A (0, Tq) :=
    (hqaxis Tq (ball_subset_closedBall (hqslice 0 (by simpa using hδq.le)))).trans (hAaxis Tq).symm
  have hpp : Ψp (cubicFlowCylinder σ (1 / 2) (0, Tp)) = A (0, Tp) :=
    (hpaxis Tp (ball_subset_closedBall (hpslice 0 (by simpa using hδp.le)))).trans (hAaxis Tp).symm
  obtain ⟨B, hBs, hBt, hBmap, hBfield, hdata⟩ :=
    exists_original_endpoint_slice_data σ ha Ψq Ψp A hAsource h0U V hqf hpf hAfield
      hδq hδp hqbox hpbox hqslice hpslice hqp hpp
  refine ⟨σ, Ψq, Ψp, B, Rq, Rp, Tq, Tp, hσ, hRq, hRp,
    hqval.trans hqv, hpval.trans hpv, hqbox, hpbox, hqf, hpf, ?_, ?_,
    hBs, hBt, hBmap, hBfield, hdata⟩
  · intro z hz
    exact (hqlimits z q).2.trans (hqbasin z (hqs ▸ hz))
  · intro z hz
    exact (hplimits z p).1.trans (hpbasin z (hps ▸ hz))

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
