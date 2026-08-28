import Wikipedia.HopfProblem.DegreeCollapseOriginalEndpointData
import Wikipedia.HopfProblem.DegreeCollapseTransverseLabelGeometry
import Wikipedia.HopfProblem.DegreeCollapseNativeTransverseCancellation

/-!
# Cancellation using the constructed original endpoint data

Native transversality is required only for the actual two label sheets.
Their genuine relative chart supplies the coordinate transversality used
by supported correction. All later fields and charts are constructed.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {m : ℕ}

theorem cancel_native_endpoint_slice_data
    (σ : Fin m → ℝ) (hσ : ∀ i, σ i = -1 ∨ σ i = 1) {a : ℝ} (ha : 0 < a)
    (Φq Φp : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞)
    (A : PartialDiffeomorph 𝓘(ℝ, (Fin m → ℝ) × ℝ) 𝓘(ℝ, E) ((Fin m → ℝ) × ℝ) M ∞)
    {Rq Rp Tq Tp : ℝ} (D : NativeEndpointSliceData σ a Φq Φp A Rq Rp Tq Tp)
    (htrans : NativeTransversality.At
      𝓘(ℝ, MorseHandle.NegativeSpace σ) 𝓘(ℝ, MorseHandle.PositiveSpace σ) 𝓘(ℝ, Fin m → ℝ)
      (fun x => D.Q (x, 0)) (fun y => D.P (0, y)) 0 0)
    {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : IsMorse E f)
    {b s : ℝ} (hs : 0 < s)
    (hheight : ∀ z ∈ A.source, z.2 ∈ Ioo (0 : ℝ) 1 → f (A z) = b - s * z.2)
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hqfield : ∀ y ∈ Φq.target, V y = nativeCubicDescent σ Φq (-(a ^ 2)) y)
    (hpfield : ∀ y ∈ Φp.target, V y = nativeCubicDescent σ Φp (-(a ^ 2)) y)
    (hAfield : ∀ y ∈ A.target, V y = FlowConstruction.partialChartField A.symm
      (fun _ : (Fin m → ℝ) × ℝ => (0, 1)) y)
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hzero : ∀ x ∈ criticalPoints E f, V x = 0)
    (hdesc : ∀ x, x ∉ criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hinj : InjOn f (criticalPoints E f))
    (hRq : 0 < Rq) (hRp : 0 < Rp)
    (hboxq : closedBall (-a, (0 : Fin m → ℝ)) Rq ⊆ Φq.source)
    (hboxp : closedBall (a, (0 : Fin m → ℝ)) Rp ⊆ Φp.source)
    (hqbasin : ∀ z ∈ Φq.source,
      Tendsto (fun t => F t (Φq z)) atBot (𝓝 (Φq (-a, 0))) ↔
        ∀ i, σ i = 1 → z.2 i = 0)
    (hpbasin : ∀ z ∈ Φp.source,
      Tendsto (fun t => F t (Φp z)) atTop (𝓝 (Φp (a, 0))) ↔
        ∀ i, σ i = -1 → z.2 i = 0)
    (hold : ∀ x, Tendsto (fun t => F t x) atBot (𝓝 (Φq (-a, 0))) →
      Tendsto (fun t => F t x) atTop (𝓝 (Φp (a, 0))) → ∃ t, F t (A (0, 0)) = x)
    (hp : Φp (a, 0) ∈ criticalPoints E f) (hq : Φq (-a, 0) ∈ criticalPoints E f)
    (hpq : f (Φp (a, 0)) < f (Φq (-a, 0)))
    {c d : ℝ} (hc : c < f (Φp (a, 0))) (hd : f (Φq (-a, 0)) < d)
    (hpair : ∀ x ∈ criticalPoints E f,
      f x ∈ Icc c d → x = Φp (a, 0) ∨ x = Φq (-a, 0)) :
    ∃ g : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧ IsMorse E g ∧
      (criticalPoints E g).ncard + 2 = (criticalPoints E f).ncard ∧
      (∀ x, x ∈ criticalPoints E g ↔
        x ∈ criticalPoints E f ∧ x ≠ Φp (a, 0) ∧ x ≠ Φq (-a, 0)) ∧
      ∀ x, f x ∉ Ioo c d → g =ᶠ[𝓝 x] f := by
  have hrelative := TransverseGerms.relative_transverse_of_label_sheets D.Q D.P D.H
    D.zero_source D.H_zero D.Q_zero D.P_zero (fun _ hz => D.Q_source ▸ hz)
    (fun _ hz => D.P_source ▸ hz) D.diagram htrans
  exact cancel_unique_native_transverse_connection σ hσ ha Φq Φp A D.source hf hm hs hheight
    V hV hqfield hpfield hAfield F hF hzero hdesc hinj D.Q D.P D.H D.zero_source D.H_zero
    D.Q_zero D.P_zero D.Q_source D.P_source D.Q_target D.P_target D.diagram hrelative
    D.phaseQ D.phaseP D.smooth_phaseQ D.smooth_phaseP D.zero_phaseQ D.zero_phaseP
    hRq hRp hboxq hboxp D.sliceQ D.sliceP D.formulaQ D.formulaP hqbasin hpbasin hold
    hp hq hpq hc hd hpair

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
