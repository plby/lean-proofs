import Wikipedia.HopfProblem.DegreeCollapseEndpointPhasePropagation

/-!
# Actual cubic overlap formulas from the corrected native cylinder

The original endpoint slice equations propagate under the original
native flow. The corrected middle chart has the prescribed two exterior
phase formulas. Exact endpoint coordinate changes and constructed box
controls then give both cubic-time overlap identities needed by the
full closed-axis field-chart gluing theorem.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E Z B M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup B] [NormedSpace ℝ B]
  [TopologicalSpace M] [ChartedSpace B M] [IsManifold 𝓘(ℝ, B) 1 M] [T2Space M]
  {m : ℕ} {V : (x : M) → TangentSpace 𝓘(ℝ, B) x}

theorem matched_cubic_time_formulas (σ : Fin m → ℝ) {a : ℝ} (ha : 0 < a)
    (Φq Φp : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, B) (Model m) M ∞)
    (A : PartialDiffeomorph 𝓘(ℝ, Z × ℝ) 𝓘(ℝ, B) (Z × ℝ) M ∞)
    {U : Set Z} (hAsource : A.source = U ×ˢ univ)
    (hV : ContMDiff 𝓘(ℝ, B) (𝓘(ℝ, B).tangent) 1
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, B) M)))
    (hqfield : ∀ y ∈ Φq.target, V y = nativeCubicDescent σ Φq (-(a ^ 2)) y)
    (hpfield : ∀ y ∈ Φp.target, V y = nativeCubicDescent σ Φp (-(a ^ 2)) y)
    (hAfield : ∀ y ∈ A.target, V y =
      FlowConstruction.partialChartField A.symm (fun _ : Z × ℝ => (0, 1)) y)
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (e : (Fin m → ℝ) ≃L[ℝ] E) (L : E ≃L[ℝ] E)
    (Q P : E → Z) (v₀ v₁ : E → ℝ) {Oq Op : Set E}
    (hOq : IsOpen Oq) (hOp : IsOpen Op) (h0q : (0 : E) ∈ Oq) (h0p : (0 : E) ∈ Op)
    (hQU : ∀ u ∈ Oq, Q u ∈ U) (hPU : ∀ u ∈ Op, P u ∈ U)
    {Rq Rp Tq Tp : ℝ}
    (hboxq : closedBall (-a, (0 : Fin m → ℝ)) Rq ⊆ Φq.source)
    (hboxp : closedBall (a, (0 : Fin m → ℝ)) Rp ⊆ Φp.source)
    (hsliceq : ∀ u ∈ Oq, cubicFlowCylinder σ a (e.symm u, Tq) ∈
      closedBall (-a, (0 : Fin m → ℝ)) Rq)
    (hslicep : ∀ u ∈ Op, cubicFlowCylinder σ a (e.symm u, Tp) ∈
      closedBall (a, (0 : Fin m → ℝ)) Rp)
    (hphaseq : ∀ u ∈ Oq,
      Φq (cubicFlowCylinder σ a (e.symm u, Tq)) = A (Q u, Tq + v₀ u))
    (hphasep : ∀ u ∈ Op,
      Φp (cubicFlowCylinder σ a (e.symm u, Tp)) = A (P u, Tp + v₁ u))
    (Ψq Ψp Φm : Model m → M) (Ξ : E × ℝ → M)
    (hnewq : ∀ p, Ψq p = Φq p)
    (hnewp : ∀ z t, Ψp (cubicFlowCylinder σ a (z, t)) =
      Φp (cubicFlowCylinder σ a (e.symm (L (e z)), t)))
    (hmid : ∀ z t, Φm (cubicFlowCylinder σ a (z, t)) = Ξ (e z, t))
    {rq rp : ℝ}
    (hcontrolq : closedBall (-a, (0 : Fin m → ℝ)) rq ⊆
      closedBall (-a, (0 : Fin m → ℝ)) Rq)
    (hcontrolp : ∀ z t, cubicFlowCylinder σ a (z, t) ∈
      closedBall (a, (0 : Fin m → ℝ)) rp →
      cubicFlowCylinder σ a (e.symm (L (e z)), t) ∈ closedBall (a, (0 : Fin m → ℝ)) Rp)
    (hleft : ∀ᶠ u in 𝓝 (0 : E), ∀ t : ℝ, t ≤ -1 → Ξ (u, t) = A (Q u, t + v₀ u))
    (hright : ∀ᶠ u in 𝓝 (0 : E), ∀ t : ℝ, 2 ≤ t → Ξ (u, t) = A (P (L u), t + v₁ (L u))) :
    (∀ᶠ z : Fin m → ℝ in 𝓝 0, ∀ t : ℝ, t ≤ -1 →
      cubicFlowCylinder σ a (z, t) ∈ closedBall (-a, (0 : Fin m → ℝ)) rq →
      Ψq (cubicFlowCylinder σ a (z, t)) = Φm (cubicFlowCylinder σ a (z, t))) ∧
    (∀ᶠ z : Fin m → ℝ in 𝓝 0, ∀ t : ℝ, 2 ≤ t →
      cubicFlowCylinder σ a (z, t) ∈ closedBall (a, (0 : Fin m → ℝ)) rp →
      Ψp (cubicFlowCylinder σ a (z, t)) = Φm (cubicFlowCylinder σ a (z, t))) := by
  have he : Tendsto e (𝓝 (0 : Fin m → ℝ)) (𝓝 (0 : E)) := by
    simpa only [map_zero] using e.continuous.tendsto 0
  have heL : Tendsto (fun z : Fin m → ℝ => L (e z)) (𝓝 0) (𝓝 (0 : E)) := by
    have hh : Tendsto L (𝓝 (0 : E)) (𝓝 (0 : E)) := by
      simpa only [map_zero] using L.continuous.tendsto 0
    exact hh.comp he
  constructor
  · filter_upwards [he.eventually hleft, he.eventually (hOq.mem_nhds h0q)] with z hformula hz
    intro t ht hp
    have hstart : cubicFlowCylinder σ a (z, Tq) ∈
        closedBall (-a, (0 : Fin m → ℝ)) Rq := by
      simpa only [e.symm_apply_apply] using hsliceq (e z) hz
    have hphase : Φq (cubicFlowCylinder σ a (z, Tq)) = A (Q (e z), Tq + v₀ (e z)) := by
      simpa only [e.symm_apply_apply] using hphaseq (e z) hz
    calc
      Ψq (cubicFlowCylinder σ a (z, t)) = Φq (cubicFlowCylinder σ a (z, t)) := hnewq _
      _ = A (Q (e z), t + v₀ (e z)) :=
        native_endpoint_phase_through_box σ ha Φq A hAsource hV hqfield hAfield F hF
          hboxq z (hQU (e z) hz) hstart hphase t (hcontrolq hp)
      _ = Ξ (e z, t) := (hformula t ht).symm
      _ = Φm (cubicFlowCylinder σ a (z, t)) := (hmid z t).symm
  · filter_upwards [he.eventually hright, heL.eventually (hOp.mem_nhds h0p)] with z hformula hz
    intro t ht hp
    calc
      Ψp (cubicFlowCylinder σ a (z, t)) =
          Φp (cubicFlowCylinder σ a (e.symm (L (e z)), t)) := hnewp z t
      _ = A (P (L (e z)), t + v₁ (L (e z))) :=
        native_endpoint_phase_through_box σ ha Φp A hAsource hV hpfield hAfield F hF
          hboxp (e.symm (L (e z))) (hPU (L (e z)) hz)
          (hslicep (L (e z)) hz) (hphasep (L (e z)) hz) t (hcontrolp z t hp)
      _ = Ξ (e z, t) := (hformula t ht).symm
      _ = Φm (cubicFlowCylinder σ a (z, t)) := (hmid z t).symm

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
