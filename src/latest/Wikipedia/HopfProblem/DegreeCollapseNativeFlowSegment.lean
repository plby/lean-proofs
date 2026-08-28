import Wikipedia.HopfProblem.DegreeCollapseNativeSuspensionField
import Wikipedia.HopfProblem.DegreeCollapsePerturbedNoReturn

/-!
# Comparing actual native flow on a closed chart segment

Uniqueness on the open interval and continuity on its closure identify
both endpoints. The curve need not be globally continuous outside the
chart domain. Actual coordinate integral curves then determine the exact
transition of the original native complete flow.
-/

noncomputable section

open Set Function Manifold
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.FlowSuspension

variable {B M : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [TopologicalSpace M] [ChartedSpace B M] [IsManifold 𝓘(ℝ, B) 1 M] [T2Space M]
  {V : (x : M) → TangentSpace 𝓘(ℝ, B) x}

/-- Only continuity on the closed segment is needed for the endpoint comparison. -/
theorem native_flow_segment_endpoints
    (hV : ContMDiff 𝓘(ℝ, B) (𝓘(ℝ, B).tangent) 1
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, B) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    {γ : ℝ → M} {a b : ℝ} (hab : a < b) (hγcont : ContinuousOn γ (Icc a b))
    (hγ : IsMIntegralCurveOn γ V (Ioo a b)) : F (b - a) (γ a) = γ b := by
  let c := (a + b) / 2
  have hc : c ∈ Ioo a b := by constructor <;> dsimp [c] <;> linarith
  have hη : IsMIntegralCurve (fun t => F (t - c) (γ c)) V := by
    have hh := (hcurve (γ c)).comp_add (-c)
    simpa only [sub_eq_add_neg, Function.comp_def] using hh
  have heq : EqOn γ (fun t => F (t - c) (γ c)) (Ioo a b) :=
    isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless hc hV hγ
      (hη.isMIntegralCurveOn _) (by simp)
  have heqclosed : EqOn γ (fun t => F (t - c) (γ c)) (Icc a b) :=
    heq.of_subset_closure hγcont hη.continuous.continuousOn Ioo_subset_Icc_self
      (by rw [closure_Ioo hab.ne])
  have ha := heqclosed (show a ∈ Icc a b from ⟨le_rfl, hab.le⟩)
  have hb := heqclosed (show b ∈ Icc a b from ⟨hab.le, le_rfl⟩)
  change γ a = F (a - c) (γ c) at ha
  change γ b = F (b - c) (γ c) at hb
  rw [ha, ← F.map_add, show b - a + (a - c) = b - c by ring, ← hb]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A genuine coordinate flow segment gives the exact native transition,
provided its whole trajectory stays in the actual chart source. -/
theorem native_chart_flow_at_time
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, B) E M ∞)
    (hV : ContMDiff 𝓘(ℝ, B) (𝓘(ℝ, B).tangent) 1
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, B) M)))
    (G : Flow ℝ M) (hGcurve : ∀ x, IsMIntegralCurve (fun t => G t x) V)
    (F : Flow ℝ E) (W : E → E)
    (hFcurve : ∀ p t, HasDerivAt (fun s => F s p) (W (F t p)) t)
    (hmodel : ∀ x ∈ Φ.target, V x = FlowConstruction.partialChartField Φ.symm W x)
    {p : E} {T : ℝ} (hT : 0 < T) (hstay : ∀ t ∈ Icc (0 : ℝ) T, F t p ∈ Φ.source) :
    G T (Φ p) = Φ (F T p) := by
  let γ : ℝ → M := fun t => Φ (F t p)
  have hcont : ContinuousOn γ (Icc (0 : ℝ) T) :=
    Φ.contMDiffOn_toFun.continuousOn.comp
      (F.continuous continuous_id continuous_const).continuousOn hstay
  have hγ : IsMIntegralCurveOn γ V (Ioo (0 : ℝ) T) := by
    intro t ht
    have hs := hstay t ⟨ht.1.le, ht.2.le⟩
    have hd := FlowConstruction.hasMFDerivAt_lift_partialChartCurve Φ.symm W (hFcurve p t) hs
    have hy := Φ.map_source' hs
    have hd' : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, B) γ t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (FlowConstruction.partialChartField Φ.symm W (γ t))) := hd
    rw [← hmodel (γ t) hy] at hd'
    exact hd'.hasMFDerivWithinAt
  have hh := native_flow_segment_endpoints hV G hGcurve hT hcont hγ
  simpa only [γ, sub_zero, F.map_zero_apply] using hh

end Wikipedia.HopfProblem.DegreeCollapse.FlowSuspension
