import Wikipedia.HopfProblem.DegreeCollapseNativeCylinderInvariance
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Exact complete flow in a native vertical cylinder

Native uniqueness identifies every vertical coordinate line with the
original complete flow. Consequently the unchanged lower and translated
upper halves of a corrected cylinder retain the original exterior tails.
-/

noncomputable section

open Set Function Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.FlowSuspension

variable {Z E M : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M] [T2Space M]

theorem native_vertical_cylinder_flow
    (Φ : PartialDiffeomorph 𝓘(ℝ, Z × ℝ) 𝓘(ℝ, E) (Z × ℝ) M ∞)
    {U : Set Z} (hsource : Φ.source = U ×ˢ univ)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hmodel : ∀ x ∈ Φ.target, V x =
      FlowConstruction.partialChartField Φ.symm (fun _ : Z × ℝ => (0, 1)) x)
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (z : Z) (hz : z ∈ U) (s t : ℝ) : F t (Φ (z, s)) = Φ (z, s + t) := by
  let γ : ℝ → M := fun t => Φ (z, s + t)
  have hγ : IsMIntegralCurve γ V := by
    intro t
    have hstay : (z, s + t) ∈ Φ.source := by rw [hsource]; exact ⟨hz, mem_univ _⟩
    have hcoord : HasDerivAt (fun r : ℝ => (z, s + r)) (0, 1) t :=
      (hasDerivAt_const t z).prodMk ((hasDerivAt_id t).const_add s)
    have hd := FlowConstruction.hasMFDerivAt_lift_partialChartCurve
      Φ.symm (fun _ : Z × ℝ => (0, 1)) hcoord hstay
    change HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        (FlowConstruction.partialChartField Φ.symm (fun _ : Z × ℝ => (0, 1)) (γ t))) at hd
    rw [← hmodel (γ t) (Φ.map_source' hstay)] at hd
    exact hd
  have heq := isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless hV (hF (Φ (z, s))) hγ
    (t₀ := 0) (by simp only [γ, F.map_zero_apply, add_zero])
  exact congrFun heq t

theorem native_corrected_cylinder_tails
    (Φ Ω : PartialDiffeomorph 𝓘(ℝ, Z × ℝ) 𝓘(ℝ, E) (Z × ℝ) M ∞)
    {U : Set Z} (hΦsource : Φ.source = U ×ˢ univ) (hΩsource : Ω.source = U ×ˢ univ)
    {V W : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hW : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1
      (fun x => (⟨x, W x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hΦmodel : ∀ x ∈ Φ.target, V x =
      FlowConstruction.partialChartField Φ.symm (fun _ : Z × ℝ => (0, 1)) x)
    (hΩmodel : ∀ x ∈ Ω.target, W x =
      FlowConstruction.partialChartField Ω.symm (fun _ : Z × ℝ => (0, 1)) x)
    (F G : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hG : ∀ x, IsMIntegralCurve (fun t => G t x) W)
    (D : Z → Z) (hDU : MapsTo D U U)
    (hleft : ∀ p, p.2 ≤ 0 → Ω p = Φ p)
    (hright : ∀ p, 1 ≤ p.2 → Ω p = Φ (D p.1, p.2)) :
    (∀ z ∈ U, ∀ t : ℝ, t ≤ 0 → G t (Φ (z, 0)) = F t (Φ (z, 0))) ∧
    (∀ z ∈ U, ∀ t : ℝ, 0 ≤ t → G t (Ω (z, 1)) = F t (Ω (z, 1))) := by
  constructor
  · intro z hz t ht
    rw [← hleft (z, 0) le_rfl,
      native_vertical_cylinder_flow Ω hΩsource hW hΩmodel G hG z hz 0 t, zero_add,
      hleft (z, t) ht, hleft (z, 0) le_rfl,
      native_vertical_cylinder_flow Φ hΦsource hV hΦmodel F hF z hz 0 t, zero_add]
  · intro z hz t ht
    rw [native_vertical_cylinder_flow Ω hΩsource hW hΩmodel G hG z hz 1 t,
      hright (z, 1 + t) (by dsimp; linarith), hright (z, 1) le_rfl,
      native_vertical_cylinder_flow Φ hΦsource hV hΦmodel F hF (D z) (hDU hz) 1 t]

end Wikipedia.HopfProblem.DegreeCollapse.FlowSuspension
