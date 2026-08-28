import Wikipedia.HopfProblem.DegreeCollapseCompactPhaseFlow
import Wikipedia.HopfProblem.DegreeCollapseNativePositiveRescaling
import Wikipedia.HopfProblem.DegreeCollapseNativeCylinderInvariance
import Wikipedia.HopfProblem.DegreeCollapseNativeTimeChange
import Wikipedia.SmoothSixDPoincare.CompactFlow
import Wikipedia.HopfProblem.DegreeCollapseNativeCylinderConjugacy

/-!
# Native compact phase realization preserving complete orbit geometry

The scalar phase germ constructs a compact positive rescaling of the
original native field. Its actual complete flow has the prescribed phase
on the right and the original time coordinate on the left. All whole
orbits, both endpoint limits, zeros, strict descent, exterior field germs,
and the full reference-axis motion are retained.
-/

noncomputable section

open Set Function Filter Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.FlowTimeChange

variable {E B M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B]
  [TopologicalSpace M] [ChartedSpace B M] [IsManifold 𝓘(ℝ, B) ∞ M]
  [T2Space M] [CompactSpace M]

/-- Realize the original transverse phase germ by an actual compact native
speed change, retaining the complete connecting-orbit geometry. -/
theorem exists_native_phase_realization
    (Φ : PartialDiffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, B) (E × ℝ) M ∞)
    {U : Set E} (hU : IsOpen U) (h0U : (0 : E) ∈ U) (hsource : Φ.source = U ×ˢ univ)
    (V : (x : M) → TangentSpace 𝓘(ℝ, B) x)
    (hV : ContMDiff 𝓘(ℝ, B) (𝓘(ℝ, B).tangent) ∞
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, B) M)))
    (hmodel : ∀ x ∈ Φ.target, V x =
      FlowConstruction.partialChartField Φ.symm (fun _ : E × ℝ => (0, 1)) x)
    (H : Flow ℝ M) (hH : ∀ x, IsMIntegralCurve (fun t => H t x) V)
    {v : E → ℝ} (hv : ContDiff ℝ ∞ v) (hv0 : v 0 = 0) :
    ∃ (N : Set M) (g : E → ℝ) (V' : (x : M) → TangentSpace 𝓘(ℝ, B) x) (G : Flow ℝ M),
      IsCompact N ∧ N ⊆ Φ.target ∩ Φ '' (U ×ˢ Ioo (0 : ℝ) 1) ∧
      ContDiff ℝ ∞ g ∧ g =ᶠ[𝓝 0] v ∧ g 0 = 0 ∧
      ContMDiff 𝓘(ℝ, B) (𝓘(ℝ, B).tangent) ∞
        (fun x => (⟨x, V' x⟩ : TangentBundle 𝓘(ℝ, B) M)) ∧
      (∀ x, IsMIntegralCurve (fun t => G t x) V') ∧
      (∀ x, V' x = 0 ↔ V x = 0) ∧
      (∀ (f : M → ℝ) x, mvfderiv 𝓘(ℝ, B) f x (V x) < 0 →
        mvfderiv 𝓘(ℝ, B) f x (V' x) < 0) ∧
      (∀ x ∉ N, ∀ᶠ y in 𝓝 x, V' y = V y) ∧
      (∀ x, range (fun t => G t x) = range (fun t => H t x) ∧
        (∀ p, Tendsto (fun t => G t x) atTop (𝓝 p) ↔ Tendsto (fun t => H t x) atTop (𝓝 p)) ∧
        ∀ p, Tendsto (fun t => G t x) atBot (𝓝 p) ↔ Tendsto (fun t => H t x) atBot (𝓝 p)) ∧
      (∀ z ∈ U, ∀ t : ℝ, t ≤ 1 / 3 → G t (Φ (z, 0)) = Φ (z, t)) ∧
      (∀ z ∈ U, ∀ t : ℝ, 2 / 3 ≤ t → G t (Φ (z, 0)) = Φ (z, t + g z)) ∧
      (∀ s t : ℝ, G t (Φ (0, s)) = Φ (0, s + t)) ∧
      ∃ Ω : PartialDiffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, B) (E × ℝ) M ∞,
        Ω.source = U ×ˢ univ ∧ Ω.target = Φ.target ∧
        (∀ y ∈ Ω.target, V' y =
          FlowConstruction.partialChartField Ω.symm (fun _ : E × ℝ => (0, 1)) y) ∧
        (∀ p, p.2 ≤ 1 / 3 → Ω p = Φ p) ∧
        (∀ p, 2 / 3 ≤ p.2 → Ω p = Φ (p.1, p.2 + g p.1)) ∧
        (∀ t : ℝ, Ω (0, t) = Φ (0, t)) ∧
        ∀ z ∈ U, ∀ t : ℝ, Ω (z, t) = G t (Φ (z, 0)) := by
  obtain ⟨K, C, g, W, F, -, hKU, hC, hCsub, hg, -, hgerm, hg0, hW,
    hWbase, hWpos, hWfix, hF, hFbase, hleft, hright, haxis, ⟨Cdata⟩⟩ :=
    exists_compact_phase_flow hv hv0 hU h0U
  have hCsource : C ⊆ Φ.source := by
    rw [hsource]
    exact fun p hp => ⟨hKU (hCsub hp).1, mem_univ _⟩
  obtain ⟨ρ, hρ, hρpos, hV', hnew, hzeros, hneg, hρgerm⟩ :=
    exists_native_positive_cylinder_rescaling Φ V hV hmodel W hW hWbase
      (fun p => (by norm_num : (0 : ℝ) < 1 / 2).trans (hWpos p)) hC hCsource hWfix
  let V' : (x : M) → TangentSpace 𝓘(ℝ, B) x := fun x => ρ x • V x
  let N := Φ '' C
  have hN : IsCompact N := hC.image_of_continuousOn (Φ.contMDiffOn_toFun.continuousOn.mono hCsource)
  have hNsub : N ⊆ Φ.target ∩ Φ '' (U ×ˢ Ioo (0 : ℝ) 1) := by
    rintro x ⟨p, hp, rfl⟩
    exact ⟨Φ.map_source' (hCsource hp), ⟨p, ⟨hKU (hCsub hp).1, (hCsub hp).2⟩, rfl⟩⟩
  have hV'₁ := hV'.of_le (show (1 : WithTop ℕ∞) ≤ ∞ by simp)
  let G := FlowConstruction.compactFlow hV'₁
  have hG (x : M) : IsMIntegralCurve (fun t => G t x) V' :=
    FlowConstruction.isMIntegralCurve_compactFlow hV'₁ x
  have hstay (p : E × ℝ) (hp : p ∈ Φ.source) (t : ℝ) : F t p ∈ Φ.source := by
    rw [hsource] at hp ⊢
    exact ⟨(hFbase p t) ▸ hp.1, mem_univ _⟩
  have hfull (p : E × ℝ) (hp : p ∈ Φ.source) (t : ℝ) : G t (Φ p) = Φ (F t p) :=
    FlowSuspension.native_chart_flow_all_time Φ hV'₁ G hG F W hF hnew (hstay p hp) t
  have hnew' (y : M) (hy : y ∈ Φ.target) : V' y =
      FlowConstruction.partialChartField Φ.symm (FlowSuspension.suspensionField Cdata.chart) y := by
    exact (hnew y hy).trans
      (congrArg (fun w => FlowConstruction.partialChartField Φ.symm w y) Cdata.field_eq)
  obtain ⟨Ω, hΩsource, hΩtarget, hΩmap, hΩfield⟩ :=
    FlowSuspension.exists_native_cylinder_conjugacy Φ hsource Cdata.chart
      (fun p => by rw [Cdata.base]) V' hnew'
  have hΩlower (p : E × ℝ) (hp : p.2 ≤ 1 / 3) : Ω p = Φ p := by
    rw [hΩmap, Cdata.lower p hp]
  have hΩupper (p : E × ℝ) (hp : 2 / 3 ≤ p.2) : Ω p = Φ (p.1, p.2 + g p.1) := by
    rw [hΩmap, Cdata.upper p hp]
  have hΩaxis (t : ℝ) : Ω (0, t) = Φ (0, t) := by rw [hΩmap, Cdata.axis]
  have hΩflow (z : E) (hz : z ∈ U) (t : ℝ) : Ω (z, t) = G t (Φ (z, 0)) := by
    have h0 : (z, (0 : ℝ)) ∈ Φ.source := by rw [hsource]; exact ⟨hz, mem_univ _⟩
    have hC0 : Cdata.chart (z, (0 : ℝ)) = (z, 0) := Cdata.lower _ (by norm_num)
    have hFt : F t (z, 0) = Cdata.chart (z, t) := by
      calc
        F t (z, 0) = FlowSuspension.suspensionFlow Cdata.chart t (z, 0) :=
          congrArg (fun A : Flow ℝ (E × ℝ) => A t (z, 0)) Cdata.flow_eq
        _ = FlowSuspension.suspensionFlow Cdata.chart t (Cdata.chart (z, 0)) :=
          congrArg (FlowSuspension.suspensionFlow Cdata.chart t) hC0.symm
        _ = Cdata.chart (z, 0 + t) := FlowSuspension.suspensionFlow_chart Cdata.chart t (z, 0)
        _ = Cdata.chart (z, t) := by rw [zero_add]
    rw [hΩmap]
    exact ((hfull (z, 0) h0 t).trans (congrArg Φ hFt)).symm
  refine ⟨N, g, V', G, hN, hNsub, hg, hgerm, hg0, hV', hG, hzeros, hneg,
    ?_, native_flow_time_change_orbits hρ.continuous hρpos hV'₁ H G hH hG, ?_, ?_, ?_,
    Ω, hΩsource, hΩtarget, hΩfield, hΩlower, hΩupper, hΩaxis, hΩflow⟩
  · intro x hx
    filter_upwards [hρgerm x hx] with y hy
    simp only [V', hy, one_smul]
  · intro z hz t ht
    have hp : (z, (0 : ℝ)) ∈ Φ.source := by rw [hsource]; exact ⟨hz, mem_univ _⟩
    rw [hfull _ hp, hleft z t ht]
  · intro z hz t ht
    have hp : (z, (0 : ℝ)) ∈ Φ.source := by rw [hsource]; exact ⟨hz, mem_univ _⟩
    rw [hfull _ hp, hright z t ht]
  · intro s t
    have hp : ((0 : E), s) ∈ Φ.source := by rw [hsource]; exact ⟨h0U, mem_univ _⟩
    rw [hfull _ hp, haxis]

end Wikipedia.HopfProblem.DegreeCollapse.FlowTimeChange
