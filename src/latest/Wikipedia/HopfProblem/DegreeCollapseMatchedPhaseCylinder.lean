import Wikipedia.HopfProblem.DegreeCollapseNativePhaseCylinder
import Wikipedia.HopfProblem.DegreeCollapseNativePhaseRealization

/-!
# Matching both scalar phases in the corrected native cylinder

Use the outgoing transverse chart and phase as full cylinder coordinates.
The difference of the prescribed endpoint phases constructs a compact
positive time change. Its actual native chart has both prescribed exterior
formulas on one transverse neighborhood, while retaining complete orbit
geometry and the entire reference axis.
-/

noncomputable section

open Set Function Filter Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.FlowTimeChange

variable {E Z B M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B]
  [TopologicalSpace M] [ChartedSpace B M] [IsManifold 𝓘(ℝ, B) ∞ M]
  [T2Space M] [CompactSpace M]

theorem exists_native_matched_phase_cylinder
    (Φ Ω : PartialDiffeomorph 𝓘(ℝ, Z × ℝ) 𝓘(ℝ, B) (Z × ℝ) M ∞)
    {U : Set Z} (hsource : Ω.source = U ×ˢ univ)
    (Q : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, Z) E Z ∞)
    (hQtarget : Q.target = U) (hQ0 : (0 : E) ∈ Q.source) (hQzero : Q 0 = 0)
    (P : E → Z) {v₀ v₁ : E → ℝ}
    (hv₀ : ContDiff ℝ ∞ v₀) (hv₁ : ContDiff ℝ ∞ v₁)
    (hv₀zero : v₀ 0 = 0) (hv₁zero : v₁ 0 = 0)
    (V : (x : M) → TangentSpace 𝓘(ℝ, B) x)
    (hV : ContMDiff 𝓘(ℝ, B) (𝓘(ℝ, B).tangent) ∞
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, B) M)))
    (hmodel : ∀ y ∈ Ω.target, V y =
      FlowConstruction.partialChartField Ω.symm (fun _ : Z × ℝ => (0, 1)) y)
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hleft : ∀ p, p.2 ≤ 0 → Ω p = Φ p)
    (hright : ∀ᶠ z in 𝓝 (0 : E), ∀ t : ℝ, 1 ≤ t → Ω (Q z, t) = Φ (P z, t)) :
    ∃ (N : Set M) (W : (x : M) → TangentSpace 𝓘(ℝ, B) x) (G : Flow ℝ M)
      (Ξ : PartialDiffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, B) (E × ℝ) M ∞),
      IsCompact N ∧ N ⊆ Ω.target ∧
      ContMDiff 𝓘(ℝ, B) (𝓘(ℝ, B).tangent) ∞
        (fun x => (⟨x, W x⟩ : TangentBundle 𝓘(ℝ, B) M)) ∧
      (∀ x, IsMIntegralCurve (fun t => G t x) W) ∧
      (∀ x, W x = 0 ↔ V x = 0) ∧
      (∀ (f : M → ℝ) x, mvfderiv 𝓘(ℝ, B) f x (V x) < 0 →
        mvfderiv 𝓘(ℝ, B) f x (W x) < 0) ∧
      (∀ x ∉ N, ∀ᶠ y in 𝓝 x, W y = V y) ∧
      (∀ x, range (fun t => G t x) = range (fun t => F t x) ∧
        (∀ p, Tendsto (fun t => G t x) atTop (𝓝 p) ↔ Tendsto (fun t => F t x) atTop (𝓝 p)) ∧
        ∀ p, Tendsto (fun t => G t x) atBot (𝓝 p) ↔ Tendsto (fun t => F t x) atBot (𝓝 p)) ∧
      Ξ.source = Q.source ×ˢ univ ∧ Ξ.target = Ω.target ∧
      (∀ y ∈ Ξ.target, W y =
        FlowConstruction.partialChartField Ξ.symm (fun _ : E × ℝ => (0, 1)) y) ∧
      (∀ t : ℝ, Ξ (0, t) = Ω (0, t)) ∧
      ∀ᶠ z in 𝓝 (0 : E),
        (∀ t : ℝ, t ≤ -1 → Ξ (z, t) = Φ (Q z, t + v₀ z)) ∧
        (∀ t : ℝ, 2 ≤ t → Ξ (z, t) = Φ (P z, t + v₁ z)) := by
  obtain ⟨Ψ, hΨsource, hΨtarget, hΨmap, hΨmodel⟩ :=
    FlowSuspension.exists_native_phase_cylinder Ω hsource Q hQtarget v₀ hv₀ V hmodel
  let v : E → ℝ := fun z => v₁ z - v₀ z
  have hv : ContDiff ℝ ∞ v := hv₁.sub hv₀
  have hvzero : v 0 = 0 := by simp only [v, hv₁zero, hv₀zero, sub_self]
  obtain ⟨N, g, W, G, hN, hNsub, _, hgerm, _, hW, hG, hzero, hdesc, hfield,
      hgeometry, _, _, _, Ξ, hΞsource, hΞtarget, hΞmodel, hΞleft, hΞright, hΞaxis, _⟩ :=
    exists_native_phase_realization Ψ Q.open_source hQ0 hΨsource V hV hΨmodel F hF hv hvzero
  have hsmall₀ : ∀ᶠ z in 𝓝 (0 : E), v₀ z ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2) :=
    hv₀.continuous.continuousAt.eventually
      (isOpen_Ioo.mem_nhds (by rw [hv₀zero]; constructor <;> norm_num))
  have hsmall₁ : ∀ᶠ z in 𝓝 (0 : E), v₁ z ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2) :=
    hv₁.continuous.continuousAt.eventually
      (isOpen_Ioo.mem_nhds (by rw [hv₁zero]; constructor <;> norm_num))
  refine ⟨N, W, G, Ξ, hN, fun x hx => hΨtarget ▸ (hNsub hx).1,
    hW, hG, hzero, hdesc, hfield, hgeometry, hΞsource, hΞtarget.trans hΨtarget,
    hΞmodel, ?_, ?_⟩
  · intro t
    rw [hΞaxis, hΨmap, hQzero, hv₀zero, add_zero]
  · filter_upwards [hgerm, hright, hsmall₀, hsmall₁] with z hg hr h₀ h₁
    constructor
    · intro t ht
      rw [hΞleft (z, t) (by dsimp; linarith), hΨmap]
      exact hleft (Q z, t + v₀ z) (by dsimp; linarith [h₀.2])
    · intro t ht
      have hclock : t + g z + v₀ z = t + v₁ z := by
        change g z = v₁ z - v₀ z at hg
        rw [hg]
        ring
      rw [hΞright (z, t) (by dsimp; linarith), hΨmap, hclock]
      exact hr (t + v₁ z) (by linarith [h₁.1])

end Wikipedia.HopfProblem.DegreeCollapse.FlowTimeChange
