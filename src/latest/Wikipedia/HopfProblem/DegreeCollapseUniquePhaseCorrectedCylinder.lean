import Wikipedia.HopfProblem.DegreeCollapseNativeRelativeIntersection
import Wikipedia.HopfProblem.DegreeCollapseNativeBlockHolonomy
import Wikipedia.HopfProblem.DegreeCollapseCorrectedConnectionUniqueness
import Wikipedia.HopfProblem.DegreeCollapseMatchedPhaseCylinder

/-!
# A corrected native cylinder with both phases and unique connection

The original basin labels and complete-connection uniqueness construct
the relative plane-intersection criterion. Actual native transversality
constructs the supported block correction. Native insertion and positive
phase matching give one new smooth field, its genuine full cylinder,
both exterior formulas, preserved critical germs, and the unique complete
connecting orbit. No corrected field or corrected chart is an input.
-/

noncomputable section

open Set Function Filter Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.FlowSuspension

variable {A B Z E M : Type*}
  [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]

theorem exists_unique_phase_corrected_cylinder
    (Φ : PartialDiffeomorph 𝓘(ℝ, Z × ℝ) 𝓘(ℝ, E) (Z × ℝ) M ∞)
    {U : Set Z} (hsource : Φ.source = U ×ˢ univ)
    {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {c : ℝ}
    (hheight : ∀ p ∈ Φ.source, p.2 ∈ Ioo (0 : ℝ) 1 → f (Φ p) = c - p.2)
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hmodel : ∀ x ∈ Φ.target, V x =
      FlowConstruction.partialChartField Φ.symm (fun _ : Z × ℝ => (0, 1)) x)
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (Q P : PartialDiffeomorph 𝓘(ℝ, A × B) 𝓘(ℝ, Z) (A × B) Z ∞)
    (H : PartialDiffeomorph 𝓘(ℝ, A × B) 𝓘(ℝ, A × B) (A × B) (A × B) ∞)
    (h0 : (0 : A × B) ∈ H.source) (hH0 : H 0 = 0)
    (hQ0 : Q 0 = 0) (hP0 : P 0 = 0)
    (hHs : H.source ⊆ Q.source) (hHt : H.target ⊆ P.source)
    (hQtarget : Q.target = U) (hPtarget : P.target = U)
    (hdiagram : ∀ z ∈ H.source, P (H z) = Q z)
    (htrans : NativeTransversality.At 𝓘(ℝ, A) 𝓘(ℝ, B) 𝓘(ℝ, A × B)
      (fun x : A => H (x, 0)) (fun y : B => (0, y)) 0 0)
    {p q : M}
    (hleftBasin : ∀ z ∈ U, Tendsto (fun t => F t (Φ (z, 0))) atBot (𝓝 q) ↔
      ∃ x : A, (x, (0 : B)) ∈ H.source ∧ Q (x, 0) = z)
    (hrightBasin : ∀ z ∈ U, Tendsto (fun t => F t (Φ (z, 1))) atTop (𝓝 p) ↔
      ∃ y ∈ H.target, y.1 = 0 ∧ P y = z)
    (hold : ∀ x, Tendsto (fun t => F t x) atBot (𝓝 q) →
      Tendsto (fun t => F t x) atTop (𝓝 p) → ∃ t, F t (Φ (0, 0)) = x)
    {v₀ v₁ : (A × B) → ℝ} (hv₀ : ContDiff ℝ ∞ v₀) (hv₁ : ContDiff ℝ ∞ v₁)
    (hv₀zero : v₀ 0 = 0) (hv₁zero : v₁ 0 = 0) :
    ∃ (L₁ : A ≃L[ℝ] A) (L₂ : B ≃L[ℝ] B) (N : Set M)
      (W : (x : M) → TangentSpace 𝓘(ℝ, E) x) (G : Flow ℝ M)
      (Ξ : PartialDiffeomorph 𝓘(ℝ, (A × B) × ℝ) 𝓘(ℝ, E) ((A × B) × ℝ) M ∞),
      IsCompact N ∧ N ⊆ Φ.target ∧
      ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
        (fun x => (⟨x, W x⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
      (∀ x, IsMIntegralCurve (fun t => G t x) W) ∧
      (∀ x, W x = 0 ↔ V x = 0) ∧
      (∀ x, mvfderiv 𝓘(ℝ, E) f x (V x) < 0 → mvfderiv 𝓘(ℝ, E) f x (W x) < 0) ∧
      (∀ x ∉ N, ∀ᶠ y in 𝓝 x, W y = V y) ∧
      Ξ.source = Q.source ×ˢ univ ∧ Ξ.target = Φ.target ∧
      (∀ y ∈ Ξ.target, W y = FlowConstruction.partialChartField Ξ.symm
        (fun _ : (A × B) × ℝ => (0, 1)) y) ∧
      (∀ t : ℝ, Ξ (0, t) = Φ (0, t)) ∧
      (∀ x, Tendsto (fun t => G t x) atBot (𝓝 q) →
        Tendsto (fun t => G t x) atTop (𝓝 p) → ∃ t, G t (Φ (0, 0)) = x) ∧
      ∀ᶠ u in 𝓝 (0 : A × B),
        (∀ t : ℝ, t ≤ -1 → Ξ (u, t) = Φ (Q u, t + v₀ u)) ∧
        (∀ t : ℝ, 2 ≤ t → Ξ (u, t) = Φ (P (L₁ u.1, L₂ u.2), t + v₁ (L₁ u.1, L₂ u.2))) := by
  have hQU : Q.target ⊆ U := fun _ hz => hQtarget ▸ hz
  have hPU : P.target ⊆ U := fun _ hz => hPtarget ▸ hz
  have h0U : (0 : Z) ∈ U := by
    have hh := hQU (Q.map_source' (hHs h0))
    rwa [hQ0] at hh
  have hflow (z : Z) (hz : z ∈ U) (t : ℝ) : Φ (z, t) = F t (Φ (z, 0)) := by
    simpa only [zero_add] using
      (native_vertical_cylinder_flow Φ hsource (hV.of_le (by simp)) hmodel F hF z hz 0 t).symm
  have hrelative := relative_intersection_of_native_unique_connection Φ hsource h0U F hflow
    Q P H h0 hH0 hQ0 hHs hQU hdiagram hleftBasin hrightBasin hold
  obtain ⟨L₁, L₂, N₁, V₁, G₁, Ω, hN₁, hN₁sub, hV₁, hG₁, hzero₁, hdesc₁, hgerm₁,
      hout₁, hΩsource, hΩtarget, hΩfield, hΩflow, hΩleft, haxis₁,
      hΩsection, hleftTail, hrightTail, hsection, hΩright⟩ :=
    exists_native_block_holonomy Φ hsource hf hheight V hV hmodel F hF Q P H h0 hH0
      hQ0 hP0 hHs hHt hQU hPU hdiagram htrans hrelative
  have hunique₁ := corrected_cylinder_unique_connection Φ Ω h0U hsource hΩsource hΩtarget
    F G₁ hflow hΩflow hΩsection hleftTail hrightTail hout₁ Q P hQ0 H.source H.target
    hleftBasin hrightBasin hsection hold
  let L := L₁.prodCongr L₂
  have hv₁L : ContDiff ℝ ∞ (fun u : A × B => v₁ (L u)) := hv₁.comp L.contDiff
  have hv₁L0 : v₁ (L (0 : A × B)) = 0 := by rw [map_zero, hv₁zero]
  obtain ⟨N₂, W, G, Ξ, hN₂, hN₂sub, hW, hG, hzero₂, hdesc₂, hgerm₂, hgeometry,
      hΞsource, hΞtarget, hΞfield, hΞaxis, hΞmatch⟩ :=
    FlowTimeChange.exists_native_matched_phase_cylinder Φ Ω hΩsource Q hQtarget (hHs h0) hQ0
      (fun u => P (L u)) hv₀ hv₁L hv₀zero hv₁L0 V₁ hV₁ hΩfield G₁ hG₁ hΩleft hΩright
  let N := N₁ ∪ N₂
  have hN : IsCompact N := hN₁.union hN₂
  have hNsub : N ⊆ Φ.target := by
    intro x hx
    rcases hx with hx | hx
    · exact (hN₁sub hx).1
    · exact hΩtarget ▸ hN₂sub hx
  have hkeep (x : M) (hx : x ∉ N) : ∀ᶠ y in 𝓝 x, W y = V y := by
    filter_upwards [hgerm₂ x (fun h => hx (Or.inr h)),
      hgerm₁ x (fun h => hx (Or.inl h))] with y h₂ h₁
    exact h₂.trans h₁
  have haxis (t : ℝ) : Ξ (0, t) = Φ (0, t) := by
    rw [hΞaxis, hΩflow 0 h0U t, haxis₁ 0 t, zero_add]
  have hunique : ∀ x, Tendsto (fun t => G t x) atBot (𝓝 q) →
      Tendsto (fun t => G t x) atTop (𝓝 p) → ∃ t, G t (Φ (0, 0)) = x := by
    intro x hbot htop
    obtain ⟨t, ht⟩ := hunique₁ x ((hgeometry x).2.2 q |>.mp hbot)
      ((hgeometry x).2.1 p |>.mp htop)
    have hmem : x ∈ range (fun t => G₁ t (Φ (0, 0))) := ⟨t, ht⟩
    rw [← (hgeometry (Φ (0, 0))).1] at hmem
    exact hmem
  exact ⟨L₁, L₂, N, W, G, Ξ, hN, hNsub, hW, hG,
    fun x => (hzero₂ x).trans (hzero₁ x),
    fun x hx => hdesc₂ f x (hdesc₁ x hx), hkeep,
    hΞsource, hΞtarget.trans hΩtarget, hΞfield, haxis, hunique, hΞmatch⟩

end Wikipedia.HopfProblem.DegreeCollapse.FlowSuspension
