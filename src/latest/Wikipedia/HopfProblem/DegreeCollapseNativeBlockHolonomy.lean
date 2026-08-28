import Wikipedia.HopfProblem.DegreeCollapseCylinderBlockCorrection
import Wikipedia.HopfProblem.DegreeCollapseFullCylinderHolonomy

/-!
# Native realization of the actual transverse block correction

The original endpoint transversality constructs one supported correction
of the common labels. Inserting its retained isotopy gives a new smooth
descending native field and an actual complete flow cylinder. The native
right-section transition has the exact block germ and retains its unique
coordinate-plane intersection on the entire relative-chart domain.
-/

noncomputable section

open Set Function Filter Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare SupportedDiffeomorph

namespace Wikipedia.HopfProblem.DegreeCollapse.FlowSuspension

variable {A B Z E M : Type*}
  [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]

open Classical in
theorem exists_native_block_holonomy
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
    (hQzero : Q 0 = 0) (hPzero : P 0 = 0)
    (hHs : H.source ⊆ Q.source) (hHt : H.target ⊆ P.source)
    (hQU : Q.target ⊆ U) (hPU : P.target ⊆ U)
    (hdiagram : ∀ z ∈ H.source, P (H z) = Q z)
    (htrans : NativeTransversality.At 𝓘(ℝ, A) 𝓘(ℝ, B) 𝓘(ℝ, A × B)
      (fun x : A => H (x, 0)) (fun y : B => (0, y)) 0 0)
    (hunique : ∀ x : A, (x, (0 : B)) ∈ H.source → ((H (x, 0)).1 = 0 ↔ x = 0)) :
    ∃ (L₁ : A ≃L[ℝ] A) (L₂ : B ≃L[ℝ] B) (N : Set M)
      (W : (x : M) → TangentSpace 𝓘(ℝ, E) x) (G : Flow ℝ M)
      (Ω : PartialDiffeomorph 𝓘(ℝ, Z × ℝ) 𝓘(ℝ, E) (Z × ℝ) M ∞),
      IsCompact N ∧ N ⊆ Φ.target ∩ f ⁻¹' Ioo (c - 1) c ∧
      ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
        (fun x => (⟨x, W x⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
      (∀ x, IsMIntegralCurve (fun t => G t x) W) ∧
      (∀ x, W x = 0 ↔ V x = 0) ∧
      (∀ x, mvfderiv 𝓘(ℝ, E) f x (V x) < 0 → mvfderiv 𝓘(ℝ, E) f x (W x) < 0) ∧
      (∀ x ∉ N, ∀ᶠ y in 𝓝 x, W y = V y) ∧
      (∀ x ∉ Φ.target, ∀ t, G t x = F t x) ∧
      Ω.source = U ×ˢ univ ∧ Ω.target = Φ.target ∧
      (∀ y ∈ Ω.target, W y =
        FlowConstruction.partialChartField Ω.symm (fun _ : Z × ℝ => (0, 1)) y) ∧
      (∀ z ∈ U, ∀ t : ℝ, Ω (z, t) = G t (Φ (z, 0))) ∧
      (∀ p, p.2 ≤ 0 → Ω p = Φ p) ∧
      (∀ s t : ℝ, G t (Φ (0, s)) = Φ (0, s + t)) ∧
      (∀ z ∈ U, ∃ w ∈ U, Ω (z, 1) = Φ (w, 1)) ∧
      (∀ z ∈ U, ∀ t : ℝ, t ≤ 0 → G t (Φ (z, 0)) = F t (Φ (z, 0))) ∧
      (∀ z ∈ U, ∀ t : ℝ, 0 ≤ t → G t (Ω (z, 1)) = F t (Ω (z, 1))) ∧
      (∀ x : A, (x, (0 : B)) ∈ H.source → ∀ y ∈ H.target, y.1 = 0 →
        Ω (Q (x, 0), 1) = Φ (P y, 1) → x = 0 ∧ y = 0) ∧
      ∀ᶠ z in 𝓝 (0 : A × B), ∀ t : ℝ, 1 ≤ t →
        Ω (Q z, t) = Φ (P (L₁ z.1, L₂ z.2), t) := by
  obtain ⟨L₁, L₂, D, K, hK, hKU, ⟨I⟩, hD0, hDP, huniq, hgerm⟩ :=
    TransverseGerms.exists_cylinder_block_correction Q P H h0 hH0 hQzero hPzero
      hHs hHt hdiagram htrans hunique
  have hKU' : K ⊆ U := fun z hz => hQU (hKU hz).1
  have h0U : (0 : Z) ∈ U := by
    have hh := hQU (Q.map_source' (hHs h0))
    rwa [hQzero] at hh
  obtain ⟨N, W, G, hN, hNsub, hW, hG, hzero, hdesc, hgerms, _, hout, _, haxis,
      Ω, hΩsource, hΩtarget, hΩfield, hΩlower, hΩupper, hΩflow,
      hΩsection, hleftTail, hrightTail⟩ :=
    exists_full_cylinder_holonomy Φ hsource hf hheight V hV hmodel F hF D hK hKU' I
  refine ⟨L₁, L₂, N, W, G, Ω, hN, hNsub, hW, hG, hzero, hdesc, hgerms, hout,
    hΩsource, hΩtarget, hΩfield, hΩflow, hΩlower, haxis 0 ⟨h0U, rfl⟩,
    hΩsection, hleftTail, hrightTail, ?_, ?_⟩
  · intro x hx y hy hy0 heq
    have hw : D (Q (x, 0)) ∈ P.target := hDP (x, 0) hx
    have hs₁ : (D (Q (x, 0)), (1 : ℝ)) ∈ Φ.source := by
      rw [hsource]
      exact ⟨hPU hw, mem_univ _⟩
    have hs₂ : (P y, (1 : ℝ)) ∈ Φ.source := by
      rw [hsource]
      exact ⟨hPU (P.map_source' (hHt hy)), mem_univ _⟩
    rw [hΩupper _ le_rfl] at heq
    have hlabel : D (Q (x, 0)) = P y :=
      congrArg Prod.fst (Φ.toOpenPartialHomeomorph.injOn hs₁ hs₂ heq)
    have hinv : P.symm (D (Q (x, 0))) = y := by
      rw [hlabel]
      exact P.left_inv' (hHt hy)
    have hx0 : x = 0 := (huniq x hx).mp (by rw [hinv]; exact hy0)
    refine ⟨hx0, ?_⟩
    have hP0 : (0 : A × B) ∈ P.source := by
      have hh := hHt (H.map_source' h0)
      rwa [hH0] at hh
    have hPy : P y = 0 := by
      rw [← hlabel, hx0]
      change D (Q (0 : A × B)) = 0
      rw [hQzero, hD0]
    exact P.toOpenPartialHomeomorph.injOn (hHt hy) hP0 (hPy.trans hPzero.symm)
  · filter_upwards [hgerm] with z hz
    intro t ht
    rw [hΩupper _ ht, hz]

end Wikipedia.HopfProblem.DegreeCollapse.FlowSuspension
