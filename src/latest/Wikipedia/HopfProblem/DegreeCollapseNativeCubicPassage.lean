import Wikipedia.HopfProblem.DegreeCollapseBandResidence
import Wikipedia.HopfProblem.DegreeCollapseNativeFieldResidence
import Wikipedia.HopfProblem.DegreeCollapseNativeCubicFieldCancellation

/-!
# Actual native cubic field cancellation with uniform finite band passage

The cutoff is constructed inside the no-return inner neighborhood, while
the field formula holds on the entire original chart. The polynomial
Lyapunov function bounds residence on the supplied compact outer chart
region. Thus the field replacement both removes exactly the two original
zeros and has uniformly bounded residence in the full critical band.
-/

noncomputable section

open Set Function Manifold Filter
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]

/-- Native cubic cancellation with a constructed finite band residence bound. -/
theorem exists_native_cubic_field_finite_passage {m : ℕ} (σ : Fin m → ℝ)
    (hσ : ∀ i, σ i ≠ 0) {a : ℝ} (ha : 0 < a)
    (Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞)
    (haxis : Icc (-a) a ×ˢ {(0 : Fin m → ℝ)} ⊆ Φ.source)
    {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hmodel : ∀ x ∈ Φ.target, V x = nativeCubicDescent σ Φ (-(a ^ 2)) x)
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    {c d : ℝ} {N U : Set M} (hN : IsOpen N) (hNU : N ⊆ U)
    (haxisN : ∀ s ∈ Icc (-a) a, Φ (s, 0) ∈ N)
    {C : Set (Model m)} (hC : IsCompact C) (hCΦ : C ⊆ Φ.source)
    (hUC : U ⊆ Φ '' C)
    (hneg : ∀ x, f x ∈ Icc c d → x ∉ N → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hnoreturn : ∀ x ∈ N, ∀ t : ℝ, 0 ≤ t → F t x ∈ N →
      ∀ s ∈ Icc (0 : ℝ) t, F s x ∈ U) :
    ∃ (K : Set M) (V' : (x : M) → TangentSpace 𝓘(ℝ, E) x),
      IsCompact K ∧ K ⊆ N ∧
      ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
        (fun x => (⟨x, V' x⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
      (∀ x, V' x = 0 ↔ V x = 0 ∧ x ≠ Φ (a, 0) ∧ x ≠ Φ (-a, 0)) ∧
      (∀ x ∉ K, ∀ᶠ y in 𝓝 x, V' y = V y) ∧
      ∃ T : ℝ, 0 < T ∧ ∀ γ : ℝ → M, IsMIntegralCurve γ V' →
        ∃ t ∈ Icc (0 : ℝ) T, f (γ t) ∉ Icc c d := by
  obtain ⟨φ, hφ, hc, hsupp, hsuppN, hrange, hone, V', hV', heq, hzero, hkeep⟩ :=
    exists_native_cubic_field_cancellation_in σ hσ ha Φ haxis V hV hmodel hN haxisN
  have hK : IsCompact (Φ '' tsupport φ) :=
    hc.image_of_continuousOn (Φ.contMDiffOn_toFun.continuousOn.mono hsupp)
  obtain ⟨T₀, hT₀, hres⟩ := exists_native_cancelledDescent_residence_bound σ hσ ha Φ hφ
    (fun p => (hrange p).1) hone hC hCΦ (fun x hx => heq x (by
      obtain ⟨z, hz, rfl⟩ := hx
      exact Φ.map_source' (hCΦ hz)))
  have hinner : ∃ T : ℝ, 0 < T ∧ ∀ γ : ℝ → M, IsMIntegralCurve γ V' →
      ∃ t ∈ Icc (0 : ℝ) T, γ t ∉ U := by
    refine ⟨T₀, hT₀, ?_⟩
    intro γ hγ
    obtain ⟨t, ht, hout⟩ := hres γ hγ
    exact ⟨t, ht, fun h => hout (hUC h)⟩
  refine ⟨Φ '' tsupport φ, V', hK, hsuppN, hV', hzero, hkeep, ?_⟩
  exact FlowCancellation.exists_perturbed_band_residence hf hV hV' F hcurve
    hK.isClosed hN hsuppN hNU (fun x hx => (hkeep x hx).self_of_nhds)
    hneg hnoreturn hinner

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
