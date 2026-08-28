import Wikipedia.HopfProblem.DegreeCollapseNativeFlowSegment
import Wikipedia.SmoothSixDPoincare.CompactFlow

/-!
# Realizing a supported holonomy correction by the original native field

The complete compact suspension is inserted in a genuine regular-height
tube. Its exact model trajectories remain in that original tube, so native
ODE uniqueness identifies the prescribed endpoint transition and every
fixed-locus segment with the new complete native flow. The zero set,
strict descent, and all exterior field germs are retained.
-/

noncomputable section

open Set Function Filter Manifold
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare SupportedDiffeomorph

namespace Wikipedia.HopfProblem.DegreeCollapse.FlowSuspension

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A flow vertical outside the support preserves every base region
containing that support, by applying its inverse flow to a proposed exit. -/
theorem flow_preserves_base_region (F : Flow ℝ (E × ℝ)) {K U : Set E} (hKU : K ⊆ U)
    (hfix : ∀ x ∉ K, ∀ s t : ℝ, F t (x, s) = (x, s + t))
    {p : E × ℝ} (hp : p.1 ∈ U) (t : ℝ) : (F t p).1 ∈ U := by
  by_contra hout
  have hnotK : (F t p).1 ∉ K := fun h => hout (hKU h)
  have hh := hfix (F t p).1 hnotK (F t p).2 (-t)
  change F (-t) (F t p) = ((F t p).1, (F t p).2 + -t) at hh
  rw [← F.map_add, neg_add_cancel, F.map_zero_apply] at hh
  have he := congrArg (fun z : E × ℝ => z.1) hh
  change p.1 = (F t p).1 at he
  exact hout (he ▸ hp)

variable [FiniteDimensional ℝ E]
  {B M : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B]
  [TopologicalSpace M] [ChartedSpace B M] [IsManifold 𝓘(ℝ, B) ∞ M] [T2Space M] [CompactSpace M]

/-- Construct a smooth native field with the prescribed supported holonomy,
preserving zeros, strict descent, exterior germs, and the entire fixed-axis segment. -/
theorem exists_native_holonomy_realization
    (Φ : PartialDiffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, B) (E × ℝ) M ∞)
    {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, B) 𝓘(ℝ, ℝ) ∞ f) {b : ℝ}
    (hheight : ∀ p ∈ Φ.source, f (Φ p) = b - p.2)
    (V : (x : M) → TangentSpace 𝓘(ℝ, B) x)
    (hV : ContMDiff 𝓘(ℝ, B) (𝓘(ℝ, B).tangent) ∞
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, B) M)))
    (hmodel : ∀ x ∈ Φ.target, V x =
      FlowConstruction.partialChartField Φ.symm (fun _ : E × ℝ => (0, 1)) x)
    (D : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞) {K S U : Set E}
    (hK : IsCompact K) (hKU : K ⊆ U) (hsource : U ×ˢ Icc (0 : ℝ) 1 ⊆ Φ.source)
    (I : SupportedRelativeIsotopy D K S) :
    ∃ (N : Set M) (V' : (x : M) → TangentSpace 𝓘(ℝ, B) x) (G : Flow ℝ M),
      IsCompact N ∧ N ⊆ Φ.target ∩ f ⁻¹' Ioo (b - 1) b ∧
      ContMDiff 𝓘(ℝ, B) (𝓘(ℝ, B).tangent) ∞
        (fun x => (⟨x, V' x⟩ : TangentBundle 𝓘(ℝ, B) M)) ∧
      (∀ x, IsMIntegralCurve (fun t => G t x) V') ∧
      (∀ x, V' x = 0 ↔ V x = 0) ∧
      (∀ x ∈ Φ.target, mvfderiv 𝓘(ℝ, B) f x (V' x) = -1) ∧
      (∀ x, mvfderiv 𝓘(ℝ, B) f x (V x) < 0 → mvfderiv 𝓘(ℝ, B) f x (V' x) < 0) ∧
      (∀ x ∉ N, ∀ᶠ y in 𝓝 x, V' y = V y) ∧
      (∀ x ∈ U, G 1 (Φ (x, 0)) = Φ (D x, 1)) ∧
      ∀ x ∈ U ∩ S, ∀ t ∈ Icc (0 : ℝ) 1, G t (Φ (x, 0)) = Φ (x, t) := by
  obtain ⟨W, F, hW, hWheight, -, hsupp, hFcurve, hFend, hFheight, hFoutside, hFfixed, _⟩ :=
    exists_compact_isotopy_suspension D hK I
  let C : Set (E × ℝ) := K ×ˢ Icc (1 / 3 : ℝ) (2 / 3)
  have hC : IsCompact C := hK.prod isCompact_Icc
  have hCsource : C ⊆ Φ.source := by
    rintro ⟨x, t⟩ ⟨hx, ht⟩
    apply hsource
    exact ⟨hKU hx, ⟨by linarith [ht.1], by linarith [ht.2]⟩⟩
  have hWfix (p : E × ℝ) (hp : p ∉ C) : W p = (0, 1) := by
    have hn : p ∉ tsupport (fun z : E × ℝ => W z - (0, 1)) := fun h => hp (hsupp h)
    have hh := image_eq_zero_of_notMem_tsupport hn
    change W p - (0, 1) = 0 at hh
    exact sub_eq_zero.mp hh
  obtain ⟨V', hV', hnew, hnewheight, hzeros, hgerm⟩ :=
    exists_native_suspension_field Φ hf hheight V hV hmodel hW hWheight hC hCsource hWfix
  let N := Φ '' C
  have hN : IsCompact N := hC.image_of_continuousOn (Φ.contMDiffOn_toFun.continuousOn.mono hCsource)
  have hNsub : N ⊆ Φ.target ∩ f ⁻¹' Ioo (b - 1) b := by
    rintro x ⟨⟨z, t⟩, ht, rfl⟩
    refine ⟨Φ.map_source' (hCsource ht), ?_⟩
    change f (Φ (z, t)) ∈ Ioo (b - 1) b
    rw [hheight (z, t) (hCsource ht)]
    constructor <;> linarith [ht.2.1, ht.2.2]
  have hV'₁ := hV'.of_le (show (1 : WithTop ℕ∞) ≤ ∞ by simp)
  let G := FlowConstruction.compactFlow hV'₁
  have hGcurve (x : M) : IsMIntegralCurve (fun t => G t x) V' :=
    FlowConstruction.isMIntegralCurve_compactFlow hV'₁ x
  have hstay (x : E) (hx : x ∈ U) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      F t (x, 0) ∈ Φ.source := by
    apply hsource
    refine ⟨flow_preserves_base_region F hKU hFoutside (p := (x, 0)) hx t, ?_⟩
    simpa only [hFheight, zero_add] using ht
  refine ⟨N, V', G, hN, hNsub, hV', hGcurve, hzeros, hnewheight, ?_, hgerm, ?_, ?_⟩
  · intro x hx
    by_cases ht : x ∈ Φ.target
    · rw [hnewheight x ht]
      norm_num
    · have hout : x ∉ N := fun h => ht (hNsub h).1
      rw [(hgerm x hout).self_of_nhds]
      exact hx
  · intro x hx
    have hh := native_chart_flow_at_time Φ hV'₁ G hGcurve F W hFcurve hnew zero_lt_one (hstay x hx)
    exact hh.trans (congrArg Φ (hFend x))
  · intro x hx t ht
    rcases ht.1.eq_or_lt with hz | hpos
    · subst t
      rw [G.map_zero_apply]
    · have hstay' (s : ℝ) (hs : s ∈ Icc (0 : ℝ) t) : F s (x, 0) ∈ Φ.source :=
        hstay x hx.1 s ⟨hs.1, hs.2.trans ht.2⟩
      rw [native_chart_flow_at_time Φ hV'₁ G hGcurve F W hFcurve hnew hpos hstay',
        hFfixed x hx.2 0 t, zero_add]

end Wikipedia.HopfProblem.DegreeCollapse.FlowSuspension
