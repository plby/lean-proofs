import Wikipedia.HopfProblem.DegreeCollapseNativeVerticalReplacement
import Wikipedia.HopfProblem.DegreeCollapseNativeCylinderInvariance
import Wikipedia.HopfProblem.DegreeCollapseNativeHolonomyRealization
import Wikipedia.HopfProblem.DegreeCollapseNativeExteriorFlow
import Wikipedia.HopfProblem.DegreeCollapseNativeSuspensionChart
import Wikipedia.HopfProblem.DegreeCollapseNativeVerticalCylinderFlow

/-!
# Supported holonomy with full native cylinder control

Insert the compact suspension on the entire original flow cylinder.
Coordinate uniqueness proves invariance of the cylinder and its complement,
and every exterior orbit is the original orbit. The local height identity
is needed only on the open slab, where the compact change occurs.
-/

noncomputable section

open Set Function Filter Manifold
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare SupportedDiffeomorph

namespace Wikipedia.HopfProblem.DegreeCollapse.FlowSuspension

variable {E B M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B]
  [TopologicalSpace M] [ChartedSpace B M] [IsManifold 𝓘(ℝ, B) ∞ M]
  [T2Space M] [CompactSpace M]

/-- Realize the supported transition while retaining all exterior orbits,
strict descent, zeros, and the full fixed-axis trajectories. -/
theorem exists_full_cylinder_holonomy
    (Φ : PartialDiffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, B) (E × ℝ) M ∞)
    {U : Set E} (hsource : Φ.source = U ×ˢ univ)
    {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, B) 𝓘(ℝ, ℝ) ∞ f) {c : ℝ}
    (hheight : ∀ p ∈ Φ.source, p.2 ∈ Ioo (0 : ℝ) 1 → f (Φ p) = c - p.2)
    (V : (x : M) → TangentSpace 𝓘(ℝ, B) x)
    (hV : ContMDiff 𝓘(ℝ, B) (𝓘(ℝ, B).tangent) ∞
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, B) M)))
    (hmodel : ∀ x ∈ Φ.target, V x =
      FlowConstruction.partialChartField Φ.symm (fun _ : E × ℝ => (0, 1)) x)
    (H : Flow ℝ M) (hH : ∀ x, IsMIntegralCurve (fun t => H t x) V)
    (D : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞) {K S : Set E}
    (hK : IsCompact K) (hKU : K ⊆ U) (I : SupportedRelativeIsotopy D K S) :
    ∃ (N : Set M) (V' : (x : M) → TangentSpace 𝓘(ℝ, B) x) (G : Flow ℝ M),
      IsCompact N ∧ N ⊆ Φ.target ∩ f ⁻¹' Ioo (c - 1) c ∧
      ContMDiff 𝓘(ℝ, B) (𝓘(ℝ, B).tangent) ∞
        (fun x => (⟨x, V' x⟩ : TangentBundle 𝓘(ℝ, B) M)) ∧
      (∀ x, IsMIntegralCurve (fun t => G t x) V') ∧
      (∀ x, V' x = 0 ↔ V x = 0) ∧
      (∀ x, mvfderiv 𝓘(ℝ, B) f x (V x) < 0 → mvfderiv 𝓘(ℝ, B) f x (V' x) < 0) ∧
      (∀ x ∉ N, ∀ᶠ y in 𝓝 x, V' y = V y) ∧
      (∀ x ∈ Φ.target, ∀ t, G t x ∈ Φ.target) ∧
      (∀ x ∉ Φ.target, ∀ t, G t x = H t x) ∧
      (∀ x ∈ U, G 1 (Φ (x, 0)) = Φ (D x, 1)) ∧
      (∀ x ∈ U ∩ S, ∀ s t : ℝ, G t (Φ (x, s)) = Φ (x, s + t)) ∧
      ∃ Ω : PartialDiffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, B) (E × ℝ) M ∞,
        Ω.source = U ×ˢ univ ∧ Ω.target = Φ.target ∧
        (∀ y ∈ Ω.target, V' y =
          FlowConstruction.partialChartField Ω.symm (fun _ : E × ℝ => (0, 1)) y) ∧
        (∀ p, p.2 ≤ 0 → Ω p = Φ p) ∧
        (∀ p, 1 ≤ p.2 → Ω p = Φ (D p.1, p.2)) ∧
        (∀ z ∈ U, ∀ t : ℝ, Ω (z, t) = G t (Φ (z, 0))) ∧
        (∀ z ∈ U, ∃ w ∈ U, Ω (z, 1) = Φ (w, 1)) ∧
        (∀ z ∈ U, ∀ t : ℝ, t ≤ 0 → G t (Φ (z, 0)) = H t (Φ (z, 0))) ∧
        (∀ z ∈ U, ∀ t : ℝ, 0 ≤ t → G t (Ω (z, 1)) = H t (Ω (z, 1))) := by
  obtain ⟨W, F, hW, hWheight, -, hsupp, hF, hFend, -, hFoutside, hFfixed, ⟨Cdata⟩⟩ :=
    exists_compact_isotopy_suspension D hK I
  let C : Set (E × ℝ) := K ×ˢ Icc (1 / 3 : ℝ) (2 / 3)
  have hC : IsCompact C := hK.prod isCompact_Icc
  have hCsource : C ⊆ Φ.source := by
    rw [hsource]
    exact fun p hp => ⟨hKU hp.1, mem_univ _⟩
  have hWfix (p : E × ℝ) (hp : p ∉ C) : W p = (0, 1) := by
    have hn : p ∉ tsupport (fun z : E × ℝ => W z - (0, 1)) := fun h => hp (hsupp h)
    have hh := image_eq_zero_of_notMem_tsupport hn
    exact sub_eq_zero.mp hh
  obtain ⟨V', hV', hnew, hzeros, hgerm⟩ :=
    exists_native_vertical_field_replacement Φ V hV hmodel hW hWheight hC hCsource hWfix
  let N := Φ '' C
  have hN : IsCompact N := hC.image_of_continuousOn (Φ.contMDiffOn_toFun.continuousOn.mono hCsource)
  have hslab (p : E × ℝ) (hp : p ∈ C) : p.2 ∈ Ioo (0 : ℝ) 1 := by
    constructor <;> linarith [hp.2.1, hp.2.2]
  have hNsub : N ⊆ Φ.target ∩ f ⁻¹' Ioo (c - 1) c := by
    rintro y ⟨p, hp, rfl⟩
    refine ⟨Φ.map_source' (hCsource hp), ?_⟩
    change f (Φ p) ∈ Ioo (c - 1) c
    rw [hheight p (hCsource hp) (hslab p hp)]
    constructor <;> linarith [(hslab p hp).1, (hslab p hp).2]
  let R := PartialChart.restrictSource Φ (isOpen_univ.prod (isOpen_Ioo : IsOpen (Ioo (0 : ℝ) 1)))
  have hRheight (p : E × ℝ) (hp : p ∈ R.source) : f (R p) = c - p.2 :=
    hheight p hp.1 hp.2.2
  have hnegN (y : M) (hy : y ∈ N) : mvfderiv 𝓘(ℝ, B) f y (V' y) = -1 := by
    rcases hy with ⟨p, hp, rfl⟩
    have hpR : p ∈ R.source := ⟨hCsource hp, mem_univ _, hslab p hp⟩
    rw [hnew (Φ p) (Φ.map_source' (hCsource hp))]
    change mvfderiv 𝓘(ℝ, B) f (R p) (FlowConstruction.partialChartField R.symm W (R p)) = -1
    rw [mvfderiv_native_height_field R hf hRheight W (R.map_source' hpR), hWheight]
  have hV'₁ := hV'.of_le (show (1 : WithTop ℕ∞) ≤ ∞ by simp)
  let G := FlowConstruction.compactFlow hV'₁
  have hG (x : M) : IsMIntegralCurve (fun t => G t x) V' :=
    FlowConstruction.isMIntegralCurve_compactFlow hV'₁ x
  have hstay (p : E × ℝ) (hp : p ∈ Φ.source) (t : ℝ) : F t p ∈ Φ.source := by
    rw [hsource] at hp ⊢
    exact ⟨flow_preserves_base_region F hKU hFoutside hp.1 t, mem_univ _⟩
  have hfull (p : E × ℝ) (hp : p ∈ Φ.source) (t : ℝ) : G t (Φ p) = Φ (F t p) :=
    native_chart_flow_all_time Φ hV'₁ G hG F W hF hnew (hstay p hp) t
  have hinv := native_chart_target_invariant Φ hV'₁ G hG F W hF hnew hstay
  have hcomp := flow_complement_invariant G hinv
  obtain ⟨Ω, hΩsource, hΩtarget, hΩmap, hΩfield, hΩlower, hΩupper⟩ :=
    exists_native_suspension_chart Φ hsource hKU Cdata V' hnew
  have hΩflow (z : E) (hz : z ∈ U) (t : ℝ) : Ω (z, t) = G t (Φ (z, 0)) := by
    have h0 : (z, (0 : ℝ)) ∈ Φ.source := by rw [hsource]; exact ⟨hz, mem_univ _⟩
    have hC0 : Cdata.chart (z, (0 : ℝ)) = (z, 0) := Cdata.lower _ le_rfl
    have hFt : F t (z, 0) = Cdata.chart (z, t) := by
      calc
        F t (z, 0) = suspensionFlow Cdata.chart t (z, 0) :=
          congrArg (fun A : Flow ℝ (E × ℝ) => A t (z, 0)) Cdata.flow_eq
        _ =
            suspensionFlow Cdata.chart t (Cdata.chart (z, 0)) :=
          congrArg (suspensionFlow Cdata.chart t) hC0.symm
        _ = Cdata.chart (z, 0 + t) := suspensionFlow_chart Cdata.chart t (z, 0)
        _ = Cdata.chart (z, t) := by rw [zero_add]
    rw [hΩmap]
    exact ((hfull (z, 0) h0 t).trans (congrArg Φ hFt)).symm
  have hDU : MapsTo D U U := mapsTo_of_fixed_outside D.toEquiv
    (fun z hz => I.endpoint_fixed_outside z (fun h => hz (hKU h)))
  have hΩsection (z : E) (hz : z ∈ U) : ∃ w ∈ U, Ω (z, 1) = Φ (w, 1) :=
    ⟨D z, hDU hz, hΩupper (z, 1) le_rfl⟩
  obtain ⟨hleftTail, hrightTail⟩ := native_corrected_cylinder_tails Φ Ω hsource
    (hΩsource.trans hsource) (hV.of_le (by simp)) hV'₁ hmodel hΩfield H G hH hG
    D hDU hΩlower hΩupper
  refine ⟨N, V', G, hN, hNsub, hV', hG, hzeros, ?_, hgerm, hinv, ?_, ?_, ?_,
    Ω, hΩsource.trans hsource, hΩtarget, hΩfield, hΩlower, hΩupper, hΩflow,
    hΩsection, hleftTail, hrightTail⟩
  · intro x hx
    by_cases hn : x ∈ N
    · rw [hnegN x hn]
      norm_num
    · rw [(hgerm x hn).self_of_nhds]
      exact hx
  · intro x hx t
    have hagree (s : ℝ) : V' (G s x) = V (G s x) :=
      (hgerm (G s x) (fun h => hcomp x hx s (hNsub h).1)).self_of_nhds
    rcases le_total 0 t with ht | ht
    · exact FlowCancellation.native_flow_eq_on_positive_halfline
        (hV.of_le (by simp)) H G hH hG (fun s _ => hagree s) t ht
    · exact FlowCancellation.native_flow_eq_on_negative_halfline
        (hV.of_le (by simp)) H G hH hG (fun s _ => hagree s) t ht
  · intro x hx
    have hp : (x, (0 : ℝ)) ∈ Φ.source := by rw [hsource]; exact ⟨hx, mem_univ _⟩
    rw [hfull _ hp, hFend]
  · intro x hx s t
    have hp : (x, s) ∈ Φ.source := by rw [hsource]; exact ⟨hx.1, mem_univ _⟩
    rw [hfull _ hp, hFfixed x hx.2 s t]

end Wikipedia.HopfProblem.DegreeCollapse.FlowSuspension
