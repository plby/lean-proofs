import Wikipedia.HopfProblem.DegreeCollapseAxisTransitionData
import Wikipedia.HopfProblem.DegreeCollapseShearedFrameJoin
import Wikipedia.HopfProblem.DegreeCollapseAxisGermCorrection
import Wikipedia.SmoothSixDPoincare.ShearedTubularChart

/-!
# A genuine tubular chart retaining both full native endpoint charts

The derivative blocks are extracted from the actual native transitions.
A same-component frame join and two flat nonlinear corrections yield a
single local diffeomorphism along the compact axis. Compact injectivity then
constructs one partial chart with a positive fiber radius. Both complete
endpoint chart germs, not just their values or derivatives, are retained.
-/

noncomputable section

open Set Filter Function Module Manifold
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.AxisCoordinates

variable {V E M ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [Finite ι] [Nontrivial ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

/-- Join two original endpoint charts along a supplied native tube, retaining full germs. -/
theorem exists_native_axis_chart_with_endpoint_germs (basis : Basis ι ℝ V)
    (Ψ Φ₀ Φ₁ : PartialDiffeomorph 𝓘(ℝ, ℝ × V) 𝓘(ℝ, E) (ℝ × V) M ∞)
    {p q : ℝ} (hpq : p < q) {K : Set ℝ} (hK : IsCompact K) (hzero : K ×ˢ {(0 : V)} ⊆ Ψ.source)
    (hΨ₀ : (p, (0 : V)) ∈ Ψ.source) (hΨ₁ : (q, (0 : V)) ∈ Ψ.source)
    (hΦ₀ : (p, (0 : V)) ∈ Φ₀.source) (hΦ₁ : (q, (0 : V)) ∈ Φ₁.source)
    (haxis₀ : (fun s : ℝ => Φ₀ (s, 0)) =ᶠ[𝓝 p] (fun s => Ψ (s, 0)))
    (haxis₁ : (fun s : ℝ => Φ₁ (s, 0)) =ᶠ[𝓝 q] (fun s => Ψ (s, 0)))
    (hsign : 0 <
      (transverseBlock (fderiv ℝ (Ψ.symm ∘ Φ₀) (p, 0))).toLinearMap.det *
      (transverseBlock (fderiv ℝ (Ψ.symm ∘ Φ₁) (q, 0))).toLinearMap.det) :
    ∃ ε : ℝ, 0 < ε ∧
      ∃ Φ : PartialDiffeomorph 𝓘(ℝ, ℝ × V) 𝓘(ℝ, E) (ℝ × V) M ∞,
        K ×ˢ Metric.closedBall (0 : V) ε ⊆ Φ.source ∧ Φ.target ⊆ Ψ.target ∧
        (∀ s : ℝ, Φ (s, 0) = Ψ (s, 0)) ∧
        ((Φ : (ℝ × V) → M) =ᶠ[𝓝 (p, (0 : V))] Φ₀) ∧
        ((Φ : (ℝ × V) → M) =ᶠ[𝓝 (q, (0 : V))] Φ₁) := by
  let R₀ := Φ₀.trans Ψ.symm
  let R₁ := Φ₁.trans Ψ.symm
  obtain ⟨U₀, hU₀, h0U, hs₀, hx₀, ha₀, ht₀, -, hb₀⟩ :=
    exists_native_axis_transition_data Φ₀ Ψ hΦ₀ hΨ₀ haxis₀
  obtain ⟨U₁, hU₁, h1U, hs₁, hx₁, ha₁, ht₁, -, hb₁⟩ :=
    exists_native_axis_transition_data Φ₁ Ψ hΦ₁ hΨ₁ haxis₁
  obtain ⟨A, T, hA, hT, -, hinv, hA₀, hA₁, hT₀, hT₁⟩ :=
    exists_smooth_sheared_frame_join_at basis hpq ha₀ ha₁ ht₀ ht₁ hU₀ hU₁ h0U h1U hsign
  let H := FrameField.shearedMap A T
  have hH : ContDiff ℝ ∞ H :=
    (contDiff_fst.add ((hA.comp contDiff_fst).clm_apply contDiff_snd)).prodMk
      ((hT.comp contDiff_fst).clm_apply contDiff_snd)
  have hHd (s : ℝ) : fderiv ℝ H (s, (0 : V)) = FrameField.shearedBlock (A s) (T s) :=
    (FrameField.hasFDerivAt_shearedMap_zero
      (hA.differentiable (by simp) s) (hT.differentiable (by simp) s)).fderiv
  have hv₀ : (fun s : ℝ => R₀ (s, (0 : V))) =ᶠ[𝓝 p] (fun s => H (s, 0)) := by
    filter_upwards [hU₀.mem_nhds h0U] with s hs
    exact (hx₀ s hs).trans (FrameField.shearedMap_zero A T s).symm
  have hv₁ : (fun s : ℝ => R₁ (s, (0 : V))) =ᶠ[𝓝 q] (fun s => H (s, 0)) := by
    filter_upwards [hU₁.mem_nhds h1U] with s hs
    exact (hx₁ s hs).trans (FrameField.shearedMap_zero A T s).symm
  have hd₀ : (fun s : ℝ => fderiv ℝ R₀ (s, (0 : V))) =ᶠ[𝓝 p]
      (fun s => fderiv ℝ H (s, 0)) := by
    filter_upwards [hU₀.mem_nhds h0U, hA₀, hT₀] with s hs ha ht
    change fderiv ℝ (Ψ.symm ∘ Φ₀) (s, 0) = _
    rw [hb₀ s hs, hHd s, ha, ht]
  have hd₁ : (fun s : ℝ => fderiv ℝ R₁ (s, (0 : V))) =ᶠ[𝓝 q]
      (fun s => fderiv ℝ H (s, 0)) := by
    filter_upwards [hU₁.mem_nhds h1U, hA₁, hT₁] with s hs ha ht
    change fderiv ℝ (Ψ.symm ∘ Φ₁) (s, 0) = _
    rw [hb₁ s hs, hHd s, ha, ht]
  obtain ⟨G, hG, hvG, hdG, hg₀, hg₁⟩ := exists_axis_germ_correction hpq hH
    R₀.contMDiffOn_toFun.contDiffOn R₁.contMDiffOn_toFun.contDiffOn
    R₀.open_source R₁.open_source (hs₀ p h0U) (hs₁ q h1U) hv₀ hv₁ hd₀ hd₁
  have hGaxis (s : ℝ) : G (s, (0 : V)) = (s, 0) :=
    (hvG s).trans (FrameField.shearedMap_zero A T s)
  have hGi : InjOn G (K ×ˢ {(0 : V)}) := by
    rintro ⟨s, z⟩ ⟨hs, hz⟩ ⟨t, w⟩ ⟨ht, hw⟩ heq
    have hz0 : z = 0 := hz
    have hw0 : w = 0 := hw
    subst z
    subst w
    simpa only [hGaxis] using heq
  have hGl : ∀ p ∈ K ×ˢ {(0 : V)},
      IsLocalDiffeomorphAt 𝓘(ℝ, ℝ × V) 𝓘(ℝ, ℝ × V) ∞ G p := by
    rintro ⟨s, z⟩ ⟨hs, hz⟩
    have hz0 : z = 0 := hz
    subst z
    apply isLocalDiffeomorphAt_of_contMDiffOn isOpen_univ (mem_univ _) hG.contMDiff.contMDiffOn
    rw [mfderiv_eq_fderiv, hdG s, hHd s]
    exact hinv s
  have hGO : K ×ˢ {(0 : V)} ⊆ G ⁻¹' Ψ.source := by
    rintro ⟨s, z⟩ ⟨hs, hz⟩
    have hz0 : z = 0 := hz
    subst z
    change G (s, 0) ∈ Ψ.source
    rw [hGaxis]
    exact hzero ⟨hs, rfl⟩
  obtain ⟨χ, hχzero, hχsub, hχ⟩ := exists_partialDiffeomorph_near_compact
    (hK.prod isCompact_singleton) hGi hGl (Ψ.open_source.preimage hG.continuous) hGO
  let Φ := χ.trans Ψ
  have hΦzero : K ×ˢ {(0 : V)} ⊆ Φ.source := by
    intro p hp
    refine ⟨hχzero hp, ?_⟩
    change χ p ∈ Ψ.source
    rw [hχ]
    exact hχsub (hχzero hp)
  obtain ⟨ε, hε, hprod⟩ :=
    DiskFraming.exists_pos_prod_closedBall_subset hK Φ.open_source hΦzero
  have hformula (p : ℝ × V) : Φ p = Ψ (G p) := by
    change Ψ (χ p) = Ψ (G p)
    rw [hχ]
  refine ⟨ε, hε, Φ, hprod, fun _ hy => hy.1, ?_, ?_, ?_⟩
  · intro s
    rw [hformula, hGaxis]
  · filter_upwards [hg₀, R₀.open_source.mem_nhds (hs₀ p h0U)] with p hp hs
    rw [hformula, hp]
    exact Ψ.right_inv' hs.2
  · filter_upwards [hg₁, R₁.open_source.mem_nhds (hs₁ q h1U)] with p hp hs
    rw [hformula, hp]
    exact Ψ.right_inv' hs.2

end Wikipedia.HopfProblem.DegreeCollapse.AxisCoordinates
