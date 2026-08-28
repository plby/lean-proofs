import Wikipedia.SmoothSixDPoincare.RegularBandFlow

/-!
# Exact height translation through a regular band

Scalar ODE uniqueness compares the constructed height trajectory with a
linear function. The comparison is made on a slightly larger open interval,
so the result includes both closed endpoints of the regular band.
-/

noncomputable section

open Set Manifold
open scoped ContDiff Topology

namespace Wikipedia.SmoothSixDPoincare.FlowConstruction

/-- An open neighborhood of a closed interval contains a slightly enlarged open interval. -/
theorem exists_enlarged_interval {a b : ℝ} (hab : a ≤ b) {W : Set ℝ}
    (hW : IsOpen W) (hIW : Icc a b ⊆ W) :
    ∃ l u : ℝ, l < a ∧ b < u ∧ Ioo l u ⊆ W := by
  obtain ⟨l, r, hla, hL⟩ := mem_nhds_iff_exists_Ioo_subset.mp
    (hW.mem_nhds (hIW ⟨le_rfl, hab⟩))
  obtain ⟨s, u, hbu, hR⟩ := mem_nhds_iff_exists_Ioo_subset.mp
    (hW.mem_nhds (hIW ⟨hab, le_rfl⟩))
  refine ⟨l, u, hla.1, hbu.2, ?_⟩
  intro y hy
  by_cases hya : y < a
  · exact hL ⟨hy.1, hya.trans hla.2⟩
  by_cases hby : b < y
  · exact hR ⟨hbu.1.trans hby, hy.2⟩
  exact hIW ⟨le_of_not_gt hya, le_of_not_gt hby⟩

/-- A scalar trajectory has exact unit speed between any two heights in the closed unit plateau. -/
theorem scalar_height_translation {φ γ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    {W : Set ℝ} (hW : IsOpen W) {a b c t : ℝ} (hIW : Icc a b ⊆ W)
    (hφW : EqOn φ (fun _ => 1) W)
    (hγ : ∀ s, HasDerivAt γ (φ (γ s)) s) (hγ₀ : γ 0 = c)
    (hc : c ∈ Icc a b) (ht : c + t ∈ Icc a b) : γ t = c + t := by
  obtain ⟨l, u, hl, hu, hlu⟩ := exists_enlarged_interval (hc.1.trans hc.2) hW hIW
  let V : (x : ℝ) → TangentSpace 𝓘(ℝ, ℝ) x :=
    fun x => (NormedSpace.fromTangentSpace x).symm (φ x)
  have hV : ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).tangent) 1
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) :=
    contMDiff_vectorSpace_iff_contDiff.mpr (hφ.of_le (by simp))
  have hactual : IsMIntegralCurveOn γ V (Ioo (l - c) (u - c)) := by
    intro s hs
    exact (hγ s).hasFDerivAt.hasMFDerivAt.hasMFDerivWithinAt
  have hlinear : IsMIntegralCurveOn (fun s => c + s) V (Ioo (l - c) (u - c)) := by
    intro s hs
    have hcs : c + s ∈ W := hlu ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have hd : HasDerivAt (fun r => c + r) (φ (c + s)) s := by
      rw [hφW hcs]
      exact (hasDerivAt_id s).const_add c
    exact hd.hasFDerivAt.hasMFDerivAt.hasMFDerivWithinAt
  have hzero : (0 : ℝ) ∈ Ioo (l - c) (u - c) :=
    ⟨by linarith [hc.1], by linarith [hc.2]⟩
  have htime : t ∈ Ioo (l - c) (u - c) :=
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  exact isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless hzero hV hactual hlinear
    (by simpa only [add_zero] using hγ₀) htime

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]

/-- A regular band has a constructed flow that translates the height exactly within the band. -/
theorem exists_heightTranslatingFlow {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ}
    (hband : ∀ x, f x ∈ Icc a b → x ∉ ManifoldMorse.criticalPoints E f) :
    ∃ F : Flow ℝ M, ∀ x t, f x ∈ Icc a b → f x + t ∈ Icc a b →
      f (F t x) = f x + t := by
  obtain ⟨φ, W, F, hφ, hW, hIW, hφW, hF⟩ := exists_regularBandFlow hf hband
  refine ⟨F, ?_⟩
  intro x t hx ht
  exact scalar_height_translation hφ hW hIW hφW (hF x)
    (by simp only [Flow.map_zero_apply]) hx ht

end Wikipedia.SmoothSixDPoincare.FlowConstruction
