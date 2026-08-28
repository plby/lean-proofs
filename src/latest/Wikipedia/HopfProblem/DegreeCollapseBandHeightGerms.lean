import Wikipedia.HopfProblem.DegreeCollapseBoundaryGermCorrection

/-!
# A strictly descending band height retaining both boundary germs

Directed passage places the entire original closed band in the actual
open crossing basin. Normalized signed times give its initial smooth
height. Two constructed boundary corrections preserve each other's full
germs, and leave strict native descent everywhere in the basin.
-/

noncomputable section

open Set Function Filter Manifold
open scoped Topology ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.FlowCancellation

variable {X : Type*} [TopologicalSpace X]

/-- Uniform directed crossing puts every point of the closed band in both
actual level basins, by the intermediate value theorem along its orbit. -/
theorem band_subset_crossingBasin (F : Flow ℝ X) {f : X → ℝ} (hf : Continuous f)
    {c d T : ℝ} (hT : 0 < T)
    (hforward : ∀ x, f x ≤ d → f (F T x) < c)
    (hbackward : ∀ x, c ≤ f x → d < f (F (-T) x)) :
    f ⁻¹' Icc c d ⊆ crossingBasin F f c d := by
  intro x hx
  have hcont : Continuous (fun t : ℝ => f (F t x)) :=
    hf.comp (F.continuous continuous_id continuous_const)
  constructor
  · obtain ⟨t, -, ht⟩ := intermediate_value_Icc' hT.le hcont.continuousOn
      (show c ∈ Icc (f (F T x)) (f (F 0 x)) from
        ⟨(hforward x hx.2).le, by simpa only [F.map_zero_apply] using hx.1⟩)
    exact ⟨t, ht⟩
  · obtain ⟨t, -, ht⟩ := intermediate_value_Icc' (show -T ≤ (0 : ℝ) by linarith)
      hcont.continuousOn (show d ∈ Icc (f (F 0 x)) (f (F (-T) x)) from
        ⟨by simpa only [F.map_zero_apply] using hx.2, (hbackward x hx.1).le⟩)
    exact ⟨t, ht⟩

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M]
  {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}

/-- Construct a smooth strictly descending height on an open neighborhood
of the entire closed band, retaining the old function's full germs at
both boundary levels. -/
theorem exists_smooth_band_height_germs {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    {c d : ℝ} (hcd : c < d)
    (hc : ∀ x, f x = c → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hd : ∀ x, f x = d → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hcross : ∃ T : ℝ, 0 < T ∧ (∀ x, f x ≤ d → f (F T x) < c) ∧
      ∀ x, c ≤ f x → d < f (F (-T) x)) :
    ∃ (U : Set M) (g : M → ℝ), IsOpen U ∧ f ⁻¹' Icc c d ⊆ U ∧
      ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g U ∧
      (∀ x ∈ U, mvfderiv 𝓘(ℝ, E) g x (V x) < 0) ∧
      ∀ x, f x = c ∨ f x = d → g =ᶠ[𝓝 x] f := by
  let U := crossingBasin F f c d
  let g := flowBandHeight F f c d
  obtain ⟨hU, hg, hgder⟩ := smooth_flowBandHeight hf hV F hcurve hcd hc hd
  obtain ⟨T, hT, hforward, hbackward⟩ := hcross
  have hband : f ⁻¹' Icc c d ⊆ U := band_subset_crossingBasin F hf.continuous hT hforward hbackward
  have hcU : {x | f x = c} ⊆ U := fun x hx =>
    hband (show f x ∈ Icc c d from ⟨by rw [hx], by rw [hx]; exact hcd.le⟩)
  have hdU : {x | f x = d} ⊆ U := fun x hx =>
    hband (show f x ∈ Icc c d from ⟨by rw [hx]; exact hcd.le, by rw [hx]⟩)
  let D (x : M) := mvfderiv 𝓘(ℝ, E) f x (V x)
  have hD : Continuous D := (MorseCancellation.contMDiff_directionalDerivative hf hV).continuous
  have hder (x : M) (t : ℝ) : HasDerivAt (fun s => f (F s x)) (D (F t x)) t :=
    Wikipedia.SmoothSixDPoincare.FlowConstruction.hasDerivAt_comp_integralCurve hf (hcurve x) t
  have hgc (x : M) (hx : f x = c) : g x = f x :=
    (flowBandHeight_lower F hf.continuous hD hder hc hx).trans hx.symm
  have hgd (x : M) (hx : f x = d) : g x = f x :=
    (flowBandHeight_upper F hf.continuous hD hder hc hd hcd (hdU hx) hx).trans hx.symm
  obtain ⟨b, hb, hbneg, hbc, hbd⟩ := exists_boundary_correction_preserving_level
    hU hf hg hV F hcurve hcd.ne hcU hdU inter_subset_left hgc hc (fun x hx => (hgder x hx).2)
  have hbdval (x : M) (hx : f x = d) : b x = f x :=
    (hbd x hx).eq_of_nhds.trans (hgd x hx)
  obtain ⟨k, hk, hkneg, hkd, hkc⟩ := exists_boundary_correction_preserving_level
    hU hf hb hV F hcurve hcd.ne' hdU hcU inter_subset_right hbdval hd hbneg
  refine ⟨U, k, hU, hband, hk, hkneg, ?_⟩
  intro x hx
  rcases hx with hx | hx
  · exact (hkc x hx).trans (hbc x hx)
  · exact hkd x hx

end Wikipedia.HopfProblem.DegreeCollapse.FlowCancellation
