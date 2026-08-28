import Wikipedia.SmoothSixDPoincare.TubularSheetTransition

/-!
# Smooth actual sheet differentials and their disk-tangent components

The full transverse derivative in tubular coordinates has a disk component
as well as the previously constructed normal frame. Both components vary
smoothly on the actual native chart overlap.
-/

noncomputable section

open Set Function
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.StripNormalData

variable {A B Z E M : Type*}
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  {S : Set M} {k : (ℝ × ℝ) → M} (d : StripNormalData A B (E := E) S k)
  (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞)

def sheetBaseFrame (t : ℝ) : A →L[ℝ] (ℝ × ℝ) :=
  (ContinuousLinearMap.fst ℝ (ℝ × ℝ) Z).comp
    ((d.sheetDifferential Ψ t).comp (ContinuousLinearMap.inr ℝ ℝ A))

theorem contDiffOn_sheetDifferential :
    ContDiffOn ℝ ∞ (d.sheetDifferential Ψ)
      {t | StripCoordinates.center t ∈ d.chart.source ∧
        d.chart (StripCoordinates.center t) ∈ Ψ.target} := by
  intro t ht
  have htransition : ContDiffAt ℝ ∞ (Ψ.symm ∘ d.chart) (StripCoordinates.center t) :=
    ((Ψ.contMDiffOn_invFun.contMDiffAt (Ψ.open_target.mem_nhds ht.2)).comp
      (StripCoordinates.center t)
      (d.chart.contMDiffOn_toFun.contMDiffAt (d.chart.open_source.mem_nhds ht.1))).contDiffAt
  have hs : ContDiffAt ℝ ∞ (d.sheetTransition Ψ) (t, 0) :=
    htransition.comp (t, 0) (ContinuousLinearMap.inl ℝ (ℝ × A) B).contDiff.contDiffAt
  have hc : ContDiff ℝ ∞ (fun s : ℝ => (s, (0 : A))) :=
    contDiff_id.prodMk contDiff_const
  exact ((hs.fderiv_right (by simp)).comp t hc.contDiffAt).contDiffWithinAt

theorem contDiffOn_sheetBaseFrame :
    ContDiffOn ℝ ∞ (d.sheetBaseFrame Ψ)
      {t | StripCoordinates.center t ∈ d.chart.source ∧
        d.chart (StripCoordinates.center t) ∈ Ψ.target} :=
  contDiffOn_const.clm_comp ((d.contDiffOn_sheetDifferential Ψ).clm_comp contDiffOn_const)

theorem exists_open_sheetBaseFrame_domain
    (htarget : ∀ t ∈ Icc (0 : ℝ) 1, d.chart (StripCoordinates.center t) ∈ Ψ.target) :
    ∃ U : Set ℝ, IsOpen U ∧ Icc (0 : ℝ) 1 ⊆ U ∧
      ContDiffOn ℝ ∞ (d.sheetBaseFrame Ψ) U := by
  have hc : Continuous (StripCoordinates.center : ℝ → StripCoordinates.Space A B) :=
    (continuous_id.prodMk continuous_const).prodMk continuous_const
  have hO : IsOpen (d.chart.source ∩ d.chart ⁻¹' Ψ.target) :=
    d.chart.contMDiffOn_toFun.continuousOn.isOpen_inter_preimage
      d.chart.open_source Ψ.open_target
  exact ⟨StripCoordinates.center ⁻¹' (d.chart.source ∩ d.chart ⁻¹' Ψ.target),
    hO.preimage hc, fun t ht => ⟨d.line ht, htarget t ht⟩, d.contDiffOn_sheetBaseFrame Ψ⟩

/-- The two computed blocks reconstruct the actual full transverse sheet derivative. -/
theorem sheetDifferential_transverse_eq {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (htarget : d.chart (StripCoordinates.center t) ∈ Ψ.target) (u : A) :
    d.sheetDifferential Ψ t (0, u) = (d.sheetBaseFrame Ψ t u, d.normalFrame Ψ t u) := by
  apply Prod.ext
  · rfl
  · exact congrArg (fun L : A →L[ℝ] Z => L u) (d.normal_sheetDifferential Ψ ht htarget)

end Wikipedia.SmoothSixDPoincare.StripNormalData
