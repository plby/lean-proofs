import Wikipedia.SmoothSixDPoincare.ChartVectorField

/-!
# Smoothness of the original coordinate vector field on its chart target

The fixed tangent-bundle chart is defined above the entire base chart.
Composing the native section with the inverse base chart and this tangent
chart proves smoothness on that whole target, not just at its center.
-/

noncomputable section

open Set Manifold
open scoped ContDiff

namespace Wikipedia.SmoothSixDPoincare.FlowConstruction

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

theorem contDiffOn_coordinateField {v : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hv : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun x => (⟨x, v x⟩ : TangentBundle 𝓘(ℝ, E) M))) (p : M) :
    ContDiffOn ℝ ∞ (coordinateField v p) (chartAt E p).target := by
  let σ : M → TangentBundle 𝓘(ℝ, E) M := fun x => ⟨x, v x⟩
  let e := chartAt E p
  have hs : ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (σ ∘ e.symm) e.target :=
    hv.comp_contMDiffOn (contMDiffOn_chart_symm (I := 𝓘(ℝ, E)) (x := p))
  have hmaps : MapsTo (σ ∘ e.symm) e.target (chartAt (ModelProd E E) (σ p)).source := by
    intro y hy
    exact (TangentBundle.mem_chart_source_iff _ _).mpr (e.map_target hy)
  have hcoords := (contMDiffOn_chart (I := (𝓘(ℝ, E).tangent)) (n := ∞) (x := σ p)).comp
    hs hmaps
  have hnormed := (𝓘(ℝ, E).tangent).contMDiff.comp_contMDiffOn hcoords
  exact hnormed.contDiffOn.snd

end Wikipedia.SmoothSixDPoincare.FlowConstruction
